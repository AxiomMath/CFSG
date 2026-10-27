module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenF2
public import CFSG.ClassicalInvolution.Q3.Q3T6FusF1
public import CFSG.ClassicalInvolution.Q3.Q3T6FusConj
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenBP
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEEta

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.Blueprint

section Core


@[expose] def ResidualL3Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT3 K z S W L t V →
      ∀ x ∈ S19B.sec19BPrime K S W L, x ≠ 1 →
        (SectionLieTypeU 3 1 (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
          (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) .PSL 3 ∨
         SectionLieTypeU 3 1 (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
          (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) .PSU 3) →
          FusResidualL3 K z (Subgroup.centralizer ({x} : Set G))

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem exists_conj_eq_t_of_BPrime :
    ∃ g : G, (∀ b ∈ S19B.sec19BPrime K S W L, g * b = b * g) ∧ g * z * g⁻¹ = t :=
  exists_conj_eq_t_of_subgroup3 hd.tight.hypGen hd.tight.edgeless hd.tight.isUniqueInvolution
    hd.tight.centralizer_le_normalizer hd.hW hd.hWS hd.mem_W_z hd.isSylow2In_inf hd.memL hd.invL
    hd.mem_W hd.ne (fun _ hb => hb.1.1.1) (fun _ hb => hb.1.1.2) (fun _ hb => hb.1.2)
    (fun _ hb => hb.2)

theorem exists_conj_eq_of_mem_sec19BPrime3 (hM : Q3.M11Facts)
    (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g) (hL3 : ResidualL3Stmt)
    {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) (hx1 : x ≠ 1) {g : G}
    (hg : g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * z * c⁻¹ = g * z * g⁻¹ := by
  have ht := hd.tight
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxK : x ∈ centralizerModOdd ⊤ K := (hd.mem_sec19BPrime_iff.mp hx).2.1
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.1.2 z hd.mem_W_z)
  obtain ⟨g₀, hg₀, hg₀z⟩ := hd.exists_conj_eq_t_of_BPrime
  have hex : ∃ c₀ : G, c₀ * x = x * c₀ ∧ c₀ * z * c₀⁻¹ ≠ z ∧
      c₀ * z * c₀⁻¹ * z = z * (c₀ * z * c₀⁻¹) := by
    refine ⟨g₀, hg₀ x hx, by rw [hg₀z]; exact hd.ne, ?_⟩
    rw [hg₀z]
    exact hd.comm_of_mem t hd.mem_W z hd.mem_W_z
  exact exists_conj_eq_of_cStar3 (ht.member.toQ3 (by norm_num)) ht.hyp ht.edgeless
    ht.centralizer_le_normalizer ht.nonabelian ht.below le_rfl hM hOut
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)) hx1 hxK hzx hex
    (hL3 G K z S W L t V hd x hx hx1) hg

theorem exists_mem_centralizer_conj_eq3 (hM : Q3.M11Facts)
    (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g) (hL3 : ResidualL3Stmt)
    {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) (hx1 : x ≠ 1) {g : G}
    (hgx : g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * x * d = g⁻¹ * x * g := by
  have hgx' := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have h1 : g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [← hgx']
      _ = x * (g * z * g⁻¹) := by group
  obtain ⟨c, hc, hcz⟩ := hd.exists_conj_eq_of_mem_sec19BPrime3 hM hOut hL3 hx hx1 h1
  have hcx := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * z = c⁻¹ * (g * z * g⁻¹) * g := by group
      _ = c⁻¹ * (c * z * c⁻¹) * g := by rw [hcz]
      _ = z * (c⁻¹ * g) := by group
  · calc (c⁻¹ * g)⁻¹ * x * (c⁻¹ * g) = g⁻¹ * (c * x * c⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [hcx]; group

end Sec19DataT3

theorem c19_11b3_of (hB1 : S19B.GoldschmidtB1Tmp) (hM : Q3.M11Facts)
    (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g) (hL3 : ResidualL3Stmt) :
    C19_11b3 := by
  intro G _ _ _ K z S W L t V hd
  by_contra hne
  have hd0 := hd.toSec19Data3
  have ht := hd.tight
  have hBS : S19B.sec19BPrime K S W L ≤ (S : Subgroup G) := fun x hx => hx.1.1.1
  have hBK : S19B.sec19BPrime K S W L ≤ centralizerModOdd ⊤ K := fun x hx =>
    (hd.mem_sec19BPrime_iff.mp hx).2.1
  have hsc : fusionStronglyClosed (S19B.sec19BPrime K S W L : Set G) (S : Subgroup G) := by
    intro x hx g hg
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    obtain ⟨d, hdz, hdx⟩ := hd.exists_mem_centralizer_conj_eq3 hM hOut hL3 hx hx1 (hd0.hSz hg)
    rw [← hdx] at hg ⊢
    have hdz' : d⁻¹ * z = z * d⁻¹ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hdz)
      exact h
    have h := hd.conj_mem_sec19BPrime hx hdz' (by rwa [inv_inv])
    rwa [inv_inv] at h
  obtain ⟨g, hgB, hgz⟩ := hd.exists_conj_eq_t_of_BPrime
  have hzB : z ∈ Subgroup.centralizer (S19B.sec19BPrime K S W L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hb.1.2 z hd.mem_W_z).symm
  refine false_of_stronglyClosed_cStar hB1 S ht.nonabelian hBS hne hsc
    (ht.member.toQ3 (by norm_num)) ht.hyp ht.edgeless ht.centralizer_le_normalizer hBK hzB
    ⟨g, Subgroup.mem_centralizer_iff.mpr fun b hb => (hgB b hb).symm⟩ ?_ ?_ hM ht.below le_rfl
  · show g * z * g⁻¹ ≠ z
    rw [hgz]
    exact hd.ne
  · show g * z * g⁻¹ * z = z * (g * z * g⁻¹)
    rw [hgz]
    exact hd.comm_of_mem t hd.mem_W z hd.mem_W_z

end Core

end CFSG.ClassicalInvolution.Q3.Q3T6
