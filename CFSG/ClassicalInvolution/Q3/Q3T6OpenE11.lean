module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEC8
import CFSG.ClassicalInvolution.Q3.TL3S8BE11
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEEta

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section E11


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem mem_centralizerModOdd_of_mem_centralizer {c : G} (hcS : c ∈ (S : Subgroup G))
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) {RL : Subgroup G} (hRL : IsSylow2In RL L)
    (hc : c ∈ Subgroup.centralizer (RL : Set G)) : c ∈ centralizerModOdd ⊤ L :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.mem_centralizerModOdd_of_mem_centralizer hd.toTL3 hcS
    hcL hRL hc

theorem mem_W_of_c19_11b (h11b : C19_11b3) {a : G} (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (haW : a ∈ Subgroup.centralizer (W : Set G)) : a ∈ W := by
  have hd0 := hd.toSec19Data3
  have hcomm := hd0.comm_of_mem
  have hat : a ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp haW t hd.mem_W).symm
  obtain ⟨RL, hRL, w, hw, hc⟩ := hd.exists_mul_eq_of_mem_A haS haC hat
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (hd0.le_centralizer_of_mem hd.mem_W).trans
      (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL)
  have hcS : a * w⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem haS ((S : Subgroup G).inv_mem (hd.hWS hw.1))
  have hcL : a * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hat)
      (Subgroup.inv_mem _ (hWL hw.1))
  have hwW : w ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx w hw.1
  have hmem : a * w⁻¹ ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L :=
    ⟨⟨⟨hcS, Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hw.2)⟩,
      Subgroup.mul_mem _ haW (Subgroup.inv_mem _ hwW)⟩,
      hd.mem_centralizerModOdd_of_mem_centralizer hcS hcL hRL hc⟩
  rw [h11b G K z S W L t V hd, Subgroup.mem_bot] at hmem
  have e : a = w := by
    calc a = a * w⁻¹ * w := by group
      _ = w := by rw [hmem, one_mul]
  rw [e]
  exact hw.1

theorem exists_mul_mem_centralizer_of_comm {s : G} (hsS : s ∈ (S : Subgroup G))
    (hsU : ∀ u ∈ K ⊓ W, s * u = u * s) :
    ∃ c ∈ V, s * c⁻¹ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.exists_mul_mem_centralizer_of_comm hd.toTL3 hsS hsU

theorem inf_centralizer_W_eq (h11b : C19_11b3) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = W := by
  have hcomm := hd.comm_of_mem
  apply le_antisymm
  · rintro s ⟨hsS, hsW⟩
    obtain ⟨c, hcV, hc⟩ := hd.exists_mul_mem_centralizer_of_comm hsS
      (fun u hu => (Subgroup.mem_centralizer_iff.mp hsW u hu.2).symm)
    have hcW : c⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx c (hd.leW hcV))
    have h := hd.mem_W_of_c19_11b h11b ((S : Subgroup G).mul_mem hsS
      ((S : Subgroup G).inv_mem (hd.hWS (hd.leW hcV)))) hc (Subgroup.mul_mem _ hsW hcW)
    have e : s = s * c⁻¹ * c := by group
    rw [e]
    exact W.mul_mem h (hd.leW hcV)
  · exact le_inf hd.hWS fun w hw => Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx w hw

theorem comm_V_of_comm_U {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) (haU : ∀ u ∈ K ⊓ W, a * u = u * a) :
    ∀ v ∈ V, a * v = v * a :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.comm_V_of_comm_U hd.toTL3 haS hat haU

theorem mem_W_of_comm_U (h11b : C19_11b3) {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) (haU : ∀ u ∈ K ⊓ W, a * u = u * a) :
    a ∈ W := by
  have haV := hd.comm_V_of_comm_U haS hat haU
  have haW : a ∈ Subgroup.centralizer (W : Set G) := by
    have h := S1911.mem_centralizer_sup_of (H₁ := K ⊓ W) (H₂ := V)
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (haU u hu).symm)
      (Subgroup.mem_centralizer_iff.mpr fun v hv => (haV v hv).symm)
    rwa [← hd.sup_eq_inf_sup] at h
  exact (hd.inf_centralizer_W_eq h11b).le ⟨haS, haW⟩

end Sec19DataT3

end E11

end CFSG.ClassicalInvolution.Q3.Q3T6
