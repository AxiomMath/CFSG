module

public import CFSG.ClassicalInvolution.Q3.TL3S8BWeak

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section F2

theorem tight_conj_eq_mul_of_conj_eq_mul {G : Type} [Group G] {x t' z : G}
    (h : x * t' * x⁻¹ = t' * z) (ht2 : t' * t' = 1) (hxz : x * z = z * x) :
    t' * x * t'⁻¹ = x * z := by
  have ht' : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
  have h1 : x * t' = t' * z * x := by
    calc x * t' = x * t' * x⁻¹ * x := by group
      _ = t' * z * x := by rw [h]
  calc t' * x * t'⁻¹ = t' * (x * t') := by rw [ht', mul_assoc]
    _ = t' * (t' * z * x) := by rw [h1]
    _ = (t' * t') * z * x := by group
    _ = z * x := by rw [ht2, one_mul]
    _ = x * z := hxz.symm

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem conj_mem_sec19BPrime {x d : G} (hx : x ∈ S19B.sec19BPrime K S W L)
    (hdz : d * z = z * d) (hdS : d * x * d⁻¹ ∈ (S : Subgroup G)) :
    d * x * d⁻¹ ∈ S19B.sec19BPrime K S W L := by
  have hd0 := hd.toTightSylowData
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd0.comm_of_mem
  have htW : t ∈ W := hd.mem_W
  have hzW : z ∈ W := hd.mem_W_z
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hs))
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := by
    rw [hd.tight.normEq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hdz
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxK : x ∈ centralizerModOdd ⊤ K := (hd.mem_sec19BPrime_iff.mp hx).2.1
  have hyK : d * x * d⁻¹ ∈ centralizerModOdd ⊤ K := by
    have h := S19B.conj_mem_centralizerModOdd_top hxK d
    rwa [mem_normalizer_iff_conjSub_eq.mp hdN] at h
  have hyR := S19B.mem_centralizer_inf_of_mem S hdS hyK
  have hyW : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hd.le_normalizer_W hdS) t).mp htW
  have ht2 : t * t = 1 := hd.invL.sq
  have hyt2 : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) = 1 := by
    calc d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) =
        d * x * d⁻¹ * (t * t) * (d * x * d⁻¹)⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hyt1 : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ ≠ 1 := by
    intro h
    apply hd.invL.ne_one
    calc t = (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by group
      _ = 1 := by rw [h]; group
  rcases hd.invol_mem_W hyW hyt2 hyt1 with h | h | h
  · exfalso
    apply hd.ne
    have hyz : d * x * d⁻¹ * z * (d * x * d⁻¹)⁻¹ = z := by
      rw [hzS _ hdS, mul_assoc, mul_inv_cancel, mul_one]
    calc t = (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by group
      _ = (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * z * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by
          rw [h, hyz]
      _ = z := by group
  · have hyC : d * x * d⁻¹ ∈ Subgroup.centralizer
        (((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hle : (S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t ≤
          Subgroup.centralizer ({d * x * d⁻¹} : Set G) := by
        refine sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hyR r hr)) ?_
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        calc t * (d * x * d⁻¹) = d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹) := by
              rw [h]
          _ = d * x * d⁻¹ * t := by group
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    exact hd.mem_sec19BPrime_of_conj_mem hx hdS
      (hd.le_centralizer_W_of_mem_A (Subgroup.mem_inf.mpr ⟨hdS, hyC⟩))
  · exfalso
    have hxt : x * (d⁻¹ * t * d) * x⁻¹ = d⁻¹ * t * d * z := by
      have hdz' : d⁻¹ * z * d = z := by
        rw [mul_assoc, ← hdz, ← mul_assoc, inv_mul_cancel, one_mul]
      calc x * (d⁻¹ * t * d) * x⁻¹ =
          d⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) * d := by group
        _ = d⁻¹ * t * d * (d⁻¹ * z * d) := by rw [h]; group
        _ = d⁻¹ * t * d * z := by rw [hdz']
    have ht'2 : d⁻¹ * t * d * (d⁻¹ * t * d) = 1 := by
      calc d⁻¹ * t * d * (d⁻¹ * t * d) = d⁻¹ * (t * t) * d := by group
        _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
    have hconj := tight_conj_eq_mul_of_conj_eq_mul hxt ht'2 (hzS x hxS)
    have hzS' : z ∈ (S : Subgroup G) := hd0.hWS hzW
    have hxzS : (d⁻¹ * t * d) * x * (d⁻¹ * t * d)⁻¹ ∈ (S : Subgroup G) := by
      rw [hconj]
      exact (S : Subgroup G).mul_mem hxS hzS'
    have hxzW : (d⁻¹ * t * d) * x * (d⁻¹ * t * d)⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
      rw [hconj]
      refine (Subgroup.centralizer (W : Set G)).mul_mem hx.1.2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hcomm w hw z hzW
    have hxzB := hd.mem_sec19BPrime_of_conj_mem hx hxzS hxzW
    rw [hconj] at hxzB
    have hzB : z ∈ S19B.sec19BPrime K S W L := by
      have := (S19B.sec19BPrime K S W L).mul_mem
        ((S19B.sec19BPrime K S W L).inv_mem hx) hxzB
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have hbot := hd.inf_sec19BPrime_eq_bot
    have hz1 : z ∈ W ⊓ S19B.sec19BPrime K S W L := ⟨hzW, hzB⟩
    rw [hbot, Subgroup.mem_bot] at hz1
    exact hI.ne_one hz1

end TightSylowDataT

end F2

end CFSG.ClassicalInvolution.Q3
