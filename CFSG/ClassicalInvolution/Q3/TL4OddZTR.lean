module

public import CFSG.ClassicalInvolution.Q3.TL4OddZT
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

section Edge

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem xMem_mul_of_mem_omegaNbr (h : TypeRFam r Ω) {K J : Subgroup G}
    (hJK : J ∈ omegaNbr Ω K) {t u : G} (ht : IsUniqueInvolution K t)
    (hu : IsUniqueInvolution J u) : XMem Ω (t * u) J := by
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp ht hJK hu
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := hJK
  refine ⟨hJΩ, h.tight J hJΩ u hu (Subgroup.mem_centralizer_singleton_iff.mpr ?_),
    T, Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hJΩ hT hTJ, fun x hx => ?_⟩
  · calc t * u * u = u * t * u := by rw [ctu]
      _ = u * (t * u) := by group
  · have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hx))
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu
        (Subgroup.le_normalizer (hTJ hx)))
    calc x * (t * u) = x * t * u := by group
      _ = t * x * u := by rw [hxt]
      _ = t * (x * u) := by group
      _ = t * (u * x) := by rw [hxu]
      _ = t * u * x := by group

theorem xMem_mul_of_mem_omegaNbr' (h : TypeRFam r Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJK : J ∈ omegaNbr Ω K) {t u : G} (ht : IsUniqueInvolution K t)
    (hu : IsUniqueInvolution J u) : XMem Ω (t * u) K := by
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp ht hJK hu
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.hyp hK hJK.1 hJK
  rw [ctu]
  exact xMem_mul_of_mem_omegaNbr h hKJ hu ht

end Edge

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51At_mul_of_edge (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {B : Subgroup Y} (hB : IsElemAbelian 2 B) (htB : t ∈ B)
    (huB : u ∈ B) : Hyp51At B (t * u) := by
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htu : t ≠ u := fun e =>
    hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  have hc1 : t * u ≠ 1 := by
    intro e
    apply htu
    calc t = t * u * u := by rw [mul_assoc, hu.sq, mul_one]
      _ = u := by rw [e, one_mul]
  have hac : t ≠ t * u := by
    intro e
    apply hu.ne_one
    have e' : t * u = t * 1 := by rw [mul_one]; exact e.symm
    exact mul_left_cancel e'
  exact hyp51At_of_twinPair h4 htw hOm hL.below hL.center hL.card.le h hB htB
    (Subgroup.mul_mem _ htB huB) hc1 ht.ne_one hac rfl
    (xMem_mul_of_mem_omegaNbr' h hK₀ hJ ht hu) (xMem_mul_of_mem_omegaNbr h hJ ht hu) ht hu

theorem tightStar289ZTR_of (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR) :
    TightStar289ZTR 3 n := by
  intro Y _ _ R S t hL _ _ _ J K'' u w hF
  exact hyp51At_mul_of_edge h4 htw hOm hL hF.memJ hF.invJ (hF.isElemAbelian hL)
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
