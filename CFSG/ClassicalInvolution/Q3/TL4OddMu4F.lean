module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9V
public import CFSG.ClassicalInvolution.Q3.TL4OddBadW
public import CFSG.ClassicalInvolution.Q3.TL4OddZTR

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

section Edge

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem xMem_of_mem_omegaNbr_gen (h : TypeRFam r Ω) {J K' : Subgroup G}
    (hK'J : K' ∈ omegaNbr Ω J) {u : G} (hu : IsUniqueInvolution J u) : XMem Ω u K' := by
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK'J.1
  have huz : u * z' = z' * u := Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp hu hK'J hz'
  obtain ⟨hK'Ω, -, T, hT, hTK, hTN⟩ := hK'J
  refine ⟨hK'Ω, h.tight K' hK'Ω z' hz' (Subgroup.mem_centralizer_singleton_iff.mpr huz), T,
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hK'Ω hT hTK, fun x hx => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (hTN hx))

end Edge

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51At_of_commonNbr (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hL : TightLargeHypR 3 n Y R S t) {J K' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'₀ : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'J : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u) (hz' : IsUniqueInvolution K' (t * u)) {B : Subgroup Y}
    (hB : IsElemAbelian 2 B) (htB : t ∈ B) (huB : u ∈ B) :
    Hyp51At B t ∧ Hyp51At B u ∧ Hyp51At B (t * u) := by
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp ht hJ hu
  have htu : t ≠ u := fun e => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  refine ⟨?_, ?_, hyp51At_mul_of_edge h4 htw hOm hL hJ hu hB htB huB⟩
  ·
    refine hyp51At_of_twinPair h4 htw hOm hL.below hL.center hL.card.le h hB huB htB ht.ne_one
      hu.ne_one htu.symm ?_ (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hK'₀)
      hu hz'
    calc u * (t * u) = u * (u * t) := by rw [ctu]
      _ = t := by rw [← mul_assoc, hu.sq, one_mul]
  ·
    refine hyp51At_of_twinPair h4 htw hOm hL.below hL.center hL.card.le h hB htB huB
      hu.ne_one ht.ne_one htu ?_ (xMem_of_mem_omegaNbr_nbr h hK₀ hJ ht hu)
      (xMem_of_mem_omegaNbr_gen h hK'J hu) ht hz'
    rw [← mul_assoc, ht.sq, one_mul]

theorem hyp51At_of_noGNbr (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hL : TightLargeHypR 3 n Y R S t) {J K' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J)
    (hK'₀ : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'J : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u) {B : Subgroup Y} (hB : IsElemAbelian 2 B) (htB : t ∈ B)
    (huB : u ∈ B) : Hyp51At B t ∧ Hyp51At B u ∧ Hyp51At B (t * u) := by
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hK'₀.1
  have e : z' = t * u := hbad K' hK'₀ hK'J u z' hu hz'
  rw [e] at hz'
  exact hyp51At_of_commonNbr h4 htw hOm hL hJ hK'₀ hK'J hu hz' hB htB huB

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
