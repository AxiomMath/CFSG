module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.pair_types (hs : Z2SetR r n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    (hyt : y ≠ t) (hyu : y ≠ u) :
    ∃ Vt Vu : Subgroup Y, IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y)) ∧ y ∈ Vt ∧
      IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y)) ∧ y ∈ Vu ∧
      (Vt = Subgroup.zpowers y ∨ Vt ∈ USet (CoreAssembly.conjClass (tightCore R)) ∨
        (L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
          ⁅Vt, tightCore R⁆ ≤ oddCoreOf (tightCore R))) ∧
      (Vu = Subgroup.zpowers y ∨ Vu ∈ USet (CoreAssembly.conjClass (tightCore R)) ∨
        (L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J ∧ ⁅Vu, J⁆ ≤ oddCoreOf J)) := by
  have hΩ := hs.large.datum.hypOmegaGen
  have hTF := TightLargeHypR.typeRFam hs.large
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hy2 : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    Balance.isPGroup_zpowers_of_mul_self_eq_one hyL.sq
  have key : ∀ {M : Subgroup Y} {z : Y}, M ∈ CoreAssembly.conjClass (tightCore R) →
      IsUniqueInvolution M z → y ≠ z → y ∈ Subgroup.centralizer ({z} : Set Y) →
      ∃ V : Subgroup Y, IsSylow2In V (L ⊓ Subgroup.centralizer ({z} : Set Y)) ∧ y ∈ V ∧
        (V = Subgroup.zpowers y ∨ V ∈ USet (CoreAssembly.conjClass (tightCore R)) ∨
          (L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M ∧ ⁅V, M⁆ ≤ oddCoreOf M)) := by
    intro M z hM hz hyz hyc
    have hNz : Subgroup.centralizer ({z} : Set Y) ≤ Subgroup.normalizer (M : Set Y) :=
      hTF.tight M hM z hz
    have hLtw : L ∉ twinSet (CoreAssembly.conjClass (tightCore R)) M := by
      rintro ⟨-, z', hz'M, hz'L⟩
      exact hyz ((hyL.eq hz'L).trans (hz.eq hz'M).symm)
    obtain ⟨V, hV, hyV⟩ := IsSylow2In.exists_ge hy2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hyL.mem, hyc⟩))
    have hyV' : y ∈ V := hyV (Subgroup.mem_zpowers y)
    refine ⟨V, hV, hyV', ?_⟩
    rcases Sec6Gen.l6_2Gen Y _ hΩ M hM z hz L hL hLtw y hyL V hV hyV' with
      ⟨-, hne⟩ | ⟨hV1, -⟩ | ⟨hVU, -⟩ | ⟨hVR, hcomm⟩
    · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hNz hyc)) hne
    · exact Or.inl hV1
    · exact Or.inr (Or.inl hVU)
    · refine Or.inr (Or.inr ⟨⟨hL, (fun hLM => hyz ?_), V, hVR, hV.1.trans inf_le_left,
        (hV.1.trans inf_le_right).trans hNz⟩, hcomm⟩)
      rw [hLM] at hyL
      exact hyL.eq hz
  obtain ⟨Vt, hVt, hyVt, ht'⟩ := key hK ht hyt hyA.1.2
  obtain ⟨Vu, hVu, hyVu, hu'⟩ := key hs.hJ.1 hs.hu hyu hyA.2
  exact ⟨Vt, Vu, hVt, hyVt, hVu, hyVu, ht', hu'⟩

theorem Z2SetR.innerModOdd_u_of_type4 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1) {V : Subgroup Y} (hyV : y ∈ V)
    (hc : ⁅V, tightCore R⁆ ≤ oddCoreOf (tightCore R)) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y := by
  refine hs.innerModOdd_u_of_cent_R₀ hr hyA.2 hy2 fun q hq => ?_
  have hyq : y * q * y⁻¹ ∈ R₀ := hs.conj_mem_R₀ hyA.1.1 hyA.1.2 hq
  have hcomm : ⁅y, q⁆ ∈ oddCoreOf (tightCore R) :=
    hc (Subgroup.commutator_mem_commutator hyV (hs.hR₀.1 hq))
  have hcommR : ⁅y, q⁆ ∈ R₀ := by
    rw [commutatorElement_def]
    exact R₀.mul_mem hyq (R₀.inv_mem hq)
  have h1 : ⁅y, q⁆ = 1 :=
    aux_eq_one_of_mem_odd (P := P) (odd_natCard_oddCoreOf _) hcomm (hs.hR₀P hcommR)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem Z2SetR.innerModOdd_t_of_type4 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1) {V : Subgroup Y} (hyV : y ∈ V)
    (hc : ⁅V, J⁆ ≤ oddCoreOf J) : InnerModOdd (linkLayer R t) y := by
  refine hs.innerModOdd_t_of_cent_T₀ hr hyA.1.2 hy2 fun q hq => ?_
  have hyq : y * q * y⁻¹ ∈ T₀ := hs.conj_mem_T₀ hyA.1.1 hyA.2 hq
  have hcomm : ⁅y, q⁆ ∈ oddCoreOf J :=
    hc (Subgroup.commutator_mem_commutator hyV (hs.hT₀.1 hq))
  have hcommT : ⁅y, q⁆ ∈ T₀ := by
    rw [commutatorElement_def]
    exact T₀.mul_mem hyq (T₀.inv_mem hq)
  have h1 : ⁅y, q⁆ = 1 :=
    aux_eq_one_of_mem_odd (P := P) (odd_natCard_oddCoreOf _) hcomm (hs.hT₀P hcommT)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
