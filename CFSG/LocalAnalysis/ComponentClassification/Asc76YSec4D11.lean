module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D3

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isSylowOf_sup_of_odd_of_le_normalizer {P O : Subgroup G} (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) (hPO : P ≤ normalizer (O : Set G)) : IsSylowOf 2 P (P ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : O ⊓ P = ⊥ := eq_bot_of_isPGroup_of_odd (hP.to_le inf_le_right)
    (hO.of_dvd_nat (card_dvd_of_le inf_le_left))
  rw [isSylowOf_iff]
  refine ⟨le_sup_left, hP, ?_⟩
  have hcard : Nat.card (P ⊔ O : Subgroup G) = Nat.card O * Nat.card P := by
    rw [sup_comm]
    exact card_sup_of_le_normalizer hPO hinf
  have hrel := Subgroup.relIndex_mul_card P (P ⊔ O)
  rw [inf_eq_left.mpr le_sup_left, hcard] at hrel
  have hrelN : P.relIndex (P ⊔ O) = Nat.card O :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  rw [hrelN]
  exact fun h2 => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2)

theorem exists_mem_normalizer_conj_eq (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {A : Set G} {h : G} (hA : ∀ a ∈ A, ∀ w ∈ sec4W Ω S, a * w = w * a)
    (hAh : ∀ a ∈ A, ∀ w ∈ sec4W Ω S, (h⁻¹ * a * h) * w = w * (h⁻¹ * a * h)) :
    ∃ n ∈ normalizer (sec4W Ω S : Set G), ∀ a ∈ A, h⁻¹ * a * h = n⁻¹ * a * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  have hWC : W ≤ centralizer A := fun w hw => mem_centralizer_iff.mpr fun a ha => hA a ha w hw
  set W' := AschbacherTightEmbedding.rightConjugate W h⁻¹ with hW'def
  have hW'C : W' ≤ centralizer A := by
    intro y hy
    rw [hW'def, mem_rightConjugate_iff, inv_inv] at hy
    refine mem_centralizer_iff.mpr fun a ha => ?_
    have h1 := hAh a ha _ hy
    have h2 : h⁻¹ * (a * y) * h = h⁻¹ * (y * a) * h := by
      calc h⁻¹ * (a * y) * h = (h⁻¹ * a * h) * (h⁻¹ * y * h) := by group
        _ = (h⁻¹ * y * h) * (h⁻¹ * a * h) := h1
        _ = h⁻¹ * (y * a) * h := by group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨P, hP, hWP⟩ := exists_isSylowOf_le hW2 hWC
  obtain ⟨P', hP', hW'P'⟩ := exists_isSylowOf_le (hW2.map _ : IsPGroup 2 W') hW'C
  obtain ⟨c, hcC, hc⟩ := L26.IsSylowOf.exists_conj_mem hP hP'
  obtain ⟨S'', hS'', hPS''⟩ := exists_isSylowOf_le hP.isPGroup (le_top : P ≤ ⊤)
  have hconj : AschbacherTightEmbedding.rightConjugate W (h⁻¹ * c) ≤ S'' := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    set w := h⁻¹ * c * x * (h⁻¹ * c)⁻¹ with hw
    have hy : h * w * h⁻¹ ∈ W' := by
      rw [hW'def, mem_rightConjugate_iff, inv_inv]
      have e : h⁻¹ * (h * w * h⁻¹) * h = w := by group
      rw [e]
      exact hx
    have h1 := (hc _).mp (hW'P' hy)
    have e : c⁻¹ * (h * w * h⁻¹) * c = x := by rw [hw]; group
    rw [e] at h1
    exact hPS'' h1
  have hn := rightConjugate_sec4W_eq_of_le hΩ hS hS'' (hWP.trans hPS'') hconj
  refine ⟨(h⁻¹ * c)⁻¹, inv_mem ((rightConjugate_eq_self_iff W _).mp hn), fun a ha => ?_⟩
  have hac : a * c = c * a := mem_centralizer_iff.mp hcC a ha
  calc h⁻¹ * a * h = h⁻¹ * (a * c * c⁻¹) * h := by group
    _ = h⁻¹ * (c * a * c⁻¹) * h := by rw [hac]
    _ = ((h⁻¹ * c)⁻¹)⁻¹ * a * (h⁻¹ * c)⁻¹ := by group

omit [Finite G] in
theorem le_sup_oddCoreIn_of_imgOf_le {X V W : Subgroup G} (hVX : V ≤ X)
    (h : imgOf X V ≤ imgOf X W) : V ≤ W ⊔ oddCoreIn X := by
  intro v hv
  obtain ⟨⟨w, hwX⟩, hw, hwv⟩ :=
    h (mem_map_of_mem _ (show (⟨v, hVX hv⟩ : X) ∈ V.subgroupOf X from hv))
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwv
  have hmem : w⁻¹ * v ∈ oddCoreIn X := ⟨_, hwv, by simp⟩
  have e : v = w * (w⁻¹ * v) := by group
  rw [e]
  exact mul_mem (mem_sup_left (Subgroup.mem_subgroupOf.mp hw)) (mem_sup_right hmem)

theorem MinCounter.rot_le_sup_oddCoreIn {S : Subgroup G} (hM : MinCounter Ω S) {X : Subgroup G}
    (hX : X ≠ ⊤) (hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X)
    (hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X) {L T V : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ X)
    (hT : IsSylowOf 2 T L) (hV : IsDihedralRot V T) : V ≤ sec4W Ω S ⊔ oddCoreIn X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hWX := sec4W_le_of_omegaD_le hΩ hM.sylow hD
  obtain ⟨P₀, hP₀, hWP₀⟩ := exists_isSylowOf_le (hM.sylow.isPGroup.to_le (sec4W_le S)) hWX
  have hS₀ : IsSylowOf 2 (imgOf X P₀) ⊤ := by
    have := isSylowOf_imgOf hP₀ le_rfl
    rwa [imgOf_self] at this
  have hW := hM.ihQuot X _ hX (fun L hL => hL.1) (membersIn_inv hΩ X) hgen _ hS₀
  have h1 := imgOf_rot_le_sec4W hΩ (fun L hL => hL.1) (membersIn_inv hΩ X) hgen hS₀ hW
    ⟨hL, hLX⟩ hT hV
  rw [← imgOf_sec4W_eq hΩ hM.sylow hgen hD hP₀ hWP₀] at h1
  exact le_sup_oddCoreIn_of_imgOf_le ((hV.le.trans hT.le).trans hLX) h1

theorem MinCounter.mem_normalizer_sup_oddCoreIn {S : Subgroup G} (hM : MinCounter Ω S)
    {X : Subgroup G} (hX : X ≠ ⊤) (hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X)
    (hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X) {g : G} (hgX : g ∈ normalizer (X : Set G))
    (hg : ∀ L ∈ omegaD Ω (sec4W Ω S),
      AschbacherTightEmbedding.rightConjugate L g ∈ omegaD Ω (sec4W Ω S)) :
    g ∈ normalizer ((sec4W Ω S ⊔ oddCoreIn X : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  set B := W ⊔ oddCoreIn X with hBdef
  have hO : AschbacherTightEmbedding.rightConjugate (oddCoreIn X) g = oddCoreIn X := by
    rw [← oddCoreIn_rightConjugate_eq, (rightConjugate_eq_self_iff X g).mpr hgX]
  have hWg : AschbacherTightEmbedding.rightConjugate W g ≤ B := by
    rw [rightConjugate_le_iff]
    refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
    rw [← rightConjugate_le_iff]
    obtain ⟨K, hK, R₀, hR₀, hU₀⟩ := IsRot.exists_isDihedralRot hΩ hU
    obtain ⟨R, hR, hUR, hRW⟩ :=
      exists_isSylowOf_le_normalizer_of_isRot hΩ hS hK hR₀ hU₀ (le_sec4W hUS hU)
    have hKg := hg K ⟨hK, R, hR, hRW⟩
    exact hM.rot_le_sup_oddCoreIn hX hgen hD hKg.1 (hD _ hKg) (isSylowOf_rightConjugate hR g)
      (hUR.rightConjugate g)
  have hle : AschbacherTightEmbedding.rightConjugate B g ≤ B := by
    have e : AschbacherTightEmbedding.rightConjugate B g =
        AschbacherTightEmbedding.rightConjugate W g ⊔
          AschbacherTightEmbedding.rightConjugate (oddCoreIn X) g := Subgroup.map_sup _ _ _
    rw [e, hO]
    exact sup_le hWg le_sup_right
  have heq : AschbacherTightEmbedding.rightConjugate B g = B :=
    eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  exact (rightConjugate_eq_self_iff B g).mp heq

theorem exists_conj_mem_normalizer_of_mem_normalizer_sup {X W : Subgroup G} (hW2 : IsPGroup 2 W)
    (hWX : W ≤ X) {s : G} (hs2 : IsPGroup 2 (zpowers s))
    (hsB : s ∈ normalizer ((W ⊔ oddCoreIn X : Subgroup G) : Set G)) :
    ∃ o ∈ oddCoreIn X, o * s * o⁻¹ ∈ normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWO : W ≤ normalizer (oddCoreIn X : Set G) := hWX.trans (le_normalizer_oddCoreIn X)
  have hWB : IsSylowOf 2 W (W ⊔ oddCoreIn X) :=
    isSylowOf_sup_of_odd_of_le_normalizer hW2 (odd_card_oddCoreIn X) hWO
  obtain ⟨P, hP, hsP⟩ := exists_isSylowOf_normalized hs2 ((zpowers_le).mpr hsB)
  obtain ⟨b, hbB, hb⟩ := L26.IsSylowOf.exists_conj_mem hWB hP
  have hb' : b ∈ ((oddCoreIn X ⊔ W : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hbB
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWO] at hb'
  obtain ⟨o, ho, w, hw, rfl⟩ := hb'
  refine ⟨o⁻¹, inv_mem ho, ?_⟩
  have hsn : s ∈ normalizer (P : Set G) := hsP (mem_zpowers s)
  have hPmem : ∀ x, x ∈ P ↔ o⁻¹ * x * o ∈ W := by
    intro x
    rw [hb x]
    constructor
    · intro h
      have := W.mul_mem (W.mul_mem hw h) (W.inv_mem hw)
      have e : w * ((o * w)⁻¹ * x * (o * w)) * w⁻¹ = o⁻¹ * x * o := by group
      rwa [e] at this
    · intro h
      have := W.mul_mem (W.mul_mem (W.inv_mem hw) h) hw
      have e : w⁻¹ * (o⁻¹ * x * o) * w = (o * w)⁻¹ * x * (o * w) := by group
      rwa [e] at this
  have key : ∀ y, y ∈ W ↔ (o⁻¹ * s * o) * y * (o⁻¹ * s * o)⁻¹ ∈ W := by
    intro y
    have h1 : y ∈ W ↔ o * y * o⁻¹ ∈ P := by
      rw [hPmem]
      have e : o⁻¹ * (o * y * o⁻¹) * o = y := by group
      rw [e]
    have h2 : o * y * o⁻¹ ∈ P ↔ s * (o * y * o⁻¹) * s⁻¹ ∈ P := (mem_normalizer_iff.mp hsn) _
    have h3 : s * (o * y * o⁻¹) * s⁻¹ ∈ P ↔ (o⁻¹ * s * o) * y * (o⁻¹ * s * o)⁻¹ ∈ W := by
      rw [hPmem]
      have e : o⁻¹ * (s * (o * y * o⁻¹) * s⁻¹) * o =
          (o⁻¹ * s * o) * y * (o⁻¹ * s * o)⁻¹ := by group
      rw [e]
    exact h1.trans (h2.trans h3)
  rw [mem_normalizer_iff, inv_inv]
  exact key

end CFSG.ComponentClassification.Asc76.Sec4
