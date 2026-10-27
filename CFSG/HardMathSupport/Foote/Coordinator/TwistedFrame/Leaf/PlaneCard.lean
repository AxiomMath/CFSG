module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxF4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxE8Twelve

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


@[expose] def TwClass.ord₁ : TwClass → ℕ → ℕ
  | .f4Six, q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))
  | .e6Six, q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))
  | .e8Ten, q => q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))
  | .e8Twelve, q => CFSG.Open.ordTrialityD4 q

@[expose] def TwClass.ord₂ : TwClass → ℕ → ℕ
  | .f4Six, q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))
  | .e6Six, q => q ^ 6 * ((q ^ 4 - 1) * (q ^ 6 - 1))
  | .e8Ten, q => q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))
  | .e8Twelve, q => CFSG.Open.ordTrialityD4 q

theorem TwClass.two_le_minQ (c : TwClass) : 2 ≤ c.minQ := by
  cases c <;> decide

theorem TwClass.padicValNat_ord₁ (c : TwClass) {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = c.e) :
    padicValNat p (c.ord₁ q) = padicValNat p (q ^ c.e - 1) := by
  cases c
  · exact PlaneCard.padicValNat_suThree hp hq hord
  · exact PlaneCard.padicValNat_suThree hp hq hord
  · exact PlaneCard.padicValNat_suFive hp hq hord
  · exact PlaneCard.padicValNat_trialityD4 hp hq hord

theorem TwClass.padicValNat_ord₂ (c : TwClass) {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = c.e) :
    padicValNat p (c.ord₂ q) = padicValNat p (q ^ c.e - 1) := by
  cases c
  · exact PlaneCard.padicValNat_suThree hp hq hord
  · exact PlaneCard.padicValNat_slThreeSq hp hq hord
  · exact PlaneCard.padicValNat_suFive hp hq hord
  · exact PlaneCard.padicValNat_trialityD4 hp hq hord

theorem TwClass.factorization_card_adjointGroup (c : TwClass) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e) :
    (Nat.card ↥(adjointGroup c.tag K)).factorization p =
      2 * padicValNat p (Nat.card K ^ c.e - 1) := by
  rw [Nat.factorization_def _ hp]
  cases c
  · rw [show TwClass.tag .f4Six = Tag.F4 from rfl, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    exact PlaneCard.padicValNat_ordF4_of_orderOf_eq_six hp hp5 hq hord
  · rw [show TwClass.tag .e6Six = Tag.E6 from rfl, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
    exact PlaneCard.padicValNat_ordE6_of_orderOf_eq_six hp hp5 hq hord
  · rw [show TwClass.tag .e8Ten = Tag.E8 from rfl, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
    exact PlaneCard.padicValNat_ordE8_of_orderOf_eq_ten hp hp5 hq hord
  · rw [show TwClass.tag .e8Twelve = Tag.E8 from rfl, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
    exact PlaneCard.padicValNat_ordE8_of_orderOf_eq_twelve hp hp5 hq hord

namespace TwCardAux

theorem f4_not_isRoot_add : ∀ α ∈ rootFinset Tag.F4,
    (∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      CFSG.LieType.Steinberg.Adjoint.iform α β = 0) →
    ∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      α + β ∉ rootFinset Tag.F4 := by
  decide +kernel

theorem not_isRoot_add_f4 {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ TwClass.f4Six.S₁)
    (hβ : β ∈ TwClass.f4Six.S₂) : ¬ IsRoot Tag.F4 (α + β) := fun h =>
  f4_not_isRoot_add α (mem_rootFinset.2 hα.1)
    (fun β' hβ' hs => hα.2 β' ⟨mem_rootFinset.1 hβ', hs⟩) β (mem_rootFinset.2 hβ.1) hβ.2
    (mem_rootFinset.2 h)

theorem rootSpan_commute (c : TwClass) (L : Type) [Field L] :
    ∀ x ∈ rootSpan c.tag L c.S₁, ∀ y ∈ rootSpan c.tag L c.S₂, x * y = y * x := by
  cases c with
  | f4Six =>
    refine rootSpan_commute_of_gen' fun α hα β hβ c d => ?_
    exact pinnedX_commute_of_iform_eq_zero L hα.1 hβ.1 (hα.2 β hβ) (not_isRoot_add_f4 hα hβ) c d
  | e6Six =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inl rfl))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))
  | e8Ten =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))
  | e8Twelve =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))

theorem frame_commute (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w) :
    ∀ x ∈ c.X₁ D, ∀ y ∈ c.X₂ D, x * y = y * x := by
  intro x hx y hy
  obtain ⟨-, hx'⟩ := (mem_frame_iff D _ x).1 hx
  obtain ⟨-, hy'⟩ := (mem_frame_iff D _ y).1 hy
  have h := rootSpan_commute c D.L _ hx' _ hy'
  refine baseChangeGL_injective (algebraMap K D.L) ?_
  rw [map_mul, map_mul]
  set a := baseChangeGL (algebraMap K D.L) x
  set b := baseChangeGL (algebraMap K D.L) y
  set g := D.g
  calc a * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

end TwCardAux

theorem twPlaneCard_of_dvd (c : TwClass) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e)
    (h₁ : p ^ padicValNat p (Nat.card K ^ c.e - 1) ∣ Nat.card ↥(c.X₁ D))
    (h₂ : p ^ padicValNat p (Nat.card K ^ c.e - 1) ∣ Nat.card ↥(c.X₂ D))
    (hZ : ¬ p ∣ Nat.card ↥(c.X₁ D ⊓ c.X₂ D)) :
    ¬ p ∣ Nat.card ↥(c.X₁ D ⊓ c.X₂ D) ∧
      (Nat.card ↥(adjointGroup c.tag K)).factorization p =
        (Nat.card ↥(c.X₁ D)).factorization p + (Nat.card ↥(c.X₂ D)).factorization p := by
  refine ⟨hZ, ?_⟩
  have hq : 2 ≤ Nat.card K := (c.two_le_minQ).trans hK
  have hC := c.factorization_card_adjointGroup K hp hp5 hq hord
  haveI : Finite (Module.End K (RootModule c.tag K)) := Module.finite_of_finite K
  haveI : Finite (ModGL c.tag K) :=
    Finite.of_injective (Units.val : ModGL c.tag K → Module.End K (RootModule c.tag K))
      Units.val_injective
  haveI : Finite ↥(adjointGroup c.tag K) := inferInstance
  have hX₁ : Nat.card ↥(c.X₁ D) ≠ 0 := Nat.card_pos.ne'
  have hX₂ : Nat.card ↥(c.X₂ D) ≠ 0 := Nat.card_pos.ne'
  have hle₁ : c.X₁ D ≤ adjointGroup c.tag K := fun x hx => ((TwCardAux.mem_frame_iff D _ x).1 hx).1
  have hle₂ : c.X₂ D ≤ adjointGroup c.tag K := fun x hx => ((TwCardAux.mem_frame_iff D _ x).1 hx).1
  have hup := PlaneCard.factorization_add_le_of_commute hle₁ hle₂ (TwCardAux.frame_commute c D) hZ
  have hlow₁ := ((hp.pow_dvd_iff_le_factorization hX₁).1 h₁)
  have hlow₂ := ((hp.pow_dvd_iff_le_factorization hX₂).1 h₂)
  omega

theorem twPlaneCard_of_card (c : TwClass) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e)
    (h₁ : Nat.card ↥(c.X₁ D) = c.ord₁ (Nat.card K))
    (h₂ : Nat.card ↥(c.X₂ D) = c.ord₂ (Nat.card K))
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥(c.X₁ D))) :
    ¬ p ∣ Nat.card ↥(c.X₁ D ⊓ c.X₂ D) ∧
      (Nat.card ↥(adjointGroup c.tag K)).factorization p =
        (Nat.card ↥(c.X₁ D)).factorization p + (Nat.card ↥(c.X₂ D)).factorization p := by
  have hq : 2 ≤ Nat.card K := (c.two_le_minQ).trans hK
  have hdvd := PlaneCard.card_inf_dvd_card_center (TwCardAux.frame_commute c D)
  refine twPlaneCard_of_dvd c K hK D hp hp5 hord ?_ ?_ (fun h => hZ (h.trans hdvd))
  · rw [h₁, ← c.padicValNat_ord₁ hp hq hord]
    exact pow_padicValNat_dvd
  · rw [h₂, ← c.padicValNat_ord₂ hp hq hord]
    exact pow_padicValNat_dvd

theorem twPlaneCard (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e) :
    ¬ p ∣ Nat.card ↥(c.X₁ D ⊓ c.X₂ D) ∧
      (Nat.card ↥(adjointGroup c.tag K)).factorization p =
        (Nat.card ↥(c.X₁ D)).factorization p + (Nat.card ↥(c.X₂ D)).factorization p := by
  have hq : 2 ≤ Nat.card K := (c.two_le_minQ).trans hK
  cases c with
  | f4Six =>
    obtain ⟨h₁, h₂, h₃⟩ := TwCardAux.f4Six_frames K hK D
    refine twPlaneCard_of_card TwClass.f4Six K hK D hp hp5 hord h₁ h₂ ?_
    rw [h₃]
    exact fun h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))
      omega
  | e6Six =>
    obtain ⟨h₁, hZ⟩ := TwCardAux.e6Six_X₁ K hK D
    have hZp : ¬ p ∣ Nat.card ↥(Subgroup.center ↥(TwClass.e6Six.X₁ D)) := by
      rw [hZ]
      exact fun h => by
        have := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))
        omega
    have hdvd := PlaneCard.card_inf_dvd_card_center (TwCardAux.frame_commute TwClass.e6Six D)
    refine twPlaneCard_of_dvd TwClass.e6Six K hK D hp hp5 hord ?_ ?_ (fun h => hZp (h.trans hdvd))
    · rw [h₁, ← TwClass.e6Six.padicValNat_ord₁ hp hq hord]
      exact pow_padicValNat_dvd
    · refine TwCardAux.e6Six_X₂_dvd K D hp hp5 ?_
      rw [← TwClass.e6Six.padicValNat_ord₂ hp hq hord]
      exact pow_padicValNat_dvd
  | e8Ten =>
    obtain ⟨h₁, h₂, hZ⟩ := TwCardAux.e8Ten_frames K D
    refine twPlaneCard_of_card TwClass.e8Ten K hK D hp hp5 hord h₁ h₂ ?_
    rw [hZ]
    intro h
    have h5 : p ∣ 5 := h.trans (Nat.gcd_dvd_left 5 _)
    have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
    have h10 := PlaneCard.ten_dvd_sub_one hp hord
    subst hp5'
    omega
  | e8Twelve =>
    obtain ⟨h₁, h₂, hZ⟩ := TwCardAux.e8Twelve_frames K D
    refine twPlaneCard_of_card TwClass.e8Twelve K hK D hp hp5 hord h₁ h₂ ?_
    rw [hZ]
    exact fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
