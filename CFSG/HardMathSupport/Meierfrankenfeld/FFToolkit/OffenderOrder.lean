module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderSup
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_isFFStarOffender_le_of_offender {G E : Subgroup (MulAut W)} (hEG : E ≤ G)
    (hE : E ≠ ⊥) (hel : IsElemAbelian2 E) (hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E)) :
    ∃ A : Subgroup (MulAut W), A ≤ E ∧ IsFFStarOffender G A ∧
      Nat.card W ≤ Nat.card A * Nat.card (fixV A) :=
  (B1.exists_offender_below (X := G) ⟨hEG, hE, hel⟩ 0 (by simpa using hoff)).imp fun _ h =>
    ⟨h.1, h.2.1, by simpa using h.2.2⟩

omit [Finite W] in
theorem fixV_eq_bot_of_isIrrOn {L : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) : fixV L = ⊥ := by
  have hinv : ∀ g ∈ L, ∀ u ∈ fixV L, g u ∈ fixV L := by
    intro g hg u hu
    rw [hu g hg]
    exact hu
  rcases hirr.2 (fixV L) hinv with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hL.2.2
    have hone : ∀ l : ↥L, l = 1 := by
      intro l
      apply Subtype.ext
      apply MulEquiv.ext
      intro w
      have hw : w ∈ fixV L := by rw [h]; exact Subgroup.mem_top w
      exact hw l l.2
    apply hab
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b => rw [hone a, hone b]

theorem card_le_card_sup_of_offender (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E)) :
    Nat.card W ≤ Nat.card ↥(L ⊔ E) := by
  classical
  have : Finite (MulAut W) := B42Disp.finite_mulAut
  obtain ⟨A, hAE, hA, -⟩ :=
    exists_isFFStarOffender_le_of_offender (G := L ⊔ E) le_sup_right hE hEel hoff
  set ks : List (MulAut W) := (Set.toFinite (L : Set (MulAut W))).toFinset.toList with hks_def
  have hmem : ∀ k, k ∈ ks ↔ k ∈ L := by
    intro k
    rw [hks_def, Finset.mem_toList, Set.Finite.mem_toFinset]
    rfl
  have hbound := card_le_weight_closure_conj hA ks fun k hk =>
    Subgroup.mem_sup_left ((hmem k).mp hk)
  set N := Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} with hN
  have hgen : ∀ k ∈ L, ∀ a ∈ A, k * a * k⁻¹ ∈ N := fun k hk a ha =>
    Subgroup.subset_closure ⟨k, (hmem k).mpr hk, a, ha, rfl⟩
  have hNle : N ≤ L ⊔ E := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨k, hk, a, ha, rfl⟩
    have hkL : k ∈ L ⊔ E := Subgroup.mem_sup_left ((hmem k).mp hk)
    exact (L ⊔ E).mul_mem ((L ⊔ E).mul_mem hkL (Subgroup.mem_sup_right (hAE ha)))
      ((L ⊔ E).inv_mem hkL)
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := hAE.trans hEN
  have hne : ⁅L, A⁆ ≠ ⊥ := by
    intro hb
    apply hA.2.1
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have hLc := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    refine CFSG.QuasithinUnique.Setup.Family.eq_one_of_pow_two_pow hW hirr.2 (z := a)
      (fun l hl => ?_) 1 (by rw [pow_one]; exact hA.2.2.1.2 a ha)
    exact Subgroup.mem_centralizer_iff.mp (hLc hl) a ha
  have hLA : ⁅L, A⁆ = L := GeneralFF.commutator_eq_of_ne_bot hL hAN hne
  have hLN : L ≤ N := by
    rw [← hLA, Subgroup.commutator_le]
    intro l hl a ha
    rw [commutatorElement_def]
    have h1 : l * a * l⁻¹ ∈ N := hgen l hl a ha
    have h2 : a⁻¹ ∈ N := by
      have := hgen 1 L.one_mem a ha
      rw [one_mul, inv_one, mul_one] at this
      exact N.inv_mem this
    exact N.mul_mem h1 h2
  have hfixN : fixV N = ⊥ := by
    rw [eq_bot_iff, ← fixV_eq_bot_of_isIrrOn hL hirr]
    intro w hw g hg
    exact hw g (hLN hg)
  rw [hfixN, Subgroup.card_bot, mul_one] at hbound
  exact hbound.trans (Subgroup.card_le_of_le hNle)

theorem card_mul_card_fixV_lt_of_card_sup_lt (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hlt : Nat.card ↥(L ⊔ E) < Nat.card W) : Nat.card E * Nat.card (fixV E) < Nat.card W :=
  lt_of_not_ge fun h => absurd (card_le_card_sup_of_offender hW hL hirr hEN hE hEel h)
    (not_le.mpr hlt)

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
