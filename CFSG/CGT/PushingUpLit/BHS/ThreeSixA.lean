module

public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.Offender

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

section Weights

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem wt_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) : wt (conjSub g A) = wt A := by
  unfold wt
  rw [conjSub, Glauberman.card_map_conj, Glauberman.fixV_map_conj,
    Subgroup.card_map_of_injective g.injective]

omit [Finite V] in
theorem isElemAbelian2_conjSub {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) (g : MulAut V) :
    IsElemAbelian2 (conjSub g A) :=
  CFSG.Quasithin.B6.isElemAbelian2_conjSub h g

omit [Finite V] in
theorem IsOff.conj {A : Subgroup (MulAut V)} (hA : IsOff A) (g : MulAut V) :
    IsOff (conjSub g A) := by
  refine ⟨le_top, ?_, isElemAbelian2_conjSub hA.2.2.1 g, fun B hB => ?_⟩
  · intro h
    exact hA.2.1 ((conjSub_inj g).1 (h.trans (Subgroup.map_bot _).symm))
  · have h1 : conjSub g⁻¹ B ≤ A := by
      have := conjSub_mono g⁻¹ hB
      rwa [FourTwoTools.conjSub_inv_conjSub] at this
    have h2 := hA.2.2.2 _ h1
    have h3 : wt B = wt (conjSub g⁻¹ B) := by
      rw [wt_conjSub]
    have h4 : wt (conjSub g A) = wt A := wt_conjSub g A
    show wt B ≤ wt (conjSub g A)
    rw [h3, h4]
    exact h2

omit [Finite V] in
theorem IsAOff.conj {P A : Subgroup (MulAut V)} (h : IsAOff P A) {g : MulAut V} (hg : g ∈ P) :
    IsAOff P (conjSub g A) := by
  obtain ⟨hAP, hOff, hwt, hmin⟩ := h
  refine ⟨Glauberman.map_conj_le hg hAP, hOff.conj g, by rw [wt_conjSub, hwt], ?_⟩
  intro B hB hBoff hBwt
  have h1 : conjSub g⁻¹ B ≤ A := by
    have := conjSub_mono g⁻¹ hB
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  have h2 := hmin _ h1 (hBoff.conj g⁻¹) (by rw [wt_conjSub, hBwt])
  rw [← h2, FourTwoTools.conjSub_conjSub_inv]

theorem bddAbove_wt (P : Subgroup (MulAut V)) :
    BddAbove {n | ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A ∧ wt A = n} := by
  refine (Set.finite_range (fun B : Subgroup (MulAut V) => wt B)).bddAbove.mono ?_
  rintro n ⟨A, -, -, rfl⟩
  exact ⟨A, rfl⟩

theorem wt_le_offMax {P X : Subgroup (MulAut V)} (hXP : X ≤ P) (hX : IsOff X) :
    wt X ≤ offMax P :=
  le_csSup (bddAbove_wt P) ⟨X, hXP, hX, rfl⟩

theorem exists_wt_max (X : Subgroup (MulAut V)) :
    ∃ X₀ : Subgroup (MulAut V), X₀ ≤ X ∧ ∀ B : Subgroup (MulAut V), B ≤ X → wt B ≤ wt X₀ := by
  classical
  have : Nonempty {B : Subgroup (MulAut V) // B ≤ X} := ⟨⟨⊥, bot_le⟩⟩
  have : Finite {B : Subgroup (MulAut V) // B ≤ X} :=
    Finite.of_injective (fun B : {B : Subgroup (MulAut V) // B ≤ X} => (B.1 : Set (MulAut V)))
      (fun a b h => Subtype.ext (SetLike.coe_injective h))
  obtain ⟨X₀, hX₀⟩ := Finite.exists_max (fun B : {B : Subgroup (MulAut V) // B ≤ X} => wt B.1)
  exact ⟨X₀.1, X₀.2, fun B hB => hX₀ ⟨B, hB⟩⟩

theorem IsAOff.wt_le {P A X : Subgroup (MulAut V)} (hA : IsAOff P A) (hXP : X ≤ P)
    (hX : IsElemAbelian2 X) : wt X ≤ wt A := by
  obtain ⟨X₀, hX₀X, hmax⟩ := exists_wt_max X
  refine (hmax X le_rfl).trans ?_
  by_cases h0 : X₀ = ⊥
  · subst h0
    have : wt (⊥ : Subgroup (MulAut V)) = Nat.card V := by
      unfold wt
      rw [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top]
    rw [this]
    exact hA.2.1.card_le_wt
  · have hoff : IsOff X₀ :=
      ⟨le_top, h0, isElemAbelian2_mono' hX hX₀X, fun B hB => hmax B (hB.trans hX₀X)⟩
    rw [hA.2.2.1]
    exact wt_le_offMax (hX₀X.trans hXP) hoff

omit [Finite V] in
theorem IsAOff.wt_lt_of_lt {P A B : Subgroup (MulAut V)} (hA : IsAOff P A) (hBA : B ≤ A)
    (hB0 : B ≠ ⊥) (hne : B ≠ A) : wt B < wt A := by
  have hle : wt B ≤ wt A := hA.2.1.2.2.2 B hBA
  refine lt_of_le_of_ne hle fun heq => hne ?_
  refine hA.2.2.2 B hBA ⟨le_top, hB0, isElemAbelian2_mono' hA.2.1.2.2.1 hBA, fun B' hB' => ?_⟩
    (heq.trans hA.2.2.1)
  exact (hA.2.1.2.2.2 B' (hB'.trans hBA)).trans heq.ge

end Weights

end CFSG.CGT.PushingUpLit.BHS
