module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOFamily
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ReachGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONKFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def SOR : GroupClass := fun X _ =>
  (∃ n : ℕ, 2 ≤ n ∧ LieModel X .PSL 3 2 n) ∨ IsSporadic X .Suz ∨ IsSporadic X .He ∨
    IsSporadic X .ONan

theorem soR_iso : GroupClass.IsoInv SOR := by
  intro X Y _ _ e h
  rcases h with ⟨n, hn, hX⟩ | hS | hH | hO
  · exact Or.inl ⟨n, hn, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hX⟩
  · obtain ⟨f⟩ := hS
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · obtain ⟨f⟩ := hH
    exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))
  · obtain ⟨f⟩ := hO
    exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans f⟩))

theorem suz_card_pinned : ∀ (Y : Type) [Group Y], IsSporadic Y .Suz →
    Nat.card Y = 448345497600 := by
  intro Y _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv]
  exact suz_pinned.2.2.2

theorem on_card_pinned : ∀ (Y : Type) [Group Y], IsSporadic Y .ONan →
    Nat.card Y = 460815505920 := by
  intro Y _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv]
  exact on_pinned.2.2.2

theorem he_pinned : ∀ (Y : Type) [Group Y], IsSporadic Y .He →
    IsSimpleGroup Y ∧ Nat.card Y = 4030387200 := by
  intro Y _ ⟨e⟩
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.He := e
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e',
    by rw [Nat.card_congr e'.toEquiv]; exact CFSG.Sporadic.He.card_He⟩

theorem fi23Excl_of_card_ne {s : TauCeti.SporadicName} {n : ℕ}
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = n)
    (hn : n ≠ 4089470473293004800) : Fi23Excl s := by
  intro X _ hX hXs
  obtain ⟨e⟩ := hX
  have e' : X ≃* CFSG.Blueprint.NativeSporadic.Fi23 := e
  have hcard : Nat.card X = 4089470473293004800 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Fi23.card_Fi23
  have hsimple : IsSimpleGroup X :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e'
  have hnc : ∃ a b : X, a * b ≠ b * a :=
    nonabelian_of_isSimpleGroup_of_not_prime (by rw [hcard]; norm_num)
  have hZ : center X = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hnc
  have h1 : Nat.card (X ⧸ center X) = Nat.card X :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  exact hn (by rw [← hs _ hXs, h1, hcard])

theorem suz_fi23 : Fi23Excl .Suz := fi23Excl_of_card_ne suz_card_pinned (by norm_num)

theorem on_fi23 : Fi23Excl .ONan := fi23Excl_of_card_ne on_card_pinned (by norm_num)

theorem suz_sp_not_exc : SporadicNotExc .Suz :=
  sporadicNotExc_of_card suz_card_pinned (c := 9643) (by norm_num) (by norm_num) (by norm_num)

theorem he_sp_not_exc : SporadicNotExc .He :=
  sporadicNotExc_of_card (fun Y _ h => (he_pinned Y h).2) (c := 2005) (by norm_num)
    (by norm_num) (by norm_num)

theorem on_sp_not_exc : SporadicNotExc .ONan :=
  sporadicNotExc_of_card on_card_pinned (c := 9731) (by norm_num) (by norm_num) (by norm_num)

theorem soR_notExc : ∀ (X : Type) [Group X], SOR X → NotExc X := by
  intro X _ h
  rcases h with ⟨n, hn, hX⟩ | hS | hH | hO
  · exact notExc_of_card_l3 hn (card_of_lieModel_psl_three hX)
  · exact suz_sp_not_exc X hS
  · exact he_sp_not_exc X hH
  · exact on_sp_not_exc X hO

theorem suz_thm24 (lo : LieModelOrders) : ∀ s ∈ [TauCeti.SporadicName.Suz],
    s = .M ∨ (s ≠ .M ∧ Thm24Hex s) := by
  intro s hs
  rcases List.mem_singleton.1 hs with rfl
  refine Or.inr ⟨by decide, fun X _ hq hodd hX => thm24Hex_of_card lo (N := 448345497600)
    suz_card_pinned (by norm_num)
    (factorial_div_two_ne_of_between (n₀ := 14) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial])) X hq hodd hX⟩

theorem on_thm24 (lo : LieModelOrders) : ∀ s ∈ [TauCeti.SporadicName.ONan],
    s = .M ∨ (s ≠ .M ∧ Thm24Hex s) := by
  intro s hs
  rcases List.mem_singleton.1 hs with rfl
  refine Or.inr ⟨by decide, fun X _ hq hodd hX => thm24Hex_of_card lo (N := 460815505920)
    on_card_pinned (by norm_num)
    (factorial_div_two_ne_of_between (n₀ := 14) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial])) X hq hodd hX⟩

theorem so_fStar_cases {Y : Type} [Group Y] [Finite Y] (h46 : Sol78Thm46FSAt Y) {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hty : (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
      IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He)
    (hsuz : IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P))) :
    (∃ m : ℕ, 2 ≤ m ∧ LieModel ↥N' .PSL 3 2 (2 * m)) ∨
      (LieModel ↥P .PSL 3 2 2 ∧ IsSporadic ↥N' .Suz) ∨
      (IsKleinFour ↥(center ↥P) ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧
        IsSporadic ↥N' .He) ∨
      (Nonempty (↥(center ↥P) ≃* Multiplicative (ZMod 4)) ∧
        LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧ IsSporadic ↥N' .ONan ∧ P ≤ N') :=
  h46 N' hN hidx hK P hP hPq hty hsuz

theorem so_closure_core {Y : Type} [Group Y] [Finite Y] (h46 : Sol78Thm46FSAt Y) {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) (hR : SOR (↥P ⧸ center ↥P))
    (hnON : ¬ IsSporadic (↥P ⧸ center ↥P) .ONan)
    (hsuz : IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P))) : SOR ↥N' := by
  have hty : (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
      IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He := by
    rcases hR with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hnON
  rcases so_fStar_cases h46 hN hidx hK hP hPq hty hsuz with ⟨m, hm, hNm⟩ | ⟨-, hS⟩ |
    ⟨-, -, hHe⟩ | ⟨-, -, hON, -⟩
  · exact Or.inl ⟨2 * m, by omega, hNm⟩
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hHe))
  · exact Or.inr (Or.inr (Or.inr hON))

theorem so_pair_suz {Y : Type} [Group Y] [Finite Y] (h46 : Sol78Thm46FSAt Y) {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hty : (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
      IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He)
    (hsuz : IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P)))
    (hsN : IsSporadic ↥N' .Suz) : LieModel ↥P .PSL 3 2 2 := by
  have h1 := suz_card_pinned _ hsN
  rcases so_fStar_cases h46 hN hidx hK hP hPq hty hsuz with ⟨m, hm, hNm⟩ | ⟨hL, -⟩ |
    ⟨-, -, hHe⟩ | ⟨-, -, hON, -⟩
  · exact absurd ((card_of_lieModel_psl_three hNm).symm.trans h1)
      (ordA_ne_suz (n := 2 * m) (by omega))
  · exact hL
  · exfalso
    have := (he_pinned _ hHe).2
    omega
  · exfalso
    have := on_card_pinned _ hON
    omega

theorem so_pair_on {Y : Type} [Group Y] [Finite Y] (h46 : Sol78Thm46FSAt Y) {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hty : (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
      IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He)
    (hsuz : IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P)))
    (hsN : IsSporadic ↥N' .ONan) :
    Nonempty (↥(center ↥P) ≃* Multiplicative (ZMod 4)) ∧
      LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧ P ≤ N' := by
  have h1 := on_card_pinned _ hsN
  rcases so_fStar_cases h46 hN hidx hK hP hPq hty hsuz with ⟨m, hm, hNm⟩ | ⟨-, hS⟩ |
    ⟨-, -, hHe⟩ | ⟨hZ, hQ, -, hle⟩
  · exact absurd ((card_of_lieModel_psl_three hNm).symm.trans h1)
      (ordA_ne_on (n := 2 * m) (by omega))
  · exfalso
    have := suz_card_pinned _ hS
    omega
  · exfalso
    have := (he_pinned _ hHe).2
    omega
  · exact ⟨hZ, hQ, hle⟩

end CFSG.EvenSporadicStandard.Induction
