module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodIn
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag
public import CFSG.HardMathSupport.Lang.TwE6Step3.CubesV4
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPlacement
public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Seven
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8One
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4One
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6One

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding

@[expose] def ExcCubeOpenClass (d : TauCeti.LieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∨ ∃ q : TauCeti.PrimePower,
    ((d = .F4 q ∨ d = .E7 q ∨ d = .twistedE6 q) ∧ orderOf ((q.card : ℕ) : ZMod p) = 2) ∨
    (d = .E8 q ∧ (orderOf ((q.card : ℕ) : ZMod p) = 2 ∨ orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 4 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6 ∨
      (p = 5 ∧ orderOf ((q.card : ℕ) : ZMod p) = 1)))

@[expose] def SeitzGoodInnerExcOpen : Prop :=
  SeitzHyperLie fun d p E₀ => IsTopIndex d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    ExcCubeOpenClass d.1 p

@[expose] def OrthOrderTwo (d : TauCeti.LieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), (d = .B r q ∨ d = .D r q ∨ d = .twistedD r q) ∧
    orderOf ((q.card : ℕ) : ZMod p) = 2

@[expose] def SeitzGoodInnerOrthTwo : Prop :=
  SeitzHyperLie fun d p E₀ => IsOrthogonalIndex d.1 ∧ ¬ OReducible d p E₀ ∧
    SeitzGoodIndex p d.1 ∧ OrthOrderTwo d.1 p

@[expose] def UDiagLift (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E₀ : Subgroup (Cat d)) : Prop :=
  ∃ (ℓ f n : ℕ) (K : Type) (_ : Field K)
    (_ : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K)
    (π : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1) →* Cat d),
    Function.Surjective π ∧
    (∀ g ∈ π.ker, ∃ c : K,
      ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1) ∧
    p ∣ ℓ ^ f + 1 ∧ ℓ ^ f ≠ 2 ∧
    (∀ x y : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1), π x ∈ E₀ → π y ∈ E₀ →
      x * y = y * x) ∧
    ∀ x : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1), π x ∈ E₀ →
      x ^ (ℓ ^ f + 1) = 1

@[expose] def SeitzGoodInnerUnitaryNonDiag : Prop :=
  SeitzHyperLie fun d p E₀ => UToralRestPrime d p ∧ ¬ UReducible d p E₀ ∧ SeitzGoodIndex p d.1 ∧
    ¬ UDiagLift d p E₀

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem isPGroup_of_elemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsPGroup p E :=
  fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩

theorem normalizesRSub_of_aut {d : TauCeti.ValidLieTypeIndex} {E₀ : Subgroup (Cat d)}
    (h : NormalizesRSubgroup d (E₀.map (MulAut.conj : Cat d →* MulAut (Cat d)))) :
    NormalizesRSub d E₀ := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  exact ⟨R, hR1, hRp, fun x hx => hRn _ ⟨x, hx, rfl⟩⟩

theorem isPGroup_map_conj {d : TauCeti.ValidLieTypeIndex} {p : ℕ} {E₀ : Subgroup (Cat d)}
    (hE : IsElemAbelian p E₀) :
    IsPGroup p (E₀.map (MulAut.conj : Cat d →* MulAut (Cat d))) :=
  (isPGroup_of_elemAbelian hE).map _

theorem innerPlane_map_conj {d : TauCeti.ValidLieTypeIndex} {p : ℕ} (E₀ : Subgroup (Cat d)) :
    InnerPlane d p (E₀.map (MulAut.conj : Cat d →* MulAut (Cat d))) :=
  Subgroup.map_le_range _ _

theorem hyperGen_of_unique_cube {d : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hS : SylowTorus (Cat d) p 3)
    (hcube : (∃ E₀ : Subgroup (Cat d), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3) →
      ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        (NormalizesRSub d E ∨ HyperGen p ⊤ E))
    {E₀ : Subgroup (Cat d)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3)
    (hN : ¬ NormalizesRSub d E₀) : HyperGen p ⊤ E₀ := by
  obtain ⟨E, hE, hEc, hcase⟩ := hcube ⟨E₀, hE₀, hc⟩
  obtain ⟨x, hx⟩ := ExcHigh.exists_conj_of_sylowTorus_cube hp hS hE hEc hE₀ hc
  rcases hcase with hnorm | hhyp
  · exfalso
    apply hN
    have h1 : CFSG.HardMathSupport.Lang.AnisoE6.NormRSub d.1.characteristic E := hnorm
    have h2 := CFSG.HardMathSupport.Lang.AnisoE6.normRSub_map (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective h1
    rw [← hx] at h2
    exact h2
  · rw [hx]
    exact hyperGen_conj x hhyp

theorem one_le_card (q : TauCeti.PrimePower) : 1 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def]
  exact Nat.one_le_pow _ _ q.prime_p.pos

theorem dvd_sq_sub_one_of_orderOf_dvd_two {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) ∣ 2) : p ∣ q ^ 2 - 1 := by
  have h2 : ((q : ℕ) : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
    Nat.cast_one, h2, sub_self]

theorem orderOf_pos_of_ne {q : TauCeti.PrimePower} {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p) :
    0 < orderOf ((q.card : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : ((q.card : ℕ) : ZMod p) ≠ 0 := fun h0 =>
    (not_dvd_card_of_ne hp hpq) ((ZMod.natCast_eq_zero_iff _ p).1 h0)
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hne⟩)

theorem seven_le_of_ne_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h5 : p ≠ 5) : 7 ≤ p := by
  have h6 : p ≠ 6 := fun h => by
    rw [h] at hp
    norm_num at hp
  omega

section Families

set_option linter.unusedSectionVars false

open CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Timmesfeld.CrossChar (rankLE2_cat_E6 rankLE2_cat_E7 rankLE2_cat_E8
  rankLE2_cat_twistedE6 eq_of_three_le_degCount_E6 eq_of_three_le_degCount_E7
  eq_of_three_le_degCount_E8 eq_of_three_le_degCountTw)

open CFSG.HardMathSupport.Malle.SeitzCube (ExcCubeHighAt)

theorem false_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ≠ q.p) {E₀ : Subgroup (Cat ⟨.F4 q, hv⟩)} (hE₀ : IsElemAbelian p E₀)
    (hc : Nat.card E₀ = p ^ 3) (hN : ¬ NormalizesRSub ⟨.F4 q, hv⟩ E₀)
    (h2 : orderOf ((q.card : ℕ) : ZMod p) ≠ 2) : False := by
  rcases Nat.lt_or_ge (degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · exact false_of_rankLE2_of_card hp
      (ExcHigh.rankLE2_cat_F4_of_degCount_le_two q hv hp hp5 hpq (by omega)) hE₀ hc
  · have key : ∀ e ≤ 30, 3 ≤ degCount Tag.F4 e → e = 1 ∨ e = 2 := by decide
    rcases key _ (le_thirty_of_degCount_pos (τ := Tag.F4) (by simp) (by omega)) hge with h1 | h2'
    · exact hN (normalizesRSub_of_aut (ExcHigh.normalizesRSubgroup_F4_of_dvd_sub_one q hv hp hp5
        (ExcHigh.dvd_sub_one_of_orderOf_eq_one (one_le_card q) h1) (isPGroup_map_conj hE₀)
        (innerPlane_map_conj E₀)))
    · exact h2 h2'

theorem hyperGen_E6 (h63 : ExcCubeHighAt LieTypeIndex.E6 3) {q : PrimePower}
    (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) (hlist : ¬ P1ThreeLieList p ⟨.E6 q, hv⟩) {E₀ : Subgroup (Cat ⟨.E6 q, hv⟩)}
    (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3)
    (hN : ¬ NormalizesRSub ⟨.E6 q, hv⟩ E₀) : HyperGen p ⊤ E₀ := by
  by_cases hsq : p ∣ q.card ^ 2 - 1
  · exact absurd (normalizesRSub_of_aut (ExcHigh.normalizesRSubgroup_E6_of_dvd_sq_sub_one q hv hp
      hp5 hsq (isPGroup_map_conj hE₀) (innerPlane_map_conj E₀))) hN
  rcases Nat.lt_or_ge (degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · exfalso
    rcases Nat.lt_or_ge (degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt' | hge'
    · exact false_of_rankLE2_of_card hp (rankLE1_cat_E6 q hv hp hpq (by omega)).rankLE2 hE₀ hc
    · exact false_of_rankLE2_of_card hp (rankLE2_cat_E6 q hv hp (by omega)) hE₀ hc
  · rcases eq_of_three_le_degCount_E6 hge with h1 | h2 | h3
    · exact absurd (dvd_sq_sub_one_of_orderOf_dvd_two (one_le_card q) (by rw [h1]; norm_num)) hsq
    · exact absurd (dvd_sq_sub_one_of_orderOf_dvd_two (one_le_card q) (by rw [h2])) hsq
    · exact hyperGen_of_unique_cube hp
        (ExcHigh.sylowTorus_cat_E6_three hv hp (ExcHigh.seven_le_of_orderOf_three hp hp5 h3) hpq h3)
        (h63 q hv p hp hp2 hpq hlist hsq h3) hE₀ hc hN

theorem hyperGen_E7 (h76 : ExcCubeHighAt LieTypeIndex.E7 6) {q : PrimePower}
    (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) (hlist : ¬ P1ThreeLieList p ⟨.E7 q, hv⟩) {E₀ : Subgroup (Cat ⟨.E7 q, hv⟩)}
    (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) (hN : ¬ NormalizesRSub ⟨.E7 q, hv⟩ E₀)
    (h2 : orderOf ((q.card : ℕ) : ZMod p) ≠ 2) : HyperGen p ⊤ E₀ := by
  rcases Nat.lt_or_ge (degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · exfalso
    rcases Nat.lt_or_ge (degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt' | hge'
    · exact false_of_rankLE2_of_card hp (rankLE1_cat_E7 q hv hp hpq (by omega)).rankLE2 hE₀ hc
    · exact false_of_rankLE2_of_card hp (rankLE2_cat_E7 q hv hp (by omega)) hE₀ hc
  · rcases eq_of_three_le_degCount_E7 hge with h1 | h2' | h3 | h6
    · exact absurd (normalizesRSub_of_aut (ExcHigh.normalizesRSubgroup_E7_A6_of_not_dvd_index q hv
        hp (ExcHigh.not_dvd_index_A6_of_dvd_sub_one hp hp5 (one_le_card q)
          (ExcHigh.dvd_sub_one_of_orderOf_eq_one (one_le_card q) h1))
        (isPGroup_map_conj hE₀) (innerPlane_map_conj E₀))) hN
    · exact absurd h2' h2
    · exact absurd (normalizesRSub_of_aut (ExcHigh.normalizesRSubgroup_E7_of_not_dvd_index q hv
        hp (ExcHigh.not_dvd_index_E7_of_orderOf_eq_three hp hp5 h3)
        (isPGroup_map_conj hE₀) (innerPlane_map_conj E₀))) hN
    · exact hyperGen_of_unique_cube hp
        (ExcHigh.sylowTorus_cat_E7_six hv hp (ExcHigh.seven_le_of_orderOf_six hp h6) hpq h6)
        (h76 q hv p hp hp2 hpq hlist
          (ExcHigh.not_dvd_sq_sub_one_of_orderOf hp (one_le_card q) h6 (by decide)) h6)
        hE₀ hc hN

theorem false_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ≠ q.p) {E₀ : Subgroup (Cat ⟨.E8 q, hv⟩)} (hE₀ : IsElemAbelian p E₀)
    (hc : Nat.card E₀ = p ^ 3) (hN : ¬ NormalizesRSub ⟨.E8 q, hv⟩ E₀)
    (hopen : ¬ (orderOf ((q.card : ℕ) : ZMod p) = 2 ∨ orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 4 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6 ∨
      (p = 5 ∧ orderOf ((q.card : ℕ) : ZMod p) = 1))) : False := by
  rcases Nat.lt_or_ge (degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · rcases Nat.lt_or_ge (degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt' | hge'
    · exact false_of_rankLE2_of_card hp (rankLE1_cat_E8 q hv hp hpq (by omega)).rankLE2 hE₀ hc
    · exact false_of_rankLE2_of_card hp (rankLE2_cat_E8 q hv hp (by omega)) hE₀ hc
  · rcases eq_of_three_le_degCount_E8 hge with h1 | h2 | h3 | h4 | h6
    · have h5 : p ≠ 5 := fun h5 => hopen (Or.inr (Or.inr (Or.inr (Or.inr ⟨h5, h1⟩))))
      exact hN (normalizesRSub_of_aut (ExcHigh.normalizesRSubgroup_E8_of_dvd_sub_one q hv hp
        (seven_le_of_ne_five hp hp5 h5)
        (ExcHigh.dvd_sub_one_of_orderOf_eq_one (one_le_card q) h1) (isPGroup_map_conj hE₀)
        (innerPlane_map_conj E₀)))
    · exact hopen (Or.inl h2)
    · exact hopen (Or.inr (Or.inl h3))
    · exact hopen (Or.inr (Or.inr (Or.inl h4)))
    · exact hopen (Or.inr (Or.inr (Or.inr (Or.inl h6))))

theorem hyperGen_twistedE6 (h26 : ExcCubeHighAt LieTypeIndex.twistedE6 6) {q : PrimePower}
    (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) (hlist : ¬ P1ThreeLieList p ⟨.twistedE6 q, hv⟩)
    {E₀ : Subgroup (Cat ⟨.twistedE6 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3)
    (hN : ¬ NormalizesRSub ⟨.twistedE6 q, hv⟩ E₀) (h2 : orderOf ((q.card : ℕ) : ZMod p) ≠ 2) :
    HyperGen p ⊤ E₀ := by
  rcases Nat.lt_or_ge (degCountTw (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · exfalso
    rcases Nat.lt_or_ge (degCountTw (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt' | hge'
    · exact false_of_rankLE2_of_card hp
        (rankLE1_cat_twistedE6 q hv hp hpq (by omega)).rankLE2 hE₀ hc
    · exact false_of_rankLE2_of_card hp (rankLE2_cat_twistedE6 q hv hp (by omega)) hE₀ hc
  · rcases eq_of_three_le_degCountTw hge with h1 | h2' | h6
    · exact absurd (normalizesRSub_of_aut (ExcHigh.normalizesRSubgroup_twistedE6_of_dvd_sub_one q
        hv hp hp5 (ExcHigh.dvd_sub_one_of_orderOf_eq_one (one_le_card q) h1)
        (isPGroup_map_conj hE₀) (innerPlane_map_conj E₀))) hN
    · exact absurd h2' h2
    · exact hyperGen_of_unique_cube hp
        (ExcHigh.sylowTorus_cat_twE6_six hv hp (ExcHigh.seven_le_of_orderOf_six hp h6) hpq h6)
        (h26 q hv p hp hp2 hpq hlist
          (ExcHigh.not_dvd_sq_sub_one_of_orderOf hp (one_le_card q) h6 (by decide)) h6)
        hE₀ hc hN

end Families

section Orthogonal

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_primaryFactor_ne_X_sub_one {L W : Type*} [Field L] [AddCommGroup W] [Module L W]
    [FiniteDimensional L W] {x : Module.End L W} (hx : Squarefree (minpoly L x)) (hx1 : x ≠ 1) :
    ∃ c ∈ primaryFactors x, c ≠ X - C 1 := by
  classical
  by_contra hall
  push Not at hall
  have hdvd : minpoly L x ∣ X - C 1 := by
    rw [← prod_primaryFactors hx]
    have hsub : primaryFactors x ⊆ {X - C 1} := fun c hc => Finset.mem_singleton.mpr (hall c hc)
    calc ∏ a ∈ primaryFactors x, a ∣ ∏ a ∈ ({X - C 1} : Finset L[X]), a :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
      _ = X - C 1 := Finset.prod_singleton _ _
  have h0 : aeval x (X - C (1 : L)) = 0 := by
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  apply hx1
  simpa [sub_eq_zero] using h0

theorem exists_singular_of_oddOrder (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hodd : Odd (orderOf ((Nat.card K : ℕ) : ZMod p)))
    {x : V ≃ₗ[K] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ w ∈ W, Q w = 0) ∧
      ∀ y : V ≃ₗ[K] V, Commute y.toLinearMap x.toLinearMap → ∀ w ∈ W, y w ∈ W := by
  classical
  have hOdd : OddOrderIsometry Q p x := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    simpa using hv w⟩
  have hsq := hOdd.squarefree_minpoly
  have hx1' : x.toLinearMap ≠ 1 := fun h => hx1 (LinearEquiv.ext fun v => by
    simpa using LinearMap.congr_fun h v)
  obtain ⟨h, hh, hne1⟩ := exists_primaryFactor_ne_X_sub_one hsq hx1'
  have hne1' : h ≠ X - 1 := by rwa [← C_1]
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hpl : p ≠ ringChar K := fun hc => hpK (by rw [hc]; exact ringChar.Nat.cast_ringChar)
  have hdeg := natDegree_eq_orderOf_of_dvd hp hpl hmon hirr (hOdd.dvd_X_pow_sub_one hh) hne1'
  have hself : h ≠ reciprocalPolynomial h := by
    intro hs
    obtain ⟨d, hd, -⟩ := hOdd.selfDualModel (hp.odd_of_ne_two hp2) hh hne1' hs
    rw [hdeg] at hd
    exact (Nat.not_even_iff_odd.2 hodd) ⟨d, by omega⟩
  set W₀ := primaryComponent x.toLinearMap h with hW₀def
  have hW₀ : W₀ ≠ ⊥ := primaryComponent_ne_bot hsq hh
  have hpol : ∀ v ∈ W₀, ∀ w ∈ W₀, polar Q v w = 0 := fun v hv w hw =>
    hOdd.polar_primaryComponent_eq_zero hh hh hself hv hw
  have hxW₀ : ∀ v ∈ W₀, x v ∈ W₀ := fun v hv => apply_mem_primaryComponent (Commute.refl _) hv
  refine ⟨W₀.map (x.toLinearMap - 1), ?_, ?_, ?_⟩
  · intro hbot
    apply hW₀
    rw [eq_bot_iff]
    intro v hv
    have h1 : (x.toLinearMap - 1) v = 0 := by
      have : (x.toLinearMap - 1) v ∈ W₀.map (x.toLinearMap - 1) := ⟨v, hv, rfl⟩
      rw [hbot] at this
      exact (Submodule.mem_bot K).1 this
    have hv1 : v ∈ primaryComponent x.toLinearMap (X - C 1) := by
      rw [mem_primaryComponent]
      simpa using h1
    have hcop : IsCoprime h (X - C 1) := isCoprime_of_irreducible_monic_ne hirr
      (irreducible_X_sub_C 1) hmon (monic_X_sub_C 1) hne1
    exact (Submodule.mem_bot K).2 (Submodule.disjoint_def.1
      (Polynomial.disjoint_ker_aeval_of_isCoprime x.toLinearMap hcop) v hv hv1)
  · rintro _ ⟨u, hu, rfl⟩
    have h1 : polar Q (x u) u = 0 := hpol _ (hxW₀ u hu) _ hu
    have h2 : polar Q u u = 0 := hpol _ hu _ hu
    have h3 : Q (x u) = Q u := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hxO) u
    have h4 : polar Q (x u) (-u) = Q (x u + -u) - Q (x u) - Q (-u) := rfl
    rw [polar_neg_right, h1, neg_zero, QuadraticMap.map_neg, h3] at h4
    have h5 : polar Q u u = 2 • Q u := polar_self Q u
    rw [h2, two_smul] at h5
    have e : (x.toLinearMap - 1) u = x u + -u := by simp [sub_eq_add_neg]
    rw [e]
    linear_combination (-1 : K) * h4 - h5
  · intro y hy w hw
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨y u, apply_mem_primaryComponent hy hu, ?_⟩
    have hc : y.toLinearMap * (x.toLinearMap - 1) = (x.toLinearMap - 1) * y.toLinearMap :=
      (hy.sub_right (Commute.one_right _)).eq
    exact (LinearMap.congr_fun hc u).symm

theorem exists_singular_stable_of_oddOrder {G : Type} [Group G] {π : elementaryGroup Q →* G}
    (hc : IsOrthogonalCover Q π) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hodd : Odd (orderOf ((Nat.card K : ℕ) : ZMod p))) {E₀ : Subgroup G}
    (hE : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      ∀ g : elementaryGroup Q, π g ∈ E₀ → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  have hE1 : 1 < Nat.card E₀ := by
    rw [hcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have h1 : ∀ a b : elementaryGroup Q, a = b := fun a b =>
      Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    have h2 : ∀ a b : G, a = b := fun a b => by
      obtain ⟨a', rfl⟩ := hc.surjective a
      obtain ⟨b', rfl⟩ := hc.surjective b
      rw [h1 a' b']
    have h3 : Nat.card E₀ ≤ 1 := Finite.card_le_one_iff_subsingleton.2
      ⟨fun a b => Subtype.ext (h2 _ _)⟩
    omega
  have hker := not_dvd_card_ker_of_scalar hc hp hp2
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, -, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian π hc.surjective hker hcomm hE.2
  obtain ⟨a₀, ha₀1⟩ : ∃ a : A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card A ≤ 1 := Finite.card_le_one_iff_subsingleton.2 ⟨fun x y => by
      rw [hcon x, hcon y]⟩
    omega
  set x : V ≃ₗ[K] V := ((a₀ : elementaryGroup Q) : V ≃ₗ[K] V) with hxdef
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (a₀ : elementaryGroup Q).2
  have hxp : x ^ p = 1 := by
    have := congrArg (fun g : elementaryGroup Q => (g : V ≃ₗ[K] V)) (hAexp _ a₀.2)
    simpa [hxdef] using this
  have hx1 : x ≠ 1 := fun h1 => ha₀1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨W, hW0, hWQ, hWst⟩ := exists_singular_of_oddOrder hc.nondegenerate hp hp2 hpK hodd
    hxO hxp hx1
  refine ⟨W, hW0, hWQ, fun g hg w hw => ?_⟩
  rw [← hAE] at hg
  obtain ⟨a, ha, hag⟩ := hg
  have hz : a⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
  obtain ⟨c, hcz⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.1 (hc.ker_scalar _ hz)
  have hcomm_a : Commute ((a : elementaryGroup Q) : V ≃ₗ[K] V).toLinearMap x.toLinearMap := by
    have h1 := hAcomm a ha (a₀ : elementaryGroup Q) a₀.2
    have h2 : ((a * a₀ : elementaryGroup Q) : V ≃ₗ[K] V) =
        ((a₀ * a : elementaryGroup Q) : V ≃ₗ[K] V) := by rw [h1]
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun e : V ≃ₗ[K] V => e v) h2
    simpa [hxdef] using this
  have hga : g = a * (a⁻¹ * g) := by group
  rw [hga, Subgroup.coe_mul, LinearEquiv.mul_apply, hcz w]
  exact hWst _ hcomm_a _ (W.smul_mem c hw)

end Model

theorem exists_orth_model_card {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1)
    {p : ℕ} (hp : p.Prime) (hpd : p ≠ d.1.characteristic) :
    ∃ (q : TauCeti.PrimePower) (K V : Type) (_ : Field K) (_ : Finite K) (_ : AddCommGroup V)
      (_ : Module K V) (_ : FiniteDimensional K V) (Q : QuadraticForm K V)
      (π : elementaryGroup Q →* Cat d),
      (∃ r, d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) ∧ Nat.card K = q.card ∧
        IsOrthogonalCover Q π ∧ (p : K) ≠ 0 := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard
      have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p :=
        ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 :=
      natCast_ne_zero_of_not_dvd_card hp (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    obtain ⟨V, _, _, _, Q, π, hπ⟩ := orthCover_odd hr3 h2
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq hr3)
    exact ⟨q, _, V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q,
      π, ⟨r, Or.inl rfl⟩, by rw [hcard, TauCeti.PrimePower.card_def], hπ, hpK⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) ≠ 0 :=
      natCast_ne_zero_of_not_dvd_card hp (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    obtain ⟨V, _, _, _, Q, π, hπ⟩ := orthCover_plus (by omega : 3 ≤ r)
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)
    exact ⟨q, _, V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q,
      π, ⟨r, Or.inr (Or.inl rfl)⟩, by rw [hcard, TauCeti.PrimePower.card_def], hπ, hpK⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)) ≠ 0 :=
      natCast_ne_zero_of_not_dvd_card hp (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    obtain ⟨V, _, _, _, Q, π, hπ⟩ := orthCover_minus hr4 hirr e
    exact ⟨q, _, V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q,
      π, ⟨r, Or.inr (Or.inr rfl)⟩, by rw [hcard, TauCeti.PrimePower.card_def], hπ, hpK⟩

theorem oReducible_of_oddOrder {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hodd : ∃ (r : ℕ) (q : TauCeti.PrimePower),
      (d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) ∧
        Odd (orderOf ((q.card : ℕ) : ZMod p)))
    {E₀ : Subgroup (Cat d)} (hE : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3) :
    OReducible d p E₀ := by
  obtain ⟨q, K, V, _, _, _, _, _, Q, π, ⟨r, hdq⟩, hK, hc, hpK⟩ := exists_orth_model_card hd hp hpd
  obtain ⟨r', q', hdq', hodd'⟩ := hodd
  have hqq : q' = q := by
    rcases hdq with h | h | h <;> rcases hdq' with h' | h' | h' <;> rw [h] at h' <;>
      first
        | (cases h'; rfl)
        | exact absurd h' (by simp)
  subst hqq
  exact ⟨K, V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, π, hc,
    hpK, exists_singular_stable_of_oddOrder hc hp hp2 hpK (by rw [hK]; exact hodd') hE hcard⟩

end Orthogonal

section OrthHigh

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.CTP OrthBlk OrthNS HyperBlocks
open CFSG.RankThree.Classical2 (orthDerived)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem finite_linearEquiv : Finite (V ≃ₗ[K] V) := by
  haveI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective

@[expose] noncomputable def aRep (A : Subgroup (elementaryGroup Q)) : A →* Module.End K V :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)).comp
    ((elementaryGroup Q).subtype.comp A.subtype)

theorem aRep_apply (A : Subgroup (elementaryGroup Q)) (a : A) (v : V) :
    aRep A a v = ((a : elementaryGroup Q) : V ≃ₗ[K] V) v := rfl

theorem finite_sub (A : Subgroup (elementaryGroup Q)) : Finite A := by
  haveI := (finite_linearEquiv : Finite (V ≃ₗ[K] V))
  infer_instance

noncomputable abbrev topFintype (A : Subgroup (elementaryGroup Q)) :
    Fintype (⊤ : Subgroup A) :=
  haveI := finite_sub A
  Fintype.ofFinite _

@[expose] noncomputable def hblk (A : Subgroup (elementaryGroup Q)) (F : Subgroup A) :
    Submodule K V :=
  letI := topFintype A
  block (aRep A) ⊤ F

structure HighSetup (Q : QuadraticForm K V) (p : ℕ) (A : Subgroup (elementaryGroup Q)) :
    Prop where
  nondeg : (polarBilin Q).Nondegenerate
  prime : p.Prime
  cast_ne_zero : (p : K) ≠ 0
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  pow_eq_one : ∀ a ∈ A, a ^ p = 1
  card_eq : Nat.card A = p ^ 3
  four_le : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)

namespace HighSetup

variable {p : ℕ} {A : Subgroup (elementaryGroup Q)}

theorem not_dvd_card (S : HighSetup Q p A) : ¬ p ∣ Nat.card K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  intro hd
  rw [Nat.card_eq_fintype_card, hcard] at hd
  have hpl : p = ringChar K :=
    (Nat.prime_dvd_prime_iff_eq S.prime hℓ).1 (S.prime.dvd_of_dvd_pow hd)
  exact S.cast_ne_zero (by rw [hpl]; exact ringChar.Nat.cast_ringChar)

theorem five_le (S : HighSetup Q p A) : 5 ≤ p := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  have h0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h0 =>
    S.not_dvd_card ((ZMod.natCast_eq_zero_iff _ p).1 h0)
  have hdvd : orderOf ((Nat.card K : ℕ) : ZMod p) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
  have := Nat.le_of_dvd (by have := S.prime.two_le; omega) hdvd
  have := S.four_le
  omega

theorem isElemAbelian (S : HighSetup Q p A) : IsElemAbelian p A :=
  ⟨⟨⟨fun a b => Subtype.ext (S.comm a a.2 b b.2)⟩⟩, S.pow_eq_one⟩

theorem comm' (S : HighSetup Q p A) (a b : A) : a * b = b * a :=
  Subtype.ext (S.comm a a.2 b b.2)

theorem pow' (S : HighSetup Q p A) (a : A) : a ^ p = 1 :=
  Subtype.ext (by simpa using S.pow_eq_one a a.2)

end HighSetup

theorem mem_orth {A : Subgroup (elementaryGroup Q)} (a : A) :
    ((a : elementaryGroup Q) : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q (a : elementaryGroup Q).2

theorem polar_aRep {A : Subgroup (elementaryGroup Q)} (a : A) (x y : V) :
    polarBilin Q (aRep A a x) (aRep A a y) = polarBilin Q x y := by
  simp only [polarBilin_apply_apply, aRep_apply]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (mem_orth a) x y

theorem eq_one_of_aRep {A : Subgroup (elementaryGroup Q)} (a : A) (h : aRep A a = 1) : a = 1 := by
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
  have := LinearMap.congr_fun h v
  simpa [aRep_apply] using this

namespace HighSetup

variable {p : ℕ} {A : Subgroup (elementaryGroup Q)}

section Blocks

variable (S : HighSetup Q p A)
include S

theorem card_top_ne_zero : letI := topFintype A
    ((Fintype.card (⊤ : Subgroup A) : ℕ) : K) ≠ 0 := by
  letI := topFintype A
  rw [Fintype.card_eq_nat_card, Subgroup.card_top, S.card_eq, Nat.cast_pow]
  exact pow_ne_zero 3 S.cast_ne_zero

omit S in
theorem hblk_le_fixSub (F : Subgroup A) : hblk A F ≤ fixSub (aRep A) F := by
  letI := topFintype A
  exact inf_le_left

theorem fixSub_inf_hblk (F : Subgroup A) : fixSub (aRep A) ⊤ ⊓ hblk A F = ⊥ := by
  letI := topFintype A
  exact fixSub_inf_block (aRep A) S.card_top_ne_zero F

theorem fixSub_eq (F : Subgroup A) : fixSub (aRep A) F = fixSub (aRep A) ⊤ ⊔ hblk A F := by
  letI := topFintype A
  exact fixSub_eq_sup (aRep A) S.card_top_ne_zero le_top

theorem hblk_stable (F : Subgroup A) (a : A) {v : V} (hv : v ∈ hblk A F) :
    aRep A a v ∈ hblk A F := by
  letI := topFintype A
  exact block_invariant (aRep A) le_top (fun a _ b _ => S.comm' a b) (Subgroup.mem_top a) hv

theorem eq_zero_of_fixed {F : Subgroup A} (hF : F.index = p) {x : A} (hx : x ∉ F) {v : V}
    (hv : v ∈ hblk A F) (hxv : aRep A x v = v) : v = 0 := by
  letI := topFintype A
  exact block_fixed_eq_zero (aRep A) S.card_top_ne_zero
    (sup_zpowers_eq S.prime le_top (by rw [Subgroup.relIndex_top_right]; exact hF)
      (Subgroup.mem_top x) hx) hv hxv

theorem sup_eq_top {F F' : Subgroup A} (hF : F.index = p) (hF' : F'.index = p)
    (hne : F ≠ F') : F ⊔ F' = ⊤ :=
  sup_eq_of_ne_relIndex_prime S.prime le_top le_top
    (by rw [Subgroup.relIndex_top_right]; exact hF)
    (by rw [Subgroup.relIndex_top_right]; exact hF') hne

theorem hblk_inf {F F' : Subgroup A} (hF : F.index = p) (hF' : F'.index = p) (hne : F ≠ F') :
    hblk A F ⊓ hblk A F' = ⊥ := by
  letI := topFintype A
  exact block_inf_block (aRep A) S.card_top_ne_zero (S.sup_eq_top hF hF' hne)

theorem card_hyperplane {F : Subgroup A} (hF : F.index = p) : Nat.card F = p ^ 2 := by
  have h := F.card_mul_index
  rw [hF, S.card_eq] at h
  have : Nat.card F * p = p ^ 2 * p := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right S.prime.pos this

theorem polar_hblk {F F' : Subgroup A} (hF : F.index = p) (hF' : F'.index = p) (hne : F ≠ F')
    {v w : V} (hv : v ∈ hblk A F) (hw : w ∈ hblk A F') : polar Q v w = 0 := by
  letI := topFintype A
  haveI := finite_sub A
  letI : Fintype F := Fintype.ofFinite _
  letI : Fintype F' := Fintype.ofFinite _
  have hKF : ((Fintype.card F : ℕ) : K) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, S.card_hyperplane hF, Nat.cast_pow]
    exact pow_ne_zero 2 S.cast_ne_zero
  have h := block_orthogonal (aRep A) S.card_top_ne_zero (polarBilin Q)
    (fun g x y => polar_aRep g x y) (fun a _ b _ => S.comm' a b) le_top le_top
    (S.sup_eq_top hF hF' hne) hKF hv hw
  simpa [polarBilin_apply_apply] using h

theorem polar_fixSub_hblk {F : Subgroup A} {v w : V} (hv : v ∈ fixSub (aRep A) ⊤)
    (hw : w ∈ hblk A F) : polar Q v w = 0 := by
  letI := topFintype A
  have h1 := sumOp_adjoint (aRep A) (polarBilin Q) (fun g x y => polar_aRep g x y) ⊤ v w
  rw [sumOp_apply_of_fix (aRep A) ⊤ hv, LinearMap.mem_ker.mp hw.2, map_zero,
    LinearMap.map_smul₂] at h1
  simp only [LinearMap.smul_apply, smul_eq_mul, polarBilin_apply_apply] at h1
  exact (mul_eq_zero.mp h1).resolve_left S.card_top_ne_zero

theorem le_sup_hblk :
    (⊤ : Submodule K V) ≤ fixSub (aRep A) ⊤ ⊔ ⨆ (F : Subgroup A) (_ : F.index = p), hblk A F := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := finite_sub A
  intro m _
  have h := mem_iSup_hyperFixed_top S.cast_ne_zero S.comm' S.pow' (aRep A) ⊤
    (fun _ _ _ => Submodule.mem_top) (k := 3) (by norm_num) S.card_eq
    (Submodule.mem_top (x := m))
  have hle : (⨆ (F : Subgroup A) (_ : F.index = p), hyperFixed (aRep A) F ⊓ ⊤) ≤
      fixSub (aRep A) ⊤ ⊔ ⨆ (F : Subgroup A) (_ : F.index = p), hblk A F := by
    refine iSup₂_le fun F hF => ?_
    intro v hv
    have hvF : v ∈ fixSub (aRep A) F := fun f hf => mem_hyperFixed.1 hv.1 f hf
    rw [S.fixSub_eq F] at hvF
    exact (sup_le_sup_left
      (le_iSup₂ (f := fun (F : Subgroup A) (_ : F.index = p) => hblk A F) F hF) _) hvF
  exact hle h

theorem orderOf_le_finrank {F : Subgroup A} (h0 : hblk A F ≠ ⊥) :
    orderOf ((Nat.card K : ℕ) : ZMod p) ≤ finrank K (hblk A F) := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := finite_sub A
  haveI : Finite V := Module.finite_of_finite K
  set B := hblk A F with hB
  let _ : MulAction A B :=
    { smul := fun a v => ⟨aRep A a v, S.hblk_stable F a v.2⟩
      one_smul := fun v => Subtype.ext (by
        change aRep A 1 v = v
        rw [map_one]
        rfl)
      mul_smul := fun a b v => Subtype.ext (by
        change aRep A (a * b) v = aRep A a (aRep A b v)
        rw [map_mul]
        rfl) }
  have hfix : MulAction.fixedPoints A B = {0} := by
    ext v
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hv
      apply Subtype.ext
      have hvA : (v : V) ∈ fixSub (aRep A) ⊤ := fun a _ => congrArg Subtype.val (hv a)
      have : (v : V) ∈ fixSub (aRep A) ⊤ ⊓ hblk A F := ⟨hvA, v.2⟩
      rw [S.fixSub_inf_hblk F] at this
      exact this
    · rintro rfl a
      apply Subtype.ext
      change aRep A a 0 = 0
      exact map_zero _
  have h := (IsPGroup.of_card S.card_eq).card_modEq_card_fixedPoints B
  have hone : Nat.card (MulAction.fixedPoints A B) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  rw [hone, Module.natCard_eq_pow_finrank (K := K) (V := B)] at h
  have h1 : ((Nat.card K : ℕ) : ZMod p) ^ finrank K B = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ p).2 h
    push_cast at this
    exact this
  have hpos : 0 < finrank K B := Submodule.one_le_finrank_iff.2 h0
  exact Nat.le_of_dvd hpos (orderOf_dvd_of_pow_eq_one h1)

theorem exists_two_hblk : ∃ F₁ F₂ : Subgroup A, F₁.index = p ∧ F₂.index = p ∧ F₁ ≠ F₂ ∧
    hblk A F₁ ≠ ⊥ ∧ hblk A F₂ ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := finite_sub A
  by_contra hcon
  push Not at hcon
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 2)
    (by rw [S.card_eq]; exact pow_dvd_pow p (by norm_num))
  have hF₀i : F₀.index = p := by
    have h := F₀.card_mul_index
    rw [hF₀, S.card_eq] at h
    have : p ^ 2 * F₀.index = p ^ 2 * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos S.prime.pos 2) this
  obtain ⟨F₁, hF₁, hall⟩ : ∃ F₁ : Subgroup A, F₁.index = p ∧
      ∀ F : Subgroup A, F.index = p → F ≠ F₁ → hblk A F = ⊥ := by
    by_cases hex : ∃ F : Subgroup A, F.index = p ∧ hblk A F ≠ ⊥
    · obtain ⟨F₁, hF₁, hb₁⟩ := hex
      exact ⟨F₁, hF₁, fun F hF hne => hcon F₁ F hF₁ hF (Ne.symm hne) hb₁⟩
    · push Not at hex
      exact ⟨F₀, hF₀i, fun F hF _ => hex F hF⟩
  have htriv : ∀ f ∈ F₁, aRep A f = 1 := by
    intro f hf
    refine LinearMap.ext fun v => ?_
    have hv := S.le_sup_hblk (Submodule.mem_top (x := v))
    have hle : fixSub (aRep A) ⊤ ⊔ ⨆ (F : Subgroup A) (_ : F.index = p), hblk A F ≤
        fixSub (aRep A) F₁ := by
      refine sup_le (fun w hw g _ => hw g (Subgroup.mem_top g)) (iSup₂_le fun F hF => ?_)
      by_cases hFF : F = F₁
      · rw [hFF]
        exact hblk_le_fixSub F₁
      · rw [hall F hF hFF]
        exact bot_le
    exact hle hv f hf
  obtain ⟨f, hfF, hf1⟩ : ∃ f ∈ F₁, f ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : F₁ = ⊥ := (Subgroup.eq_bot_iff_forall F₁).2 h
    have := S.card_hyperplane hF₁
    rw [hbot, Subgroup.card_bot] at this
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) S.prime.one_lt
    omega
  exact hf1 (eq_one_of_aRep f (htriv f hfF))

omit S in
theorem dvd_of_zpow_mem (hp : p.Prime) {F : Subgroup A} {x : A} (hxp : x ^ p = 1) (hx : x ∉ F)
    {j : ℤ} (hj : x ^ j ∈ F) : (p : ℤ) ∣ j := by
  by_contra hpj
  have hcop : IsCoprime j (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    have h1 : ¬ p ∣ j.natAbs := fun h => hpj (Int.natCast_dvd.2 h)
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 h1) |>.symm
  obtain ⟨a, b, hab⟩ := hcop
  have hx' : x = (x ^ j) ^ a * (x ^ (p : ℤ)) ^ b := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm j a, mul_comm (p : ℤ) b, hab, zpow_one]
  rw [zpow_natCast, hxp, one_zpow, mul_one] at hx'
  exact hx (hx' ▸ F.zpow_mem hj a)

theorem eichler_mem {F₁ F₂ : Subgroup A} (h1 : F₁.index = p) (h2 : F₂.index = p)
    (hne : F₁ ≠ F₂) (hb1 : hblk A F₁ ≠ ⊥) (hb2 : hblk A F₂ ≠ ⊥) :
    ∀ e ∈ fixSub (aRep A) (F₁ ⊓ F₂), ∀ w ∈ fixSub (aRep A) (F₁ ⊓ F₂),
      eichler Q e w ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := finite_sub A
  have hp2 : p ≠ 2 := by have := S.five_le; omega
  obtain ⟨f, hf, hf1⟩ : ∃ f ∈ F₁ ⊓ F₂, f ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : F₁ ⊓ F₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    have hle := Subgroup.index_inf_le (H := F₁) (K := F₂)
    rw [hbot, Subgroup.index_bot, S.card_eq, h1, h2] at hle
    have : p * p < p ^ 3 := by
      have := S.prime.two_le
      calc p * p = p ^ 2 := by ring
        _ < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  set fV : V ≃ₗ[K] V := ((f : elementaryGroup Q) : V ≃ₗ[K] V) with hfV
  set U := fixIn fV ⊤ with hUdef
  have hfO : fV ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mem_orth f
  have hfp : fV ^ p = 1 := by
    have := congrArg (fun g : A => ((g : elementaryGroup Q) : V ≃ₗ[K] V)) (S.pow' f)
    simpa [hfV] using this
  have hU : PolarNondegOn Q U := polarNondegOn_fixIn hfO hfp S.cast_ne_zero
    (polarNondegOn_top S.nondeg) fun _ _ => Submodule.mem_top
  have hinU : ∀ {G : Subgroup A}, f ∈ G → fixSub (aRep A) G ≤ U := fun hfG v hv =>
    mem_fixIn.2 ⟨Submodule.mem_top, hv f hfG⟩
  have hb1U : hblk A F₁ ≤ U := (hblk_le_fixSub F₁).trans (hinU hf.1)
  have hb2U : hblk A F₂ ≤ U := (hblk_le_fixSub F₂).trans (hinU hf.2)
  have h8 : 8 ≤ finrank K U := by
    have hsup : hblk A F₁ ⊔ hblk A F₂ ≤ U := sup_le hb1U hb2U
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (hblk A F₁) (hblk A F₂)
    rw [S.hblk_inf h1 h2 hne, finrank_bot, add_zero] at hd
    have := Submodule.finrank_mono hsup
    have := S.orderOf_le_finrank hb1
    have := S.orderOf_le_finrank hb2
    have := S.four_le
    omega
  have hTU := exists_ts_three_comp hU h8
  have hQU := nondegenerate_comp_subtype hU
  have hEU := (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQU hTU).1
  have hpl : p ≠ ringChar K := fun h => S.cast_ne_zero (by rw [h]; exact ringChar.Nat.cast_ringChar)
  have hnle : ∀ {G G' : Subgroup A}, G.index = p → G'.index = p → G ≠ G' → ∃ x ∈ G, x ∉ G' := by
    intro G G' hG hG' hGG
    by_contra h
    push Not at h
    exact hGG (Subgroup.eq_of_le_of_card_ge h (by rw [S.card_hyperplane hG, S.card_hyperplane hG']))
  obtain ⟨X, hX1, hX2⟩ := hnle h1 h2 hne
  obtain ⟨Y, hY2, hY1⟩ := hnle h2 h1 hne.symm
  have hst : ∀ a : A, ((a : elementaryGroup Q) : V ≃ₗ[K] V) ∈ stab U := fun a =>
    stab_fixIn_of_commute (by
      have := congrArg (fun g : A => ((g : elementaryGroup Q) : V ≃ₗ[K] V)) (S.comm' f a)
      exact this)
  let φ : A →* stab U := MonoidHom.codRestrict
    ((elementaryGroup Q).subtype.comp A.subtype) (stab U) hst
  have hRO : ∀ a : A, res U (φ a) ∈ orthDerived (Q.comp U.subtype) := fun a =>
    mem_orthDerived_of_odd_pow hQU hTU (S.prime.odd_of_ne_two hp2)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun u => by
        change Q (((a : elementaryGroup Q) : V ≃ₗ[K] V) (u : V)) = Q (u : V)
        exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (mem_orth a) u)
      (by rw [← map_pow, ← map_pow, S.pow' a, map_one, map_one])
  let R : A →* orthDerived (Q.comp U.subtype) := ((res U).comp φ).codRestrict _ hRO
  have hRv : ∀ (a : A) (u : U), (((R a : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) u : V) =
      aRep A a u := fun _ _ => rfl
  have hind : ∀ i j : ℤ, R X ^ i * R Y ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j hij
    have hfix : ∀ u ∈ U, aRep A (X ^ i * Y ^ j) u = u := by
      intro u hu
      have := congrArg (fun z : orthDerived (Q.comp U.subtype) =>
        (((z : U ≃ₗ[K] U) ⟨u, hu⟩ : U) : V)) hij
      simp only [← map_zpow, ← map_mul, hRv] at this
      exact this
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb1
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb2
    have hXv : aRep A (X ^ i) v = v := hblk_le_fixSub F₁ hv _ (F₁.zpow_mem hX1 i)
    have hYw : aRep A (Y ^ j) w = w := hblk_le_fixSub F₂ hw _ (F₂.zpow_mem hY2 j)
    have hYv : aRep A (Y ^ j) v = v := by
      have h1' := hfix v (hb1U hv)
      rw [map_mul, Module.End.mul_apply] at h1'
      have hc : aRep A (X ^ i) (aRep A (Y ^ j) v) = aRep A (Y ^ j) (aRep A (X ^ i) v) := by
        rw [← Module.End.mul_apply, ← map_mul, S.comm' (X ^ i) (Y ^ j), map_mul,
          Module.End.mul_apply]
      rw [hc, hXv] at h1'
      exact h1'
    have hXw : aRep A (X ^ i) w = w := by
      have h1' := hfix w (hb2U hw)
      rw [map_mul, Module.End.mul_apply, hYw] at h1'
      exact h1'
    constructor
    · by_contra hpi
      have hXi : X ^ i ∉ F₂ := fun hmem => hpi (dvd_of_zpow_mem S.prime (S.pow' X) hX2 hmem)
      exact hw0 (S.eq_zero_of_fixed h2 hXi hw hXw)
    · by_contra hpj
      have hYj : Y ^ j ∉ F₁ := fun hmem => hpj (dvd_of_zpow_mem S.prime (S.pow' Y) hY1 hmem)
      exact hv0 (S.eq_zero_of_fixed h1 hYj hv hYv)
  have hRp : ∀ a : A, R a ^ p = 1 := fun a => by rw [← map_pow, S.pow' a, map_one]
  obtain ⟨P', hP'c, hP'p, hP'card, hP'form⟩ := OrthBlk.exists_plane_of_two S.prime
    ((Commute.map (S.comm' X Y : Commute X Y) R)) (hRp X) (hRp Y) hind
  have hgen := orthMaster K U (Q.comp U.subtype) hQU hTU (by omega) p S.prime S.five_le hpl P'
    hP'c hP'p hP'card
  set H := (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype with hHdef
  have hle : Subgroup.closure {h : orthDerived (Q.comp U.subtype) | ∃ x ∈ P', x ≠ 1 ∧
      h * x = x * h} ≤ H.comap ((extU hU).comp (orthDerived (Q.comp U.subtype)).subtype) := by
    rw [Subgroup.closure_le]
    rintro h ⟨x, hxP, hx1, hhx⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    obtain ⟨i, j, rfl⟩ := hP'form x hxP
    have hXst := hst (X ^ i * Y ^ j)
    refine extU_mem_hyperClosure hU hEU S.prime S.isElemAbelian S.card_eq
      (a := (f : elementaryGroup Q)) (X := ((X ^ i * Y ^ j : A) : elementaryGroup Q)) f.2
      (X ^ i * Y ^ j).2 (fun h1' => hf1 (Subtype.ext h1')) (fun u hu => (mem_fixIn.1 hu).2)
      hXst hx1 (hP'p _ hxP) ?_ hhx
    rw [← map_zpow, ← map_zpow, ← map_mul]
    rfl
  intro e he w hw
  have heU : e ∈ U := hinU hf he
  have hwU : w ∈ U := hinU hf hw
  have hmem : eichler (Q.comp U.subtype) ⟨e, heU⟩ ⟨w, hwU⟩ ∈
      orthDerived (Q.comp U.subtype) := by
    rw [hEU]
    exact eichler_mem_elementaryGroup _ _ _
  have htop : (⟨eichler (Q.comp U.subtype) ⟨e, heU⟩ ⟨w, hwU⟩, hmem⟩ :
      orthDerived (Q.comp U.subtype)) ∈ Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
        ∃ x ∈ P', x ≠ 1 ∧ h * x = x * h} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have := Subgroup.mem_comap.mp (hle htop)
  rwa [MonoidHom.comp_apply, Subgroup.coe_subtype, extU_eichler] at this

theorem hyperClosure_eq_top : hyperClosure p ⊤ A = ⊤ := by
  classical
  obtain ⟨F₁, F₂, h1, h2, hne, hb1, hb2⟩ := S.exists_two_hblk
  set H := (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype with hHdef
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q x.2
  let ι := {F : Subgroup A // F.index = p ∧ F ≠ F₁ ∧ hblk A F ≠ ⊥}
  haveI : Nonempty ι := ⟨⟨F₂, h2, hne.symm, hb2⟩⟩
  set V₀ := fixSub (aRep A) (⊤ : Subgroup A) with hV₀
  have hP0 : OrthSep Q (hblk A F₁) V₀ := fun s hs t ht => by
    rw [polar_comm]
    exact S.polar_fixSub_hblk ht hs
  have hPR : ∀ i : ι, OrthSep Q (hblk A F₁) (hblk A i.1) := fun i s hs t ht =>
    S.polar_hblk h1 i.2.1 i.2.2.1.symm hs ht
  have hspan : (⊤ : Submodule K V) ≤ V₀ ⊔ hblk A F₁ ⊔ ⨆ i : ι, hblk A i.1 := by
    refine S.le_sup_hblk.trans (sup_le (le_sup_left.trans le_sup_left) (iSup₂_le fun F hF => ?_))
    by_cases hF1 : F = F₁
    · rw [hF1]
      exact le_sup_right.trans le_sup_left
    · by_cases hb : hblk A F = ⊥
      · rw [hb]
        exact bot_le
      · exact (le_iSup (fun i : ι => hblk A i.1) ⟨F, hF, hF1, hb⟩).trans le_sup_right
  have hP : PolarNondegOn Q (hblk A F₁) := by
    intro x hx hxy
    have hker : V₀ ⊔ hblk A F₁ ⊔ ⨆ i : ι, hblk A i.1 ≤ LinearMap.ker (polarBilin Q x) := by
      refine sup_le (sup_le ?_ ?_) (iSup_le fun i => ?_)
      · intro y hy
        rw [LinearMap.mem_ker, polarBilin_apply_apply, polar_comm]
        exact S.polar_fixSub_hblk hy hx
      · intro y hy
        rw [LinearMap.mem_ker, polarBilin_apply_apply]
        exact hxy y hy
      · intro y hy
        rw [LinearMap.mem_ker, polarBilin_apply_apply]
        exact S.polar_hblk h1 i.2.1 i.2.2.1.symm hx hy
    exact S.nondeg.1 x fun y => LinearMap.mem_ker.1 (hker (hspan Submodule.mem_top))
  have h3 : 3 ≤ finrank K (hblk A F₁) := by
    have := S.orderOf_le_finrank hb1
    have := S.four_le
    omega
  have hEich : ∀ i : ι, ∀ e ∈ V₀ ⊔ hblk A F₁ ⊔ hblk A i.1,
      ∀ w ∈ V₀ ⊔ hblk A F₁ ⊔ hblk A i.1, eichler Q e w ∈ H := by
    intro i e he w hw
    have hle : V₀ ⊔ hblk A F₁ ⊔ hblk A i.1 ≤ fixSub (aRep A) (F₁ ⊓ i.1) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact fun v hv g _ => hv g (Subgroup.mem_top g)
      · exact fun v hv g hg => hblk_le_fixSub F₁ hv g hg.1
      · exact fun v hv g hg => hblk_le_fixSub i.1 hv g hg.2
    exact S.eichler_mem h1 i.2.1 i.2.2.1.symm hb1 i.2.2.2 e (hle he) w (hle hw)
  have hle := elementaryGroup_le_of_pieces S.nondeg hHO hP h3 (fun i : ι => hblk A i.1) hP0 hPR
    hspan hEich
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show x = y from Subtype.ext hyx.symm]

end Blocks

end HighSetup

theorem hyperGen_of_orderOf_ge_four {G : Type} [Group G] {π : elementaryGroup Q →* G}
    (hc : IsOrthogonalCover Q π) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) {E₀ : Subgroup G}
    (hE : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3) :
    HyperGen p (⊤ : Subgroup G) E₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hE1 : 1 < Nat.card E₀ := by
    rw [hcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have h1 : ∀ a b : elementaryGroup Q, a = b := fun a b =>
      Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    have h2 : ∀ a b : G, a = b := fun a b => by
      obtain ⟨a', rfl⟩ := hc.surjective a
      obtain ⟨b', rfl⟩ := hc.surjective b
      rw [h1 a' b']
    have h3 : Nat.card E₀ ≤ 1 := Finite.card_le_one_iff_subsingleton.2
      ⟨fun a b => Subtype.ext (h2 _ _)⟩
    omega
  have hker := not_dvd_card_ker_of_scalar hc hp hp2
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian π hc.surjective hker hcomm hE.2
  have htop := HighSetup.hyperClosure_eq_top
    ⟨hc.nondegenerate, hp, hpK, hAcomm, hAexp, hAcard.trans hcard, h4⟩
  intro k _
  obtain ⟨g, rfl⟩ := hc.surjective k
  have hg : g ∈ hyperClosure p ⊤ A := by
    rw [htop]
    exact Subgroup.mem_top g
  exact map_hyperClosure_le_of_lift hAE hAdis ⟨g, hg, rfl⟩

end OrthHigh

theorem eq_of_orth_index {d : TauCeti.LieTypeIndex} {r r' : ℕ} {q q' : TauCeti.PrimePower}
    (h : d = .B r q ∨ d = .D r q ∨ d = .twistedD r q)
    (h' : d = .B r' q' ∨ d = .D r' q' ∨ d = .twistedD r' q') : q' = q := by
  rcases h with h | h | h <;> rcases h' with h' | h' | h' <;> rw [h] at h' <;>
    first
      | (cases h'; rfl)
      | exact absurd h' (by simp)

theorem hyperGen_orth_of_orderOf_ge_four {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthogonalIndex d.1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ≠ d.1.characteristic)
    (h4 : ∃ (r : ℕ) (q : TauCeti.PrimePower),
      (d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) ∧
        4 ≤ orderOf ((q.card : ℕ) : ZMod p))
    {E₀ : Subgroup (Cat d)} (hE : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3) :
    HyperGen p (⊤ : Subgroup (Cat d)) E₀ := by
  obtain ⟨q, K, V, _, _, _, _, _, Q, π, ⟨r, hdq⟩, hK, hc, hpK⟩ := exists_orth_model_card hd hp hpd
  obtain ⟨r', q', hdq', h4'⟩ := h4
  obtain rfl := eq_of_orth_index hdq hdq'
  exact hyperGen_of_orderOf_ge_four hc hp hp2 hpK (by rw [hK]; exact h4') hE hcard

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KCUnitaryModel

theorem ratio_apply_eq_one_iff {M : Type*} [Group M] {F : Type*} [Field F] (χ ψ : M →* F)
    (x : M) : (χ.toHomUnits / ψ.toHomUnits) x = 1 ↔ χ x = ψ x := by
  rw [MonoidHom.div_apply, div_eq_one, Units.ext_iff]
  rfl

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem hyperGen_of_unitary_diag (h : UnitaryFieldData ℓ f K) {n : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {G : Type*} [Group G]
    (π : unitarySU ℓ f K (n + 1) →* G) (hπ : Function.Surjective π)
    (hker : ∀ g ∈ π.ker, ∃ c : K,
      ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hcomm : ∀ x y : unitarySU ℓ f K (n + 1), π x ∈ E → π y ∈ E → x * y = y * x)
    (hpow : ∀ x : unitarySU ℓ f K (n + 1), π x ∈ E → x ^ (ℓ ^ f + 1) = 1) :
    HyperGen p (⊤ : Subgroup G) E := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  set Eh : Subgroup (unitarySU ℓ f K (n + 1)) := E.comap π with hEh
  have hle : unitarySU ℓ f K (n + 1) ≤ primeFormUnitary h (idGram K (n + 1)) :=
    unitarySU_le_primeFormUnitary h
  let Gu : Subgroup (primeFormUnitary h (idGram K (n + 1))) := Eh.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ Gu, ∀ v ∈ Gu, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x y hx hy]
  have hGpow : ∀ u ∈ Gu, u ^ (ℓ ^ f + 1) = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hdvdK : ℓ ^ f + 1 ∣ Nat.card K - 1 := by
    have h1 : Nat.card K - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      rw [h.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvdK
  haveI : NeZero (ℓ ^ f + 1) := ⟨by omega⟩
  obtain ⟨P, hP⟩ :=
    CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hζ dvd_rfl Gu hGcomm hGpow
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : unitarySU ℓ f K (n + 1) → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg
  have hdiag : ∀ x : Eh,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP (Subgroup.inclusion hle x) ⟨x, x.2, rfl⟩
  have hDmul : ∀ x y : unitarySU ℓ f K (n + 1), Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → Eh →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : Eh) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  let π' : Eh →* E := (π.comp Eh.subtype).codRestrict E fun x => x.2
  have hπ' : Function.Surjective π' := by
    rintro ⟨e, he⟩
    obtain ⟨g, hg⟩ := hπ e
    exact ⟨⟨g, show π g ∈ E by rw [hg]; exact he⟩, Subtype.ext hg⟩
  have hπ'v : ∀ x : Eh, ((π' x : E) : G) = π x := fun _ => rfl
  have hscal : ∀ x : Eh, π' x = 1 → ∀ a b : Fin (n + 1), χ a x = χ b x := by
    intro x hx a b
    have hx' : (x : unitarySU ℓ f K (n + 1)) ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ'v, hx]
      rfl
    obtain ⟨c, hc⟩ := hker _ hx'
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1 := by
      have hPinv : ((Pg⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          (Pg : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1 := Units.inv_mul _
      simp only [Dg, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPinv]
    show ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) a a =
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) b b
    rw [hD]
    simp
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hhyper : ∀ i : Fin n, ∃ H : Subgroup E, H.index = p ∧ ∀ x : Eh, π' x ∈ H →
      χ i.castSucc x = χ i.succ x := by
    intro i
    let ρ : Eh →* Kˣ := (χ i.castSucc).toHomUnits / (χ i.succ).toHomUnits
    have hkerρ : π'.ker ≤ ρ.ker := fun x hx =>
      (ratio_apply_eq_one_iff _ _ x).2 (hscal x hx _ _)
    let ρb : E →* Kˣ := (QuotientGroup.lift π'.ker ρ hkerρ).comp
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm.toMonoidHom
    have hρb : ∀ x : Eh, ρb (π' x) = ρ x := by
      intro x
      have h1 : (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x) =
          (x : Eh ⧸ π'.ker) := (MulEquiv.symm_apply_eq _).2 rfl
      show QuotientGroup.lift π'.ker ρ hkerρ
        ((QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x)) = ρ x
      rw [h1]
      rfl
    obtain ⟨H, hH, hHeq⟩ := exists_hyperplane_eq_of_hom hp hexpE hcard
      ((Units.coeHom K).comp ρb) 1
    refine ⟨H, hH, fun x hx => ?_⟩
    have h1 : ρb (π' x) = 1 := Units.ext (by simpa using hHeq _ hx)
    rw [hρb] at h1
    exact (ratio_apply_eq_one_iff _ _ x).1 h1
  have hS : (hyperClosure p ⊤ E).comap π = ⊤ := by
    refine eq_top_of_blocks_mem h hq P _ fun i y A hA => ?_
    obtain ⟨H, hH, hHc⟩ := hhyper i
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, H.map E.subtype,
      Subgroup.map_subtype_le _, ?_, ?_⟩
    · have hsub : (H.map E.subtype).subgroupOf E = H :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective H
      rw [Subgroup.relIndex, hsub]
      exact hH
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨x, rfl⟩ := hπ' e
      have hxχ := hHc x he
      have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
      have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
          Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
        apply Units.ext
        simp only [Units.val_mul]
        rw [hA, hD]
        exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp)
          (by simp) hxχ A
      have hxeq : ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) = Pg * Dg x * Pg⁻¹ := by
        simp [Dg, mul_assoc]
      have hcx : (x : unitarySU ℓ f K (n + 1)) * conjSU h P y =
          conjSU h P y * (x : unitarySU ℓ f K (n + 1)) := by
        apply Subtype.ext
        show ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) *
            (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) =
          Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
            ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)
        rw [hxeq]
        calc Pg * Dg x * Pg⁻¹ * (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
            = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
              group
          _ = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by
              rw [hYD]
          _ = Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
              (Pg * Dg x * Pg⁻¹) := by group
      show ((π' x : E) : G) * π (conjSU h P y) = π (conjSU h P y) * ((π' x : E) : G)
      rw [hπ'v, ← map_mul, ← map_mul, hcx]
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ (hyperClosure p ⊤ E).comap π := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux

theorem seitzGoodInnerOrth_of_two (h : SeitzGoodInnerOrthTwo) : SeitzGoodInnerOrth := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, hgood⟩
  obtain ⟨r, q, hdq⟩ : ∃ (r : ℕ) (q : TauCeti.PrimePower),
      d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q := by
    rcases ho with ⟨r, q, h, -, -⟩ | ⟨r, q, h⟩ | ⟨r, q, h⟩
    exacts [⟨r, q, Or.inl h⟩, ⟨r, q, Or.inr (Or.inl h)⟩, ⟨r, q, Or.inr (Or.inr h)⟩]
  have hpq : p ≠ q.p := by
    rcases hdq with h' | h' | h' <;> rw [h'] at hpd <;> simpa using hpd
  have hpos := orderOf_pos_of_ne hp hpq
  rcases Nat.even_or_odd (orderOf ((q.card : ℕ) : ZMod p)) with hev | hodd
  · by_cases h2 : orderOf ((q.card : ℕ) : ZMod p) = 2
    · exact h d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, hgood, r, q, hdq, h2⟩
    · obtain ⟨k, hk⟩ := hev
      exact hyperGen_orth_of_orderOf_ge_four ho hp hp2 hpd ⟨r, q, hdq, by omega⟩ hE₀ hcard
  · exact absurd (oReducible_of_oddOrder ho hp hp2 hpd ⟨r, q, hdq, hodd⟩ hE₀ hcard) hred

theorem seitzHyperLie_unitaryDiag : SeitzHyperLie fun d p E₀ => UDiagLift d p E₀ := by
  intro d p hp _ _ _ E₀ hE₀ hcard ⟨ℓ, f, n, K, _, h, π, hπ, hker, hpq, hq, hcomm, hpow⟩
  exact hyperGen_of_unitary_diag h hp hpq hq π hπ hker hE₀ hcard hcomm hpow

theorem seitzGoodInnerUnitary_of_nonDiag (h : SeitzGoodInnerUnitaryNonDiag) :
    SeitzGoodInnerUnitary := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨hrest, hred, hgood⟩
  by_cases hdiag : UDiagLift d p E₀
  · exact seitzHyperLie_unitaryDiag d p hp hp2 hpd hlist E₀ hE₀ hcard hdiag
  · exact h d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨hrest, hred, hgood, hdiag⟩

section Exceptional

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Malle.SeitzCube (ExcCubeHighAt)

theorem seitzGoodInnerExc_of_cubes (h63 : ExcCubeHighAt TauCeti.LieTypeIndex.E6 3)
    (h76 : ExcCubeHighAt TauCeti.LieTypeIndex.E7 6)
    (h26 : ExcCubeHighAt TauCeti.LieTypeIndex.twistedE6 6) (hopen : SeitzGoodInnerExcOpen) :
    SeitzGoodInnerExc := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood⟩
  by_cases ho : ExcCubeOpenClass d.1 p
  · exact hopen d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, ho⟩
  have hp5 : 5 ≤ p := (eq_three_or_five_le hp hp2).resolve_left fun h3 => ho (Or.inl h3)
  obtain ⟨d, hv⟩ := d
  rcases htop with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hpq : p ≠ q.p := by simpa using hpd
    exact (false_F4 hv hp hp5 hpq hE₀ hcard hN fun h2 =>
      ho (Or.inr ⟨q, Or.inl ⟨Or.inl rfl, h2⟩⟩)).elim
  · have hpq : p ≠ q.p := by simpa using hpd
    exact hyperGen_E6 h63 hv hp hp2 hp5 hpq hlist hE₀ hcard hN
  · have hpq : p ≠ q.p := by simpa using hpd
    exact hyperGen_E7 h76 hv hp hp2 hp5 hpq hlist hE₀ hcard hN fun h2 =>
      ho (Or.inr ⟨q, Or.inl ⟨Or.inr (Or.inl rfl), h2⟩⟩)
  · have hpq : p ≠ q.p := by simpa using hpd
    exact (false_E8 hv hp hp5 hpq hE₀ hcard hN fun h =>
      ho (Or.inr ⟨q, Or.inr ⟨rfl, h⟩⟩)).elim
  · have hpq : p ≠ q.p := by simpa using hpd
    exact hyperGen_twistedE6 h26 hv hp hp2 hp5 hpq hlist hE₀ hcard hN fun h2 =>
      ho (Or.inr ⟨q, Or.inl ⟨Or.inr (Or.inr rfl), h2⟩⟩)

end Exceptional

section ExceptionalProved

set_option linter.unusedSectionVars false

theorem seitzGoodInnerExc_of_open (hopen : SeitzGoodInnerExcOpen) : SeitzGoodInnerExc := by
  have hres := CFSG.HardMathSupport.Lang.TwE6Step3.excCubeResidualsV4_of_phi6 fun r hr =>
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_neg_of_coreW hr
      (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6CoreW_of_placementSome hr
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSome_holds r hr)
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSomeThree_holds r hr))
  exact seitzGoodInnerExc_of_cubes hres.e6Three hres.e7Six hres.twE6Six hopen

end ExceptionalProved

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
