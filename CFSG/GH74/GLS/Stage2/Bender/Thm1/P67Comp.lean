module

public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open CFSG.LocalCores (ComponentIndex)
open scoped commutatorElement

section Layer

variable {G : Type} [Group G]

theorem exists_component_not_le {N M : Subgroup G} (h : ¬ Em N ≤ M) :
    ∃ K : Subgroup ↥N, CFSG.IsComponent K ∧ ¬ K.map N.subtype ≤ M := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [Em_def, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact hcon K hK

end Layer

section Count

variable {Y : Type} [Group Y] [Finite Y]

theorem card_componentIndex_le_two (hY : SectionalTwoRankLE Y 4) :
    Nat.card (ComponentIndex Y) ≤ 2 := by
  classical
  have h1 : SectionalTwoRankLE (layer Y) 4 := SectionalTwoRankLE.subgroup (layer Y) hY
  have h2 : SectionalTwoRankLE (layer Y ⧸ center (layer Y)) 4 :=
    SectionalTwoRankLE.quotient (center (layer Y)) h1
  have hProd : SectionalTwoRankLE (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) 4 :=
    SectionalTwoRankLE.of_mulEquiv (CFSG.LocalCores.layerCentralQuotientEquiv Y).symm h2
  have hfour : ∀ K : ComponentIndex Y, ∃ A : Subgroup (K.1 ⧸ center K.1),
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
    intro K
    have : IsSimpleGroup (K.1 ⧸ center K.1) := K.2.1.2.1
    have hnc : ∃ a b : K.1 ⧸ center K.1, a * b ≠ b * a := K.2.1.2.2
    have hq := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hnc
    have hcen : center (K.1 ⧸ center K.1) = ⊥ :=
      CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc
    exact CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
      (CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
        (by rw [hcen, Subgroup.card_bot]; exact odd_one))
  choose A hA hAc using hfour
  let φ : (∀ K : ComponentIndex Y, ↥(A K)) →* (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) :=
    MonoidHom.pi fun K => (A K).subtype.comp (Pi.evalMonoidHom _ K)
  have hφ : Function.Injective φ := fun x y hxy => funext fun K =>
    Subtype.ext (congrFun hxy K)
  let E : Subgroup (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) := φ.range
  have hEcard : Nat.card E = 4 ^ Nat.card (ComponentIndex Y) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_pi]
    simp only [hAc, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hEel : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : ∀ K : ComponentIndex Y, K.1 ⧸ center K.1) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul]
      congr 1
      funext K
      exact Subtype.ext (by
        have := (hA K).1.is_comm.comm (x K) (y K)
        exact congrArg Subtype.val this)
    · obtain ⟨x, rfl⟩ := hg
      rw [← map_pow]
      have : x ^ 2 = 1 := funext fun K => Subtype.ext (by
        have := (hA K).2 (x K) (x K).2
        simpa using this)
      rw [this, map_one]
  have hle := hProd.card_le_of_elementary E hEel
  rw [hEcard] at hle
  by_contra hgt
  push Not at hgt
  have : 4 ^ 3 ≤ 4 ^ Nat.card (ComponentIndex Y) := Nat.pow_le_pow_right (by norm_num) hgt
  omega

end Count

section Odd

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
@[expose] def compConj (a : Y) (K : ComponentIndex Y) : ComponentIndex Y :=
  ⟨K.1.map (MulAut.conj a).toMonoidHom,
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) K.2⟩

omit [Finite Y] in
theorem compConj_one (K : ComponentIndex Y) : compConj (1 : Y) K = K := by
  apply Subtype.ext
  show K.1.map (MulAut.conj (1 : Y)).toMonoidHom = K.1
  ext x
  simp [Subgroup.mem_map]

omit [Finite Y] in
theorem compConj_mul (a b : Y) (K : ComponentIndex Y) :
    compConj (a * b) K = compConj a (compConj b K) := by
  apply Subtype.ext
  show K.1.map (MulAut.conj (a * b)).toMonoidHom =
    (K.1.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b * y * b⁻¹, ⟨y, hy, rfl⟩, by group⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩

instance : MulAction Y (ComponentIndex Y) where
  smul := compConj
  one_smul := compConj_one
  mul_smul := compConj_mul

omit [Finite Y] in
theorem smul_component_val (a : Y) (K : ComponentIndex Y) :
    (a • K).1 = K.1.map (MulAut.conj a).toMonoidHom := rfl

theorem mem_normalizer_of_odd_orderOf (hcard : Nat.card (ComponentIndex Y) ≤ 2) {a : Y}
    (ha : Odd (orderOf a)) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    a ∈ normalizer (K : Set Y) := by
  classical
  let P : Y →* Equiv.Perm (ComponentIndex Y) := MulAction.toPermHom Y (ComponentIndex Y)
  have h1 : orderOf (P a) ∣ orderOf a := orderOf_map_dvd P a
  have h2 : orderOf (P a) ∣ 2 := by
    refine (orderOf_dvd_natCard (P a)).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
    calc (Nat.card (ComponentIndex Y)).factorial ∣ (2 : ℕ).factorial :=
          Nat.factorial_dvd_factorial hcard
      _ = 2 := rfl
  have h3 : orderOf (P a) = 1 := by
    have h4 : orderOf (P a) ∣ Nat.gcd (orderOf a) 2 := Nat.dvd_gcd h1 h2
    have h5 : Nat.gcd (orderOf a) 2 = 1 := by
      rcases ha with ⟨m, hm⟩
      rw [hm]
      simp
    rw [h5] at h4
    exact Nat.dvd_one.mp h4
  have h6 : P a = 1 := orderOf_eq_one_iff.mp h3
  have h7 : a • (⟨K, hK⟩ : ComponentIndex Y) = ⟨K, hK⟩ := by
    have := congrArg (fun f : Equiv.Perm (ComponentIndex Y) => f ⟨K, hK⟩) h6
    simpa [P] using this
  have h8 : K.map (MulAut.conj a).toMonoidHom = K := congrArg Subtype.val h7
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h8]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h8] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h9 : a * y * a⁻¹ = a * x * a⁻¹ := by simpa [MulAut.conj_apply] using hyx
    have : y = x := mul_left_cancel (mul_right_cancel h9)
    rw [← this]
    exact hy

end Odd

end CFSG.GH74.GLS.Stage2.Bender.Thm1
