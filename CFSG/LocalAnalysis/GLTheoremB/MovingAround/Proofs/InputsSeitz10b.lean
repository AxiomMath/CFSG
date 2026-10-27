module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz10
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz9
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusRot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

set_option linter.unusedSectionVars false

section CharTwoGeom

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem natCast_eq_one_of_odd_orthEight {n : ℕ} (hn : Odd n) : (n : K) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add]

theorem polarNondegOn_fixSub_orthEight (hQ : (polarBilin Q).Nondegenerate) {E : Subgroup (V ≃ₗ[K] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card E)) :
    PolarNondegOn Q (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub E) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  haveI := Fintype.ofFinite E
  intro x hx hxx
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  have haF : (∑ g : E, (g : V ≃ₗ[K] V) v) ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub E := by
    intro h hh
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : E)) _ _ fun g => rfl
  have h1 : polar Q x (∑ g : E, (g : V ≃ₗ[K] V) v) = polar Q x v := by
    rw [← polarBilin_apply_apply, map_sum]
    have : ∀ g : E, polarBilin Q x ((g : V ≃ₗ[K] V) v) = polarBilin Q x v := fun g => by
      rw [polarBilin_apply_apply, polarBilin_apply_apply]
      conv_lhs => rw [← hx g g.2]
      exact polar_map_of_mem (hEO g.2) x v
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, natCast_eq_one_of_odd_orthEight hodd,
      one_smul, polarBilin_apply_apply]
  rw [← h1]
  exact hxx _ haF

@[expose] noncomputable def subAct_orthEight {D : Subgroup (V ≃ₗ[K] V)} {U : Submodule K V}
    (hU : ∀ g ∈ D, ∀ x ∈ U, g x ∈ U) : ↥D →* MulAut (Multiplicative ↥U) where
  toFun g :=
    { toFun := fun x => Multiplicative.ofAdd ⟨(g : V ≃ₗ[K] V) (Multiplicative.toAdd x : ↥U),
        hU g g.2 _ (Multiplicative.toAdd x).2⟩
      invFun := fun x => Multiplicative.ofAdd ⟨((g : V ≃ₗ[K] V)⁻¹) (Multiplicative.toAdd x : ↥U),
        hU _ (inv_mem g.2) _ (Multiplicative.toAdd x).2⟩
      left_inv := fun x => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show ((g : V ≃ₗ[K] V)⁻¹) ((g : V ≃ₗ[K] V) (Multiplicative.toAdd x : ↥U)) = _
        rw [← LinearEquiv.mul_apply, inv_mul_cancel]
        rfl
      right_inv := fun x => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show (g : V ≃ₗ[K] V) (((g : V ≃ₗ[K] V)⁻¹) (Multiplicative.toAdd x : ↥U)) = _
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show (g : V ≃ₗ[K] V) ((Multiplicative.toAdd x : ↥U) + (Multiplicative.toAdd y : ↥U)) = _
        rw [map_add]
        rfl }
  map_one' := by
    ext x
    rfl
  map_mul' := fun g h => by
    ext x
    rfl

theorem exists_hyperplane_fix_orthEight {D : Subgroup (V ≃ₗ[K] V)} (hD : IsElemAbelian 3 D)
    (hD1 : D ≠ ⊥) {U : Submodule K V} (hU : ∀ g ∈ D, ∀ x ∈ U, g x ∈ U) (hU0 : U ≠ ⊥) :
    ∃ H : Subgroup (V ≃ₗ[K] V), H ≤ D ∧ Nat.card D = 3 * Nat.card H ∧
      ∃ x ∈ U, x ≠ 0 ∧ ∀ h ∈ H, h x = x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : IsElementaryAbelian 3 ↥D :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 D).2 hD
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).2 hD1
  letI : MulDistribMulAction ↥D (Multiplicative ↥U) :=
    MulDistribMulAction.compHom _ (subAct_orthEight hU)
  have hcop : ¬ 3 ∣ Nat.card (Multiplicative ↥U) := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [show Nat.card (Multiplicative ↥U) = Nat.card ↥U from rfl, Module.natCard_eq_pow_finrank (K := K),
      Nat.card_eq_fintype_card, hn, ← pow_mul]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := 3) (A := ↥D)
    (H := Multiplicative ↥U) hcop
  obtain ⟨B, hBi, hBne⟩ : ∃ B : Subgroup ↥D, B.index = 3 ∧
      CFSG.fixedPointSubgroup B (Multiplicative ↥U) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Subgroup (Multiplicative ↥U)) = ⊥ := by
      rw [← hgen]
      exact iSup₂_eq_bot.2 fun B hB => hcon B hB
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hne : (Multiplicative.ofAdd (⟨u, hu⟩ : ↥U)) ≠ 1 := by
      intro h
      apply hu0
      have := congrArg (fun z => ((Multiplicative.toAdd z : ↥U) : V)) h
      simpa using this
    exact hne (Subgroup.eq_bot_iff_forall _ |>.1 htop _ (Subgroup.mem_top _))
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  refine ⟨B.map D.subtype, Subgroup.map_subtype_le B, ?_,
    ((Multiplicative.toAdd (w : Multiplicative ↥U) : ↥U) : V), (Multiplicative.toAdd (w : Multiplicative ↥U)).2,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective D.subtype_injective, ← hBi, Subgroup.index_mul_card]
  · intro h0
    apply hw1
    apply Subtype.ext
    show (w : Multiplicative ↥U) = 1
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h0
  · rintro _ ⟨b, hb, rfl⟩
    have h1 := (FixedPoints.mem_subgroup ↥B (Multiplicative ↥U)
      (w : Multiplicative ↥U)).1 w.2 ⟨b, hb⟩
    have h3 := congrArg (fun z => ((Multiplicative.toAdd z : ↥U) : V)) h1
    exact h3

theorem exists_singular_of_polar_eq_zero_orthEight {v w : V} (hvw : polar Q v w = 0) (hQv : Q v ≠ 0)
    (hw : ∀ a : K, w ≠ a • v) :
    ∃ s t : K, t • v + s • w ≠ 0 ∧ Q (t • v + s • w) = 0 := by
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q v)
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hQv hs
  refine ⟨s, t, ?_, ?_⟩
  · intro h0
    apply hw (-(s⁻¹ * t))
    have h1 : s • w = -(t • v) := eq_neg_of_add_eq_zero_right h0
    calc w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = -(s⁻¹ * t) • v := by rw [h1, smul_neg, smul_smul, neg_smul]
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hvw, hs, ht]
    simp only [smul_eq_mul, mul_zero, add_zero]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (s * s * (t * t)) * h2

theorem exists_card_twentySeven_orthEight {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsElemAbelian 3 H) (h27 : 27 ≤ Nat.card H) :
    ∃ F : Subgroup G, F ≤ H ∧ Nat.card F = 3 ^ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hH.isPGroup.exists_card_eq
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨F₀, hF₀c, -, hF₀H⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 3)
    (H := ⊥) (L := H) (by rw [Subgroup.card_bot]; exact one_dvd _) (by rw [hm]; exact Nat.pow_dvd_pow 3 hm3)
    bot_le
  exact ⟨F₀, hF₀H, hF₀c⟩

theorem exists_fix_singular_orthEight (hQ : (polarBilin Q).Nondegenerate) {D : Subgroup (V ≃ₗ[K] V)}
    (hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : IsElemAbelian 3 D)
    (hD5 : 3 ^ 5 ≤ Nat.card D) :
    ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ D ∧ Nat.card F = 3 ^ 3 ∧
      ∃ u : V, u ≠ 0 ∧ Q u = 0 ∧ ∀ g ∈ F, g u = u := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD5
    norm_num at hD5
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have htop : (⊤ : Submodule K V) ≠ ⊥ := by
    obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
    have hg1' : (g : V ≃ₗ[K] V) ≠ 1 := fun h => hg1 (Subtype.ext h)
    obtain ⟨x, hx⟩ : ∃ x : V, (g : V ≃ₗ[K] V) x ≠ x := by
      by_contra hall
      push Not at hall
      exact hg1' (LinearEquiv.ext hall)
    intro h
    have hx0 : x = 0 := by
      have : x ∈ (⊥ : Submodule K V) := h ▸ Submodule.mem_top
      exact (Submodule.mem_bot K).1 this
    exact hx (by rw [hx0, map_zero])
  obtain ⟨H₁, hH₁D, hH₁c, v, -, hv0, hvH⟩ := exists_hyperplane_fix_orthEight hD hD1
    (U := ⊤) (fun _ _ _ _ => Submodule.mem_top) htop
  have hH₁el : IsElemAbelian 3 H₁ := GL83.CompFam.elem_mono hD hH₁D
  by_cases hQv : Q v = 0
  · obtain ⟨F, hFH, hFc⟩ := exists_card_twentySeven_orthEight hH₁el (by omega)
    exact ⟨F, hFH.trans hH₁D, hFc, v, hv0, hQv, fun g hg => hvH g (hFH hg)⟩
  set W := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub H₁ with hWdef
  have hvW : v ∈ W := fun h hh => hvH h hh
  have hH₁odd : Odd (Nat.card H₁) := by
    obtain ⟨k, hk⟩ := hH₁el.isPGroup.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hWnd := polarNondegOn_fixSub_orthEight hQ (hH₁D.trans hDO) hH₁odd
  set U := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.perpSub Q W with hUdef
  have hcompl : IsCompl W U := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isCompl_perpSub hWnd
  have hDW : ∀ g ∈ D, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw h hh
    calc h (g w) = (h * g) w := rfl
      _ = (g * h) w := by rw [hDcomm h (hH₁D hh) g hg]
      _ = g (h w) := rfl
      _ = g w := by rw [hw h hh]
  have hDU : ∀ g ∈ D, ∀ x ∈ U, g x ∈ U := by
    intro g hg x hx w hw
    have hw' : g⁻¹ w ∈ W := hDW _ (inv_mem hg) w hw
    have h1 := polar_map_of_mem (hDO hg) x (g⁻¹ w)
    have h2 : g (g⁻¹ w) = w := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [h2] at h1
    rw [h1]
    exact hx _ hw'
  have hU0 : U ≠ ⊥ := by
    intro hU0
    have hWtop : W = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hU0, sup_bot_eq] at this
    have hH₁bot : H₁ = ⊥ := by
      rw [eq_bot_iff]
      intro h hh
      rw [Subgroup.mem_bot]
      refine LinearEquiv.ext fun x => ?_
      have hx : x ∈ W := by rw [hWtop]; exact Submodule.mem_top
      exact hx h hh
    rw [hH₁bot, Subgroup.card_bot] at hH₁c
    omega
  obtain ⟨H₂, hH₂D, hH₂c, w, hwU, hw0, hwH⟩ := exists_hyperplane_fix_orthEight hD hD1 hDU hU0
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H₁ H₂
    (fun x hx y hy => hDcomm x (hH₁D hx) y (hH₂D hy))).1
  have hsupD : Nat.card ↥(H₁ ⊔ H₂) ≤ Nat.card D := Subgroup.card_le_of_le (sup_le hH₁D hH₂D)
  have hF₀ : 27 ≤ Nat.card ↥(H₁ ⊓ H₂) := by
    have h1 : Nat.card H₁ * Nat.card H₂ ≤ Nat.card D * Nat.card ↥(H₁ ⊓ H₂) := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ hsupD
    have hpos : 0 < Nat.card H₁ := Nat.card_pos
    have h2 : Nat.card H₁ * Nat.card H₂ ≤ Nat.card H₁ * (3 * Nat.card ↥(H₁ ⊓ H₂)) := by
      rw [hH₁c] at h1
      linarith
    have h3 := Nat.le_of_mul_le_mul_left h2 hpos
    omega
  have hvw : polar Q v w = 0 := by
    rw [polar_comm]
    exact hwU v hvW
  have hwv : ∀ a : K, w ≠ a • v := by
    intro a ha
    have hwW : w ∈ W := ha ▸ W.smul_mem a hvW
    have hmem : w ∈ W ⊓ U := ⟨hwW, hwU⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hw0 hmem
  obtain ⟨s, t, hu0, hQu⟩ := exists_singular_of_polar_eq_zero_orthEight hvw hQv hwv
  obtain ⟨F, hFF₀, hFc⟩ := exists_card_twentySeven_orthEight
    (GL83.CompFam.elem_mono hD (inf_le_left.trans hH₁D)) hF₀
  refine ⟨F, hFF₀.trans (inf_le_left.trans hH₁D), hFc, t • v + s • w, hu0, hQu, fun g hg => ?_⟩
  have hg1 : g ∈ H₁ := (Subgroup.mem_inf.1 (hFF₀ hg)).1
  have hg2 : g ∈ H₂ := (Subgroup.mem_inf.1 (hFF₀ hg)).2
  rw [map_add, map_smul, map_smul, hvH g hg1, hwH g hg2]

end CharTwoGeom

section RankFive

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus (IsRotPair)

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem elemAbelian_sup_step_orthEight {A : Subgroup (V ≃ₗ[K] V)} {k : ℕ} (hA : IsElemAbelian 3 A)
    (hAc : Nat.card A = 3 ^ k) {t : V ≃ₗ[K] V} (ht3 : t ^ 3 = 1) (hAt : ∀ a ∈ A, a * t = t * a)
    {x : V} (hmove : t x ≠ x) (hAx : ∀ a ∈ A, a x = x) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers t) ∧ Nat.card ↥(A ⊔ Subgroup.zpowers t) = 3 ^ (k + 1) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hAt a ha) i).eq
  have ht1 : t ≠ 1 := fun h => hmove (by rw [h]; rfl)
  have htA : t ∉ A := fun h => hmove (hAx t h)
  have hdisj : A ⊓ Subgroup.zpowers t = ⊥ := by
    rw [inf_comm]
    exact ClassicalEA.zpowers_inf_eq_bot Nat.prime_three ht3 htA
  refine ⟨IsElemAbelian.sup_of_commute hA (isElemAbelian_zpowers ht3) hcomm, ?_⟩
  rw [ClassicalEA.card_sup_of_inf_eq_bot hcomm hdisj, hAc,
    ClassicalEA.card_zpowers_of_prime Nat.prime_three ht3 ht1, pow_succ]

theorem three_ne_zero_orthEight : (3 : K) ≠ 0 := by
  have h : (3 : K) = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  rw [h]
  exact one_ne_zero

theorem exists_elemAbelian_five_orthEight (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {c : Fin 5 → K} {u v : Fin 5 → V} (h : ∀ i, IsRotPair Q (c i) (u i) (v i))
    (horth : ∀ i j, i ≠ j → polar Q (u i) (u j) = 0 ∧ polar Q (u i) (v j) = 0 ∧
      polar Q (v i) (u j) = 0 ∧ polar Q (v i) (v j) = 0) :
    ∃ A : Subgroup (V ≃ₗ[K] V), A ≤ elementaryGroup Q ∧ IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 5 := by
  classical
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  set t : Fin 5 → (V ≃ₗ[K] V) := fun i => (h i).rotAut with htdef
  have ht3 : ∀ i, t i ^ 3 = 1 := fun i => (h i).rotAut_pow_three
  have htE : ∀ i, t i ∈ elementaryGroup Q := by
    intro i
    rw [← hE]
    refine hodd (t i) (h i).rotAut_mem_orthogonalGroup ?_
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (ht3 i))
  have hcomm : ∀ i j, i ≠ j → t i * t j = t j * t i := by
    intro i j hij
    obtain ⟨h1, h2, h3, h4⟩ := horth i j hij
    exact (h i).rotAut_comm_rotAut (h j) h1 h2 h3 h4
  have hfix : ∀ i j, i ≠ j → t j (u i) = u i := by
    intro i j hij
    obtain ⟨h1, -, h3, -⟩ := horth j i (Ne.symm hij)
    exact (h j).rotAut_of_perp h1 h3
  have hmove : ∀ i, t i (u i) ≠ u i := fun i => (h i).rotAut_ne three_ne_zero_orthEight
  set Z : Fin 5 → Subgroup (V ≃ₗ[K] V) := fun j =>
    Subgroup.centralizer ({t j} : Set (V ≃ₗ[K] V)) ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (u j) with hZdef
  have hZ : ∀ i j, i ≠ j → Subgroup.zpowers (t i) ≤ Z j := by
    intro i j hij
    rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_centralizer_iff.2 fun y hy => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact (hcomm i j hij).symm
    · exact hfix j i (Ne.symm hij)
  have hZc : ∀ j, ∀ a ∈ Z j, a * t j = t j * a := fun j a ha =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ha).1 (t j) (Set.mem_singleton _)).symm
  have hZs : ∀ j, ∀ a ∈ Z j, a (u j) = u j := fun j a ha => (Subgroup.mem_inf.1 ha).2
  have h0 : IsElemAbelian 3 (⊥ : Subgroup (V ≃ₗ[K] V)) := CFSG.Open.isElemAbelian_bot 3
  obtain ⟨e1, c1⟩ := elemAbelian_sup_step_orthEight h0 (by rw [Subgroup.card_bot, pow_zero]) (ht3 0)
    (fun a ha => by rw [(Subgroup.mem_bot.1 ha), one_mul, mul_one]) (hmove 0)
    (fun a ha => by rw [Subgroup.mem_bot.1 ha]; rfl)
  have l1 : ⊥ ⊔ Subgroup.zpowers (t 0) ≤ Z 1 := sup_le bot_le (hZ 0 1 (by decide))
  obtain ⟨e2, c2⟩ := elemAbelian_sup_step_orthEight e1 c1 (ht3 1) (fun a ha => hZc 1 a (l1 ha))
    (hmove 1) (fun a ha => hZs 1 a (l1 ha))
  have l2 : ⊥ ⊔ Subgroup.zpowers (t 0) ⊔ Subgroup.zpowers (t 1) ≤ Z 2 :=
    sup_le (sup_le bot_le (hZ 0 2 (by decide))) (hZ 1 2 (by decide))
  obtain ⟨e3, c3⟩ := elemAbelian_sup_step_orthEight e2 c2 (ht3 2) (fun a ha => hZc 2 a (l2 ha))
    (hmove 2) (fun a ha => hZs 2 a (l2 ha))
  have l3 : ⊥ ⊔ Subgroup.zpowers (t 0) ⊔ Subgroup.zpowers (t 1) ⊔ Subgroup.zpowers (t 2) ≤ Z 3 :=
    sup_le (sup_le (sup_le bot_le (hZ 0 3 (by decide))) (hZ 1 3 (by decide))) (hZ 2 3 (by decide))
  obtain ⟨e4, c4⟩ := elemAbelian_sup_step_orthEight e3 c3 (ht3 3) (fun a ha => hZc 3 a (l3 ha))
    (hmove 3) (fun a ha => hZs 3 a (l3 ha))
  have l4 : ⊥ ⊔ Subgroup.zpowers (t 0) ⊔ Subgroup.zpowers (t 1) ⊔ Subgroup.zpowers (t 2) ⊔
      Subgroup.zpowers (t 3) ≤ Z 4 :=
    sup_le (sup_le (sup_le (sup_le bot_le (hZ 0 4 (by decide))) (hZ 1 4 (by decide)))
      (hZ 2 4 (by decide))) (hZ 3 4 (by decide))
  obtain ⟨e5, c5⟩ := elemAbelian_sup_step_orthEight e4 c4 (ht3 4) (fun a ha => hZc 4 a (l4 ha))
    (hmove 4) (fun a ha => hZs 4 a (l4 ha))
  refine ⟨_, ?_, e5, c5⟩
  have hz : ∀ i, Subgroup.zpowers (t i) ≤ elementaryGroup Q := fun i => (Subgroup.zpowers_le).2 (htE i)
  exact sup_le (sup_le (sup_le (sup_le (sup_le bot_le (hz 0)) (hz 1)) (hz 2)) (hz 3)) (hz 4)

end RankFive

section CoordPairs

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus (IsRotPair)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus quadMinus quadMinus_apply
  polar_quadMinus)

variable {K : Type} [Field K]

theorem quadPlus_elim_orthEight {n : ℕ} (f g : Fin n → K) :
    quadPlus n K (Sum.elim f g) = ∑ i, f i * g i := by
  rw [quadPlus_apply]
  simp

theorem polar_quadPlus_elim_orthEight {n : ℕ} (f g f' g' : Fin n → K) :
    polar (quadPlus n K) (Sum.elim f g) (Sum.elim f' g') = ∑ i, (f i * g' i + f' i * g i) := by
  rw [polar_quadPlus]
  simp

theorem quadMinus_hyp_orthEight {n : ℕ} (b c : K) (f g : Fin (n - 1) → K) :
    quadMinus n K b c (Sum.elim f (Sum.elim g 0)) = ∑ i, f i * g i := by
  rw [quadMinus_apply]
  simp

theorem quadMinus_aniso_orthEight {n : ℕ} (b c : K) (h : Fin 2 → K) :
    quadMinus n K b c (Sum.elim 0 (Sum.elim 0 h)) = h 0 ^ 2 + b * h 0 * h 1 + c * h 1 ^ 2 := by
  rw [quadMinus_apply]
  simp

theorem polar_quadMinus_hyp_orthEight {n : ℕ} (b c : K) (f g f' g' : Fin (n - 1) → K) :
    polar (quadMinus n K b c) (Sum.elim f (Sum.elim g 0)) (Sum.elim f' (Sum.elim g' 0)) =
      ∑ i, (f i * g' i + f' i * g i) := by
  rw [polar_quadMinus]
  simp

theorem polar_quadMinus_hyp_aniso_orthEight {n : ℕ} (b c : K) (f g : Fin (n - 1) → K) (h : Fin 2 → K) :
    polar (quadMinus n K b c) (Sum.elim f (Sum.elim g 0)) (Sum.elim 0 (Sum.elim 0 h)) = 0 := by
  rw [polar_quadMinus]
  simp

theorem polar_quadMinus_aniso_orthEight {n : ℕ} (b c : K) (h h' : Fin 2 → K) :
    polar (quadMinus n K b c) (Sum.elim 0 (Sum.elim 0 h)) (Sum.elim 0 (Sum.elim 0 h')) =
      2 * (h 0 * h' 0) + b * (h 0 * h' 1 + h' 0 * h 1) + 2 * c * (h 1 * h' 1) := by
  rw [polar_quadMinus]
  simp

variable [CharP K 2]

theorem sum_single_mul_single_orthEight {n : ℕ} (x y : Fin n) :
    (∑ i, Pi.single x (1 : K) i * Pi.single y (1 : K) i) = if x = y then (1 : K) else 0 := by
  classical
  rw [Finset.sum_eq_single x (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_mul])
    (fun h => absurd (Finset.mem_univ x) h), Pi.single_eq_same, one_mul]
  by_cases hxy : x = y
  · subst hxy
    simp
  · simp [Pi.single_apply, hxy]

theorem rotPairs_block_orthEight {m : ℕ} {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hv : (Fin m → K) → (Fin m → K) → V) (hQ : ∀ f g, Q (hv f g) = ∑ i, f i * g i)
    (hP : ∀ f g f' g', polar Q (hv f g) (hv f' g') = ∑ i, (f i * g' i + f' i * g i))
    {a b : Fin m} (hab : a ≠ b) :
    IsRotPair Q 1 (hv (Pi.single a 1) (Pi.single a 1)) (hv (Pi.single a 1 + Pi.single b 1) (Pi.single b 1)) ∧
    IsRotPair Q 1 (hv (Pi.single a 1 + Pi.single b 1) (Pi.single a 1))
      (hv (Pi.single a 1) (Pi.single a 1 + Pi.single b 1)) ∧
    polar Q (hv (Pi.single a 1) (Pi.single a 1)) (hv (Pi.single a 1 + Pi.single b 1) (Pi.single a 1)) = 0 ∧
    polar Q (hv (Pi.single a 1) (Pi.single a 1)) (hv (Pi.single a 1) (Pi.single a 1 + Pi.single b 1)) = 0 ∧
    polar Q (hv (Pi.single a 1 + Pi.single b 1) (Pi.single b 1))
      (hv (Pi.single a 1 + Pi.single b 1) (Pi.single a 1)) = 0 ∧
    polar Q (hv (Pi.single a 1 + Pi.single b 1) (Pi.single b 1))
      (hv (Pi.single a 1) (Pi.single a 1 + Pi.single b 1)) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hba : b ≠ a := Ne.symm hab
  have hm1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  refine ⟨⟨one_ne_zero, ?_, ?_, ?_⟩, ⟨one_ne_zero, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hQ, hP, hm1, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
      sum_single_mul_single_orthEight, if_pos, if_neg hab, if_neg hba] <;>
    simp <;> linear_combination h2

theorem exists_five_rotPairs_quadPlus_orthEight {n : ℕ} (hn : 6 ≤ n) :
    ∃ (c : Fin 5 → K) (u v : Fin 5 → Fin n ⊕ Fin n → K),
      (∀ i, IsRotPair (quadPlus n K) (c i) (u i) (v i)) ∧
      ∀ i j, i ≠ j → polar (quadPlus n K) (u i) (u j) = 0 ∧ polar (quadPlus n K) (u i) (v j) = 0 ∧
        polar (quadPlus n K) (v i) (u j) = 0 ∧ polar (quadPlus n K) (v i) (v j) = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ := quadPlus_elim_orthEight (K := K) (n := n)
  have hP := polar_quadPlus_elim_orthEight (K := K) (n := n)
  let a : ℕ → Fin n := fun k => ⟨k % 6, by omega⟩
  have ha : ∀ k l, k < 6 → l < 6 → (a k = a l ↔ k = l) := by
    intro k l hk hl
    simp only [a, Fin.mk.injEq]
    rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl]
  obtain ⟨p1, p2, o1, o2, o3, o4⟩ := rotPairs_block_orthEight (fun f g => Sum.elim f g) hQ hP
    (a := a 0) (b := a 1) (by rw [Ne, ha 0 1 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨p3, p4, o5, o6, o7, o8⟩ := rotPairs_block_orthEight (fun f g => Sum.elim f g) hQ hP
    (a := a 2) (b := a 3) (by rw [Ne, ha 2 3 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨p5, -, -, -, -, -⟩ := rotPairs_block_orthEight (fun f g => Sum.elim f g) hQ hP
    (a := a 4) (b := a 5) (by rw [Ne, ha 4 5 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Fin n → K, ∀ k, s k = Pi.single (a k) 1 := ⟨_, fun _ => rfl⟩
  rw [← hs 0, ← hs 1] at p1 p2 o1 o2 o3 o4
  rw [← hs 2, ← hs 3] at p3 p4 o5 o6 o7 o8
  rw [← hs 4, ← hs 5] at p5
  have hss : ∀ k l, k < 6 → l < 6 → ∑ i, s k i * s l i = if k = l then (1 : K) else 0 := by
    intro k l hk hl
    rw [hs k, hs l, sum_single_mul_single_orthEight]
    by_cases hkl : k = l
    · rw [if_pos ((ha k l hk hl).2 hkl), if_pos hkl]
    · rw [if_neg (fun h => hkl ((ha k l hk hl).1 h)), if_neg hkl]
  let u : Fin 5 → Fin n ⊕ Fin n → K :=
    ![Sum.elim (s 0) (s 0), Sum.elim (s 0 + s 1) (s 0), Sum.elim (s 2) (s 2), Sum.elim (s 2 + s 3) (s 2),
      Sum.elim (s 4) (s 4)]
  let v : Fin 5 → Fin n ⊕ Fin n → K :=
    ![Sum.elim (s 0 + s 1) (s 1), Sum.elim (s 0) (s 0 + s 1), Sum.elim (s 2 + s 3) (s 3),
      Sum.elim (s 2) (s 2 + s 3), Sum.elim (s 4 + s 5) (s 5)]
  refine ⟨fun _ => 1, u, v, fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
  · have key : ∀ f g f' g' : Fin n → K, polar (quadPlus n K) (Sum.elim f g) (Sum.elim f' g') =
        ∑ i, f i * g' i + ∑ i, f' i * g i := fun f g f' g' => by
      rw [hP, Finset.sum_add_distrib]
    fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
      simp [u, v, key, hss, add_mul, mul_add, Finset.sum_add_distrib] <;> linear_combination h2

theorem exists_rotCoeff_orthEight [Finite K] (hK : Nat.card K = 2 ^ 3) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 ∧ ∃ a : K, a ^ 2 + a + c / b ^ 2 = 1 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := by
    rintro rfl
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    apply hirr r
    rw [hr]
    linear_combination (r * r) * h2
  refine ⟨hb, ?_⟩
  let φ : K →+ K :=
    { toFun := fun a => a ^ 2 + a
      map_zero' := by ring
      map_add' := fun x y => by linear_combination (x * y) * h2 }
  have hφ : ∀ a, φ a = a ^ 2 + a := fun a => rfl
  have hker : ∀ a, φ a = 0 ↔ a = 0 ∨ a = 1 := by
    intro a
    rw [hφ]
    constructor
    · intro h
      have h' : a * (a + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linear_combination h1 - h2)
    · rintro (rfl | rfl)
      · ring
      · linear_combination h2
  have hkc : Nat.card φ.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨0, (AddMonoidHom.mem_ker).2 ((hker 0).2 (Or.inl rfl))⟩,
      ⟨1, (AddMonoidHom.mem_ker).2 ((hker 1).2 (Or.inr rfl))⟩, ?_, ?_⟩
    · intro h
      exact zero_ne_one (congrArg Subtype.val h)
    · ext ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases (hker x).1 ((AddMonoidHom.mem_ker).1 hx) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hidx : φ.range.index = 2 := by
    have h1 := AddSubgroup.index_mul_card φ.ker
    have h3 := AddSubgroup.index_mul_card φ.range
    rw [hkc, hK, AddSubgroup.index_ker] at h1
    rw [hK] at h3
    have hcr : Nat.card φ.range = 4 := by omega
    rw [hcr] at h3
    omega
  have h1n : (1 : K) ∉ φ.range := by
    rintro ⟨a, ha⟩
    rw [hφ] at ha
    have h3 : a ^ 3 = 1 := by linear_combination (a - 1) * ha + (a - 1) * h2
    have h8 : a ^ 8 = a := by
      haveI := Fintype.ofFinite K
      have := FiniteField.pow_card a
      rwa [Fintype.card_eq_nat_card, hK] at this
    have h6 : a ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, one_pow]
    have ha2 : a ^ 2 = a := by
      have e : a ^ 8 = a ^ 6 * a ^ 2 := by ring
      rw [h6, one_mul, h8] at e
      exact e.symm
    have h10 : (1 : K) = 0 := by
      rw [← ha, ha2]
      linear_combination a * h2
    exact one_ne_zero h10
  have hen : c / b ^ 2 ∉ φ.range := by
    rintro ⟨a, ha⟩
    rw [hφ] at ha
    apply hirr (b * a)
    have hb2 : b ^ 2 * (c / b ^ 2) = c := by field_simp
    linear_combination b ^ 2 * ha + hb2 + c * h2
  have hmem : 1 + c / b ^ 2 ∈ φ.range := by
    rw [AddSubgroup.add_mem_iff_of_index_two hidx]
    exact iff_of_false h1n hen
  obtain ⟨a, ha⟩ := hmem
  rw [hφ] at ha
  exact ⟨a, by linear_combination ha + (c / b ^ 2) * h2⟩

theorem exists_five_rotPairs_quadMinus_orthEight [Finite K] (hK : Nat.card K = 2 ^ 3) {n : ℕ} (hn : 5 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (c' : Fin 5 → K) (u v : Fin 5 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      (∀ i, IsRotPair (quadMinus n K b c) (c' i) (u i) (v i)) ∧
      ∀ i j, i ≠ j → polar (quadMinus n K b c) (u i) (u j) = 0 ∧
        polar (quadMinus n K b c) (u i) (v j) = 0 ∧ polar (quadMinus n K b c) (v i) (u j) = 0 ∧
        polar (quadMinus n K b c) (v i) (v j) = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hb, α, hα⟩ := exists_rotCoeff_orthEight hK hirr
  have hQ := quadMinus_hyp_orthEight (K := K) (n := n) b c
  have hP := polar_quadMinus_hyp_orthEight (K := K) (n := n) b c
  let a : ℕ → Fin (n - 1) := fun k => ⟨k % 4, by omega⟩
  have ha : ∀ k l, k < 4 → l < 4 → (a k = a l ↔ k = l) := by
    intro k l hk hl
    simp only [a, Fin.mk.injEq]
    rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl]
  obtain ⟨p1, p2, o1, o2, o3, o4⟩ := rotPairs_block_orthEight (fun f g => Sum.elim f (Sum.elim g 0)) hQ hP
    (a := a 0) (b := a 1) (by rw [Ne, ha 0 1 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨p3, p4, o5, o6, o7, o8⟩ := rotPairs_block_orthEight (fun f g => Sum.elim f (Sum.elim g 0)) hQ hP
    (a := a 2) (b := a 3) (by rw [Ne, ha 2 3 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Fin (n - 1) → K, ∀ k, s k = Pi.single (a k) 1 := ⟨_, fun _ => rfl⟩
  rw [← hs 0, ← hs 1] at p1 p2 o1 o2 o3 o4
  rw [← hs 2, ← hs 3] at p3 p4 o5 o6 o7 o8
  have hss : ∀ k l, k < 4 → l < 4 → ∑ i, s k i * s l i = if k = l then (1 : K) else 0 := by
    intro k l hk hl
    rw [hs k, hs l, sum_single_mul_single_orthEight]
    by_cases hkl : k = l
    · rw [if_pos ((ha k l hk hl).2 hkl), if_pos hkl]
    · rw [if_neg (fun h => hkl ((ha k l hk hl).1 h)), if_neg hkl]
  obtain ⟨z₁, hz₁⟩ : ∃ z : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      z = Sum.elim (0 : Fin (n - 1) → K) (Sum.elim (0 : Fin (n - 1) → K) ![(1 : K), 0]) := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      z = Sum.elim (0 : Fin (n - 1) → K) (Sum.elim (0 : Fin (n - 1) → K) ![α, b⁻¹]) := ⟨_, rfl⟩
  have p5 : IsRotPair (quadMinus n K b c) 1 z₁ z₂ := by
    refine ⟨one_ne_zero, ?_, ?_, ?_⟩
    · rw [hz₁, quadMinus_aniso_orthEight]
      simp
    · rw [hz₂, quadMinus_aniso_orthEight]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hα]
      field_simp
    · rw [hz₁, hz₂, polar_quadMinus_aniso_orthEight, CharTwo.neg_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, add_zero, one_mul,
        zero_mul, mul_inv_cancel₀ hb]
      linear_combination α * h2
  have hza : ∀ f g : Fin (n - 1) → K, ∀ z ∈ ({z₁, z₂} : Set _),
      polar (quadMinus n K b c) (Sum.elim f (Sum.elim g 0)) z = 0 ∧
        polar (quadMinus n K b c) z (Sum.elim f (Sum.elim g 0)) = 0 := by
    intro f g z hz
    rcases hz with rfl | rfl
    · rw [polar_comm (quadMinus n K b c) _ (Sum.elim f (Sum.elim g 0)), hz₁]
      exact ⟨polar_quadMinus_hyp_aniso_orthEight b c f g _, polar_quadMinus_hyp_aniso_orthEight b c f g _⟩
    · rw [polar_comm (quadMinus n K b c) _ (Sum.elim f (Sum.elim g 0)), hz₂]
      exact ⟨polar_quadMinus_hyp_aniso_orthEight b c f g _, polar_quadMinus_hyp_aniso_orthEight b c f g _⟩
  have hz₁a := fun f g => hza f g z₁ (Or.inl rfl)
  have hz₂a := fun f g => hza f g z₂ (Or.inr rfl)
  let u : Fin 5 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
    ![Sum.elim (s 0) (Sum.elim (s 0) 0), Sum.elim (s 0 + s 1) (Sum.elim (s 0) 0),
      Sum.elim (s 2) (Sum.elim (s 2) 0), Sum.elim (s 2 + s 3) (Sum.elim (s 2) 0), z₁]
  let v : Fin 5 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
    ![Sum.elim (s 0 + s 1) (Sum.elim (s 1) 0), Sum.elim (s 0) (Sum.elim (s 0 + s 1) 0),
      Sum.elim (s 2 + s 3) (Sum.elim (s 3) 0), Sum.elim (s 2) (Sum.elim (s 2 + s 3) 0), z₂]
  refine ⟨fun _ => 1, u, v, fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
  · have key : ∀ f g f' g' : Fin (n - 1) → K,
        polar (quadMinus n K b c) (Sum.elim f (Sum.elim g 0)) (Sum.elim f' (Sum.elim g' 0)) =
          ∑ i, f i * g' i + ∑ i, f' i * g i := fun f g f' g' => by
      rw [hP, Finset.sum_add_distrib]
    fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
      simp [u, v, key, hss, add_mul, mul_add, Finset.sum_add_distrib, (hz₁a _ _).1, (hz₁a _ _).2,
        (hz₂a _ _).1, (hz₂a _ _).2] <;> linear_combination h2

end CoordPairs

section Models

open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus quadPlus_apply quadMinus_apply)

theorem subgroupOf_scalars_eq_bot_orthEight {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {v₀ : V} (hv₀ : Q v₀ ≠ 0) :
    (scalars K V).subgroupOf (elementaryGroup Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hgE⟩ hg
  rw [Subgroup.mem_subgroupOf, mem_scalars] at hg
  obtain ⟨c, hc⟩ := hg
  have h1 : Q (g v₀) = Q v₀ := map_of_mem (elementaryGroup_le_orthogonalGroup Q hgE) v₀
  rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hc2 : c * c = 1 := by
    have h0 : (c * c - 1) * Q v₀ = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hv₀)
  have hc1 : c = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h0 : (c + 1) * (c + 1) = 0 := by linear_combination hc2 + (c + 1) * h2
    have := mul_self_eq_zero.1 h0
    linear_combination this - h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  rw [hc v, hc1, one_smul]
  rfl

theorem nonempty_equiv_elementaryGroup_plus_orthEight {n : ℕ} (hn : 3 ≤ n) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D n q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 3) {S : Type} [Group S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ 3 ∧
      Nonempty (S ≃* ↥(elementaryGroup (quadPlus n F))) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv hqp eS
  rw [hqp, hqe] at hF
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hF
  have hv₀ : quadPlus n F (Sum.elim (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F))
      (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F))) ≠ 0 := by
    rw [quadPlus_elim_orthEight, sum_single_mul_single_orthEight, if_pos rfl]
    exact one_ne_zero
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ⟨e.trans ?_⟩⟩
  exact (statedProjEquiv (coe_quadPlus n F) (commutator_orthogonalGroup_quadPlus hn)).trans
    ((QuotientGroup.quotientMulEquivOfEq (subgroupOf_scalars_eq_bot_orthEight hv₀)).trans
      QuotientGroup.quotientBot)

theorem nonempty_equiv_elementaryGroup_minus_orthEight {n : ℕ} (hn : 2 ≤ n) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 3) {S : Type}
    [Group S] (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (b c : F), Nat.card F = 2 ^ 3 ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (S ≃* ↥(elementaryGroup (quadMinus n F b c))) := by
  obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv hqp eS
  rw [hqp, hqe] at hF
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hF
  have hv₀ : quadMinus n F b c (Sum.elim (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) (1 : F))
      (Sum.elim (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) (1 : F)) 0)) ≠ 0 := by
    rw [quadMinus_hyp_orthEight, sum_single_mul_single_orthEight, if_pos rfl]
    exact one_ne_zero
  refine ⟨F, inferInstance, inferInstance, inferInstance, b, c, hF, hbc, ⟨e.trans ?_⟩⟩
  exact (statedProjEquiv (coe_quadMinus n F b c) (commutator_orthogonalGroup_quadMinus_of_two_le hn hbc)).trans
    ((QuotientGroup.quotientMulEquivOfEq (subgroupOf_scalars_eq_bot_orthEight hv₀)).trans
      QuotientGroup.quotientBot)

end Models

section InnerGen

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_fix_hypPair_orthEight (hQ : (polarBilin Q).Nondegenerate) {D : Subgroup (V ≃ₗ[K] V)}
    (hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : IsElemAbelian 3 D)
    (hD5 : 3 ^ 5 ≤ Nat.card D) :
    ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ D ∧ Nat.card F = 3 ^ 3 ∧
      ∃ P : HypPair Q, ∀ g ∈ F, g P.e = P.e ∧ g P.f = P.f := by
  classical
  obtain ⟨F, hFD, hFc, u, hu0, hQu, hFu⟩ := exists_fix_singular_orthEight hQ hDO hD hD5
  have hFodd : Odd (Nat.card F) := by rw [hFc]; decide
  have hWnd := polarNondegOn_fixSub_orthEight hQ (hFD.trans hDO) hFodd
  have huW : u ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub F := fun h hh => hFu h hh
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub F,
      polar Q u w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hWnd u huW hcon)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨z, hz⟩ : ∃ z : V, z = (polar Q u w)⁻¹ • w := ⟨_, rfl⟩
  have hzW : ∀ g ∈ F, g z = z := fun g hg => by rw [hz, map_smul, hwW g hg]
  have hcu : polar Q u z = 1 := by
    rw [hz, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw]
  have hQf : Q (z + Q z • u) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQu, polar_smul_right, polar_comm Q z u, hcu]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
    linear_combination Q z * h2
  have hpf : polar Q u (z + Q z • u) = 1 := by
    rw [polar_add_right, polar_smul_right, hcu, polar_self, hQu]
    simp
  refine ⟨F, hFD, hFc, ⟨u, z + Q z • u, hQu, hQf, hpf⟩, fun g hg => ⟨hFu g hg, ?_⟩⟩
  show g (z + Q z • u) = z + Q z • u
  rw [map_add, map_smul, hFu g hg, hzW g hg]

theorem le_centGenI_of_lift_orthEight {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : commutator ↥L = ⊤) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    {A : Subgroup X} (hAel : IsElemAbelian 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hQ : (polarBilin Q).Nondegenerate)
    (φ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(elementaryGroup Q))
    (Yh : ↥A →* ↥(elementaryGroup Q))
    (hYh : ∀ (a : ↥A) (k : ↥L),
      φ (QuotientGroup.mk (L.normalizerMonoidHom ⟨(a : X), hAL a.2⟩ k)) =
        Yh a * φ (QuotientGroup.mk k) * (Yh a)⁻¹)
    (P : HypPair Q)
    (hP : ∀ a : ↥A, ((Yh a : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) P.e = P.e ∧
      ((Yh a : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) P.f = P.f) :
    L ≤ GL83.CompFam.centGenI 3 A L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := ↥L with hY
  set ξ : Y →* ↥(elementaryGroup Q) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hξ
  have hξsurj : Function.Surjective ξ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hξker : ξ.ker = Subgroup.center Y := by
    ext y
    simp [hξ]
  let ρ : A →* (V ≃ₗ[K] V) := (elementaryGroup Q).subtype.comp Yh
  have hρO : ∀ a : A, ρ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun a =>
    elementaryGroup_le_orthogonalGroup Q (Yh a).2
  have hfin : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) fun g g' h =>
      LinearEquiv.ext (congrFun h)
  set Ab : Subgroup (V ≃ₗ[K] V) := ρ.range with hAb
  have hAbO : Ab ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, rfl⟩
    exact hρO a
  have hAbcomm : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm a b]
  have hAbexp : ∀ x ∈ Ab, x ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hAel.2 a a.2)
    rw [this, map_one]
  have hP' : ∀ g ∈ Ab, g P.e = P.e ∧ g P.f = P.f := by
    rintro _ ⟨a, rfl⟩
    exact hP a
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_ofNat]
    exact three_ne_zero_orthEight
  have hgen := CFSG.HardMathSupport.Timmesfeld.Coordinator.elementaryGroup_le_closure_hyperEichlerSet
    (Q := Q) Nat.prime_three hpK hQ hAbO hAbcomm hAbexp P (fun h hh => (hP' h hh).1)
    (fun h hh => (hP' h hh).2)
  set S := CFSG.HardMathSupport.Timmesfeld.Coordinator.hyperEichlerSet Q 3 Ab with hS
  have hSle : ∀ g ∈ S, g ∈ elementaryGroup Q := by
    rintro g ⟨F, -, -, u, w, -, -, rfl⟩
    exact eichler_mem_elementaryGroup Q u w
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set 𝒢 : Set Y := {y | ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) ∈ S} with h𝒢
  have hTtop : Subgroup.closure {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[K] V) ∈ S} = ⊤ := by
    rw [eq_top_iff]
    rintro ω -
    have hω : (ω : V ≃ₗ[K] V) ∈ Subgroup.closure S := hgen ω.2
    have key : ∀ g ∈ Subgroup.closure S, ∃ t ∈ Subgroup.closure
        {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[K] V) ∈ S}, (t : V ≃ₗ[K] V) = g := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        exact ⟨⟨x, hSle x hx⟩, Subgroup.subset_closure hx, rfl⟩
      | one => exact ⟨1, one_mem _, rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨t', ht', rfl⟩ := hy
        exact ⟨t * t', mul_mem ht ht', rfl⟩
      | inv x _ hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        exact ⟨t⁻¹, inv_mem ht, rfl⟩
    obtain ⟨t, ht, hte⟩ := key _ hω
    have : t = ω := Subtype.ext hte
    rwa [this] at ht
  have himage : ξ '' 𝒢 = {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[K] V) ∈ S} := by
    ext ω
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hω
      obtain ⟨y, rfl⟩ := hξsurj ω
      exact ⟨y, hω, rfl⟩
  have hgen' : Subgroup.closure 𝒢 ⊔ Subgroup.center Y = ⊤ := by
    have hmap : (Subgroup.closure 𝒢).map ξ = ⊤ := by
      rw [MonoidHom.map_closure, himage, hTtop]
    have := Subgroup.comap_map_eq ξ (Subgroup.closure 𝒢)
    rw [hmap, Subgroup.comap_top, hξker] at this
    exact this.symm
  have hsq : ∀ y ∈ 𝒢, y ^ 2 ∈ Subgroup.center Y := by
    intro y hy
    rw [← hξker, MonoidHom.mem_ker, map_pow]
    obtain ⟨F, -, -, u, w, -, -, hg⟩ := hy
    apply Subtype.ext
    change ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) *
      ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) = 1
    rw [hg]
    exact CFSG.HardMathSupport.Timmesfeld.Coordinator.eichler_mul_self_of_two_eq_zero h2 u w
  set ℰ : Set (Subgroup X) := {E | E ≤ A ∧ Nat.card A ≤ 3 * Nat.card E} with hℰdef
  have hℰ : ∀ E ∈ ℰ, E ≤ Subgroup.normalizer (L : Set X) := fun E hE => hE.1.trans hAL
  have hfix' : ∀ y ∈ 𝒢, ∃ E, ∃ hE : E ∈ ℰ, ∀ (a : X) (ha : a ∈ E),
      ((L.normalizerMonoidHom ⟨a, hℰ E hE ha⟩ : MulAut ↥L) y)⁻¹ * y ∈ Subgroup.center ↥L := by
    intro y hy
    have hg : ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) ∈ S := hy
    obtain ⟨F, hFAb, hF, hcomm⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.exists_commute_of_mem_hyperEichlerSet hAbO hg
    set N : Subgroup A := F.comap ρ with hN
    have hcardN : Nat.card A ≤ 3 * Nat.card N := by
      have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
      set F' : Subgroup Ab := F.subgroupOf Ab with hF'
      have hNeq : N = F'.comap ρ.rangeRestrict := by
        ext a
        simp [hN, hF', Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      have hidx : N.index = F'.index := by
        rw [hNeq]
        exact Subgroup.index_comap_of_surjective F' hsurj
      have hF'card : Nat.card F' = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFAb).toEquiv
      have h1 : F'.index * Nat.card F' = Nat.card Ab := F'.index_mul_card
      have h2' : N.index * Nat.card N = Nat.card A := N.index_mul_card
      have hFpos : 0 < Nat.card F := Nat.card_pos
      have hle : F'.index ≤ 3 := by
        by_contra hlt
        push Not at hlt
        have h3 : 3 * Nat.card F < F'.index * Nat.card F := Nat.mul_lt_mul_of_pos_right hlt hFpos
        have h4 : F'.index * Nat.card F = Nat.card Ab := by rw [← hF'card]; exact h1
        omega
      calc Nat.card A = N.index * Nat.card N := h2'.symm
        _ ≤ 3 * Nat.card N := Nat.mul_le_mul_right _ (hidx ▸ hle)
    have hE : N.map A.subtype ∈ ℰ := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩
        exact a.2
      · rw [Subgroup.card_map_of_injective A.subtype_injective]
        exact hcardN
    refine ⟨N.map A.subtype, hE, ?_⟩
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    have hcom := hcomm (ρ a') ha'
    rw [← hξker, MonoidHom.mem_ker, map_mul, map_inv]
    show (ξ (L.normalizerMonoidHom ⟨(a' : X), hAL a'.2⟩ y))⁻¹ * ξ y = 1
    have hξa : ξ (L.normalizerMonoidHom ⟨(a' : X), hAL a'.2⟩ y) =
        Yh a' * ξ y * (Yh a')⁻¹ := hYh a' y
    rw [hξa]
    have hfixed : Yh a' * ξ y * (Yh a')⁻¹ = ξ y := by
      apply Subtype.ext
      change (ρ a') * ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) * (ρ a')⁻¹ =
        ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V)
      rw [hcom, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfixed, inv_mul_cancel]
  have hmain := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.le_iSup_centralizer_of_lifts
    hL hZ ℰ hℰ 𝒢 hgen' hsq hfix'
  refine hmain.trans (iSup₂_le fun E hE => ?_)
  exact le_iSup (fun E : {E : Subgroup X // E ≤ A ∧ Nat.card A ≤ 3 * Nat.card E} =>
    L ⊓ Subgroup.centralizer (E.1 : Set X)) ⟨E, hE.1, hE.2⟩

end InnerGen

section Inner

theorem le_glbCore_of_inner_orthEight {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hinn : InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate)
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(elementaryGroup Q))
    (h5 : ∃ A : Subgroup (V ≃ₗ[F] V), A ≤ elementaryGroup Q ∧ IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 5) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (V ≃ₗ[F] V) := by
    have : Finite V := Module.finite_of_finite F
    exact Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) DFunLike.coe_injective
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  set E := elementaryGroup Q with hEdef
  have hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [← hZ, Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun ψ : MulAut ↥K => ψ h) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  have hB5 : 5 ≤ CFSG.Open.pRank 3 B := by
    obtain ⟨A, hAE, hAel, hAc⟩ := h5
    let ι : ↥E →* X := K.subtype.comp
      ((InputsSeitz3.equivCenterQuot hZ).symm.toMonoidHom.comp φ.symm.toMonoidHom)
    have hι : Function.Injective ι := by
      intro x y hxy
      have h1 := Subtype.val_injective hxy
      exact φ.symm.injective ((InputsSeitz3.equivCenterQuot hZ).symm.injective h1)
    set A' : Subgroup X := (A.subgroupOf E).map ι with hA'
    have hA'c : Nat.card A' = 3 ^ 5 := by
      rw [hA', Subgroup.card_map_of_injective hι, ← hAc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv
    have hA'el : IsElemAbelian 3 A' :=
      CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hAel E) ι
    rw [hrk]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hA'el hA'c
  let α : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hαmem : ∀ b : ↥B, α b ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun b =>
    hinn ⟨⟨b, hBN b.2⟩, Subgroup.mem_subgroupOf.2 b.2, rfl⟩
  let β : ↥B →* ↥(MulAut.conj : ↥K →* MulAut ↥K).range := α.codRestrict _ hαmem
  let κ : ↥B →* ↥K := (MonoidHom.ofInjective hconj).symm.toMonoidHom.comp β
  have hκ : ∀ b : ↥B, MulAut.conj (κ b) = α b := fun b => by
    have h1 : MonoidHom.ofInjective hconj (κ b) = β b := MulEquiv.apply_symm_apply _ _
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  let Yh : ↥B →* ↥E := (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))).comp κ
  have hrel : ∀ (b : ↥B) (k : ↥K),
      φ (QuotientGroup.mk (α b k)) = Yh b * φ (QuotientGroup.mk k) * (Yh b)⁻¹ := by
    intro b k
    rw [← hκ b, MulAut.conj_apply]
    simp only [Yh, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
  have hαapp : ∀ (b : ↥B) (k : ↥K), ((α b k : ↥K) : X) = (b : X) * k * (b : X)⁻¹ := fun b k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K _ k
  have hmk : ∀ k k' : ↥K, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k' →
      k = k' := by
    intro k k' h
    have h' := QuotientGroup.eq.1 h
    rw [hZ, Subgroup.mem_bot] at h'
    exact inv_mul_eq_one.1 h'
  have hYhinj : Function.Injective Yh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hcen : (b : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hrel b ⟨k, hk⟩
      rw [hb, one_mul, inv_one, mul_one] at h1
      have h3 := congrArg Subtype.val (hmk _ _ (φ.injective h1))
      rw [hαapp] at h3
      calc k * (b : X) = (b : X) * k * (b : X)⁻¹ * b := by rw [h3]
        _ = (b : X) * k := by group
    have hbC : (b : X) ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨b.2, hcen⟩
    rw [hC, Subgroup.mem_bot] at hbC
    exact Subgroup.mem_bot.2 (Subtype.ext hbC)
  let ρ : ↥B →* (V ≃ₗ[F] V) := E.subtype.comp Yh
  have hρinj : Function.Injective ρ := E.subtype_injective.comp hYhinj
  set D := ρ.range with hD
  have hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨b, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q (Yh b).2
  have hDel : IsElemAbelian 3 D := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      rw [← map_mul, ← map_mul, hB.1.is_comm.comm a b]
    · obtain ⟨b, rfl⟩ := hg
      rw [← map_pow]
      have : b ^ 3 = 1 := Subtype.ext (hB.2 b b.2)
      rw [this, map_one]
  have hBc : Nat.card ↥B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hD5 : 3 ^ 5 ≤ Nat.card D := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, hBc]
    exact Nat.pow_le_pow_right (by norm_num) hB5
  obtain ⟨F₀, hF₀D, hF₀c, P, hP⟩ := exists_fix_hypPair_orthEight hQ hDO hDel hD5
  have hF₀r : F₀ ≤ ρ.range := hF₀D
  set E' : Subgroup X := (F₀.comap ρ).map B.subtype with hE'
  have hE'B : E' ≤ B := Subgroup.map_subtype_le _
  have hE'c : Nat.card E' = Nat.card F₀ := by
    rw [hE', Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_map_of_injective hρinj,
      Subgroup.map_comap_eq_self hF₀r]
  have hE'el : IsElemAbelian 3 E' := GL83.CompFam.elem_mono hB hE'B
  have hmemE' : ∀ a : ↥E', ρ (Subgroup.inclusion hE'B a) ∈ F₀ := by
    rintro ⟨_, ⟨b, hb, rfl⟩⟩
    have : Subgroup.inclusion hE'B ⟨B.subtype b, ⟨b, hb, rfl⟩⟩ = b := Subtype.ext rfl
    rw [this]
    exact hb
  have hgen : K ≤ GL83.CompFam.centGenI 3 E' K := by
    refine le_centGenI_of_lift_orthEight hperf (by rw [hZ, Subgroup.card_bot]; decide) hE'el
      (hE'B.trans hBN) hQ φ (Yh.comp (Subgroup.inclusion hE'B)) (fun a k => ?_) P
      (fun a => hP _ (hmemE' a))
    exact hrel (Subgroup.inclusion hE'B a) k
  exact InputsSeitz3.le_glbCore_of_centGenI Nat.prime_three hE'B hE'el (hE'c.trans hF₀c).ge hgen

open CFSG.LieType.Universal.Spin (quadPlus quadMinus nondegenerate_polarBilin_quadPlus
  nondegenerate_polarBilin_quadMinus_of_finite)

@[expose] def IsOrthEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ n : ℕ, ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
    ((6 ≤ n ∧ d.1 = .D n q) ∨ (5 ≤ n ∧ d.1 = .twistedD n q))

theorem le_glbCore_of_orthEight_inner {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsOrthEightIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hinn : InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    K ≤ GLBCore 3 2 B := by
  have hFin : ∀ {m : ℕ} (i j : ℕ) (hi : i < m) (hj : j < m), i ≠ j → (⟨i, hi⟩ : Fin m) ≠ ⟨j, hj⟩ :=
    fun i j _ _ hij h => hij (congrArg Fin.val h)
  obtain ⟨n, q, hqp, hqe, ⟨hn, hdq⟩ | ⟨hn, hdq⟩⟩ := hd
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨F, _, _, _, hF, ⟨φ⟩⟩ := nonempty_equiv_elementaryGroup_plus_orthEight (by omega) hv hqp hqe e
    have hQ := nondegenerate_polarBilin_quadPlus n F
    refine le_glbCore_of_inner_orthEight hcore hB hrk hK hBN hC hinn hQ φ ?_
    obtain ⟨c, u, v, hp, ho⟩ := exists_five_rotPairs_quadPlus_orthEight (K := F) hn
    have hT := exists_totallySingular_of_hypPairs
      (plusPair_orth (K := F) (hFin (m := n) 0 1 (by omega) (by omega) (by norm_num)))
      (plusPair_orth (K := F) (hFin (m := n) 0 2 (by omega) (by omega) (by norm_num)))
      (plusPair_orth (K := F) (hFin (m := n) 1 2 (by omega) (by omega) (by norm_num)))
    exact exists_elemAbelian_five_orthEight hQ hT (commutator_orthogonalGroup_quadPlus (by omega)) hp ho
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨F, _, _, _, b, c, hF, hirr, ⟨φ⟩⟩ :=
      nonempty_equiv_elementaryGroup_minus_orthEight (by omega) hv hqp hqe e
    have hQ := nondegenerate_polarBilin_quadMinus_of_finite n F hirr
    refine le_glbCore_of_inner_orthEight hcore hB hrk hK hBN hC hinn hQ φ ?_
    obtain ⟨c', u, v, hp, ho⟩ := exists_five_rotPairs_quadMinus_orthEight hF hn hirr
    have hT := exists_totallySingular_of_hypPairs
      (minusPair_orth (K := F) (b := b) (c := c) (hFin (m := n - 1) 0 1 (by omega) (by omega) (by norm_num)))
      (minusPair_orth (K := F) (b := b) (c := c) (hFin (m := n - 1) 0 2 (by omega) (by omega) (by norm_num)))
      (minusPair_orth (K := F) (b := b) (c := c) (hFin (m := n - 1) 1 2 (by omega) (by omega) (by norm_num)))
    exact exists_elemAbelian_five_orthEight hQ hT (commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr)
      hp ho

end Inner

section TwE6Eight

open CFSG.LieType.Chevalley (twistedE6RootGroup twistedE6Inn twistedE6Diag)
open CFSG.LieType.Seitz (seitzHyperGamma)

theorem le_glbCore_of_twE6Eight_diag
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.TwE6EightDiagCubes)
    {X : Type} [Group X] [Finite X] {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    {L : Type} [Field L] [Finite L] {σ : L ≃+* L} (hL : Nat.card L = (2 ^ 3) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ 3)) (θ : ↥K ≃* twistedE6RootGroup L σ)
    (hdiag : (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤
      twistedE6Inn L σ ⊔ twistedE6Diag L σ) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := InputsSeitz3.autIm B K with hAdef
  set A' := A.map (MulAut.congr θ).toMonoidHom with hA'def
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  have hA'el : IsElemAbelian 3 A' := CFSG.LieType.SeitzGeneration.isElemAbelian_map_congr θ hAel
  have hA'c : Nat.card A' = 3 ^ CFSG.Open.pRank 3 B := by
    rw [hA'def, CFSG.LieType.SeitzGeneration.card_map_congr θ A, hAdef, InputsSeitz3.card_autIm hBN hC,
      GL83.PiGen.card_eq_pow_pRank hB]
  have hout' := CFSG.LieType.SeitzGeneration.not_le_range_conj_map_congr θ hout
  obtain ⟨a, haA', ha⟩ := SetLike.not_le_iff_exists.1 hout'
  have ha3 : a ^ 3 = 1 := hA'el.2 a haA'
  obtain ⟨E, hEc, hEa, hEA'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 3)
    (H := Subgroup.zpowers a) (L := A')
    (by rw [Nat.card_zpowers]; exact (orderOf_dvd_of_pow_eq_one ha3).trans (by norm_num))
    (by rw [hA'c]; exact Nat.pow_dvd_pow 3 (by omega))
    ((Subgroup.zpowers_le).2 haA')
  have hEel : IsElemAbelian 3 E := GL83.CompFam.elem_mono hA'el hEA'
  have hEi : ¬ E ≤ twistedE6Inn L σ := fun h => ha (h (hEa (Subgroup.mem_zpowers a)))
  have htop := hD L hL σ hσ E hEel hEc (hEA'.trans hdiag) hEi
  set E₀ := E.comap (MulAut.congr θ).toMonoidHom with hE₀
  have hE₀map : E₀.map (MulAut.congr θ).toMonoidHom = E :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.congr θ).surjective E
  have htop₀ : seitzHyperGamma 3 E₀ = ⊤ :=
    CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map θ
      (MulAut.congr θ).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
      (MulAut.congr θ).injective (by rw [hE₀map]; exact htop)
  have hE₀A : E₀ ≤ A := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hEA' hx
    have : y = x := (MulAut.congr θ).injective hyx
    rw [← this]
    exact hy
  have hE₀c : Nat.card E₀ = 3 ^ 3 := by
    rw [← CFSG.LieType.SeitzGeneration.card_map_congr θ E₀, hE₀map, hEc]
  exact le_glbCore_of_seitzHyperGamma_cube hB le_rfl hC hE₀A hE₀c htop₀

end TwE6Eight

section Residual

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.LieType.Chevalley (twistedE6RootGroup twistedE6Inn twistedE6Diag)

section ResidualDef

@[expose] def Input23_19ExcThreeRest4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      B ≤ Subgroup.normalizer (K : Set X) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex 3 d.1 → d.1 ≠ .tits → ¬ IsL2EightIndex d.1 → ¬ Gen2318Index d.1 →
        ¬ InputsSeitz7.IsSpTwoIndex d → ¬ InputsSeitz7.IsUnitaryTwoIndex d →
        ¬ InputsSeitz7.IsSpEightIndex d → ¬ InputsSeitz7.IsUnitaryEightIndex d →
        ¬ InputsSeitz7.IsUThreeEightIndex d →
        ¬ InputsSeitz8.IsOrthTwoIndex d → ¬ InputsSeitz8.IsTriD4TwoIndex d →
        ¬ InputsSeitz8.IsG2EightIndex d → ¬ InputsSeitz7.IsUSixIndex d →
        ¬ InputsSeitz8.IsOmegaEightTwoIndex d → ¬ IsD4FourIndex d.1 →
        ¬ Bal209F4Aux.IsF4TwoIndex d.1 → ¬ IsTwistedE6FourIndex d.1 → ¬ IsF4EightIndex d.1 →
        ¬ OuterFourAux.IsD4EightIndex d.1 →
        (IsOrthEightIndex d → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (OuterFourInAux.IsTwE6EightIndex d.1 → B ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
          ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L), Nat.card L = (2 ^ 3) ^ 2 →
            (∀ c, σ c = c ^ (2 ^ 3)) → ∀ θ : ↥K ≃* twistedE6RootGroup L σ,
              ¬ (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤
                twistedE6Inn L σ ⊔ twistedE6Diag L σ) →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ((Subgroup.center ↥K ≠ ⊥ ∧ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 ∧
            B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) ∨
          B ⊓ Subgroup.centralizer (K : Set X) = ⊥) →
        K ≤ GLBCore 3 2 B

end ResidualDef

theorem not_coverIndex_d4Eight {d : TauCeti.LieTypeIndex} (hd : OuterFourAux.IsD4EightIndex d) :
    ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d := by
  cases d with
  | D r q => exact id
  | _ => exact absurd hd (by simp [OuterFourAux.IsD4EightIndex])

theorem not_coverIndex_orthEight {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthEightIndex d) :
    ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 := by
  obtain ⟨n, q, -, -, ⟨-, hdq⟩ | ⟨-, hdq⟩⟩ := hd <;> rw [hdq] <;> exact id

theorem fourIndex_of_twE6Eight {d : TauCeti.LieTypeIndex} (hd : OuterFourInAux.IsTwE6EightIndex d) :
    FourIndex d := by
  cases d with
  | twistedE6 q => exact hd
  | _ => exact hd.elim

theorem input23_19ExcThreeRest3_of_rest4
    (hD8 : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.TwE6EightDiagCubes)
    (h : Input23_19ExcThreeRest4) : InputsSeitz9.Input23_19ExcThreeRest3 := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall hBN d hd hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hsix hrest
  obtain ⟨e⟩ := hd
  by_cases hD : OuterFourAux.IsD4EightIndex d.1
  · have hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
      hrest.resolve_left fun hc => not_coverIndex_d4Eight hD hc.2.1
    exact le_glbCore_of_d4Eight_outer hcore hB hB4 hrk hK d e hD hBN hC
      (hsix (Or.inr (Or.inr ((OuterFourAux.fourIndex_iff d.1).2 (Or.inr hD)))))
  by_cases hO : IsOrthEightIndex d ∧ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range
  · have hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
      hrest.resolve_left fun hc => not_coverIndex_orthEight hO.1 hc.2.1
    exact le_glbCore_of_orthEight_inner hcore hB hrk hK d e hO.1 hBN hC hO.2
  by_cases hT : OuterFourInAux.IsTwE6EightIndex d.1 ∧ B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
      ∃ (L : Type) (_ : Field L) (_ : Finite L) (σ : L ≃+* L), Nat.card L = (2 ^ 3) ^ 2 ∧
        (∀ c, σ c = c ^ (2 ^ 3)) ∧ ∃ θ : ↥K ≃* twistedE6RootGroup L σ,
          (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤ twistedE6Inn L σ ⊔ twistedE6Diag L σ
  · obtain ⟨hT8, hC, L, _, _, σ, hL, hσ, θ, hdiag⟩ := hT
    exact le_glbCore_of_twE6Eight_diag hD8 hB hB4 hBN hC
      (hsix (Or.inr (Or.inr (fourIndex_of_twE6Eight hT8)))) hL hσ θ hdiag
  refine h X hKX hcore B hB hB4 hrk K hK haut hsmall hBN d ⟨e⟩ hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hD (fun hO' hinn => hO ⟨hO', hinn⟩) ?_ hsix hrest
  intro hT8 hC L _ _ σ hL hσ θ hdiag
  exact hT ⟨hT8, hC, L, inferInstance, inferInstance, σ, hL, hσ, θ, hdiag⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10

end
