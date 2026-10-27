module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.LieType.ChevTwo.OrthogonalPlusTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremB (IsTransvection)
open QuadraticMap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isoGrp_eq_isometryCore (Q : (ι → ZMod 2) → ZMod 2) :
    isoGrp Q = CFSG.MatrixModel.isometryCore Q := by
  apply le_antisymm
  · intro g hg
    exact Subgroup.subset_closure hg
  · rw [CFSG.MatrixModel.isometryCore, Subgroup.closure_le]
    intro g hg
    exact hg

theorem statedOmega_eq_commutator (Q : (ι → ZMod 2) → ZMod 2) :
    StatedOmega Q = ⁅isoGrp Q, isoGrp Q⁆ := by
  rw [isoGrp_eq_isometryCore]
  rfl

theorem statedOmega_le_isoGrp (Q : (ι → ZMod 2) → ZMod 2) : StatedOmega Q ≤ isoGrp Q := by
  rw [statedOmega_eq_commutator]
  exact Subgroup.commutator_le_self _

theorem isoGrp_le_normalizer (Q : (ι → ZMod 2) → ZMod 2) :
    isoGrp Q ≤ Subgroup.normalizer (StatedOmega Q : Set (GL ι (ZMod 2))) := by
  rw [statedOmega_eq_commutator, ← Subgroup.map_subtype_commutator]
  calc isoGrp Q = (⊤ : Subgroup (isoGrp Q)).map (isoGrp Q).subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (Subgroup.normalizer (commutator (isoGrp Q) : Set (isoGrp Q))).map (isoGrp Q).subtype := by
        rw [Subgroup.normalizer_eq_top]
    _ ≤ _ := Subgroup.le_normalizer_map _

@[expose] noncomputable def kappa (Q : (ι → ZMod 2) → ZMod 2) :
    isoGrp Q →* MulAut ↥(StatedOmega Q) :=
  (StatedOmega Q).normalizerMonoidHom.comp (Subgroup.inclusion (isoGrp_le_normalizer Q))

theorem kappa_apply_val (Q : (ι → ZMod 2) → ZMod 2) (g : isoGrp Q) (x : StatedOmega Q) :
    ((kappa Q g x : StatedOmega Q) : GL ι (ZMod 2)) = (g : GL ι (ZMod 2)) * x * (g : GL ι (ZMod 2))⁻¹ :=
  rfl

theorem inducedByIso_iff_mem_range (Q : (ι → ZMod 2) → ZMod 2) (α : MulAut ↥(StatedOmega Q)) :
    InducedByIso Q α ↔ α ∈ (kappa Q).range := by
  constructor
  · rintro ⟨g, hg, h⟩
    exact ⟨⟨g, hg⟩, MulEquiv.ext fun x => Subtype.ext ((kappa_apply_val Q _ x).trans (h x).symm)⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, kappa_apply_val Q g⟩

@[expose] def RegularQuad (Q : (ι → ZMod 2) → ZMod 2) : Prop :=
  ∃ q : QuadraticForm (ZMod 2) (ι → ZMod 2), ⇑q = Q ∧
    ∀ v, (∀ w, QuadraticMap.polar q v w = 0) → v = 0

structure GoodQ (Q : (ι → ZMod 2) → ZMod 2) : Prop where
  regular : RegularQuad Q
  card_ge : 4 ≤ Fintype.card ι
  simple : IsSimpleGroup ↥(StatedOmega Q)
  relIndex_eq : (StatedOmega Q).relIndex (isoGrp Q) = 2

noncomputable def statedProjEquivTwo (H : Subgroup (GL ι (ZMod 2))) : StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

theorem isSimpleGroup_of_statedProj (H : Subgroup (GL ι (ZMod 2))) [IsSimpleGroup (StatedProj H)] :
    IsSimpleGroup H :=
  (statedProjEquivTwo H).symm.isSimpleGroup

theorem isoGrp_eq_comap {Q : (ι → ZMod 2) → ZMod 2} {q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    (hq : ⇑q = Q) :
    isoGrp Q = (TauCeti.QuadraticMap.orthogonalGroup q).comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).toMonoidHom := by
  rw [isoGrp_eq_isometryCore, CFSG.MatrixModel.isometryCore,
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hq]

theorem relIndex_statedOmega_eq {Q : (ι → ZMod 2) → ZMod 2}
    {q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hq : ⇑q = Q) :
    (StatedOmega Q).relIndex (isoGrp Q) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup q, TauCeti.QuadraticMap.orthogonalGroup q⁆.relIndex
        (TauCeti.QuadraticMap.orthogonalGroup q) := by
  rw [isoGrp_eq_comap hq, CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hq,
    Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).surjective]

noncomputable def statedOmegaEquivDerived {Q : (ι → ZMod 2) → ZMod 2}
    {q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hq : ⇑q = Q) :
    StatedOmega Q ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
      TauCeti.QuadraticMap.orthogonalGroup q⁆ :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).subgroupMap (StatedOmega Q)).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hq]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).surjective _))

theorem regularQuad_of_nondegenerate {Q : (ι → ZMod 2) → ZMod 2}
    {q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hq : ⇑q = Q)
    (hnd : (polarBilin q).Nondegenerate) : RegularQuad Q :=
  ⟨q, hq, fun v hv => hnd.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w⟩

theorem goodQ_plus {n : ℕ} (hn : 2 ≤ n) : GoodQ (StatedQuadPlus (n + 1) (ZMod 2)) where
  regular :=
    regularQuad_of_nondegenerate (CFSG.LieType.Universal.Spin.coe_quadPlus (n + 1) (ZMod 2))
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2))
  card_ge := by simp only [Fintype.card_sum, Fintype.card_fin]; omega
  simple := by
    have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
      (K := ZMod 2) (n := n + 1) (by omega)
    exact isSimpleGroup_of_statedProj _
  relIndex_eq := by
    rw [relIndex_statedOmega_eq (CFSG.LieType.Universal.Spin.coe_quadPlus (n + 1) (ZMod 2)),
      CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup
        (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2))
        (by
          rw [Module.finrank_fintype_fun_eq_card]
          simp only [Fintype.card_sum, Fintype.card_fin]
          omega)]
    exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ _

theorem hirr_one_one : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide

theorem exists_ne_zero_of_finrank_eq_half_quadMinus {m : ℕ} (hm : 1 ≤ m)
    (U : Submodule (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2))
    (hU : Module.finrank (ZMod 2) U =
      Module.finrank (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) / 2) :
    ∃ u ∈ U, CFSG.LieType.Universal.Spin.quadMinus m (ZMod 2) 1 1 u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hm hirr_one_one ⟨U, ?_, hcon⟩
  rw [hU, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem goodQ_minus {n : ℕ} (hn : 1 ≤ n) : GoodQ (StatedQuadMinus (n + 1) (ZMod 2) 1 1) := by
  have hq := CFSG.LieType.Universal.Spin.coe_quadMinus (n + 1) (ZMod 2) 1 1
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n + 1)
    (ZMod 2) hirr_one_one
  have hdim : Module.finrank (ZMod 2) (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) =
      2 * n + 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨regularQuad_of_nondegenerate hq hnd, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]; omega
  · rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain ⟨hs, -⟩ := CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
        (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1) hnd (by omega)
        (exists_ne_zero_of_finrank_eq_half_quadMinus (by omega))
      exact (statedOmegaEquivDerived hq).isSimpleGroup
    · have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
        (K := ZMod 2) (n := n + 1) (by omega) hirr_one_one
      exact isSimpleGroup_of_statedProj _
  · rw [relIndex_statedOmega_eq hq]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨-, -, -, hidx, -⟩ :=
        CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
          (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1) hnd (by omega)
          (exists_ne_zero_of_finrank_eq_half_quadMinus (by omega))
      exact hidx
    · rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd
        (by omega)]
      exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ _

theorem not_isSimpleGroup_statedOmega_plus_two :
    ¬ IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
  not_isSimpleGroup_statedOmega_plus_two'

namespace OrthBasic

open QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal (reflect reflect_apply_of_map_eq_one reflect_conj
  reflect_mul_self reflect_mem_orthogonalGroup)
open CFSG.RankThree.Literature.FSmith (zmod2_eq_zero_or_eq_one zmod2_eq_one_of_ne_zero
  polar_self_zmod2 exists_ne_zero_polar_eq_zero)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem exists_polar_eq_one (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) {u : V} (hu : u ≠ 0) :
    ∃ x, polar q u x = 1 := by
  by_contra! h
  exact hu (hnd u fun w => by
    rcases zmod2_eq_zero_or_eq_one (polar q u w) with h0 | h1
    · exact h0
    · exact absurd h1 (h w))

theorem exists_nonsingular_perp_pair [FiniteDimensional (ZMod 2) V]
    (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) (h3 : 3 ≤ finrank (ZMod 2) V)
    {a x : V} (hax : polar q a x = 1) :
    ∃ c, q c = 1 ∧ polar q a c = 0 ∧ polar q x c = 0 := by
  obtain ⟨w, hw0, hwa, hwx⟩ := exists_ne_zero_polar_eq_zero (Q := q) h3 a x
  rcases zmod2_eq_zero_or_eq_one (q w) with hqw | hqw
  · obtain ⟨v, hv⟩ := exists_polar_eq_one hnd hw0
    have hxa : polar q x a = 1 := by rw [polar_comm]; exact hax
    set v' := v - polar q v x • a - polar q v a • x with hv'
    have h1 : polar q v' a = 0 := by
      rw [hv', polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_self_zmod2,
        hxa, smul_eq_mul, smul_eq_mul, mul_zero, mul_one, sub_zero, sub_self]
    have h2 : polar q v' x = 0 := by
      rw [hv', polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_self_zmod2,
        hax, smul_eq_mul, smul_eq_mul, mul_zero, mul_one, sub_zero, sub_self]
    have h3' : polar q w v' = 1 := by
      rw [hv', polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
        hwa, hwx, hv, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, sub_zero, sub_zero]
    rcases zmod2_eq_zero_or_eq_one (q v') with hqv | hqv
    · refine ⟨w + v', ?_, ?_, ?_⟩
      · rw [QuadraticMap.map_add q, hqw, hqv, h3', zero_add, zero_add]
      · rw [polar_add_right, polar_comm q a w, polar_comm q a v', hwa, h1, add_zero]
      · rw [polar_add_right, polar_comm q x w, polar_comm q x v', hwx, h2, add_zero]
    · exact ⟨v', hqv, by rw [polar_comm]; exact h1, by rw [polar_comm]; exact h2⟩
  · exact ⟨w, hqw, by rw [polar_comm]; exact hwa, by rw [polar_comm]; exact hwx⟩

theorem exists_nonsingular_perp [FiniteDimensional (ZMod 2) V]
    (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) (h3 : 3 ≤ finrank (ZMod 2) V) (u : V) :
    ∃ a, q a = 1 ∧ polar q u a = 0 := by
  by_cases hu : u = 0
  · have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨u', hu'⟩ := exists_ne (0 : V)
    obtain ⟨x, hx⟩ := exists_polar_eq_one hnd hu'
    obtain ⟨c, hc, -, -⟩ := exists_nonsingular_perp_pair hnd h3 hx
    exact ⟨c, hc, by rw [hu, polar_zero_left]⟩
  · obtain ⟨x, hx⟩ := exists_polar_eq_one hnd hu
    obtain ⟨c, hc, huc, -⟩ := exists_nonsingular_perp_pair hnd h3 hx
    exact ⟨c, hc, huc⟩

theorem exists_nonsingular_perp_ne [FiniteDimensional (ZMod 2) V]
    (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) (h3 : 3 ≤ finrank (ZMod 2) V) {a : V}
    (ha : q a = 1) : ∃ c, q c = 1 ∧ polar q a c = 0 ∧ c ≠ a := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact zero_ne_one ha
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd ha0
  obtain ⟨c, hc, hac, hxc⟩ := exists_nonsingular_perp_pair hnd h3 hx
  refine ⟨c, hc, hac, ?_⟩
  rintro rfl
  rw [polar_comm, hx] at hxc
  exact one_ne_zero hxc

theorem exists_nonsingular_polar_eq_one [FiniteDimensional (ZMod 2) V]
    (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) (h3 : 3 ≤ finrank (ZMod 2) V) {a : V}
    (ha : q a = 1) : ∃ b, q b = 1 ∧ polar q a b = 1 := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact zero_ne_one ha
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd ha0
  rcases zmod2_eq_zero_or_eq_one (q x) with hqx | hqx
  · obtain ⟨c, hc, hac, hxc⟩ := exists_nonsingular_perp_pair hnd h3 hx
    refine ⟨x + c, ?_, ?_⟩
    · rw [QuadraticMap.map_add q, hqx, hc, hxc, zero_add, add_zero]
    · rw [polar_add_right, hx, hac, add_zero]
  · exact ⟨x, hqx, hx⟩

theorem eq_of_reflect_eq (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) {u v : V} (hu : q u = 1)
    (hv : q v = 1) (h : reflect q u = reflect q v) : u = v := by
  have hu0 : u ≠ 0 := by rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd hu0
  have hxu : polar q x u = 1 := by rw [polar_comm]; exact hx
  have h1 := LinearEquiv.congr_fun h x
  rw [reflect_apply_of_map_eq_one hu, reflect_apply_of_map_eq_one hv, hxu, one_smul] at h1
  have h2 := add_left_cancel h1
  rcases zmod2_eq_zero_or_eq_one (polar q x v) with h0 | h0
  · rw [h0, zero_smul] at h2
    exact absurd h2 hu0
  · rw [h0, one_smul] at h2
    exact h2

theorem reflect_ne_one (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) {a : V} (ha : q a = 1) :
    reflect q a ≠ 1 := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact zero_ne_one ha
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd ha0
  intro h
  have h1 := LinearEquiv.congr_fun h x
  rw [reflect_apply_of_map_eq_one ha, polar_comm, hx, one_smul, LinearEquiv.coe_one, id] at h1
  exact ha0 (by simpa using h1)

theorem reflect_mul_comm {a c : V} (ha : q a = 1) (hc : q c = 1) (hac : polar q a c = 0) :
    reflect q a * reflect q c = reflect q c * reflect q a := by
  have hca : polar q c a = 0 := by rw [polar_comm]; exact hac
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply_of_map_eq_one ha,
    reflect_apply_of_map_eq_one hc, reflect_apply_of_map_eq_one ha,
    reflect_apply_of_map_eq_one hc, polar_add_left, polar_add_left, polar_smul_left,
    polar_smul_left, hca, hac, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero, add_zero]
  abel

theorem eq_one_of_commute_reflect [FiniteDimensional (ZMod 2) V]
    (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) (h3 : 3 ≤ finrank (ZMod 2) V)
    {z : V ≃ₗ[ZMod 2] V} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hcomm : ∀ a, q a = 1 → z * reflect q a = reflect q a * z) : z = 1 := by
  have hfix : ∀ a, q a = 1 → z a = a := by
    intro a ha
    have hza : q (z a) = 1 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hz, ha]
    refine eq_of_reflect_eq hnd hza ha ?_
    rw [← reflect_conj hz a, hcomm a ha, mul_inv_cancel_right]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.coe_one, id]
  rcases zmod2_eq_zero_or_eq_one (q v) with hv | hv
  · obtain ⟨a, ha, hva⟩ := exists_nonsingular_perp hnd h3 v
    have hva' : q (v + a) = 1 := by
      rw [QuadraticMap.map_add q, hv, ha, hva, zero_add, add_zero]
    have h1 := hfix (v + a) hva'
    rw [map_add, hfix a ha] at h1
    exact add_right_cancel h1
  · exact hfix v hv

section GroupTheory

variable {G : Type*} [Group G]

theorem le_normalizer_commutator (O : Subgroup G) :
    O ≤ Subgroup.normalizer ((⁅O, O⁆ : Subgroup G) : Set G) := by
  rw [← Subgroup.map_subtype_commutator]
  calc O = (⊤ : Subgroup O).map O.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (Subgroup.normalizer (commutator O : Set O)).map O.subtype := by
        rw [Subgroup.normalizer_eq_top]
    _ ≤ _ := Subgroup.le_normalizer_map _

theorem orderOf_eq_of_isSimpleGroup_of_comm {H : Type*} [Group H] [IsSimpleGroup H]
    (hc : ∀ a b : H, a * b = b * a) {x y : H} (hx : x ≠ 1) (hy : y ≠ 1) :
    orderOf x = orderOf y := by
  have key : ∀ {x y : H}, y ≠ 1 → orderOf x ∣ orderOf y := by
    intro x y hy
    have : (Subgroup.zpowers y).Normal :=
      ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers y) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.mp h) hy
    · exact orderOf_dvd_of_mem_zpowers (h ▸ Subgroup.mem_top x)
  exact Nat.dvd_antisymm (key hy) (key hx)

theorem eq_one_of_forall_commute {H : Subgroup G} [IsSimpleGroup H]
    (hna : ¬ ∀ x y : H, x * y = y * x) {c : G} (hc : c ∈ H) (hcw : ∀ w ∈ H, c * w = w * c) :
    c = 1 := by
  have hmem : (⟨c, hc⟩ : H) ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.mpr fun w => Subtype.ext (hcw w w.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exact absurd (fun x y => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x) hna

theorem commute_of_commute_commutator {O : Subgroup G}
    (hZ : ∀ c ∈ ⁅O, O⁆, (∀ w ∈ ⁅O, O⁆, c * w = w * c) → c = 1)
    {z : G} (hzO : z ∈ O) (hz : ∀ w ∈ ⁅O, O⁆, z * w = w * z) {g : G} (hg : g ∈ O) :
    z * g = g * z := by
  have hc : z * g * z⁻¹ * g⁻¹ ∈ ⁅O, O⁆ := Subgroup.commutator_mem_commutator hzO hg
  have hconj : ∀ w ∈ ⁅O, O⁆, g⁻¹ * w * g ∈ ⁅O, O⁆ := fun w hw => by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator O (inv_mem hg)) w).mp hw
    rwa [inv_inv] at this
  have h1 := hZ _ hc fun w hw => by
    have h2 : Commute z (g⁻¹ * w * g) := hz _ (hconj w hw)
    have h3 : z⁻¹ * (g⁻¹ * w * g) = (g⁻¹ * w * g) * z⁻¹ := h2.inv_left
    calc z * g * z⁻¹ * g⁻¹ * w = z * g * (z⁻¹ * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = z * g * ((g⁻¹ * w * g) * z⁻¹) * g⁻¹ := by rw [h3]
      _ = (z * w) * g * z⁻¹ * g⁻¹ := by group
      _ = (w * z) * g * z⁻¹ * g⁻¹ := by rw [hz w hw]
      _ = w * (z * g * z⁻¹ * g⁻¹) := by group
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem not_comm_of_witnesses {O : Subgroup G} [IsSimpleGroup ↥(⁅O, O⁆ : Subgroup G)]
    (hidx : ⁅O, O⁆.relIndex O = 2) {x r s : G} (hx : x ∈ ⁅O, O⁆) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hrO : r ∈ O) (hsO : s ∈ O) (hr1 : r ≠ 1) (hr2 : r * r = 1) (hs1 : s ≠ 1) (hs2 : s * s = 1)
    (hrs : r * s = s * r) (hrs1 : r ≠ s) : ¬ ∀ a b : ↥(⁅O, O⁆ : Subgroup G), a * b = b * a := by
  intro hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho3 : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hmem2 : ∀ y ∈ ⁅O, O⁆, y ≠ 1 → y * y = 1 → False := by
    intro y hy hy1 hy2
    have h1 : orderOf (⟨y, hy⟩ : ↥(⁅O, O⁆ : Subgroup G)) =
        orderOf (⟨x, hx⟩ : ↥(⁅O, O⁆ : Subgroup G)) :=
      orderOf_eq_of_isSimpleGroup_of_comm hc (fun h => hy1 (congrArg Subtype.val h))
        (fun h => hx1 (congrArg Subtype.val h))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ho3,
      orderOf_eq_prime (p := 2) (by rw [_root_.sq]; exact hy2) hy1] at h1
    omega
  have hr : r ∉ ⁅O, O⁆ := fun h => hmem2 r h hr1 hr2
  have hs : s ∉ ⁅O, O⁆ := fun h => hmem2 s h hs1 hs2
  have hrsmem : r * s ∈ ⁅O, O⁆ := by
    have := (Subgroup.mul_mem_iff_of_index_two (H := ⁅O, O⁆.subgroupOf O) hidx
      (a := ⟨r, hrO⟩) (b := ⟨s, hsO⟩)).mpr
      (iff_of_false (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf]))
    rwa [Subgroup.mem_subgroupOf] at this
  refine hmem2 (r * s) hrsmem ?_ ?_
  · intro h
    apply hrs1
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hr2]
  · calc r * s * (r * s) = r * (s * r) * s := by group
      _ = r * (r * s) * s := by rw [hrs]
      _ = (r * r) * (s * s) := by group
      _ = 1 := by rw [hr2, hs2, one_mul]

end GroupTheory

theorem eq_one_of_commute_commutator_orthogonalGroup [FiniteDimensional (ZMod 2) V]
    (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0) (h3 : 3 ≤ finrank (ZMod 2) V)
    [IsSimpleGroup ↥(⁅TauCeti.QuadraticMap.orthogonalGroup q,
      TauCeti.QuadraticMap.orthogonalGroup q⁆ : Subgroup (V ≃ₗ[ZMod 2] V))]
    (hidx : ⁅TauCeti.QuadraticMap.orthogonalGroup q,
      TauCeti.QuadraticMap.orthogonalGroup q⁆.relIndex (TauCeti.QuadraticMap.orthogonalGroup q) = 2)
    {z : V ≃ₗ[ZMod 2] V} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hzc : ∀ w ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup q, TauCeti.QuadraticMap.orthogonalGroup q⁆,
      z * w = w * z) : z = 1 := by
  set O := TauCeti.QuadraticMap.orthogonalGroup q with hOdef
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨a, ha, -⟩ := exists_nonsingular_perp hnd h3 0
  obtain ⟨b, hb, hab⟩ := exists_nonsingular_polar_eq_one hnd h3 ha
  obtain ⟨c, hc, hac, hca⟩ := exists_nonsingular_perp_ne hnd h3 ha
  have hna : ¬ ∀ x y : ↥(⁅O, O⁆ : Subgroup (V ≃ₗ[ZMod 2] V)), x * y = y * x := by
    refine not_comm_of_witnesses (x := reflect q a * reflect q b) (r := reflect q a)
      (s := reflect q c) hidx ?_ ?_
      (CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_pow_three ha hb hab)
      (reflect_mem_orthogonalGroup q a) (reflect_mem_orthogonalGroup q c)
      (reflect_ne_one hnd ha) (reflect_mul_self q a) (reflect_ne_one hnd hc) (reflect_mul_self q c)
      (reflect_mul_comm ha hc hac) (fun h => hca (eq_of_reflect_eq hnd ha hc h).symm)
    · rw [CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_eq_commutator_sq ha hb hab]
      exact Subgroup.pow_mem _ (Subgroup.commutator_mem_commutator
        (reflect_mem_orthogonalGroup q a) (reflect_mem_orthogonalGroup q b)) 2
    · intro h
      have h' : reflect q b = reflect q a := by
        rw [← inv_eq_of_mul_eq_one_right h, CFSG.ClassicalGroups.Orthogonal.reflect_inv]
      have hba := eq_of_reflect_eq hnd hb ha h'
      rw [hba, polar_self_zmod2] at hab
      exact zero_ne_one hab
  refine eq_one_of_commute_reflect hnd h3 hz fun a' ha' => ?_
  exact commute_of_commute_commutator (fun c' hc' hcw => eq_one_of_forall_commute hna hc' hcw)
    hz hzc (reflect_mem_orthogonalGroup q a')

end OrthBasic

variable {Q : (ι → ZMod 2) → ZMod 2}

theorem GoodQ.kappa_injective (hQ : GoodQ Q) : Function.Injective (kappa Q) := by
  obtain ⟨q, hq, hnd⟩ := hQ.regular
  have h3 : 3 ≤ Module.finrank (ZMod 2) (ι → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card]
    have := hQ.card_ge
    omega
  have := hQ.simple
  have : IsSimpleGroup ↥(⁅TauCeti.QuadraticMap.orthogonalGroup q,
      TauCeti.QuadraticMap.orthogonalGroup q⁆ : Subgroup ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))) :=
    (statedOmegaEquivDerived hq).symm.isSimpleGroup
  have hidx := hQ.relIndex_eq
  rw [relIndex_statedOmega_eq hq] at hidx
  set e := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) with he
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgO : e g ∈ TauCeti.QuadraticMap.orthogonalGroup q := (isoGrp_eq_comap hq).le g.2
  have hcomm : ∀ w ∈ StatedOmega Q, (w : GL ι (ZMod 2)) * g = g * w := by
    intro w hw
    have h1 := kappa_apply_val Q g ⟨w, hw⟩
    rw [hg, MulAut.one_apply] at h1
    exact eq_mul_inv_iff_mul_eq.mp h1
  have heg : e g = 1 := by
    refine OrthBasic.eq_one_of_commute_commutator_orthogonalGroup hnd h3 hidx hgO fun y hy => ?_
    have hw : e.symm y ∈ StatedOmega Q := by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hq, Subgroup.mem_comap,
        MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hy
    have h2 := congrArg e (hcomm _ hw)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  exact Subtype.ext ((MulEquiv.map_eq_one_iff e).mp heg)

theorem kappa_eq_conj {g : isoGrp Q} (hg : (g : GL ι (ZMod 2)) ∈ StatedOmega Q) :
    kappa Q g = MulAut.conj (⟨g, hg⟩ : StatedOmega Q) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem inner_eq_map_kappa :
    inner ↥(StatedOmega Q) = ((StatedOmega Q).subgroupOf (isoGrp Q)).map (kappa Q) := by
  ext α
  rw [Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp h
    refine ⟨⟨w, statedOmega_le_isoGrp Q w.2⟩, Subgroup.mem_subgroupOf.mpr w.2, ?_⟩
    rw [← hw]
    exact MulEquiv.ext fun _ => Subtype.ext rfl
  · intro h
    obtain ⟨g, hg, hgα⟩ := h
    rw [Subgroup.mem_subgroupOf] at hg
    rw [← hgα, kappa_eq_conj hg]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem GoodQ.kappa_mem_inner_iff (hQ : GoodQ Q) (g : isoGrp Q) :
    kappa Q g ∈ inner ↥(StatedOmega Q) ↔ (g : GL ι (ZMod 2)) ∈ StatedOmega Q := by
  rw [inner_eq_map_kappa, Subgroup.mem_map_iff_mem hQ.kappa_injective, Subgroup.mem_subgroupOf]

theorem GoodQ.relIndex_inner_range_kappa (hQ : GoodQ Q) :
    (inner ↥(StatedOmega Q)).relIndex (kappa Q).range = 2 := by
  rw [inner_eq_map_kappa, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ hQ.kappa_injective, Subgroup.relIndex_top_right]
  exact hQ.relIndex_eq

theorem GoodQ.card_le_two_of_le_range (hQ : GoodQ Q) {T : Subgroup (MulAut ↥(StatedOmega Q))}
    (hT : T ≤ (kappa Q).range) (hTi : T ⊓ inner ↥(StatedOmega Q) = ⊥) : Nat.card T ≤ 2 := by
  have h1 : (inner ↥(StatedOmega Q)).relIndex T = Nat.card T := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hTi, Subgroup.relIndex_bot_left]
  have h2 := hQ.relIndex_inner_range_kappa
  have h3 := Subgroup.relIndex_le_of_le_right (H := inner ↥(StatedOmega Q)) hT (by omega)
  omega

theorem GoodQ.isoGrp_eq_sup (hQ : GoodQ Q) {g : GL ι (ZMod 2)} (hg : g ∈ isoGrp Q)
    (hgΩ : g ∉ StatedOmega Q) : StatedOmega Q ⊔ Subgroup.zpowers g = isoGrp Q := by
  set H := StatedOmega Q ⊔ Subgroup.zpowers g with hH
  have hΩH : StatedOmega Q ≤ H := le_sup_left
  have hHO : H ≤ isoGrp Q :=
    sup_le (statedOmega_le_isoGrp Q) ((Subgroup.zpowers_le).mpr hg)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hΩH hHO
  rw [hQ.relIndex_eq] at hmul
  have hne : (StatedOmega Q).relIndex H ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hgΩ (h (le_sup_right (a := StatedOmega Q) (Subgroup.mem_zpowers g)))
  have h2 : (StatedOmega Q).relIndex H = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hmul) with h | h
    · exact absurd h hne
    · exact h
  rw [h2] at hmul
  refine le_antisymm hHO ?_
  rw [← Subgroup.relIndex_eq_one]
  omega

end CFSG.LieType.ChevTwo
