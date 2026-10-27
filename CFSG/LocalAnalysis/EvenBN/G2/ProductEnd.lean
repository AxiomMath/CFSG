module

public import CFSG.LocalAnalysis.EvenBN.G2.EndgameBase
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseEndgame

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement Pointwise

section Orders

theorem ordG2_aux_x {q : ℕ} (hq : 2 ≤ q) : ∃ x : ℕ, q ^ 6 = x + 1 ∧ 0 < x := by
  have h1 : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  exact ⟨q ^ 6 - 1, by omega, by omega⟩

theorem ordG2_aux_y {q : ℕ} (hq : 2 ≤ q) : ∃ y : ℕ, q ^ 2 = y + 1 ∧ 0 < y := by
  have h1 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact ⟨q ^ 2 - 1, by omega, by omega⟩

theorem ordG2_eq_xy {q x y : ℕ} (hx : q ^ 6 = x + 1) (hy : q ^ 2 = y + 1) :
    ordG2 q = (x + 1) * x * y := by
  unfold ordG2
  rw [hx, hy]
  simp

theorem ordG2_sq_eq_xy {q x y : ℕ} (hx : q ^ 6 = x + 1) (hy : q ^ 2 = y + 1) :
    ordG2 (q ^ 2) = (x + 1) ^ 2 * (x * (x + 2)) * (y * (y + 2)) := by
  unfold ordG2
  have e1 : (q ^ 2) ^ 6 = (x + 1) ^ 2 := by
    rw [← pow_mul, mul_comm 2 6, pow_mul, hx]
  have e2 : (q ^ 2) ^ 2 = (y + 1) ^ 2 := by rw [hy]
  have e3 : (x + 1) ^ 2 - 1 = x * (x + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e4 : (y + 1) ^ 2 - 1 = y * (y + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, e3, e4]

theorem ordG2_sq_lt_ordG2_sq {q : ℕ} (hq : 2 ≤ q) : ordG2 q ^ 2 < ordG2 (q ^ 2) := by
  obtain ⟨x, hx, hxpos⟩ := ordG2_aux_x hq
  obtain ⟨y, hy, hypos⟩ := ordG2_aux_y hq
  rw [ordG2_eq_xy hx hy, ordG2_sq_eq_xy hx hy]
  calc ((x + 1) * x * y) ^ 2 = ((x + 1) ^ 2 * x * y) * (x * y) := by ring
    _ < ((x + 1) ^ 2 * x * y) * ((x + 2) * (y + 2)) :=
        Nat.mul_lt_mul_of_pos_left (by nlinarith) (by positivity)
    _ = (x + 1) ^ 2 * (x * (x + 2)) * (y * (y + 2)) := by ring

theorem ordG2_lt_two_mul_sq {q : ℕ} (hq : 2 ≤ q) : ordG2 (q ^ 2) < 2 * ordG2 q ^ 2 := by
  obtain ⟨x, hx, hxpos⟩ := ordG2_aux_x hq
  obtain ⟨y, hy, hypos⟩ := ordG2_aux_y hq
  rw [ordG2_eq_xy hx hy, ordG2_sq_eq_xy hx hy]
  have hx63 : 63 ≤ x := by
    have := Nat.pow_le_pow_left hq 6
    omega
  have hy3 : 3 ≤ y := by
    have := Nat.pow_le_pow_left hq 2
    omega
  calc (x + 1) ^ 2 * (x * (x + 2)) * (y * (y + 2))
      = ((x + 1) ^ 2 * x * y) * ((x + 2) * (y + 2)) := by ring
    _ < ((x + 1) ^ 2 * x * y) * (2 * (x * y)) :=
        Nat.mul_lt_mul_of_pos_left (by nlinarith) (by positivity)
    _ = 2 * ((x + 1) * x * y) ^ 2 := by ring

theorem not_sq_dvd_ordG2 {q : ℕ} (hq : 2 ≤ q) : ¬ ordG2 q ^ 2 ∣ ordG2 (q ^ 2) := by
  intro hdvd
  have d1 := ordG2_sq_lt_ordG2_sq hq
  have d2 := ordG2_lt_two_mul_sq hq
  have hne : ordG2 (q ^ 2) ≠ 0 := by omega
  have := Nat.eq_of_dvd_of_lt_two_mul hne hdvd d2
  omega

end Orders

section Generic

namespace ProductEndAux

theorem isSolvable_outer_of_commutator_mem_inner {M : Type*} [Group M]
    (h : ∀ α β : MulAut M, ⁅α, β⁆ ∈ inner M) : Group.IsSolvable (Outer M) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H α =>
    induction b using QuotientGroup.induction_on with
    | H β =>
      rw [← commutatorElement_eq_one_iff_mul_comm]
      change ⁅QuotientGroup.mk' (inner M) α, QuotientGroup.mk' (inner M) β⁆ = 1
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 (h α β)

theorem zpow_eq_one_or_eq_self {G : Type*} [Group G] {t : G} (htt : t * t = 1) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, htt, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, htt, one_zpow, one_mul, zpow_one]

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {H K : Subgroup G}
    (hE : IsElemAbelian 2 H) : IsElemAbelian 2 (H.subgroupOf K) := by
  obtain ⟨hc, hsq⟩ := hE
  have key : ∀ a b : ↥(H.subgroupOf K),
      (((a : K) : G)) * ((b : K) : G) = ((b : K) : G) * ((a : K) : G) := fun a b =>
    congrArg Subtype.val (mul_comm' (⟨((a : K) : G), mem_subgroupOf.1 a.2⟩ : H)
      ⟨((b : K) : G), mem_subgroupOf.1 b.2⟩)
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (key a b))⟩⟩, fun y hy => ?_⟩
  exact Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hsq _ (mem_subgroupOf.1 hy))

theorem charP_two_of_card_two_pow {k : Type} [Field k] [Finite k] {m : ℕ} (hm : m ≠ 0)
    (hk : Nat.card k = 2 ^ m) : CharP k 2 := by
  have : Fintype k := Fintype.ofFinite k
  have h : ((Fintype.card k : ℕ) : k) = 0 := FiniteField.cast_card_eq_zero k
  rw [← Nat.card_eq_fintype_card, hk, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (pow_eq_zero_iff hm |>.mp h)

end ProductEndAux

end Generic

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem G2Data.card_eq_ordG2 (d : G2Data L K) : Nat.card L = ordG2 (Nat.card K) := by
  rw [Nat.card_congr d.equiv.toEquiv]
  exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2

namespace ProductEndAux

theorem exists_isElemAbelian_of_mul_self {a : adjointGroup .G2 K} (ha : a * a = 1) :
    ∃ E : Subgroup (adjointGroup .G2 K), IsElemAbelian 2 E ∧ a ∈ E ∧
      Nat.card E = Nat.card K ^ 3 := by
  have ha' : (a : ModGL .G2 K) * a = 1 := congrArg Subtype.val ha
  have hE : CFSG.IsElementaryAbelian 2 (zpowers (a : ModGL .G2 K)) := by
    refine isElementaryAbelian_of_forall (fun _ hx _ hy => ?_) fun _ hx => ?_
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
      exact ((Commute.refl (a : ModGL .G2 K)).zpow_zpow m n).eq
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
      rw [← (Commute.refl (a : ModGL .G2 K)).mul_zpow, ha', one_zpow]
  obtain ⟨g, hg, hXW⟩ := Model.elementary_le_conj ((zpowers_le).2 a.2) hE
  have hmem : (a : ModGL .G2 K) ∈ zpowers (a : ModGL .G2 K) := mem_zpowers _
  have key : ∀ H : Subgroup (ModGL .G2 K), H ≤ adjointGroup .G2 K →
      CFSG.IsElementaryAbelian 2 H → Nat.card H = Nat.card K ^ 3 →
      zpowers (a : ModGL .G2 K) ≤ H.map (MulAut.conj g).toMonoidHom →
      ∃ E : Subgroup (adjointGroup .G2 K), IsElemAbelian 2 E ∧ a ∈ E ∧
        Nat.card E = Nat.card K ^ 3 := by
    intro H hHC hHE hHcard hle
    have hH'C : H.map (MulAut.conj g).toMonoidHom ≤ adjointGroup .G2 K := by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hg (hHC hx)) (inv_mem hg)
    refine ⟨(H.map (MulAut.conj g).toMonoidHom).subgroupOf (adjointGroup .G2 K),
      isElemAbelian_subgroupOf (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
        (isElementaryAbelian_map_conj hHE g)), mem_subgroupOf.2 (hle hmem), ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hH'C).toEquiv, card_map_conj, hHcard]
  rcases hXW with hX | hW
  · exact key _ Model.X_le_adjointGroup Model.X_isElementaryAbelian Model.card_X hX
  · exact key _ Model.W_le_adjointGroup Model.W_isElementaryAbelian Model.card_W hW

theorem fixedGroup_fieldAut_pow_mulEquiv {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ e ∧
      Nonempty (((Model.fieldAut K ^ e).toMonoidHom.eqLocus (MonoidHom.id _) :
        Subgroup (adjointGroup .G2 K)) ≃* adjointGroup .G2 k) := by
  set σ := frobeniusEquiv K 2 ^ e with hσ
  obtain ⟨-, hk, -, hfix, -⟩ :=
    even_G2_canonical_field_full_centralizer he K hK σ (frobeniusEquiv_pow_apply e)
  have hδ : Model.fieldAut K ^ e = entrywiseAdjointAut .G2 σ := Model.fieldAut_pow e
  set E₀ := (entrywiseAdjointAut .G2 σ).toMonoidHom.eqLocus
    (MonoidHom.id (adjointGroup .G2 K)) with hE₀
  have hEq : (Model.fieldAut K ^ e).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 K)) =
      E₀ := by rw [hδ]
  refine ⟨fixSubfield σ, inferInstance, hk, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hEq).trans
    ((E₀.equivMapOfInjective _ Subtype.val_injective).trans
      ((MulEquiv.subgroupCongr hfix).trans
        ((adjointGroup .G2 (fixSubfield σ)).equivMapOfInjective _
          (baseChangeGL_injective _)).symm))

theorem exists_fixedGroup_of_outer {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f)
    {β : MulAut (adjointGroup .G2 K)} (hβ2 : β * β = 1)
    (hβ : β ∉ inner (adjointGroup .G2 K)) :
    Even f ∧ ∃ D : Subgroup (adjointGroup .G2 K), (∀ g ∈ D, β g = g) ∧ ⁅D, D⁆ = D ∧
      Nat.card D = ordG2 (2 ^ (f / 2)) ∧
      ∃ E : Subgroup (adjointGroup .G2 K), E ≤ D ∧ IsElemAbelian 2 E ∧
        Nat.card E = (2 ^ (f / 2)) ^ 3 := by
  have hβ1 : β ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hβo : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  rcases even_G2_involution_inner_or_canonical_field (by omega : 2 ≤ f) K hK β hβo with
    h | ⟨hfe, -⟩
  · exact absurd h hβ
  obtain ⟨e, he⟩ := hfe
  have hf2 : f = 2 * e := by omega
  have hfe2 : f / 2 = e := by omega
  have he2 : 2 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := hf2 ▸ hK
  refine ⟨⟨e, he⟩, ?_⟩
  obtain ⟨w, -, hw⟩ := Model.exists_inner_conj_eq_of_outer hK' (by omega) hβo hβ
  obtain ⟨k, _, hk, ⟨ε⟩⟩ := fixedGroup_fieldAut_pow_mulEquiv hK' (by omega)
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : CharP k 2 := charP_two_of_card_two_pow (by omega) hk
  set Dg : Subgroup (adjointGroup .G2 K) := β.toMonoidHom.eqLocus (MonoidHom.id _) with hDg
  have hβg : ∀ g, β g = w⁻¹ ((Model.fieldAut K ^ e) (w g)) := fun g => by
    rw [hw, MulAut.mul_apply, MulAut.mul_apply]
  have hDgiff : ∀ g, g ∈ Dg ↔ (Model.fieldAut K ^ e) (w g) = w g := fun g => by
    change β g = g ↔ _
    rw [hβg g]
    constructor
    · intro h
      have := congrArg w h
      rwa [MulAut.apply_inv_self] at this
    · intro h
      rw [h, MulAut.inv_apply_self]
  have hmap : Dg.map w.toMonoidHom =
      (Model.fieldAut K ^ e).toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hDgiff g).1 hg
    · intro hy
      refine ⟨w⁻¹ y, (hDgiff _).2 ?_, by change w (w⁻¹ y) = y; rw [MulAut.apply_inv_self]⟩
      rw [MulAut.apply_inv_self]
      exact hy
  let εD : Dg ≃* adjointGroup .G2 k :=
    ((Dg.equivMapOfInjective w.toMonoidHom w.injective).trans
      (MulEquiv.subgroupCongr hmap)).trans ε
  have hk3 : 3 ≤ Nat.card k := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right two_pos he2
  have hDperf : Group.IsPerfect Dg := by
    have := CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card k hk3
    exact Group.IsPerfect.ofSurjective (f := εD.symm.toMonoidHom) εD.symm.surjective
  obtain ⟨Ek, hEk, -, hEkcard⟩ := exists_isElemAbelian_of_mul_self (K := k) (a := 1) (mul_one 1)
  refine ⟨Dg, fun g hg => hg, Subgroup.isPerfect_iff.1 hDperf, ?_,
    (Ek.map εD.symm.toMonoidHom).map Dg.subtype, map_subtype_le _,
    SectionRank.isElemAbelian_map (SectionRank.isElemAbelian_map hEk _) _, ?_⟩
  · rw [Nat.card_congr εD.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk,
      hfe2]
  · rw [card_map_of_injective Dg.subtype_injective, card_map_of_injective εD.symm.injective,
      hEkcard, hk, hfe2]

theorem inner_or_outer_aux {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f)
    {β : MulAut (adjointGroup .G2 K)} (hβ2 : β * β = 1) :
    (∃ E : Subgroup (adjointGroup .G2 K), IsElemAbelian 2 E ∧ Nat.card E = (2 ^ f) ^ 3 ∧
        ∀ g ∈ E, β g = g) ∨
      (Even f ∧ ∃ D : Subgroup (adjointGroup .G2 K), (∀ g ∈ D, β g = g) ∧ ⁅D, D⁆ = D ∧
        Nat.card D = ordG2 (2 ^ (f / 2)) ∧
        ∃ E : Subgroup (adjointGroup .G2 K), E ≤ D ∧ IsElemAbelian 2 E ∧
          Nat.card E = (2 ^ (f / 2)) ^ 3) := by
  by_cases hin : β ∈ inner (adjointGroup .G2 K)
  · left
    obtain ⟨a, rfl⟩ := hin
    have ha : a * a = 1 := Model.conj_injective (by rw [map_mul, hβ2, map_one])
    obtain ⟨E, hE, haE, hcard⟩ := exists_isElemAbelian_of_mul_self ha
    refine ⟨E, hE, by rw [hcard, hK], fun g hg => ?_⟩
    haveI := hE.1
    have hc : a * g = g * a := congrArg Subtype.val (mul_comm' (⟨a, haE⟩ : E) ⟨g, hg⟩)
    rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
  · exact Or.inr (exists_fixedGroup_of_outer hK hf hβ2 hin)

end ProductEndAux

namespace Setup

theorem perfect_le_sup_of_le_normalizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {G₀ : Subgroup G} (e : G₀ ≃* L) (hq : CFSG.Open.IsQuasisimple G₀)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hLG : L ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom) {H : Subgroup G}
    (hH : H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hp : ⁅H, H⁆ = H) : H ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set G₂ : Subgroup G := G₀.map (MulAut.conj t).toMonoidHom with hG₂
  obtain ⟨hperf, hbot, hn₁⟩ :=
    SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hn₂ := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hn₁
  have hcomm : ∀ a ∈ G₀, ∀ b ∈ G₂, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (h₁₂ hb) a ha
  have hne : G₀ ≠ G₂ := by
    intro e
    apply hbot
    have h11 : G₀ ≤ centralizer (G₀ : Set G) := by
      calc G₀ = G₂ := e
        _ ≤ centralizer (G₀ : Set G) := h₁₂
    rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h11]
  have hperm : ∀ x ∈ normalizer ((G₀ ⊔ G₂ : Subgroup G) : Set G),
      G₀.map (MulAut.conj x).toMonoidHom = G₀ ∨ G₀.map (MulAut.conj x).toMonoidHom = G₂ :=
    fun x hx => SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂ hperf hbot hn₁ hn₂ hx
  have hHN : H ≤ normalizer (G₀ : Set G) ⊓ normalizer (G₂ : Set G) := by
    have h2 := SeitzReduction.F4Pilot.relIndex_inf_normalizer_eq_two_of_swap htt rfl hne hperm
    rw [← SeitzReduction.F4Pilot.inf_normalizer_eq_of_swap htt rfl hne hperm]
    calc H = ⁅H, H⁆ := hp.symm
      _ ≤ _ := (commutator_mono hH hH).trans
        (TrialityD4.PerfectLeSup.commutator_le_of_relIndex_eq_two h2)
  haveI hsolvM : Group.IsSolvable (Outer (adjointGroup .G2 K)) :=
    ProductEndAux.isSolvable_outer_of_commutator_mem_inner fun α β =>
      Model.commutatorElement_mem_inner hK h.two_le α β
  haveI hsolvL : Group.IsSolvable (Outer L) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv d.equiv.symm
  haveI hsolv₀ : Group.IsSolvable (Outer G₀) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  let e₂ : G₀ ≃* G₂ := Subgroup.equivMapOfInjective G₀ _ (MulAut.conj t).injective
  haveI hsolv₂ : Group.IsSolvable (Outer G₂) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e₂
  set C₀ : Subgroup G := centralizer (G₀ : Set G) ⊓ centralizer (G₂ : Set G) with hC₀
  have hmemG₂ : ∀ a ∈ G₀, t * a * t⁻¹ ∈ G₂ := fun a ha => ⟨a, ha, rfl⟩
  have hmemG₀ : ∀ b ∈ G₂, t⁻¹ * b * t ∈ G₀ := by
    rintro _ ⟨a, ha, rfl⟩
    change t⁻¹ * (t * a * t⁻¹) * t ∈ G₀
    rw [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
    exact ha
  have htC₀ : t ∈ normalizer (C₀ : Set G) := by
    refine mem_normalizer_fintype fun c hc => ?_
    have hc₁ := (mem_inf.1 hc).1
    have hc₂ := (mem_inf.1 hc).2
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, mem_centralizer_iff.2 fun b hb => ?_⟩
    · have hat : t⁻¹ * a * t ∈ G₂ := by
        rw [show t⁻¹ * a * t = t * a * t⁻¹ by rw [htinv]]
        exact hmemG₂ a ha
      have := mem_centralizer_iff.1 hc₂ _ hat
      calc a * (t * c * t⁻¹) = t * ((t⁻¹ * a * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * a * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * a := by group
    · have hbt := hmemG₀ b hb
      have := mem_centralizer_iff.1 hc₁ _ hbt
      calc b * (t * c * t⁻¹) = t * ((t⁻¹ * b * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * b * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * b := by group
  have htG₀ : t ∉ centralizer (G₀ : Set G) := by
    intro ht
    apply hne
    refine le_antisymm (fun a ha => ?_) ?_
    · have e : t * a * t⁻¹ = a := by
        rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact e ▸ hmemG₂ a ha
    · rintro _ ⟨a, ha, rfl⟩
      change t * a * t⁻¹ ∈ G₀
      rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact ha
  have hC₀t : C₀ ⊓ centralizer ({t} : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC₀, hct⟩ := mem_inf.1 hc
    have hcL : c ∈ centralizer (L : Set G) := by
      refine mem_centralizer_iff.2 fun l hl => ?_
      have hle : G₀ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).1 a ha))
        (fun b hb => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).2 b hb))
      exact mem_centralizer_singleton_iff.1 (hle (hLG hl))
    have hk : c ∈ zpowers t := h.centralizer_L_inf.le (mem_inf.2 ⟨hcL, hct⟩)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hk
    rcases ProductEndAux.zpow_eq_one_or_eq_self htt k with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hcC₀
      exact absurd (mem_inf.1 hcC₀).1 htG₀
  have hab := TrialityD4.PerfectLeSup.mul_comm_of_inf_centralizer_eq_bot htC₀ htt hC₀t
  have hdec : ∀ x ∈ H, ∃ g ∈ G₀ ⊔ G₂, ∃ c ∈ C₀, x = g * c := by
    intro x hx
    obtain ⟨a₁, ha₁, c₁, hc₁, e₁⟩ :=
      TrialityD4.PerfectLeSup.exists_mul_centralizer_of_perfect (X := G₀) hp
        (hHN.trans inf_le_left) hx
    obtain ⟨a₂, ha₂, c₂, hc₂, e₂⟩ :=
      TrialityD4.PerfectLeSup.exists_mul_centralizer_of_perfect (X := G₂) hp
        (hHN.trans inf_le_right) hx
    have h12 : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁ a₂ ha₂
    refine ⟨a₁ * a₂, mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂), (a₁ * a₂)⁻¹ * x,
      mem_inf.2 ⟨?_, ?_⟩, by group⟩
    · have e : (a₁ * a₂)⁻¹ * x = a₂⁻¹ * c₁ := by rw [e₁]; group
      rw [e]
      exact mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => hcomm g hg a₂ ha₂)) hc₁
    · have e : (a₁ * a₂)⁻¹ * x = a₁⁻¹ * c₂ := by rw [h12, e₂]; group
      rw [e]
      exact mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => (hcomm a₁ ha₁ g hg).symm)) hc₂
  have hcen : ∀ c ∈ C₀, ∀ g ∈ G₀ ⊔ G₂, c * g = g * c := by
    intro c hc g hg
    have hle : G₀ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).1 a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).2 b hb))
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm
  calc H = ⁅H, H⁆ := hp.symm
    _ ≤ G₀ ⊔ G₂ := by
      rw [commutator_le]
      intro x hx y hy
      obtain ⟨g, hg, c, hc, rfl⟩ := hdec x hx
      obtain ⟨g', hg', c', hc', rfl⟩ := hdec y hy
      rw [commutatorElement_mul_mul_of_commute (hcen c hc g' hg') (hab c hc c' hc')
        (hcen c' hc' g hg), commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')

theorem inner_or_outer_G2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {X : Subgroup G} (e : L ≃* X) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) :
    (∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ IsElemAbelian 2 E ∧
        Nat.card E = (2 ^ f) ^ 3) ∨
      (Even f ∧ ∃ D : Subgroup G, D ≤ X ∧ D ≤ centralizer ({x} : Set G) ∧ ⁅D, D⁆ = D ∧
        Nat.card D = ordG2 (2 ^ (f / 2)) ∧
        ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian 2 E ∧ Nat.card E = (2 ^ (f / 2)) ^ 3) := by
  classical
  have hf3 : 3 ≤ f := by
    have h8' : 8 ≤ 2 ^ f := hK ▸ h8
    by_contra hlt
    have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨α, hαg⟩ : ∃ α : MulAut X, ∀ a : X, ((α a : X) : G) = x * a * x⁻¹ :=
    ⟨X.normalizerMonoidHom ⟨x, hxX⟩, fun a => rfl⟩
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    change ((α (α a) : X) : G) = ((a : X) : G)
    rw [hαg, hαg]
    calc x * (x * (a : G) * x⁻¹) * x⁻¹ = (x * x) * (a : G) * (x * x)⁻¹ := by group
      _ = a := by rw [hx2, inv_one, one_mul, mul_one]
  let ψ : X ≃* adjointGroup .G2 K := e.symm.trans d.equiv
  let φ : adjointGroup .G2 K →* G := X.subtype.comp ψ.symm.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp ψ.symm.injective
  let β : MulAut (adjointGroup .G2 K) := MulAut.congr ψ α
  have hβ2 : β * β = 1 := by rw [← map_mul, hα2, map_one]
  have hβφ : ∀ g, φ (β g) = x * φ g * x⁻¹ := fun g => by
    change ((ψ.symm (ψ (α (ψ.symm g))) : X) : G) = x * ((ψ.symm g : X) : G) * x⁻¹
    rw [MulEquiv.symm_apply_apply, hαg]
  have hmapX : ∀ S : Subgroup (adjointGroup .G2 K), S.map φ ≤ X := by
    rintro S _ ⟨g, -, rfl⟩
    exact (ψ.symm g).2
  have hmapC : ∀ S : Subgroup (adjointGroup .G2 K), (∀ g ∈ S, β g = g) →
      S.map φ ≤ centralizer ({x} : Set G) := by
    rintro S hS _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : x * φ g * x⁻¹ = φ g := by rw [← hβφ, hS g hg]
    calc φ g * x = (x * φ g * x⁻¹) * x := by rw [h1]
      _ = x * φ g := by group
  rcases ProductEndAux.inner_or_outer_aux hK hf3 hβ2 with
    ⟨E₀, hE₀, hcard, hfix⟩ | ⟨hfe, D₀, hfixD, hperf, hcardD, E₀, hED, hE₀, hcardE⟩
  · refine Or.inl ⟨E₀.map φ, hmapX E₀, hmapC E₀ hfix, SectionRank.isElemAbelian_map hE₀ φ, ?_⟩
    rw [card_map_of_injective hφinj, hcard]
  · refine Or.inr ⟨hfe, D₀.map φ, hmapX D₀, hmapC D₀ hfixD, ?_, ?_, E₀.map φ, map_mono hED,
      SectionRank.isElemAbelian_map hE₀ φ, ?_⟩
    · rw [← map_commutator, hperf]
    · rw [card_map_of_injective hφinj, hcardD]
    · rw [card_map_of_injective hφinj, hcardE]

theorem false_of_normalizes_both (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {G₀ : Subgroup G} (e : G₀ ≃* L)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G)) (g : G)
    (h₁ : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (h₂ : t ∈ normalizer (((G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom :
      Subgroup G) : Set G)) : False := by
  have htt := h.t_mul_t
  have h8' : 8 ≤ 2 ^ f := hK ▸ h8
  have hf3 : 3 ≤ f := by
    by_contra hlt
    have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set X₁ : Subgroup G := G₀.map (MulAut.conj g).toMonoidHom with hX₁
  set X₂ : Subgroup G :=
    (G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom with hX₂
  let e₁ : L ≃* X₁ := e.symm.trans
    (G₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  let e₂ : L ≃* X₂ := e.symm.trans
    ((G₀.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      ((G₀.map (MulAut.conj t).toMonoidHom).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective))
  have hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hab := mem_centralizer_iff.1 (h₁₂ ⟨b, hb, rfl⟩) a ha
    change (MulAut.conj g) a * (MulAut.conj g) ((MulAut.conj t) b) =
      (MulAut.conj g) ((MulAut.conj t) b) * (MulAut.conj g) a
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g) hab
  have hinf : X₁ ⊓ X₂ = ⊥ := by
    refine le_bot_iff.1 fun z hz => ?_
    have hzc : (e₁.symm ⟨z, hz.1⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      apply e₁.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hcomm _ (e₁ l).2 z hz.2)
    rw [h.center_eq, mem_bot] at hzc
    have hz1 : (⟨z, hz.1⟩ : X₁) = 1 := by
      have := congrArg e₁ hzc
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact mem_bot.2 (congrArg Subtype.val hz1)
  have key : ∀ E₁ E₂ : Subgroup G, E₁ ≤ X₁ → E₂ ≤ X₂ → E₁ ≤ centralizer ({t} : Set G) →
      E₂ ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E₁ → IsElemAbelian 2 E₂ →
      2 * (2 ^ f) ^ 3 < Nat.card E₁ * Nat.card E₂ → False := by
    intro E₁ E₂ hE₁ hE₂ hE₁t hE₂t hE₁a hE₂a hlt
    have hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
      hcomm a (hE₁ ha) b (hE₂ hb)
    have hEinf : E₁ ⊓ E₂ = ⊥ := by
      refine le_bot_iff.1 fun z hz => ?_
      have : z ∈ X₁ ⊓ X₂ := ⟨hE₁ hz.1, hE₂ hz.2⟩
      rwa [hinf] at this
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc
    rw [hEinf, Subgroup.card_bot, mul_one] at hcard
    have hEt : E₂ ≤ centralizer (E₁ : Set G) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hc a ha b hb
    have : CFSG.IsElementaryAbelian 2 E₁ := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE₁a
    have : CFSG.IsElementaryAbelian 2 E₂ := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE₂a
    have hEE : IsElemAbelian 2 (E₁ ⊔ E₂ : Subgroup G) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
        (CFSG.IsElementaryAbelian.sup_of_le_centralizer hEt)
    obtain ⟨hb1, hb2⟩ := h.card_le_of_isElemAbelian d hK (sup_le hE₁t hE₂t) hEE
    rw [hK] at hb2
    have hle := hb1.trans (Nat.mul_le_mul_left 2 hb2)
    rw [hcard] at hle
    exact absurd hlt (not_lt.2 hle)
  have hq3 : 2 * (2 ^ f) ^ 3 < (2 ^ f) ^ 3 * (2 ^ f) ^ 3 := by
    have ha : 3 ≤ (2 ^ f) ^ 3 := by
      calc 3 ≤ 8 ^ 3 := by norm_num
        _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h8' 3
    nlinarith
  have hApos : 0 < (2 ^ f) ^ 3 := by positivity
  have hmixed : Even f → 2 * (2 ^ f) ^ 3 < (2 ^ f) ^ 3 * (2 ^ (f / 2)) ^ 3 := by
    intro hfe
    have hf2 : 1 ≤ f / 2 := by
      obtain ⟨k, hk⟩ := hfe
      omega
    have h2 : 2 < (2 ^ (f / 2)) ^ 3 := by
      have h2' : 2 ≤ 2 ^ (f / 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) hf2
      calc 2 < 2 ^ 3 := by norm_num
        _ ≤ (2 ^ (f / 2)) ^ 3 := Nat.pow_le_pow_left h2' 3
    calc 2 * (2 ^ f) ^ 3 = (2 ^ f) ^ 3 * 2 := by ring
      _ < (2 ^ f) ^ 3 * (2 ^ (f / 2)) ^ 3 := Nat.mul_lt_mul_of_pos_left h2 hApos
  rcases h.inner_or_outer_G2 d hK h8 e₁ h₁ htt with
      ⟨E₁, hE₁X, hE₁t, hE₁a, hE₁c⟩ |
        ⟨hfe, D₁, hD₁X, hD₁t, hD₁p, hD₁c, E₁, hE₁D, hE₁a, hE₁c⟩ <;>
    rcases h.inner_or_outer_G2 d hK h8 e₂ h₂ htt with
      ⟨E₂, hE₂X, hE₂t, hE₂a, hE₂c⟩ |
        ⟨hfe', D₂, hD₂X, hD₂t, hD₂p, hD₂c, E₂, hE₂D, hE₂a, hE₂c⟩
  · exact key E₁ E₂ hE₁X hE₂X hE₁t hE₂t hE₁a hE₂a (by rw [hE₁c, hE₂c]; exact hq3)
  · refine key E₁ E₂ hE₁X (hE₂D.trans hD₂X) hE₁t (hE₂D.trans hD₂t) hE₁a hE₂a ?_
    rw [hE₁c, hE₂c]
    exact hmixed hfe'
  · refine key E₁ E₂ (hE₁D.trans hD₁X) hE₂X (hE₁D.trans hD₁t) hE₂t hE₁a hE₂a ?_
    rw [hE₁c, hE₂c]
    have := hmixed hfe
    linarith [mul_comm ((2 ^ f) ^ 3) ((2 ^ (f / 2)) ^ 3)]
  ·
    have hc : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
      hcomm a (hD₁X ha) b (hD₂X hb)
    have hDinf : D₁ ⊓ D₂ = ⊥ := by
      refine le_bot_iff.1 fun z hz => ?_
      have : z ∈ X₁ ⊓ X₂ := ⟨hD₁X hz.1, hD₂X hz.2⟩
      rwa [hinf] at this
    have hperf : ⁅D₁ ⊔ D₂, D₁ ⊔ D₂⁆ = D₁ ⊔ D₂ :=
      le_antisymm (commutator_le_self _)
        (sup_le (hD₁p.ge.trans (commutator_mono le_sup_left le_sup_left))
          (hD₂p.ge.trans (commutator_mono le_sup_right le_sup_right)))
    have hsub : D₁ ⊔ D₂ ≤ L := h.perfect_le hperf (sup_le hD₁t hD₂t)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc
    rw [hDinf, Subgroup.card_bot, mul_one, hD₁c, hD₂c] at hcard
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [hcard] at hdvd
    have hf2 : 2 ≤ 2 ^ (f / 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨k, hk⟩ := hfe; omega)
    have hq2 : (2 ^ (f / 2)) ^ 2 = 2 ^ f := by
      rw [← pow_mul]
      obtain ⟨k, hk⟩ := hfe
      congr 1
      omega
    refine not_sq_dvd_ordG2 hf2 ?_
    rw [hq2, sq]
    rw [d.card_eq_ordG2, hK] at hdvd
    exact hdvd

theorem false_of_productConfig (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {G₀ : Subgroup G}
    (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) [Group.IsPerfect G₀]
    (hL : (Common.diagonalHom G₀ t hcomm).range = L)
    (hN : normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G)) : False := by
  have := h.simple
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨-, e, -⟩ := h.yamada_7_20 hcomm hL
  haveI hLq : IsSimpleGroup (L ⧸ center L) := h.std.1.2
  have hLs : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq h.center_eq).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne_mul_of_mem_L
    exact hxy (hc x hx y hy)
  have hLeven : Even (Nat.card L) := by
    rw [d.card_eq_ordG2, hK]
    unfold ordG2
    have h2 : Even ((2 ^ f) ^ 6) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := h.two_le; omega⟩, by norm_num⟩
    exact (h2.mul_right _).mul_right _
  have hZ0 : center G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxe : e x ∈ center L := by
      rw [mem_center_iff]
      intro l
      obtain ⟨a, rfl⟩ := e.surjective l
      rw [← map_mul, ← map_mul, mem_center_iff.1 hx a]
    rw [h.center_eq, mem_bot] at hxe
    exact mem_bot.2 (e.injective (by rw [hxe, map_one]))
  have hZ : Odd (Nat.card (center G₀)) := by
    rw [hZ0, Subgroup.card_bot]
    exact odd_one
  have hq : CFSG.Open.IsQuasisimple G₀ := by
    refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
    exact (((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).trans
      e).symm.symm.isSimpleGroup
  have h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G) := by
    have h1 : G₀.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (G₀ : Set G) := by
      rw [commutator_comm] at hcomm
      exact commutator_eq_bot_iff_le_centralizer.1 hcomm
    rwa [htinv] at h1
  have hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L := by
    intro x hx
    rw [← hL]
    exact ⟨⟨x, hx⟩, by rw [Common.diagonalHom_apply, htinv]⟩
  have hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y := by
    intro y hy
    rw [← hL] at hy
    obtain ⟨⟨x, hx⟩, hxy⟩ := hy
    refine ⟨x, hx, ?_⟩
    rw [← hxy, Common.diagonalHom_apply, htinv]
  have hLG : L ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  have hR : IsSylowOf 2 (yamadaR d t) (L ⊔ zpowers t) := by
    have := h.isSylowOf_yamadaR d
    rwa [h.centralizer_L_inf] at this
  have hNR : normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    simpa only [htinv] using hN
  exact Common.false_of_swap_configuration h.ht hLs hLab hLeven h.L_le_centralizer
    (fun H hH hp => h.perfect_le hp hH) hq hZ h₁₂ hδ hsurj hR hNR
    (fun H hH hp => h.perfect_le_sup_of_le_normalizer d hK e hq h₁₂ hLG hH hp)
    (fun g h₁ h₂ => h.false_of_normalizes_both d hK h8 e h₁₂ g h₁ h₂)

end Setup

end Local

end CFSG.LocalAnalysis.EvenBN.G2
