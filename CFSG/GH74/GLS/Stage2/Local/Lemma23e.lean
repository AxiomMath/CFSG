module

public import CFSG.GH74.GLS.Stage2.Local.Lemma23
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Reduction

variable {G : Type} [Group G]

theorem commutator_Cen_le (z : G) {U : Subgroup G} (hU : U ≤ Cen z) : ⁅Cen z, U⁆ ≤ Cen z :=
  Subgroup.commutator_le_of_le le_rfl hU

theorem normal_commutator_Cen (z : G) {U : Subgroup G} (hU : U ≤ Cen z) :
    (⁅Cen z, U⁆.subgroupOf (Cen z)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (commutator_Cen_le z hU)).mpr
    (Subgroup.normalizer_commutator_ge_left (Cen z) U)

theorem commutator_top_le_barOf (z : G) {U : Subgroup G} :
    ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ ≤ barOf z ⁅Cen z, U⁆ := by
  refine Subgroup.commutator_le.mpr fun x _ y hy => ?_
  obtain ⟨c, rfl⟩ := toBar_surjective z x
  obtain ⟨⟨u, huC⟩, hu, rfl⟩ := hy
  refine ⟨⁅c, ⟨u, huC⟩⁆, ?_, map_commutatorElement _ _ _⟩
  refine Subgroup.mem_subgroupOf.mpr ?_
  have : ((⁅c, (⟨u, huC⟩ : ↥(Cen z))⁆ : ↥(Cen z)) : G) = ⁅(c : G), u⁆ := by
    simp [commutatorElement_def]
  rw [this]
  exact Subgroup.commutator_mem_commutator c.2 (Subgroup.mem_subgroupOf.mp hu)

theorem le_commutator_of_barOf_le [Finite G] (z : G) {U : Subgroup G} (hU : U ≤ Cen z)
    (hU2 : ∀ u ∈ U, ∃ a : ℕ, orderOf u = 2 ^ a) (h : barOf z U ≤ barOf z ⁅Cen z, U⁆) :
    U ≤ ⁅Cen z, U⁆ := by
  intro u hu
  have huC : u ∈ Cen z := hU hu
  have := normal_commutator_Cen z hU
  have hmem : toBar z ⟨u, huC⟩ ∈ barOf z ⁅Cen z, U⁆ := h ⟨⟨u, huC⟩, hu, rfl⟩
  have := mem_of_twoElt_of_map_mem (toBar z) (⁅Cen z, U⁆.subgroupOf (Cen z)) (x := ⟨u, huC⟩)
    (by rw [Subgroup.orderOf_mk]; exact hU2 u hu) (odd_card_ker_toBar z) hmem
  exact Subgroup.mem_subgroupOf.mp this

theorem LC_le_commutator_sup_of_LBar_le (z : G) {U : Subgroup G}
    (h : LBar z ≤ barOf z ⁅Cen z, U⁆) : LC z ≤ ⁅Cen z, U⁆ ⊔ OddCore z := by
  intro l hl
  have hlC : l ∈ Cen z := LC_le_Cen z hl
  have hmem : toBar z ⟨l, hlC⟩ ∈ barOf z ⁅Cen z, U⁆ := h ⟨⟨l, hlC⟩, hl, rfl⟩
  obtain ⟨n, hn, hnl⟩ := hmem
  have hker : n⁻¹ * ⟨l, hlC⟩ ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
  rw [ker_toBar] at hker
  have hodd : ((n⁻¹ * ⟨l, hlC⟩ : ↥(Cen z)) : G) ∈ OddCore z := ⟨_, hker, rfl⟩
  have hl' : l = (n : G) * ((n⁻¹ * ⟨l, hlC⟩ : ↥(Cen z)) : G) := by simp
  rw [hl']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hn) hodd

end Reduction

section Core

variable {Y : Type} [Group Y]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup Y} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : Y} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let T : Subgroup Y :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have : b * a' = a' * b := (hc a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have : a * b = b * a := hc a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [this]
          _ = a⁻¹ * b⁻¹ := by group }
  have hA : A ≤ T := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hB : B ≤ T := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact (sup_le hA hB) hx

theorem exists_two_involutions_of_isFour {U : Subgroup Y} (hU : IVK.IsFourSubgroup U) :
    ∃ x ∈ U, ∃ y ∈ U, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 ↥U := hU.1
  have hord : ∀ x ∈ U, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU.2]; norm_num)
  have h3 : 2 < Nat.card ↥U := by rw [hU.2]; norm_num
  have : Fintype ↥U := Fintype.ofFinite _
  have h3' : 2 < Fintype.card ↥U := by rw [← Nat.card_eq_fintype_card]; exact h3
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3'
  by_cases ha : (a : Y) = 1
  · have hb : (b : Y) ≠ 1 := fun h => hab (Subtype.ext (ha.trans h.symm))
    have hc : (c : Y) ≠ 1 := fun h => hac (Subtype.ext (ha.trans h.symm))
    exact ⟨b, b.2, c, c.2, hord b b.2 hb, hord c c.2 hc, fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : (b : Y) = 1
    · have hc : (c : Y) ≠ 1 := fun h => hbc (Subtype.ext (hb.trans h.symm))
      exact ⟨a, a.2, c, c.2, hord a a.2 ha, hord c c.2 hc, fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, hord a a.2 ha, hord b b.2 hb, fun h => hab (Subtype.ext h)⟩

theorem normal_commutator_top (U : Subgroup Y) : (⁅(⊤ : Subgroup Y), U⁆).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ normalizer ((⁅(⊤ : Subgroup Y), U⁆ : Subgroup Y) : Set Y) :=
    Subgroup.normalizer_commutator_ge_left (⊤ : Subgroup Y) U (Subgroup.mem_top g)
  exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn

theorem mem_center_of_commutators_central {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) {a : Q}
    (h : ∀ g : Q, ⁅g, a⁆ ∈ center Q) : a ∈ center Q := by
  have hbot := CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hq
  have hc : (QuotientGroup.mk a : Q ⧸ center Q) ∈ center (Q ⧸ center Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have e : (g * a)⁻¹ * (a * g) = a⁻¹ * ⁅g⁻¹, a⁆ * (a⁻¹)⁻¹ := by
      simp [commutatorElement_def]; group
    rw [e]
    exact (inferInstance : (center Q).Normal).conj_mem _ (h g⁻¹) a⁻¹
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact hc

theorem le_commutator_top_of_two_comps {L₁ L₂ U : Subgroup Y}
    (hq₁ : CFSG.IsQuasisimple ↥L₁)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ₁ : ∀ a ∈ L₁, (∀ c ∈ L₁, c * a = a * c) → a ∈ L₂)
    (hinv₂ : ∀ x ∈ L₂, ∀ y ∈ L₂, orderOf x = 2 → orderOf y = 2 → x = y)
    (hU : IVK.IsFourSubgroup U) (hUle : U ≤ L₁ ⊔ L₂) : L₁ ≤ ⁅(⊤ : Subgroup Y), U⁆ := by
  have hstep : ∃ u ∈ U, ∃ a ∈ L₁, ∃ b ∈ L₂, u = a * b ∧ ∃ c ∈ L₁, c * a ≠ a * c := by
    by_contra hcon
    have hUL₂ : U ≤ L₂ := by
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hUle hu)
      have hcen : ∀ c ∈ L₁, c * a = a * c := by
        intro c hc
        by_contra hne
        exact hcon ⟨a * b, hu, a, ha, b, hb, rfl, c, hc, hne⟩
      exact L₂.mul_mem (hZ₁ a ha hcen) hb
    obtain ⟨x, hx, y, hy, hx2, hy2, hxy⟩ := exists_two_involutions_of_isFour hU
    exact hxy (hinv₂ x (hUL₂ hx) y (hUL₂ hy) hx2 hy2)
  obtain ⟨u, hu, a, ha, b, hb, rfl, c₀, hc₀, hne⟩ := hstep
  have hN := normal_commutator_top U
  have hga : ∀ g ∈ L₁, ⁅g, a⁆ ∈ ⁅(⊤ : Subgroup Y), U⁆ := by
    intro g hg
    have h1 : ⁅g, a * b⁆ ∈ ⁅(⊤ : Subgroup Y), U⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hu
    have hc : Commute g b := hcomm g hg b hb
    have e : ⁅g, a * b⁆ = ⁅g, a⁆ := by
      calc ⁅g, a * b⁆ = g * a * (b * g⁻¹) * b⁻¹ * a⁻¹ := by simp [commutatorElement_def]; group
        _ = g * a * (g⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [← hc.inv_left.eq]
        _ = ⁅g, a⁆ := by simp [commutatorElement_def]; group
    rwa [e] at h1
  have : ((⁅(⊤ : Subgroup Y), U⁆).subgroupOf L₁).Normal := hN.subgroupOf L₁
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq₁
    ((⁅(⊤ : Subgroup Y), U⁆).subgroupOf L₁) with hle | htop
  · exfalso
    have hcen : (⟨a, ha⟩ : ↥L₁) ∈ center ↥L₁ := by
      apply mem_center_of_commutators_central hq₁
      intro g
      apply hle
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : ((⁅g, (⟨a, ha⟩ : ↥L₁)⁆ : ↥L₁) : Y) = ⁅(g : Y), a⁆ := by simp [commutatorElement_def]
      rw [this]
      exact hga g.1 g.2
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨c₀, hc₀⟩)
    exact hne this
  · intro x hx
    have : (⟨x, hx⟩ : ↥L₁) ∈ (⁅(⊤ : Subgroup Y), U⁆).subgroupOf L₁ := by
      rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem commutator_top_eq_top_of_isFour {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hZ : Nat.card (center Q) = 2) {U : Subgroup Q} (hU : IVK.IsFourSubgroup U) :
    ⁅(⊤ : Subgroup Q), U⁆ = ⊤ := by
  have hN := normal_commutator_top U
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
    (⁅(⊤ : Subgroup Q), U⁆) with hle | htop
  · exfalso
    have hUc : U ≤ center Q := fun u hu =>
      mem_center_of_commutators_central hq
        (fun g => hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hu))
    have : Finite (center Q) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    have := Subgroup.card_le_of_le hUc
    rw [hU.2, hZ] at this
    omega
  · exact htop

end Core


section SL2Facts

open Matrix

variable {F : Type} [Field F]

theorem mem_center_SL2_iff' {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ A.val = 1 ∨ A.val = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    rcases sq_eq_one_iff.1 hr with rfl | rfl
    · left
      rw [← hA, map_one]
    · right
      rw [← hA, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, one_pow 2, by rw [map_one]; exact h.symm⟩
    · exact ⟨-1, by norm_num, by rw [map_neg, map_one]; exact h.symm⟩

theorem card_center_SL2_eq_two' (hF : ringChar F ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = 2 := by
  have hne : (1 : SpecialLinearGroup (Fin 2) F) ≠ -1 := by
    intro h
    have h00 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 0) h
    change (1 : Matrix (Fin 2) (Fin 2) F) 0 0 = -((1 : Matrix (Fin 2) (Fin 2) F) 0 0) at h00
    rw [Matrix.one_apply_eq] at h00
    exact Ring.neg_one_ne_one_of_char_ne_two hF h00.symm
  have hset : ((Subgroup.center (SpecialLinearGroup (Fin 2) F) :
      Set (SpecialLinearGroup (Fin 2) F))) = {1, -1} := by
    ext A
    rw [SetLike.mem_coe, mem_center_SL2_iff', Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_congr (Subtype.ext_iff (a1 := A) (a2 := (1 : SpecialLinearGroup (Fin 2) F))).symm
      (Subtype.ext_iff (a1 := A) (a2 := (-1 : SpecialLinearGroup (Fin 2) F))).symm
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]

theorem isQuasisimple_of_perfect_simple' {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨Group.isPerfect_def.mpr hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right,
      mul_inv_cancel]
  rw [hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem isQuasisimple_sl2'' [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F) :=
  isQuasisimple_of_perfect_simple'
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4).commutator_eq_top
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)

theorem SL2_unique_involution (hF : ringChar F ≠ 2) {A B : SpecialLinearGroup (Fin 2) F}
    (hA : orderOf A = 2) (hB : orderOf B = 2) : A = B := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have key : ∀ X : SpecialLinearGroup (Fin 2) F, orderOf X = 2 → (X : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro X hX
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 X ?_ ?_
    · have h := pow_orderOf_eq_one X
      rw [hX] at h
      exact h
    · intro h1
      rw [h1, orderOf_one] at hX
      exact absurd hX (by norm_num)
  exact Subtype.ext ((key A hA).trans (key B hB).symm)

theorem sl2_model_center_inv {Y : Type} [Group Y] {L : Subgroup Y} {q : ℕ} (hodd : Odd q)
    (h : HasSL2Model ↥L (fun r => r = q)) :
    Nat.card (center ↥L) = 2 ∧
      ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x = y := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = q := hq
  let e' : ↥L ≃* SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hchar : ringChar F ≠ 2 := by
    intro h2
    have : Fintype F := Fintype.ofFinite F
    have h3 := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card, hq'] at h3
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨?_, ?_⟩
  · have hc : (center ↥L).map (e' : ↥L →* SpecialLinearGroup (Fin 2) F) =
        center (SpecialLinearGroup (Fin 2) F) := Subgroup.map_center_eq e'
    rw [← card_center_SL2_eq_two' hchar, ← hc, Subgroup.card_map_of_injective e'.injective]
  · intro x hx y hy hx2 hy2
    have := SL2_unique_involution hchar (A := e' ⟨x, hx⟩) (B := e' ⟨y, hy⟩)
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hx2)
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hy2)
    exact congrArg Subtype.val (e'.injective this)

theorem sl2_model_facts {Y : Type} [Group Y] {L : Subgroup Y} {q : ℕ} (hodd : Odd q) (h4 : 4 ≤ q)
    (h : HasSL2Model ↥L (fun r => r = q)) :
    CFSG.IsQuasisimple ↥L ∧ Nat.card (center ↥L) = 2 ∧
      ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x = y := by
  obtain ⟨hZ, hinv⟩ := sl2_model_center_inv hodd h
  refine ⟨?_, hZ, hinv⟩
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = q := hq
  let e' : ↥L ≃* SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm (isQuasisimple_sl2'' (by omega))

end SL2Facts

section TwoComps

variable {Y : Type} [Group Y]

theorem central_mem_of_card_inf {A B : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZ : Nat.card ↥(center ↥A) = 2) (hI : Nat.card ↥(A ⊓ B) = 2) {a : Y} (ha : a ∈ A)
    (hc : ∀ c ∈ A, c * a = a * c) : a ∈ B := by
  have hfin : Finite ↥(center ↥A) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hle : (A ⊓ B).subgroupOf A ≤ center ↥A := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 x (Subgroup.mem_subgroupOf.mp hx).2)
  have hcardI : Nat.card ↥((A ⊓ B).subgroupOf A) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv, hI]
  have heq : (A ⊓ B).subgroupOf A = center ↥A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcardI])
  have hmem : (⟨a, ha⟩ : ↥A) ∈ center ↥A :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
  rw [← heq] at hmem
  exact (Subgroup.mem_subgroupOf.mp hmem).2

theorem sup_le_commutator_top_of_sl2_pair {L₁ L₂ U : Subgroup Y} {q₁ q₂ : ℕ}
    (hodd₁ : Odd q₁) (h4₁ : 4 ≤ q₁) (h₁ : HasSL2Model ↥L₁ (fun r => r = q₁))
    (hodd₂ : Odd q₂) (h4₂ : 4 ≤ q₂) (h₂ : HasSL2Model ↥L₂ (fun r => r = q₂))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2)
    (hU : IVK.IsFourSubgroup U) (hUle : U ≤ L₁ ⊔ L₂) : L₁ ⊔ L₂ ≤ ⁅(⊤ : Subgroup Y), U⁆ := by
  obtain ⟨hq₁, hZ₁, hinv₁⟩ := sl2_model_facts hodd₁ h4₁ h₁
  obtain ⟨hq₂, hZ₂, hinv₂⟩ := sl2_model_facts hodd₂ h4₂ h₂
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hL₁ := le_commutator_top_of_two_comps hq₁ hcomm
    (fun a ha hc => central_mem_of_card_inf hcomm hZ₁ hcard ha hc) hinv₂ hU hUle
  have hL₂ := le_commutator_top_of_two_comps hq₂ hcomm'
    (fun a ha hc => central_mem_of_card_inf hcomm' hZ₂ (by rwa [inf_comm]) ha hc) hinv₁ hU
    (by rwa [sup_comm])
  exact sup_le hL₁ hL₂

end TwoComps

section BarFour

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_toBar_eq_one (z : G) {u : ↥(Cen z)} (hu2 : u ^ 2 = 1) (h : toBar z u = 1) :
    u = 1 := by
  have hker : u ∈ (toBar z).ker := h
  have h1 : orderOf (⟨u, hker⟩ : (toBar z).ker) ∣ Nat.card (toBar z).ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  have hodd := Odd.of_dvd_nat (odd_card_ker_toBar z) h1
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp this

theorem isFour_barOf (z : G) {U : Subgroup G} (hU : U ≤ Cen z) (h4 : IVK.IsFourSubgroup U) :
    IVK.IsFourSubgroup (barOf z U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 ↥U := h4.1
  have : IsElementaryAbelian 2 ↥(U.subgroupOf (Cen z)) := IsElementaryAbelian.subgroupOf hU
  refine ⟨IsElementaryAbelian.map (toBar z), ?_⟩
  let g : ↥(U.subgroupOf (Cen z)) →* CentralizerBar z := (toBar z).comp (U.subgroupOf (Cen z)).subtype
  have hg : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : toBar z (x : ↥(Cen z)) = 1 := hx
    have hsq : (x : ↥(Cen z)) ^ 2 = 1 := by
      apply Subtype.ext
      have hxU : ((x : ↥(Cen z)) : G) ∈ U := Subgroup.mem_subgroupOf.mp x.2
      exact elemPow_eq_one_of_isElementaryAbelian _ hxU
    have := eq_one_of_toBar_eq_one z hsq hx1
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hrange : g.range = barOf z U := by
    unfold barOf
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hg).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv]
  exact h4.2

end BarFour

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem barOf_le_LBar {U : Subgroup G} (hU : U ≤ LC z) : barOf z U ≤ LBar z :=
  Subgroup.map_mono (Subgroup.comap_mono hU)

omit [Finite G] in
theorem isFour_orderOf {U : Subgroup G} (h4 : IVK.IsFourSubgroup U) :
    ∀ u ∈ U, ∃ a : ℕ, orderOf u = 2 ^ a := by
  intro u hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 ↥U := h4.1
  have h2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  have hd : orderOf u ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one h2
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨a, ha⟩

theorem lemma23e_of_LBar_le (h : Stage2Ctx G z k S) {U : Subgroup G} (hUS : U ≤ S)
    (h4 : IVK.IsFourSubgroup U) (hnorm : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U)
    (hLB : LBar z ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆) :
    U ≤ LC z ⊓ ⁅Cen z, U⁆ ∧ LC z ≤ ⁅Cen z, U⁆ ⊔ OddCore z := by
  have hUL : U ≤ LC z := h.data.base.four_le U hUS h4 hnorm
  have hUC : U ≤ Cen z := hUL.trans (LC_le_Cen z)
  have hLBle : LBar z ≤ barOf z ⁅Cen z, U⁆ := hLB.trans (commutator_top_le_barOf z)
  refine ⟨le_inf hUL (le_commutator_of_barOf_le z hUC (isFour_orderOf h4)
    ((barOf_le_LBar hUL).trans hLBle)), LC_le_commutator_sup_of_LBar_le z hLBle⟩

theorem Stage2Ctx.LBar_le_commutator (h : Stage2Ctx G z k S)
    (hr : ¬ (k = Kind.m12 ∨ (k = Kind.g2 ∧ ¬ G2Big z S))) {U : Subgroup G} (hUS : U ≤ S)
    (h4 : IVK.IsFourSubgroup U) (hnorm : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    LBar z ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ := by
  have hUL : U ≤ LC z := h.data.base.four_le U hUS h4 hnorm
  have hUC : U ≤ Cen z := hUL.trans (LC_le_Cen z)
  have h4bar := isFour_barOf z hUC h4
  have hUbar := barOf_le_LBar hUL
  have hd := h.data
  have pair : ∀ {L₁ L₂ : Subgroup (CentralizerBar z)} {q₁ q₂ : ℕ}, Odd q₁ → 4 ≤ q₁ →
      HasSL2Model ↥L₁ (fun r => r = q₁) → Odd q₂ → 4 ≤ q₂ →
      HasSL2Model ↥L₂ (fun r => r = q₂) → IsCentralProd L₁ L₂ (LBar z) →
      LBar z ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ := by
    intro L₁ L₂ q₁ q₂ ho₁ h₁ m₁ ho₂ h₂ m₂ hprod
    obtain ⟨hsup, hcomm, hcard⟩ := hprod
    have := sup_le_commutator_top_of_sl2_pair ho₁ h₁ m₁ ho₂ h₂ m₂ hcomm hcard h4bar
      (by rw [hsup]; exact hUbar)
    rwa [hsup] at this
  cases hd with
  | g2 hg =>
    have hbig : G2Big z S := by
      by_contra hn
      exact hr (Or.inr ⟨rfl, hn⟩)
    obtain ⟨r₁, r₂, L₁, L₂, hr₂, hodd₁, hodd₂, hgt, hprod, m₁, m₂, -⟩ := hbig
    exact pair hodd₁ (by omega) m₁ hodd₂ (by omega) m₂ hprod
  | m12 hM => exact absurd (Or.inl rfl) hr
  | psp4 hP =>
    obtain ⟨q, L₁, L₂, hP⟩ := hP
    exact pair hP.pair.odd (by have := hP.pair.gt3; omega) hP.pair.sl₁ hP.pair.odd
      (by have := hP.pair.gt3; omega) hP.pair.sl₂ hP.pair.prod
  | l4 ε hL =>
    obtain ⟨q, L₁, L₂, hL⟩ := hL
    exact pair hL.pair.odd (by have := hL.pair.gt3; omega) hL.pair.sl₁ hL.pair.odd
      (by have := hL.pair.gt3; omega) hL.pair.sl₂ hL.pair.prod
  | mcl hS =>
    obtain ⟨n, -, hS⟩ := hS
    obtain ⟨hq, hZ, -⟩ := hS.cover
    rw [hS.eq_L]
    exact (commutator_top_eq_top_of_isFour hq hZ h4bar).ge
  | ly hS =>
    obtain ⟨n, -, hS⟩ := hS
    obtain ⟨hq, hZ, -⟩ := hS.cover
    rw [hS.eq_L]
    exact (commutator_top_eq_top_of_isFour hq hZ h4bar).ge

end Main

end CFSG.GH74.GLS.Stage2.Local
