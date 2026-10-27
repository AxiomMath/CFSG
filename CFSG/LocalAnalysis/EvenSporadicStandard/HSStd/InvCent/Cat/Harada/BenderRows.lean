module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.RowLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.One
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Section13Count
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.GH74.Uniqueness.Bender

theorem card_le_two_of_sq_eq_one_of_sylow_cyclic {Q : Type*} [Group Q] [Finite Q]
    (hcyc : ∀ P : Sylow 2 Q, IsCyclic ↥P) (R : Subgroup Q) (hR : ∀ x ∈ R, x * x = 1) :
    Nat.card R ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (CFSG.GH74.Uniqueness.Bender.isPGroup_two_of_mul_self_eq_one hR).exists_le_sylow
  have hsq : ∀ x ∈ R.subgroupOf (P : Subgroup Q), x * x = 1 := fun x hx =>
    Subtype.ext (hR x hx)
  have h := card_le_two_of_sq_eq_one_of_isCyclic (hcyc P) (R.subgroupOf (P : Subgroup Q)) hsq
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv).symm.le.trans h

theorem card_centralizer_eq_mul_of_bender {G : Type} [Group G]
    [Finite G] {S : Subgroup G} [S.Normal] (hcent : centralizer (S : Set G) = ⊥) {n i e : ℕ}
    (hB : BenderType ↥S n i e) {t : G} (hsq : ∀ c ∈ centralizer ({t} : Set G), c * c ∈ S) :
    ∃ r : ℕ, r ≤ 2 ∧ Nat.card ↥(centralizer ({t} : Set G)) =
      Nat.card ↥(centralizer ({t} : Set G) ⊓ S) * r := by
  obtain ⟨R, hcard, hR⟩ := exists_card_eq_mul_outer_of_sq_mem S hcent hsq
  have : Finite (MulAut ↥S) := Finite.of_injective (fun f : MulAut ↥S => (f : ↥S → ↥S))
    DFunLike.coe_injective
  have : Finite (Outer ↥S) := inferInstance
  exact ⟨Nat.card R,
    card_le_two_of_sq_eq_one_of_sylow_cyclic (fun P => hB.isCyclic_sylow_outer P) R hR, hcard⟩

theorem card_centralizer_involution_of_bender {K : Type} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) {y : K} (hy : orderOf y = 2) :
    Nat.card ↥(centralizer ({y} : Set K)) = (2 ^ n) ^ i * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hyQ : y ∈ (Q : Subgroup K) := hQ (mem_zpowers y)
  exact (h.lemma_3_4_b Q hc.sq_eq_one hc.not_mem ⟨le_borel _ hyQ, hy⟩).2.2.1

theorem card_inf_centralizer_of_mem {G : Type*} [Group G] {S : Subgroup G} {t : G} (ht : t ∈ S) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ S) =
      Nat.card ↥(centralizer ({(⟨t, ht⟩ : ↥S)} : Set ↥S)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, ?_⟩
      invFun := fun y => ⟨y.1.1, ?_, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subtype.ext ((mem_centralizer_iff.1 x.2.1) t rfl)
  · refine mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact congrArg Subtype.val ((mem_centralizer_iff.1 y.2) ⟨h, ht⟩ rfl)

theorem card_inf_centralizer_eq_card_autFixed {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (t : G) : Nat.card ↥(centralizer ({t} : Set G) ⊓ S) =
      Nat.card ↥(autFixed (MulAut.conjNormal (H := S) t)) := by
  have key : ∀ x : G, x * t = t * x ↔ t * x * t⁻¹ = x := fun x => by
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, ?_⟩
      invFun := fun y => ⟨y.1.1, ?_, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · rw [mem_autFixed_iff]
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    exact (key x.1).1 (mem_centralizer_singleton_iff.1 x.2.1)
  · have h1 := congrArg Subtype.val (mem_autFixed_iff.1 y.2)
    rw [MulAut.conjNormal_apply] at h1
    exact mem_centralizer_singleton_iff.2 ((key y.1.1).2 h1)

theorem conjNormal_sq_eq_one {G : Type*} [Group G] {S : Subgroup G} [S.Normal] {t : G}
    (ht : orderOf t = 2) :
    MulAut.conjNormal (H := S) t * MulAut.conjNormal (H := S) t = 1 := by
  rw [← map_mul, mul_self_eq_one_of_orderOf_eq_two ht, map_one]

theorem conjNormal_not_inner {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (htS : t ∉ S) :
    ¬ ∃ g : ↥S, ∀ x : ↥S, MulAut.conjNormal (H := S) t x = g * x * g⁻¹ := by
  rintro ⟨g, hg⟩
  apply htS
  have h1 : MulAut.conjNormal (H := S) t = MulAut.conjNormal (H := S) (g : G) := by
    rw [MulAut.conjNormal_val]
    exact MulEquiv.ext fun x => by rw [hg x, MulAut.conj_apply]
  rw [conjNormal_injective_of_centralizer hcent h1]
  exact g.2

theorem card_inf_centralizer_L216 {G : Type} [Group G] [Finite G]
    {S : Subgroup G} [S.Normal] (hS : LieModel ↥S .PSL 2 2 4)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ S) = 16 ∨
      Nat.card ↥(centralizer ({t} : Set G) ⊓ S) = 60 := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (S := ↥S) (f := 4) (by norm_num) hS
  have hB : BenderType ↥S 4 1 1 := .linear 4 (by norm_num) e
  by_cases htS : t ∈ S
  · left
    rw [card_inf_centralizer_of_mem htS,
      card_centralizer_involution_of_bender hB (by rwa [Subgroup.orderOf_mk])]
    norm_num
  · right
    obtain ⟨m, hm, ⟨e'⟩, -⟩ := hB.fixed_linear (MulAut.conjNormal (H := S) t)
      (conjNormal_sq_eq_one ht) (conjNormal_not_inner hcent htS)
    have hm2 : m = 2 := by omega
    subst hm2
    rw [card_inf_centralizer_eq_card_autFixed, Nat.card_congr e'.toEquiv]
    exact CFSG.GH74.Uniqueness.A6.card_psl2_four

theorem card_inf_centralizer_U34 {G : Type} [Group G] [Finite G]
    {S : Subgroup G} [S.Normal] (hS : LieModel ↥S .PSU 3 2 2)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ S) = 320 ∨
      Nat.card ↥(centralizer ({t} : Set G) ⊓ S) = 60 := by
  have hSt := CFSG.GH74.Generic.stated_of_lieModel_PSU hS
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff ↥S 2 le_rfl).1 hSt
  have hB : BenderType ↥S 2 3 _ := .unitary 2 le_rfl e
  by_cases htS : t ∈ S
  · left
    rw [card_inf_centralizer_of_mem htS,
      card_centralizer_involution_of_bender hB (by rwa [Subgroup.orderOf_mk])]
    norm_num
  · right
    obtain ⟨e'⟩ := hB.fixed_unitary (MulAut.conjNormal (H := S) t)
      (conjNormal_sq_eq_one ht) (conjNormal_not_inner hcent htS)
    rw [card_inf_centralizer_eq_card_autFixed, Nat.card_congr e'.toEquiv]
    exact CFSG.GH74.Uniqueness.A6.card_psl2_four

theorem card_centralizer_L216 {G : Type} [Group G] [Finite G]
    {S : Subgroup G} [S.Normal] (hS : LieModel ↥S .PSL 2 2 4)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2)
    (hsq : ∀ c ∈ centralizer ({t} : Set G), c * c ∈ S) :
    ∃ r : ℕ, r ≤ 2 ∧ (Nat.card ↥(centralizer ({t} : Set G)) = 16 * r ∨
      Nat.card ↥(centralizer ({t} : Set G)) = 60 * r) := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (S := ↥S) (f := 4) (by norm_num) hS
  have hB : BenderType ↥S 4 1 1 := .linear 4 (by norm_num) e
  obtain ⟨r, hr, hcard⟩ := card_centralizer_eq_mul_of_bender hcent hB hsq
  refine ⟨r, hr, ?_⟩
  rcases card_inf_centralizer_L216 hS hcent ht with h | h
  · exact Or.inl (by rw [hcard, h])
  · exact Or.inr (by rw [hcard, h])

theorem card_centralizer_U34 {G : Type} [Group G] [Finite G]
    {S : Subgroup G} [S.Normal] (hS : LieModel ↥S .PSU 3 2 2)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2)
    (hsq : ∀ c ∈ centralizer ({t} : Set G), c * c ∈ S) :
    ∃ r : ℕ, r ≤ 2 ∧ (Nat.card ↥(centralizer ({t} : Set G)) = 320 * r ∨
      Nat.card ↥(centralizer ({t} : Set G)) = 60 * r) := by
  have hSt := CFSG.GH74.Generic.stated_of_lieModel_PSU hS
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff ↥S 2 le_rfl).1 hSt
  have hB : BenderType ↥S 2 3 _ := .unitary 2 le_rfl e
  obtain ⟨r, hr, hcard⟩ := card_centralizer_eq_mul_of_bender hcent hB hsq
  refine ⟨r, hr, ?_⟩
  rcases card_inf_centralizer_U34 hS hcent ht with h | h
  · exact Or.inl (by rw [hcard, h])
  · exact Or.inr (by rw [hcard, h])

theorem noZ2S5L216_holds : NoZ2S5L216 := by
  intro G _ _ S hSn hS hcent t ht hder ⟨ζ⟩
  haveI := hSn
  obtain ⟨r, hr, h⟩ := card_centralizer_L216 hS hcent ht
    (fun c hc => hder (sq_mem_centralizerDerived_of_equiv ζ hc))
  have h240 := card_centralizer_of_equiv ζ
  omega

theorem noZ2S5U34_holds : NoZ2S5U34 := by
  intro G _ _ S hSn hS hcent t ht hder ⟨ζ⟩
  haveI := hSn
  obtain ⟨r, hr, h⟩ := card_centralizer_U34 hS hcent ht
    (fun c hc => hder (sq_mem_centralizerDerived_of_equiv ζ hc))
  have h240 := card_centralizer_of_equiv ζ
  omega

theorem noTwoCfgL216_holds : NoTwoCfgL216 := by
  intro G _ _ S hSn hS hcent t v J h hder
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  obtain ⟨r, hr, hc⟩ := card_centralizer_L216 hS hcent h.ht
    (fun c hc => hder (h.sq_mem_centralizerDerived htop hc))
  have h480 := h.card_centralizer htop
  omega

theorem noTwoCfgU34_holds : NoTwoCfgU34 := by
  intro G _ _ S hSn hS hcent t v J h hder
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  obtain ⟨r, hr, hc⟩ := card_centralizer_U34 hS hcent h.ht
    (fun c hc => hder (h.sq_mem_centralizerDerived htop hc))
  have h480 := h.card_centralizer htop
  omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
