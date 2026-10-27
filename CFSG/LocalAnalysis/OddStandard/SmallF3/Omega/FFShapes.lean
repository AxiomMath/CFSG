module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux
public import CFSG.Adapters.LieModelSmallOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ff_card_isOmega5 {X : Subgroup G} (h : IsOmega5 X) :
    Nat.card (↥X ⧸ oddCore ↥X) = 25920 := by
  exact ff_card_model_psp h

theorem ff_card_isL29 {X : Subgroup G} (h : IsL29 X) : Nat.card (↥X ⧸ oddCore ↥X) = 360 := by
  exact ff_card_model_psl2 h

theorem ff_card_isL3Eps3 {X : Subgroup G} (h : IsL3Eps3 X) :
    Nat.card (↥X ⧸ oddCore ↥X) = 5616 ∨ Nat.card (↥X ⧸ oddCore ↥X) = 6048 := by
  rcases h with h | h
  · exact Or.inl (ff_card_model_psl3 h)
  · exact Or.inr (h.card_psu_three_three)

theorem ff_card_isOmega6Plus {X : Subgroup G} (h : IsOmega6Plus X) :
    Nat.card (↥X ⧸ oddCore ↥X) = 6065280 := by
  exact ff_card_model_psl4 h

theorem ff_isOmega5_ne_bot {X : Subgroup G} (h : IsOmega5 X) : X ≠ ⊥ := by
  intro hX
  have h1 := ff_card_quot_bot hX
  have h2 := ff_card_isOmega5 h
  omega

theorem ff_isL29_ne_bot {X : Subgroup G} (h : IsL29 X) : X ≠ ⊥ := by
  intro hX
  have h1 := ff_card_quot_bot hX
  have h2 := ff_card_isL29 h
  omega

theorem ff_isL3Eps3_ne_bot {X : Subgroup G} (h : IsL3Eps3 X) : X ≠ ⊥ := by
  intro hX
  have h1 := ff_card_quot_bot hX
  have h2 := ff_card_isL3Eps3 h
  omega

theorem ff_not_isOmega5_and_isL29 {X : Subgroup G} (h : IsOmega5 X) : ¬ IsL29 X := by
  intro h'
  have h1 := ff_card_isOmega5 h
  have h2 := ff_card_isL29 h'
  omega

theorem ff_not_isOmega5_and_isL3Eps3 {X : Subgroup G} (h : IsOmega5 X) : ¬ IsL3Eps3 X := by
  intro h'
  have h1 := ff_card_isOmega5 h
  have h2 := ff_card_isL3Eps3 h'
  omega

theorem ff_not_isOmega6Plus_and_isOmega5 {X : Subgroup G} (h : IsOmega6Plus X) :
    ¬ IsOmega5 X := by
  intro h'
  have h1 := ff_card_isOmega6Plus h
  have h2 := ff_card_isOmega5 h'
  omega

theorem ff_not_isOmega6Plus_and_isL29 {X : Subgroup G} (h : IsOmega6Plus X) : ¬ IsL29 X := by
  intro h'
  have h1 := ff_card_isOmega6Plus h
  have h2 := ff_card_isL29 h'
  omega

theorem ff_isOmega6Plus_ne_bot {X : Subgroup G} (h : IsOmega6Plus X) : X ≠ ⊥ := by
  intro hX
  have h1 := ff_card_quot_bot hX
  have h2 := ff_card_isOmega6Plus h
  omega

theorem ff_simple_of_lieModel_psl2 {X : Type} [Group X] (h : LieModel X .PSL 2 3 2) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psl2 h
  haveI := hfin
  exact ⟨hs, ff_noncomm_of_simple_card hs (by rw [ff_card_model_psl2 h]; norm_num)⟩

theorem ff_simple_of_lieModel_psp {X : Type} [Group X] (h : LieModel X .PSp 2 3 1) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psp h
  haveI := hfin
  exact ⟨hs, ff_noncomm_of_simple_card hs (by rw [ff_card_model_psp h]; norm_num)⟩

theorem ff_simple_of_lieModel_psl3 {X : Type} [Group X] (h : LieModel X .PSL 3 3 1) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psl3 h
  haveI := hfin
  exact ⟨hs, ff_noncomm_of_simple_card hs (by rw [ff_card_model_psl3 h]; norm_num)⟩

theorem ff_isL29_not_solvable {X : Subgroup G} (h : IsL29 X) : ¬ Group.IsSolvable ↥X := by
  intro hs
  haveI := hs
  obtain ⟨hsimple, a, b, hab⟩ := ff_simple_of_lieModel_psl2 h
  haveI := hsimple
  haveI : Group.IsSolvable (↥X ⧸ oddCore ↥X) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥X ⧸ oddCore ↥X)).mpr inferInstance a b)

theorem ff_isOmega5_of_lieModel {X : Subgroup G} (h : LieModel ↥X .PSp 2 3 1) : IsOmega5 X := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psp h
  haveI := hfin
  exact ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psp h]; norm_num)

theorem ff_isL29_of_lieModel {X : Subgroup G} (h : LieModel ↥X .PSL 2 3 2) : IsL29 X := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psl2 h
  haveI := hfin
  exact ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psl2 h]; norm_num)

theorem ff_isL3Eps3_of_lieModel {X : Subgroup G} (h : LieModel ↥X .PSL 3 3 1) : IsL3Eps3 X := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psl3 h
  haveI := hfin
  exact Or.inl (ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psl3 h]; norm_num))

theorem ff_layer_ffX_eq_of_normal_simple {B : Type} [Group B] [Finite B] (E : Subgroup B)
    [E.Normal] (hE : IsSimpleGroup ↥E) (hnc : ∃ a b : ↥E, a * b ≠ b * a)
    (hev : 2 ∣ Nat.card ↥E) (h2 : IsPGroup 2 (B ⧸ E)) : CFSG.layer B = E ∧ ffX B = E := by
  refine ⟨?_, ?_⟩
  · have hl : CFSG.layer B = sSup {K : Subgroup B | CFSG.IsComponent K} := rfl
    rw [hl]
    apply le_antisymm
    · exact sSup_le (fun K hK => ff_perfect_le_of_quot_two E h2 K hK.1.1)
    · exact le_sSup ⟨ff_isQuasisimple_of_simple hE hnc, Subgroup.Normal.isSubnormal ‹_›⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hodd : ∀ g : B, Odd (orderOf g) → g ∈ E := by
      intro g hg
      have hx : (QuotientGroup.mk g : B ⧸ E) ^ orderOf g = 1 := by
        rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp h2) (QuotientGroup.mk g)
      have hd : orderOf (QuotientGroup.mk g : B ⧸ E) ∣ orderOf g := orderOf_dvd_of_pow_eq_one hx
      rw [hj] at hd
      have hj0 : j = 0 := by
        by_contra hne
        exact (Nat.not_even_iff_odd.mpr hg)
          (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hd))
      rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
      exact (QuotientGroup.eq_one_iff g).mp hj
    have hRes : twoRes (⊤ : Subgroup B) = E := by
      have hset : {g : B | g ∈ (⊤ : Subgroup B) ∧ Odd (orderOf g)} =
          {g : B | g ∈ E ∧ Odd (orderOf g)} := by
        ext g
        exact ⟨fun h => ⟨hodd g h.2, h.2⟩, fun h => ⟨mem_top g, h.2⟩⟩
      unfold twoRes
      rw [hset]
      refine ff_closure_filter_eq E hE (fun g => Odd (orderOf g)) (fun g k hg => ?_) ?_
      · rw [Subgroup.orderOf_coe, ff_orderOf_conj]
        rwa [Subgroup.orderOf_coe] at hg
      · obtain ⟨g, hg, hg1⟩ := ff_exists_odd_ne_one hE hnc
        exact ⟨g, by rwa [Subgroup.orderOf_coe], hg1⟩
    unfold ffX
    rw [hRes]
    unfold twoPrimeRes
    refine ff_closure_filter_eq E hE (fun g => ∃ k : ℕ, orderOf g = 2 ^ k) (fun g k hg => ?_) ?_
    · obtain ⟨j, hj⟩ := hg
      exact ⟨j, by rw [Subgroup.orderOf_coe, ff_orderOf_conj, ← Subgroup.orderOf_coe, hj]⟩
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
      refine ⟨x, ⟨1, by rw [Subgroup.orderOf_coe, hx]; norm_num⟩, ?_⟩
      intro h1
      rw [h1, orderOf_one] at hx
      exact absurd hx (by norm_num)

theorem ff_layer_eq_bot_of_solvable {B : Type} [Group B] (h : Group.IsSolvable B) :
    CFSG.layer B = ⊥ := by
  haveI := h
  have hl : CFSG.layer B = sSup {K : Subgroup B | CFSG.IsComponent K} := rfl
  rw [hl, eq_bot_iff]
  refine sSup_le (fun K hK => ?_)
  exfalso
  obtain ⟨⟨hperf, -, a, b, hab⟩, -⟩ := hK
  haveI := hperf
  by_cases hsub : Subsingleton ↥K
  · haveI : Subsingleton (↥K ⧸ center ↥K) := QuotientGroup.mk_surjective.subsingleton
    exact hab (Subsingleton.elim _ _)
  · haveI : Nontrivial ↥K := not_subsingleton_iff_nontrivial.mp hsub
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance

theorem ff_layerModel_psl2 {B : Type} [Group B] [Finite B] (h : LayerModel B .PSL 2 2) :
    IsL29 (CFSG.layer B) ∧ ffX B = CFSG.layer B := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psl2 hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psl2 hlie]; norm_num
  obtain ⟨hl, hx⟩ := ff_layer_ffX_eq_of_normal_simple E hs hnc hev hp
  rw [hl]
  exact ⟨ff_isL29_of_lieModel hlie, hx⟩

theorem ff_layerModel_psp {B : Type} [Group B] [Finite B] (h : LayerModel B .PSp 2 1) :
    IsOmega5 (CFSG.layer B) ∧ ffX B = CFSG.layer B := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psp hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psp hlie]; norm_num
  obtain ⟨hl, hx⟩ := ff_layer_ffX_eq_of_normal_simple E hs hnc hev hp
  rw [hl]
  exact ⟨ff_isOmega5_of_lieModel hlie, hx⟩

theorem ff_layerModel_psl3 {B : Type} [Group B] [Finite B] (h : LayerModel B .PSL 3 1) :
    IsL3Eps3 (CFSG.layer B) ∧ ffX B = CFSG.layer B := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psl3 hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psl3 hlie]; norm_num
  obtain ⟨hl, hx⟩ := ff_layer_ffX_eq_of_normal_simple E hs hnc hev hp
  rw [hl]
  exact ⟨ff_isL3Eps3_of_lieModel hlie, hx⟩

end CFSG.OddStandard.SmallF3.Omega
