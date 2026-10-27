module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Setup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourReduce

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoL3Four

variable {G : Type} [Group G] [Finite G]

theorem benderHyp_quotient {A : Subgroup G} (hstd : standardComponentIsStandard A)
    (hnn : ¬ A.Normal) (hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set G)))
    (hB : RankTwoBenderType (rankTwoQuot A)) :
    BenderHyp (G ⧸ standardComponentOddCore G)
        (A.map (QuotientGroup.mk' (standardComponentOddCore G))) ∧
      Nonempty (rankTwoQuot A ≃*
        rankTwoQuot (A.map (QuotientGroup.mk' (standardComponentOddCore G)))) := by
  have hodd := RankTwoSporadic.odd_card_standardComponentOddCore (G := G)
  have hNA := RankTwoSporadic.standardComponentOddCore_le_centralizer hstd hrank
  set e := RankTwoSporadic.quotCenterEquivMap hNA hstd.1.1 with he
  refine ⟨⟨RankTwoSporadic.standard_map hstd hodd hNA,
    RankTwoSporadic.standardComponentOddCore_quotient_eq_bot, ?_,
    RankTwoSporadic.two_le_pRank_map hodd hNA hstd.1.1 hrank,
    RankTwoBenderType.of_mulEquiv e.symm hB⟩, ⟨e⟩⟩
  intro hn
  apply hnn
  have h1 : (A ⊔ standardComponentOddCore G).Normal := by
    have := hn.comap (QuotientGroup.mk' (standardComponentOddCore G))
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
  rw [← normalizer_eq_top_iff, ← RankTwoSporadic.normalizer_sup_eq hodd hNA hstd.1.1]
  exact normalizer_eq_top_iff.mpr h1

theorem nonempty_rankTwoX_mulEquiv_ru_of_map
    {N A : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N))
    (hNA : N ≤ centralizer (A : Set G)) (hAp : commutator ↥A = ⊤)
    (h : NativeSporadic.IsSporadic (rankTwoX (A.map (QuotientGroup.mk' N))) .Ru) :
    Nonempty (↥(rankTwoX A) ≃* NativeSporadic.Ru) := by
  set π := QuotientGroup.mk' N
  set X := rankTwoX A
  have hXN : N ≤ centralizer (X : Set G) := le_centralizer_rankTwoX hNA
  have : Group.IsPerfect ↥X := (Group.isPerfect_def).2 (commutator_rankTwoX_eq_top hAp)
  let ρ : ↥X →* ↥(X.map π) := π.subgroupMap X
  have hρ : Function.Surjective ρ := π.subgroupMap_surjective X
  have hmemker : ∀ x : ↥X, x ∈ ρ.ker ↔ (x : G) ∈ N := fun x => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π (x : G) = 1 := congrArg Subtype.val hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    · intro hx
      apply Subtype.ext
      change π (x : G) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
  have hker : ρ.ker ≤ center ↥X := fun x hx => by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hXN ((hmemker x).mp hx)) y y.2)
  have hkerodd : Odd (Nat.card ρ.ker) := by
    refine hodd.of_dvd_nat ?_
    let φ : ↥ρ.ker →* ↥N :=
      { toFun := fun x => ⟨(x : ↥X), (hmemker _).mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective φ := fun a b hab => by
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact Subgroup.card_dvd_of_injective φ hinj
  have hXbar : X.map π = rankTwoX (A.map π) := map_rankTwoX π (QuotientGroup.mk'_surjective N) A
  obtain ⟨e⟩ := h
  let f : ↥X →* NativeSporadic.Ru :=
    (((MulEquiv.subgroupCongr hXbar).trans e : ↥(X.map π) ≃* NativeSporadic.Ru) :
      ↥(X.map π) →* NativeSporadic.Ru).comp ρ
  have hf : Function.Surjective f :=
    ((MulEquiv.subgroupCongr hXbar).trans e).surjective.comp hρ
  have hfker : f.ker = ρ.ker := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_ofClass, map_eq_one_iff _ (MulEquiv.injective _)]
  have hf1 : f.ker = ⊥ :=
    CFSG.SectionRank.Ru_perfect_odd_cover_trivial f hf (hfker ▸ hker) (hfker ▸ hkerodd)
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hf1, hf⟩⟩

namespace SzMinCounter

theorem nonempty_closureIn_mulEquiv_ru
    {L : Subgroup G} (hM : SzMinCounter G L 1) {H : Subgroup G}
    (hHG : H ≠ ⊤) (hLH : L ≤ H) (hKH : centralizer (L : Set G) ≤ H)
    (hnn : ¬ (L.subgroupOf H).Normal) :
    Nonempty (↥((rankTwoX (L.subgroupOf H)).map H.subtype) ≃* NativeSporadic.Ru) := by
  obtain ⟨E, hEK, hE, hE4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hM.hyp.rank
  have hEH : E ≤ H := hEK.trans hKH
  have heven : Even (Nat.card (centralizer (L : Set G) ⊓ H : Subgroup G)) := by
    rw [inf_eq_left.mpr hKH]
    exact even_iff_two_dvd.mpr ((show 2 ∣ 4 by norm_num).trans (hE4 ▸ card_dvd_of_le hEK))
  have hstd := standard_subgroupOf hM.hyp.standard hLH heven
  have hrank : 2 ≤ Open.pRank 2 (centralizer ((L.subgroupOf H : Subgroup H) : Set H)) := by
    rw [centralizer_subgroupOf_eq hLH]
    refine two_le_pRank_of_le (E := E.subgroupOf H) ?_ ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩ ?_
    · intro x hx
      rw [mem_subgroupOf] at hx ⊢
      exact ⟨hEK hx, x.2⟩
    · apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨(x : H), x.2⟩ ⟨(y : H), y.2⟩)
      simpa using this
    · apply Subtype.ext
      simpa using hE.2 x hx
    · rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv, hE4]
  obtain ⟨hB, ⟨e⟩⟩ := benderHyp_quotient hstd hnn hrank
    (RankTwoBenderType.of_mulEquiv (BenderHyp.quotEquivSubgroupOf hLH) hM.hyp.bender)
  have hcard : Nat.card (↥H ⧸ standardComponentOddCore ↥H) < Nat.card G := by
    have hH : Nat.card H < Nat.card G :=
      lt_of_le_of_ne (card_le_card_group _) fun he => hHG ((card_eq_iff_eq_top _).mp he)
    have h1 := (standardComponentOddCore ↥H).card_eq_card_quotient_mul_card_subgroup
    have h2 : 0 < Nat.card (standardComponentOddCore ↥H) := Nat.card_pos
    calc Nat.card (↥H ⧸ standardComponentOddCore ↥H) ≤
        Nat.card (↥H ⧸ standardComponentOddCore ↥H) * Nat.card (standardComponentOddCore ↥H) :=
          Nat.le_mul_of_pos_right _ h2
      _ = Nat.card H := h1.symm
      _ < Nat.card G := hH
  obtain ⟨-, hRu⟩ := hM.ih _ hcard _ hB 1 le_rfl
    (suzukiModel_of_mulEquiv' (e.symm.trans (BenderHyp.quotEquivSubgroupOf hLH)) hM.sz)
  obtain ⟨f⟩ := nonempty_rankTwoX_mulEquiv_ru_of_map
    RankTwoSporadic.odd_card_standardComponentOddCore
    (RankTwoSporadic.standardComponentOddCore_le_centralizer hstd hrank) hstd.1.1 hRu
  exact ⟨(equivMapOfInjective _ H.subtype H.subtype_injective).symm.trans f⟩

end SzMinCounter

end CFSG.ComponentClassification.GMS78
