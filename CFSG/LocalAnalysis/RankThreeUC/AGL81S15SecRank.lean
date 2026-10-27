module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem not_isCyclic_of_isElemAbelian {Y : Type} [Group Y] [Finite Y] {q k : ℕ} (hq : q.Prime)
    (hk : 2 ≤ k) {E : Subgroup Y} (hE : CFSG.Open.IsElemAbelian q E)
    (hcard : Nat.card E = q ^ k) : ¬ IsCyclic E := by
  intro hc
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgq : g ^ q = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hE.2 _ g.2)
  have hdvd : Nat.card E ∣ q := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hgq
  rw [hcard] at hdvd
  have hle : q ^ k ≤ q := Nat.le_of_dvd hq.pos hdvd
  have h2 : q ^ 2 ≤ q ^ k := Nat.pow_le_pow_right hq.pos hk
  have hq2 : 2 ≤ q := hq.two_le
  nlinarith

theorem exists_isPGroup_map_eq_top {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    {q : ℕ} (hq : q.Prime) (f : G →* H) (hf : Function.Surjective f) (hH : IsPGroup q H) :
    ∃ S : Subgroup G, IsPGroup q S ∧ S.map f = ⊤ := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hH
  have hTop : IsPGroup q (⊤ : Subgroup H) :=
    IsPGroup.iff_card.2 ⟨n, by rw [Subgroup.card_top, hn]⟩
  have hdvd : ¬ q ∣ (⊤ : Subgroup H).index := by
    rw [Subgroup.index_top]
    exact hq.not_dvd_one
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf q (hTop.toSylow hdvd)
  exact ⟨S.toSubgroup, S.isPGroup', congrArg Sylow.toSubgroup hS⟩

theorem two_le_pRank_of_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (φ : X →* Y)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (U : Subgroup X)
    (h : 2 ≤ CFSG.Open.pRank q (U.map φ)) : 2 ≤ CFSG.Open.pRank q U := by
  have hq1 : 1 < q := hq.one_lt
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, hEU, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq1 (U.map φ)
  have hEnc : ¬ IsCyclic E := not_isCyclic_of_isElemAbelian hq h hE hEcard
  have hEp : IsPGroup q E := IsPGroup.iff_card.2 ⟨_, hEcard⟩
  let F : Subgroup X := U ⊓ E.comap φ
  let f : F →* E := (φ.comp F.subtype).codRestrict E
    (fun x => Subgroup.mem_comap.1 (Subgroup.mem_inf.1 x.2).2)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.1 (hEU y.2)
    refine ⟨⟨u, Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_comap.2 ?_⟩⟩, Subtype.ext huy⟩
    rw [huy]
    exact y.2
  obtain ⟨S, hSp, hSt⟩ := exists_isPGroup_map_eq_top hq f hsurj hEp
  have hSnc : ¬ IsCyclic S := by
    intro hc
    apply hEnc
    refine isCyclic_of_surjective (f.comp S.subtype) ?_
    intro y
    have hy : y ∈ S.map f := by
      rw [hSt]
      exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have h2S : 2 ≤ CFSG.Open.pRank q S :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hq hq2 hSp hSnc
  have hFU : (⊤ : Subgroup F).map F.subtype ≤ U := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact (Subgroup.mem_inf.1 x.2).1
  calc 2 ≤ CFSG.Open.pRank q S := h2S
    _ ≤ CFSG.Open.pRank q (⊤ : Subgroup F) := CFSG.SectionRank.pRank_mono hq1 le_top
    _ ≤ CFSG.Open.pRank q ((⊤ : Subgroup F).map F.subtype) :=
        CFSG.SectionRank.pRank_le_map hq1 F.subtype F.subtype_injective ⊤
    _ ≤ CFSG.Open.pRank q U := CFSG.SectionRank.pRank_mono hq1 hFU

theorem gnA_eq_map {X : Type} [Group X] [Finite X] (T Ti : Subgroup X)
    (L : Subgroup (X ⧸ gnC T)) :
    gnA T Ti L = (Subgroup.normalizer (Ti : Set X) ⊓ L.comap (QuotientGroup.mk' (gnC T))).map
      (QuotientGroup.mk' (gnC T)) := by
  ext x
  simp only [gnA, gnImg, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hL⟩
    exact ⟨y, ⟨hy, hL⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hL⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hL⟩

theorem two_le_pRank_normalizer_of_gnA {X : Type} [Group X] [Finite X] (T Ti : Subgroup X)
    (L : Subgroup (X ⧸ gnC T)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : 1 < CFSG.Open.pRank q (gnA T Ti L)) :
    1 < CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X)) := by
  rw [gnA_eq_map] at h
  have h2 : 2 ≤ CFSG.Open.pRank q ((Subgroup.normalizer (Ti : Set X) ⊓
      L.comap (QuotientGroup.mk' (gnC T))).map (QuotientGroup.mk' (gnC T))) := h
  have h3 := two_le_pRank_of_map (QuotientGroup.mk' (gnC T)) hq hq2
    (Subgroup.normalizer (Ti : Set X) ⊓ L.comap (QuotientGroup.mk' (gnC T))) h2
  have hle : CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X) ⊓
      L.comap (QuotientGroup.mk' (gnC T))) ≤ CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt inf_le_left
  omega

theorem dvd_card_normalizer_of_dvd_gnA {X : Type} [Group X] [Finite X] (T Ti : Subgroup X)
    (L : Subgroup (X ⧸ gnC T)) {q : ℕ} (hq : q.Prime) (h : q ∣ Nat.card (gnA T Ti L)) :
    q ∣ Nat.card (Subgroup.normalizer (Ti : Set X) ⊓
      L.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) := by
  rw [gnA_eq_map] at h
  exact h.trans (Subgroup.card_map_dvd _ _)

end CFSG.LocalAnalysis.RankThreeUC.S15
