module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceOdd
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

namespace ToralReduce

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem ibPerfectSections_map {J : Subgroup Y} (hJL : J ≤ L) {p : ℕ}
    (hIb : IbPerfectSections p J) :
    IbPerfectSections p ((J.subgroupOf L).map (twoCenterHom L)) := by
  intro W hW hWp hdvd
  let ρJ : ↥J →* TwoCenterQuot L := (twoCenterHom L).comp (Subgroup.inclusion hJL)
  have hker : ρJ.ker ≤ Subgroup.center ↥J := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hz : (a : Y) ∈ twoCenter L := twoCenterHom_eq_one_iff.mp ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (mul_comm_of_mem_twoCenter hz (hJL b.2)).symm
  have hrange : W ≤ ρJ.range := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := hW hw
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨W₀, hW₀p, -, hW₀⟩ := ParabPrime.exists_perfect_map_eq ρJ hker hWp hrange
  refine hIb (W₀.map J.subtype) (Subgroup.map_subtype_le _)
    (by rw [← Subgroup.map_commutator, hW₀p]) ?_
  rw [Subgroup.card_map_of_injective J.subtype_injective]
  exact hdvd.trans (hW₀ ▸ Subgroup.card_map_dvd W₀ ρJ)

theorem pCoreOf_map_twoCenterHom {J : Subgroup Y} (hP : IsParabolicTwo L J) :
    pCoreOf 2 ((J.subgroupOf L).map (twoCenterHom L)) =
      ((pCoreOf 2 J).subgroupOf L).map (twoCenterHom L) := by
  have hJL := hP.1
  have hZJ := twoCenter_le_of_isParabolicTwo hP
  have hOJ : pCoreOf 2 J ≤ J := pCoreOf_le 2 J
  have hZO : twoCenter L ≤ pCoreOf 2 J :=
    normal_pSubgroup_le_pCoreOf 2 hZJ (twoCenter_subgroupOf_normal hJL) isPGroup_twoCenter
  have hOJ' : ((pCoreOf 2 J).subgroupOf L).map (twoCenterHom L) ≤
      (J.subgroupOf L).map (twoCenterHom L) :=
    Subgroup.map_mono fun a (ha : (a : Y) ∈ pCoreOf 2 J) => (hOJ ha : (a : Y) ∈ J)
  apply le_antisymm
  · obtain ⟨O, hOdef⟩ : ∃ O, O = pCoreOf 2 ((J.subgroupOf L).map (twoCenterHom L)) := ⟨_, rfl⟩
    rw [← hOdef]
    have hOr : O ≤ (twoCenterHom L).range :=
      hOdef ▸ (pCoreOf_le 2 _).trans (Subgroup.map_le_range _ _)
    have hPmap := map_comap_twoCenterHom hOr
    obtain ⟨P, hPdef⟩ : ∃ P, P = (O.comap (twoCenterHom L)).map L.subtype := ⟨_, rfl⟩
    rw [← hPdef] at hPmap
    have hPL : P ≤ L := hPdef ▸ Subgroup.map_subtype_le _
    have hZP : twoCenter L ≤ P := fun z hz => by
      rw [hPdef]
      refine ⟨⟨z, twoCenter_le hz⟩, ?_, rfl⟩
      show twoCenterHom L ⟨z, twoCenter_le hz⟩ ∈ O
      rw [twoCenterHom_eq_one_iff.mpr hz]
      exact O.one_mem
    have hPJ : P ≤ J := fun y hy => by
      rw [hPdef] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      have hb' : twoCenterHom L b ∈ pCoreOf 2 ((J.subgroupOf L).map (twoCenterHom L)) :=
        hOdef ▸ hb
      exact (mem_map_twoCenterHom_iff hZJ).mp (pCoreOf_le 2 _ hb')
    have hP2 : IsPGroup 2 P := isPGroup_of_map_mem hPL
      (hOdef ▸ pCoreOf_isPGroup 2 _) fun a ha => by
        rw [hPdef] at ha
        obtain ⟨b, hb, hba⟩ := ha
        rwa [show a = b from Subtype.ext hba.symm]
    have hPn : (P.subgroupOf J).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPJ]
      intro j hj
      rw [← twoCenterHom_mem_normalizer_iff (l := ⟨j, hJL hj⟩) hPL hZP, hPmap, hOdef]
      exact subgroup_normalizes_pCoreOf 2 _ ⟨⟨j, hJL hj⟩, hj, rfl⟩
    have hPO := normal_pSubgroup_le_pCoreOf 2 hPJ hPn hP2
    rw [← hPmap]
    exact Subgroup.map_mono fun a (ha : (a : Y) ∈ P) => (hPO ha : (a : Y) ∈ pCoreOf 2 J)
  · refine normal_pSubgroup_le_pCoreOf 2 hOJ' ?_
      (((pCoreOf_isPGroup 2 J).of_equiv
        (Subgroup.subgroupOfEquivOfLe (hOJ.trans hJL)).symm).map _)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOJ']
    rintro _ ⟨j, hj, rfl⟩
    exact (twoCenterHom_mem_normalizer_iff (hOJ.trans hJL) hZO j).mpr
      (subgroup_normalizes_pCoreOf 2 J hj)

theorem commutator_subgroupOf_eq {N V : Subgroup Y} (hVN : V ≤ N) (hV : ⁅V, V⁆ = V) :
    ⁅V.subgroupOf N, V.subgroupOf N⁆ = V.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hVN, hV]

end ToralReduce

open ToralReduce in
theorem kFactBlockToralIb_of_odd (h : KFactBlockToralIbOdd) : KFactBlockToralIb := by
  intro Y _ _ L J hL hcl hP hJL hJB p hp hp5 hIb x hxL hxp hxC hV hfix hE
  obtain ⟨V, hVp, hVL, hVO, hxV⟩ := hV
  obtain ⟨E, hEle, hEel, hEc⟩ := hE
  have hJLe : J ≤ L := hP.1
  have hZJ := twoCenter_le_of_isParabolicTwo hP
  have hZO : twoCenter L ≤ pCoreOf 2 J :=
    normal_pSubgroup_le_pCoreOf 2 hZJ (twoCenter_subgroupOf_normal hJLe) isPGroup_twoCenter
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hxp' : (⟨x, hxL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hxp)
  refine h (TwoCenterQuot L) (twoCenterHom L).range ((J.subgroupOf L).map (twoCenterHom L))
    (isComponentOf_range hL) (isClassicalTwoOrG2_of_iso (centerQuotEquiv hL.2.2) hcl)
    (isParabolicTwo_map hP) (map_ne_range hP hJL) (ne_borel_map hP hJB)
    (odd_card_center_range hL.2.2) p hp hp5 (ibPerfectSections_map hJLe hIb)
    (twoCenterHom L ⟨x, hxL⟩) ⟨_, rfl⟩ (by rw [← map_pow, hxp', map_one]) ?_ ?_ ?_ ?_
  ·
    intro hc
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.mp hc (twoCenterHom L ⟨l, hl⟩) ⟨_, rfl⟩
    have h2 : twoCenterHom L (⟨x, hxL⟩ * ⟨l, hl⟩ * ⟨x, hxL⟩⁻¹) = twoCenterHom L ⟨l, hl⟩ := by
      rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
    have h3 := congrArg Subtype.val (commute_of_twoCenterHom_conj hodd hxp' h2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    calc l * x = x * l * x⁻¹ * x := by rw [h3]
      _ = x * l := by group
  ·
    refine ⟨(V.subgroupOf (Subgroup.normalizer (L : Set Y))).map (twoCenterMk L), ?_, ?_, ?_,
      ⟨⟨x, Subgroup.le_normalizer hxL⟩, hxV, rfl⟩⟩
    · rw [← Subgroup.map_commutator, commutator_subgroupOf_eq hVL hVp]
    · intro y _
      rw [Subgroup.normalizer_eq_top (twoCenterHom L).range]
      exact Subgroup.mem_top y
    · rintro _ ⟨n, hn, rfl⟩
      rw [pCoreOf_map_twoCenterHom hP]
      exact twoCenterMk_mem_normalizer hZO (hVO hn)
  ·
    rintro _ ⟨l, rfl⟩ hl
    have h2 : twoCenterHom L (⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹) = twoCenterHom L l := by
      rw [map_mul, map_mul, map_inv]
      exact hl
    have h3 := congrArg Subtype.val (commute_of_twoCenterHom_conj hodd hxp' h2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    exact ⟨l, hfix l l.2 h3, rfl⟩
  ·
    have hEL : E ≤ L := hEle.trans inf_le_left
    let f : ↥(E.subgroupOf L) →* TwoCenterQuot L :=
      (twoCenterHom L).comp (E.subgroupOf L).subtype
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro e he
      have hz : ((e : ↥L) : Y) ∈ twoCenter L := twoCenterHom_eq_one_iff.mp he
      have hep : ((e : ↥L) : Y) ^ p = 1 := hEel.2 _ e.2
      exact Subtype.ext (Subtype.ext (eq_one_of_mem_twoCenter hz hodd hep))
    have hfr : f.range = (E.subgroupOf L).map (twoCenterHom L) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    refine ⟨(E.subgroupOf L).map (twoCenterHom L), le_inf (Subgroup.map_le_range _ _) ?_, ⟨?_, ?_⟩,
      ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEle he).2 x rfl)
    · refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨_, ⟨e₁, he₁, rfl⟩⟩ := a
      obtain ⟨_, ⟨e₂, he₂, rfl⟩⟩ := b
      apply Subtype.ext
      change twoCenterHom L e₁ * twoCenterHom L e₂ = twoCenterHom L e₂ * twoCenterHom L e₁
      rw [← map_mul, ← map_mul]
      congr 1
      have := hEel.1.is_comm.comm (⟨e₁, he₁⟩ : ↥E) ⟨e₂, he₂⟩
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    · rintro _ ⟨e, he, rfl⟩
      rw [← map_pow]
      have : e ^ p = 1 := Subtype.ext (by simpa using hEel.2 _ he)
      rw [this, map_one]
    · rw [← hfr, ← hEc, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

theorem kFactBlockToralIb_of_census (hC : KFactFixCensusPrime) : KFactBlockToralIb :=
  kFactBlockToralIb_of_odd (kFactBlockToralIbOdd_of hC kFactL3RankTwo)

end CFSG.AGLEmbedding
