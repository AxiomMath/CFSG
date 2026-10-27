module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankBlk

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {K L : Subgroup G}

omit [Finite G] in
theorem card_pCore_mul_sixty (hL : IsAltType L 5) :
    Nat.card (CFSG.pCore 2 ↥L) * 60 = Nat.card ↥L := by
  obtain ⟨ρ, hρ, hρk, -⟩ := hL
  rw [← hρk]
  have : Nat.card ρ.range = 60 := by
    rw [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top, Delta5.a5_card]
  rw [← this, ← Subgroup.index_ker, Subgroup.card_mul_index]

omit [Finite G] in
theorem index_pCore_eq_sixty (hL : IsAltType L 5) : (CFSG.pCore 2 ↥L).index = 60 := by
  obtain ⟨ρ, hρ, hρk, -⟩ := hL
  rw [← hρk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top,
    Delta5.a5_card]

omit [Finite G] in
theorem card_blockQ_eq (L : Subgroup G) :
    Nat.card ↥(blockQ L) = Nat.card ↥(CFSG.pCore 2 ↥L) := by
  unfold blockQ pCoreOf
  rw [Subgroup.card_map_of_injective L.subtype_injective]

omit [Finite G] in
theorem sixteen_dvd_card_blockU (hL : IsAltType L 5) : 16 ∣ Nat.card ↥(blockU L) := by
  obtain ⟨-, -, -, β, hβ, -, -⟩ := hL
  have h1 : Nat.card β.ker * Nat.card β.range = Nat.card ↥(blockU L) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card β.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
    exact card_evenWeight_five
  exact ⟨Nat.card β.ker, by rw [← h1, h2]; ring⟩

omit [Finite G] in
theorem sixteen_dvd_card_pCore (hs : IsShort2 L) (hL : IsAltType L 5) :
    16 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
  have h1 : Nat.card ↥(blockU L) ∣ Nat.card ↥(blockQ L) :=
    Subgroup.card_dvd_of_le (C1.blockU_le_blockQ hs)
  rw [card_blockQ_eq] at h1
  exact (sixteen_dvd_card_blockU hL).trans h1

omit [Finite G] in
theorem nineSixty_dvd_card (hs : IsShort2 L) (hL : IsAltType L 5) : 960 ∣ Nat.card ↥L := by
  obtain ⟨c, hc⟩ := sixteen_dvd_card_pCore hs hL
  refine ⟨c, ?_⟩
  rw [← card_pCore_mul_sixty hL, hc]
  ring

omit [Finite G] in
theorem nineSixty_dvd_card_of_le (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K) :
    960 ∣ Nat.card ↥K :=
  (nineSixty_dvd_card hs hL).trans (Subgroup.card_dvd_of_le hLK)

omit [Finite G] in
theorem two_pow_six_dvd_card_of_le (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K) :
    64 ∣ Nat.card ↥K :=
  (show 64 ∣ 960 by norm_num).trans (nineSixty_dvd_card_of_le hs hL hLK)

omit [Finite G] in
theorem mem_blockZ_of_mem_center {u : G} (hu : u ∈ blockU L) (hLK : L ≤ K) (hK : u ∈ K)
    (hc : (⟨u, hK⟩ : ↥K) ∈ Subgroup.center ↥K) : u ∈ blockZ L := by
  refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hLK hl⟩)

theorem exists_subgroup_card_quot (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥K)) :
    ∃ (H : Subgroup (↥K ⧸ Subgroup.center ↥K)) (n : ℕ), 4 ≤ n ∧ Nat.card H = 60 * 2 ^ n := by
  classical
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set ρ : ↥L →* ↥K ⧸ Subgroup.center ↥K := π.comp (Subgroup.inclusion hLK) with hρ
  set Q' : Subgroup ↥L := CFSG.pCore 2 ↥L with hQ'
  have hkerπ : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hZ
  have hle : ρ.ker ≤ Q' := ker_le_pCore hLK π hkerπ
  have hidx : (Q'.map ρ).index = 60 * ρ.range.index := by
    rw [Subgroup.index_map, sup_eq_left.mpr hle, hQ', index_pCore_eq_sixty hL]
  have hle' : Q'.map ρ ≤ ρ.range := Subgroup.map_le_range ρ Q'
  have hne : ρ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : (Q'.map ρ).relIndex ρ.range = 60 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne)
    rw [Subgroup.relIndex_mul_index hle', hidx]
  have hcard : 60 * Nat.card (Q'.map ρ) = Nat.card ρ.range := by
    have h3 := Subgroup.relIndex_mul_card (Q'.map ρ) ρ.range
    rwa [hrel, inf_eq_left.mpr hle'] at h3
  have hQ2 : IsPGroup 2 ↥(Q'.map ρ) :=
    IsPGroup.of_surjective (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) (ρ.subgroupMap Q')
      (MonoidHom.subgroupMap_surjective ρ Q')
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hs).trans (C1.blockQ_le L)
  set μ : ↥(blockU L) →* ↥K ⧸ Subgroup.center ↥K := ρ.comp (Subgroup.inclusion hUL) with hμ
  have hμQ : μ.range ≤ Q'.map ρ := by
    rintro _ ⟨u, rfl⟩
    refine ⟨Subgroup.inclusion hUL u, ?_, rfl⟩
    exact (mem_pCore_iff_mem_pCoreOf _).mpr (C1.blockU_le_blockQ hs u.2)
  obtain ⟨-, -, -, β, hβ, hβk, -⟩ := hL
  have hkerμ : μ.ker ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hu1 : π ⟨(u : G), hLK (hUL u.2)⟩ = 1 := hu
    have hc : (⟨(u : G), hLK (hUL u.2)⟩ : ↥K) ∈ Subgroup.center ↥K :=
      (QuotientGroup.eq_one_iff _).mp hu1
    rw [hβk]
    exact mem_blockZ_of_mem_center u.2 hLK (hLK (hUL u.2)) hc
  have h16 : 16 ∣ Nat.card μ.range := by
    have h1 : Nat.card μ.ker * Nat.card μ.range = Nat.card ↥(blockU L) := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have h2 : Nat.card β.ker * 16 = Nat.card ↥(blockU L) := by
      have h3 : Nat.card β.ker * Nat.card β.range = Nat.card ↥(blockU L) := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index]
      have h4 : Nat.card β.range = 16 := by
        rw [MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
        exact card_evenWeight_five
      rwa [h4] at h3
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hkerμ
    have hpos : 0 < Nat.card μ.ker := Nat.card_pos
    have : Nat.card μ.range = 16 * c := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h1, ← h2, hc]
      ring
    exact ⟨c, this⟩
  have h16' : 16 ∣ Nat.card (Q'.map ρ) := h16.trans (Subgroup.card_dvd_of_le hμQ)
  obtain ⟨n, hn⟩ := hQ2.exists_card_eq
  have hn4 : 4 ≤ n := by
    rw [hn] at h16'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp (by simpa using h16')
  exact ⟨ρ.range, n, hn4, by rw [← hcard, hn]⟩

theorem nineSixty_dvd_card_quot (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥K)) : 960 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨H, n, hn, hH⟩ := exists_subgroup_card_quot hs hL hLK hZ
  have h1 : Nat.card H ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := Subgroup.card_subgroup_dvd_card H
  refine dvd_trans ?_ h1
  rw [hH]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨2 ^ m, by rw [pow_add]; ring⟩

omit [Finite G] in
theorem not_isSolvable_of_isAltType_five (hL : IsAltType L 5) : ¬ Group.IsSolvable ↥L := by
  obtain ⟨α, hα, -⟩ := hL
  intro h
  exact not_solvable_alt5 (Group.isSolvable_of_surjective hα)

theorem exists_blockU_K_alt5 (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K) :
    ∃ Ub : Subgroup ↥K, Ub ≠ ⊥ ∧ IsElemAbelian 2 Ub ∧ 16 ≤ Nat.card Ub ∧
      L.subgroupOf K ≤ Subgroup.normalizer (Ub : Set ↥K) ∧
      ¬ Group.IsSolvable ↥(L.subgroupOf K) := by
  have hUK : blockU L ≤ K := (Lin2.OddRank.blockU_le_L hs).trans hLK
  have hcard : Nat.card ((blockU L).subgroupOf K) = Nat.card ↥(blockU L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
  have h16 : 16 ≤ Nat.card ((blockU L).subgroupOf K) := by
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos (sixteen_dvd_card_blockU hL)
  refine ⟨(blockU L).subgroupOf K, ?_, Lin2.OddRank.isElemAbelian_subgroupOf
    (Lin2.OddRank.isElemAbelian_blockU hs), h16, Lin2.OddRank.subgroupOf_le_normalizer, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at h16
    omega
  · intro h
    have : Group.IsSolvable ↥L := by
      have e := Subgroup.subgroupOfEquivOfLe hLK
      exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact not_isSolvable_of_isAltType_five hL this

end CFSG.QuasithinUnique.A5.G3
