module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Parab
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Levi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

theorem Ree.card_dvd_mul_card_of_le_sup {G : Type*} [Group G] {P L V : Subgroup G}
    (hLP : L ≤ P) (hVP : V ≤ P) (hLV : L ≤ normalizer (V : Set G)) (hP : P ≤ L ⊔ V) :
    Nat.card P ∣ Nat.card L * Nat.card V := by
  have h1 := Subgroup.card_mul_index (L.subgroupOf P)
  have h2 : Nat.card (L.subgroupOf P) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv
  rw [← h1, h2]
  exact mul_dvd_mul_left _
    (CFSG.LieType.SeitzGeneration.index_subgroupOf_dvd_card_of_le_sup hLP hVP hLV hP)


namespace Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.SeitzGeneration
open CFSG.LieType.Ree.LargeReeInvolution
  (rankOneGroupOne rankOneGroupTwo isSimpleGroup_rankOneGroupOne isSimpleGroup_rankOneGroupTwo
    reeFixedOrbitComplementUnipotent_le)
open CFSG.LieType.Ree.LargeReeCover
  (f4i pairedTorusHom pairedTorusHom_apply torusPair torusPair_apply torusPair_mem_reeGamma)
open CFSG.RankThree.LargeReeOrder (card_reeFixedBorel card_reeFixedTorus torusPair_injective)
open CFSG.QuasithinUnique.Setup.X6 (large_Ree_opposite_simple_blocks_generate_rank_one_model)

section Ree

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

instance instFiniteReeGamma : Finite ↥(F4.reeGamma K a) := by
  haveI : Finite (ModGL F4.tag K) := finite_modGL (τ := F4.tag) (K := K)
  exact Subtype.finite

theorem two_le_pRank_reeGamma_of_dvd_sub_one {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hd : ℓ ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup ↥(F4.reeGamma K a)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  have hdvd : ℓ ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hd
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  let φ : Kˣ × Kˣ →* ↥(F4.reeGamma K a) :=
    (torusPair a).codRestrict _ (torusPair_mem_reeGamma a hK')
  have hφ : Function.Injective φ := fun x y h => torusPair_injective hK (congrArg Subtype.val h)
  have hζ1 : ζ ≠ 1 := fun h => hℓ.one_lt.ne' (hζo.symm.trans (by rw [h, orderOf_one]))
  have hord : ∀ x : Kˣ × Kˣ, orderOf (φ x) = orderOf x := fun x => orderOf_injective φ hφ x
  refine CFSG.GroupTheory.two_le_pRank_of_commute (x := φ (ζ, 1)) (y := φ (1, ζ))
    (Subgroup.mem_top _) (Subgroup.mem_top _) ?_ ?_ ((Commute.all _ _).map φ) ?_
  · rw [hord, Prod.orderOf]
    simp [hζo]
  · rw [hord, Prod.orderOf]
    simp [hζo]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← map_zpow] at hk
    have h2 := congrArg Prod.snd (hφ hk)
    simp at h2
    exact hζ1 h2.symm

theorem eq_borel_or_eq_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A : Subgroup (ModGL F4.tag K)} (hBA : F4.reeFixedBorel K a ≤ A)
    (hAΓ : A ≤ F4.reeGamma K a) (hne : A ≠ F4.reeGamma K a) :
    A = F4.reeFixedBorel K a ∨ ∃ j, A = F4.reeLocalParabolic K a j := by
  by_cases hAB : A = F4.reeFixedBorel K a
  · exact Or.inl hAB
  · right
    have hlt : F4.reeFixedBorel K a < A := lt_of_le_of_ne hBA (Ne.symm hAB)
    obtain ⟨j, hj⟩ := exists_canonicalRep_mem_of_lt hlt hAΓ
    obtain ⟨i, hi⟩ := exists_le_reeLocalParabolic_of_proper hK hBA hAΓ hne
    have hPj : F4.reeLocalParabolic K a j ≤ A := reeLocalParabolic_le_of_mem hBA hj
    refine ⟨j, le_antisymm ?_ hPj⟩
    have hji : j = i := by
      have hn := hi hj
      rw [← reeParabolic_singleton i, canonicalRep_mem_reeParabolic_iff] at hn
      exact Set.mem_singleton_iff.1 hn
    rw [hji]
    exact hi

theorem isSimpleGroup_reeLocalBlock (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) :
    IsSimpleGroup ↥(F4.reeLocalBlock K a j) ∧
      ∃ x y : ↥(F4.reeLocalBlock K a j), x * y ≠ y * x := by
  obtain ⟨hM0, hM1⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hj
  interval_cases j
  · rw [show F4.reeLocalBlock K a ⟨0, hj⟩ = rankOneGroupOne K a from hM0.1]
    exact isSimpleGroup_rankOneGroupOne ha hK
  · rw [show F4.reeLocalBlock K a ⟨1, hj⟩ = rankOneGroupTwo K a from hM1.1]
    exact isSimpleGroup_rankOneGroupTwo ha hK

theorem dvd_card_reeLocalBlock (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hd : ℓ ∣ Nat.card K - 1) (j : Fin F4.fixedOrbitCount) :
    ℓ ∣ Nat.card (F4.reeLocalBlock K a j) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd : ℓ ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hd
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hord : ∀ x : Kˣ × Kˣ, orderOf (torusPair a x) = orderOf x := fun x =>
    orderOf_injective (torusPair a) (torusPair_injective hK) x
  obtain ⟨hM0, hM1⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have key : ∀ x : Kˣ × Kˣ, orderOf x = ℓ → torusPair a x ∈ F4.reeLocalBlock K a j →
      ℓ ∣ Nat.card (F4.reeLocalBlock K a j) := by
    intro x hx hmem
    have h1 : orderOf (⟨torusPair a x, hmem⟩ : ↥(F4.reeLocalBlock K a j)) = ℓ := by
      rw [Subgroup.orderOf_mk, hord, hx]
    rw [← h1]
    exact orderOf_dvd_natCard _
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hj
  interval_cases j
  · refine key (ζ, 1) (by rw [Prod.orderOf]; simp [hζo]) ?_
    refine hM0.2.2 (MonoidHom.mem_range.2 ⟨ζ, ?_⟩)
    simp [pairedTorusHom_apply, torusPair_apply, torusElt_one]
  · refine key (1, ζ) (by rw [Prod.orderOf]; simp [hζo]) ?_
    refine hM1.2.2 (MonoidHom.mem_range.2 ⟨ζ, ?_⟩)
    simp [pairedTorusHom_apply, torusPair_apply, torusElt_one]

theorem dvd_card_reeLocalBlock_of_dvd_card_parabolic (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (j : Fin F4.fixedOrbitCount) (h : p ∣ Nat.card (F4.reeLocalParabolic K a j)) :
    p ∣ Nat.card (F4.reeLocalBlock K a j) := by
  have hBP := (reeFixedBorel_lt_reeLocalParabolic (K := K) (a := a) (t := F4) j).le
  have hHP : F4.reeFixedTorus K a ≤ F4.reeLocalParabolic K a j :=
    reeFixedTorus_le_reeFixedBorel.trans hBP
  have hLP : F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a ≤ F4.reeLocalParabolic K a j :=
    sup_le (reeLocalBlock_le j) hHP
  have hVP : F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeLocalParabolic K a j :=
    (reeFixedOrbitComplementUnipotent_le j).trans
      (reeFixedPosUnipotent_le_reeFixedBorel.trans hBP)
  have h1 := card_dvd_mul_card_of_le_sup hLP hVP
    (hLP.trans (reeLocalParabolic_le_normalizer_complement j)) (reeLocalParabolic_le_sup_levi j)
  have h2 := card_dvd_mul_card_of_le_sup (P := F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a)
    (L := F4.reeFixedTorus K a) (V := F4.reeLocalBlock K a j) le_sup_right le_sup_left
    (reeFixedTorus_le_normalizer_reeLocalBlock j) (sup_comm _ _).le
  have h3 : p ∣ Nat.card (F4.reeFixedTorus K a) * Nat.card (F4.reeLocalBlock K a j) *
      Nat.card (F4.reeFixedOrbitComplementUnipotent K a j) :=
    h.trans (h1.trans (mul_dvd_mul_right h2 _))
  rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h5
  · rcases (Nat.Prime.dvd_mul hp).1 h4 with h6 | h7
    · rw [card_reeFixedTorus hK] at h6
      exact absurd (hp.dvd_of_dvd_pow h6) hpq
    · exact h7
  · exact absurd h5 (CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (isPGroup_reeFixedOrbitComplementUnipotent j) hp hp2)

theorem leviAt_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {K₀ : Subgroup ↥(F4.reeGamma K a)}
    (hB : F4.reeFixedBorel K a ≤ K₀.map (F4.reeGamma K a).subtype) (p : ℕ) : LeviAt K₀ p := by
  intro _ hp h5 hrank _ hne hsyl
  classical
  have hK8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hpq : ¬ p ∣ Nat.card K - 1 := fun h => by
    have := two_le_pRank_reeGamma_of_dvd_sub_one hp hK h
    omega
  have hpK : p ∣ Nat.card K₀ := dvd_card_of_sylow_hyp hp hsyl
  have hcard : Nat.card (K₀.map (F4.reeGamma K a).subtype) = Nat.card K₀ :=
    Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective
  have hne' : K₀.map (F4.reeGamma K a).subtype ≠ F4.reeGamma K a := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL F4.tag K) ∈ K₀.map (F4.reeGamma K a).subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  rcases eq_borel_or_eq_reeLocalParabolic hK hB (Subgroup.map_subtype_le K₀) hne' with h | ⟨j, hj⟩
  ·
    exfalso
    have hpB : p ∣ Nat.card (F4.reeFixedBorel K a) := by
      rw [← h, hcard]
      exact hpK
    rw [card_reeFixedBorel hK] at hpB
    rcases (Nat.Prime.dvd_mul hp).1 hpB with h1 | h2
    · have h3 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h1)
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3
      omega
    · exact hpq (by rw [hK]; exact hp.dvd_of_dvd_pow h2)
  ·
    have hpP : p ∣ Nat.card (F4.reeLocalParabolic K a j) := by
      rw [← hj, hcard]
      exact hpK
    have hpM : p ∣ Nat.card (F4.reeLocalBlock K a j) :=
      dvd_card_reeLocalBlock_of_dvd_card_parabolic hK hp (by omega) hpq j hpP
    obtain ⟨f, hf, hfd⟩ := Nat.exists_prime_and_dvd (n := Nat.card K - 1) (by omega)
    have hf2 : f ≠ 2 := by
      rintro rfl
      omega
    have hfr := two_le_pRank_reeGamma_of_dvd_sub_one hf hK hfd
    have hfM := dvd_card_reeLocalBlock ha hK hf hfd j
    set M : Subgroup (ModGL F4.tag K) := F4.reeLocalBlock K a j
    have hMΓ : M ≤ F4.reeGamma K a := reeLocalBlock_le_reeGamma j
    have hMK : M ≤ K₀.map (F4.reeGamma K a).subtype := by
      rw [hj]
      exact reeLocalBlock_le j
    set Y : Subgroup ↥(F4.reeGamma K a) := M.subgroupOf (F4.reeGamma K a)
    let eY : ↥Y ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMΓ
    obtain ⟨hMsimple, x, y, hxy⟩ := isSimpleGroup_reeLocalBlock ha hK j
    haveI : IsSimpleGroup ↥M := hMsimple
    haveI : IsSimpleGroup ↥Y := eY.isSimpleGroup
    have hnab : ∃ u v : ↥Y, u * v ≠ v * u := by
      refine ⟨eY.symm x, eY.symm y, fun h => hxy ?_⟩
      have := congrArg eY h
      simpa using this
    have hsec : S622IsSimpleSection Y ⊥ := by
      have := S622IsSimpleSection.of_surjective (A := ↥(F4.reeGamma K a)) (Y := Y)
        (MonoidHom.id ↥Y) Function.surjective_id hnab
      rwa [MonoidHom.ker_id, Subgroup.map_bot] at this
    have hYK₀ : Y ≤ K₀ := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := hMK (show (z : ModGL F4.tag K) ∈ M from hz)
      rwa [← Subtype.ext hwz]
    have hcardY : Nat.card ↥Y = Nat.card ↥M := Nat.card_congr eY.toEquiv
    refine ⟨f, Y, ⊥, hf, hf2, ?_, hfr, hYK₀, hsec, ?_, ?_, ?_⟩
    · rintro rfl
      omega
    · rw [Subgroup.relIndex_bot_left, hcardY]
      exact hfM
    · rw [Subgroup.relIndex_bot_left, hcardY]
      exact hpM
    · rw [Subgroup.card_bot]
      exact hp.not_dvd_one

theorem leviSubAt_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    LeviSubAt ↥(F4.reeGamma K a) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨T₀, hT₀⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => leviAt_reeGamma ha hK ?_ p
  have hB : (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) ≤
      Subgroup.normalizer ((T₀ : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hT₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1
      (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hb)) x
  have hBK₀ := hB.trans hN
  exact fun x hx => ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩, hBK₀ (Subgroup.mem_subgroupOf.2 hx), rfl⟩

end Ree

end Ree

theorem leviSubAt_twistedF4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ReeTitsModel S .twistedF4 2 f) : LeviSubAt S := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hm
  exact LeviSubAt.of_mulEquiv e (Ree.leviSubAt_reeGamma ha hK)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
