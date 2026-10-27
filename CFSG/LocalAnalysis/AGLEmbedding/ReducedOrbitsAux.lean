module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankForm
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem pow_index_eq_one_of_mem_center (hG : commutator G = ⊤) (P : Subgroup G)
    [IsMulCommutative P] {g : G} (hg : g ∈ Subgroup.center G) : g ^ P.index = 1 := by
  let _ : CommGroup P := IsMulCommutative.instCommGroup
  have hker : g ∈ (MonoidHom.transfer (MonoidHom.id P)).ker :=
    Abelianization.commutator_subset_ker _ (hG ▸ Subgroup.mem_top g)
  rw [MonoidHom.mem_ker, MonoidHom.transfer_eq_pow _ g fun k g₀ _ => ?_] at hker
  · exact congrArg Subtype.val hker
  · rw [mul_assoc, ← Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hg k) g₀,
      inv_mul_cancel_left]

theorem eq_one_of_mem_center_of_pow_eq_one {p : ℕ} [Fact p.Prime] (hG : commutator G = ⊤)
    (P : Sylow p G) [IsMulCommutative (P : Subgroup G)] {g : G} (hg : g ∈ Subgroup.center G)
    {k : ℕ} (hk : g ^ p ^ k = 1) : g = 1 := by
  have hcop : (p ^ k).Coprime (P : Subgroup G).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one (pow_index_eq_one_of_mem_center hG P hg)))

theorem mem_normalizer_of_conj_map_le {H : Subgroup G} {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hg
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hg ⟨x, hx, rfl⟩, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hxy : y = x := by simpa using hyx
  exact hxy ▸ hy

theorem succ_le_pRank_of_isElemAbelian_of_mem_centralizer {p : ℕ} (hp : p.Prime)
    {E H : Subgroup G} (hE : IsElemAbelian p E) {k : ℕ} (hcard : Nat.card E = p ^ k) {t : G}
    (htp : t ^ p = 1) (htE : t ∉ E) (htC : t ∈ Subgroup.centralizer (E : Set G))
    (hEH : E ≤ H) (htH : t ∈ H) : k + 1 ≤ Open.pRank p H := by
  have hEt : E ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr htC)
  have hJ := elementary_abelian_sup_of_commuting p hE (isElemAbelian_zpowers htp) hEt
  by_contra hlt
  have heq := elementary_subgroup_eq_of_rank_bound p hp hJ le_sup_left k hcard
    (by have := PreuniquenessRankFour.Helpers.pRank_mono p hp
          (sup_le hEH (Subgroup.zpowers_le.mpr htH)); omega)
  exact htE (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem two_le_pRank_of_commute_of_not_mem_zpowers {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    {a b : G} (ha : orderOf a = p) (hb : b ^ p = 1) (hba : b ∉ Subgroup.zpowers a)
    (hab : Commute a b) (haH : a ∈ H) (hbH : b ∈ H) : 2 ≤ Open.pRank p H :=
  succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp
    (isElemAbelian_zpowers (ha ▸ pow_orderOf_eq_one a)) (k := 1)
    (by rw [Nat.card_zpowers, ha, pow_one]) hb hba
    (Subgroup.mem_centralizer_iff.mpr fun x hx => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hab.zpow_left n).eq)
    (Subgroup.zpowers_le.mpr haH) hbH

theorem two_le_pRank_of_isPGroup_not_isCyclic {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {T : Subgroup G} (hT : IsPGroup p T) (hnc : ¬ IsCyclic T) : 2 ≤ Open.pRank p T := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p T) := ⟨hT⟩
  obtain ⟨S, -, hScard, hSelem⟩ := lemma_4_5_a hodd hnc
  refine le_csSup (pRank_bddAbove p hp T) ⟨S.map T.subtype, Subgroup.map_subtype_le S,
    elementary_abelian_map p ⟨hSelem.toIsMulCommutative,
      fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩ _, ?_⟩
  rw [Subgroup.card_map_of_injective T.subtype_injective, hScard]

theorem exists_mem_centralizer_orderOf_eq {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hT : IsPGroup p T) (hne : T ≠ ⊥) :
    ∃ c ∈ T, orderOf c = p ∧ c ∈ Subgroup.centralizer (T : Set G) := by
  have : Nontrivial T := T.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨n, hn, hcard⟩ :=
    (hT.to_subgroup (Subgroup.center T)).nontrivial_iff_card.mp hT.center_nontrivial
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ dvd_pow_self p hn.ne')
  refine ⟨((c : T) : G), (c : T).2, by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc], ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩)

theorem two_le_pRank_inf_centralizer_zpowers {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {T : Subgroup G} (hT : IsPGroup p T) (hnc : ¬ IsCyclic T) {t : G} (htT : t ∈ T)
    (ht : orderOf t = p) :
    2 ≤ Open.pRank p (T ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : T ≠ ⊥ := fun hbot =>
    hp.one_lt.ne' (ht ▸ orderOf_eq_one_iff.mpr (Subgroup.mem_bot.mp (hbot ▸ htT)))
  obtain ⟨c, hcT, hc, hcC⟩ := exists_mem_centralizer_orderOf_eq hT hne
  have htC : t ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance (Subgroup.mem_zpowers t)
  by_cases hct : c ∈ Subgroup.zpowers t
  ·
    have hzeq : Subgroup.zpowers c = Subgroup.zpowers t :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hct)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hc, ht])
    have hTC : T ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
      rw [← hzeq, Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hcC
    rw [inf_eq_left.mpr hTC]
    exact two_le_pRank_of_isPGroup_not_isCyclic hp hodd hT hnc
  · exact two_le_pRank_of_commute_of_not_mem_zpowers hp ht (hc ▸ pow_orderOf_eq_one c) hct
      (Subgroup.mem_centralizer_iff.mp hcC t htT) ⟨htT, htC⟩
      ⟨hcT, Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htT) hcC⟩

theorem le_centralizer_of_component_ne {L₁ L₂ : Subgroup G} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) : L₁ ≤ Subgroup.centralizer (L₂ : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne)

end CFSG.AGLEmbedding
