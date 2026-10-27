module

public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type*} [Group G]

theorem normal_map_center {K : Subgroup G} (hKn : K.Normal) :
    ((Subgroup.center K).map K.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hn
  refine ⟨⟨g * y * g⁻¹, hKn.conj_mem y y.2 g⟩, Subgroup.mem_center_iff.mpr fun k => ?_, rfl⟩
  have hk : g⁻¹ * (k : G) * g ∈ K := by simpa using hKn.conj_mem k k.2 g⁻¹
  have hyk : g⁻¹ * (k : G) * g * y = y * (g⁻¹ * k * g) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨_, hk⟩)
  apply Subtype.ext
  show (k : G) * (g * y * g⁻¹) = g * y * g⁻¹ * k
  calc (k : G) * (g * y * g⁻¹) = g * (g⁻¹ * k * g * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [hyk]
    _ = g * y * g⁻¹ * k := by group

theorem center_ne_bot_of_mem {p : ℕ} (hp : p.Prime) {z : G} (hz : z ∈ Subgroup.center G)
    (hzp : orderOf z = p) {K : Subgroup G} (hzK : z ∈ K) : Subgroup.center K ≠ ⊥ := by
  intro hbot
  have hzZ : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hz k)
  rw [hbot, Subgroup.mem_bot] at hzZ
  have hz1 : z = 1 := congrArg Subtype.val hzZ
  rw [hz1, orderOf_one] at hzp
  exact hp.one_lt.ne hzp

theorem mem_zpowers_of_orderOf_eq_of_isCyclic [Finite G] {Z : Subgroup G} [IsCyclic Z] {c z : G}
    (hc : c ∈ Z) (hz : z ∈ Z) (hcz : orderOf c = orderOf z) : c ∈ Subgroup.zpowers z := by
  have heq : Subgroup.zpowers (⟨c, hc⟩ : Z) = Subgroup.zpowers ⟨z, hz⟩ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hcz])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers (⟨c, hc⟩ : Z))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem normal_range_mulAutConj (G : Type*) [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal := by
  refine ⟨fun a ha σ => ?_⟩
  obtain ⟨g, rfl⟩ := ha
  refine ⟨σ g, ?_⟩
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem exists_pow_mem_of_mem_sup {p : ℕ} {I S : Subgroup G} [I.Normal] (hS : IsPGroup p S)
    {a : G} (ha : a ∈ I ⊔ S) : ∃ k : ℕ, a ^ p ^ k ∈ I := by
  have hmap : (I ⊔ S).map (QuotientGroup.mk' I) = S.map (QuotientGroup.mk' I) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  obtain ⟨k, hk⟩ := hS.map (QuotientGroup.mk' I) ⟨_, hmap ▸ Subgroup.mem_map_of_mem _ ha⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact congrArg Subtype.val hk

theorem le_sylow_sup_of_pow_mem [Finite G] {p : ℕ} [Fact p.Prime] (R : Sylow p G)
    {N W : Subgroup G} [N.Normal] [W.Normal] (hW : ∀ w ∈ W, ∃ k : ℕ, w ^ p ^ k ∈ N) :
    W ≤ (R : Subgroup G) ⊔ N := by
  have hWp : IsPGroup p (W.map (QuotientGroup.mk' N)) := by
    rintro ⟨_, w, hw, rfl⟩
    obtain ⟨k, hk⟩ := hW w hw
    refine ⟨k, Subtype.ext ?_⟩
    change QuotientGroup.mk' N w ^ p ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hle := hWp.le_sylow_of_normal (R.mapSurjective (QuotientGroup.mk'_surjective N))
  rw [Sylow.coe_mapSurjective] at hle
  calc W ≤ (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := Subgroup.le_comap_map _ W
    _ ≤ ((R : Subgroup G).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
      Subgroup.comap_mono hle
    _ = N ⊔ R := QuotientGroup.comap_map_mk' N R
    _ = (R : Subgroup G) ⊔ N := sup_comm _ _

theorem comap_range_conj_le {K : Subgroup G} [K.Normal] {H : Subgroup G} (hKH : K ≤ H)
    (hCH : Subgroup.centralizer (K : Set G) ≤ H) :
    (MulAut.conj : K →* MulAut K).range.comap (MulAut.conjNormal (H := K)) ≤ H := by
  rintro x ⟨k, hk⟩
  have hxk : x * (k : G)⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    rw [← ker_conjNormal_eq_centralizer, MonoidHom.mem_ker, map_mul, map_inv,
      MulAut.conjNormal_val, hk, mul_inv_cancel]
  simpa using H.mul_mem (hCH hxk) (hKH k.2)

theorem exists_map_of_exists_centralizer {p : ℕ} {K : Subgroup G} {T : Subgroup K}
    (hA : ∃ A : Subgroup K, A ≤ T ⊓ Subgroup.centralizer (T : Set K) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ 2) :
    ∃ A : Subgroup G, A ≤ T.map K.subtype ∧
      A ≤ Subgroup.centralizer ((T.map K.subtype : Subgroup G) : Set G) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ 2 := by
  obtain ⟨A, hAT, hA, hAcard⟩ := hA
  refine ⟨A.map K.subtype, Subgroup.map_mono (hAT.trans inf_le_left), ?_,
    elementary_abelian_map p hA _, by rw [Subgroup.card_map_of_injective K.subtype_injective,
      hAcard]⟩
  rintro _ ⟨a, ha, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨t, ht, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hAT ha).2 t ht)

theorem pow_and_pRank_map [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G} {T : Subgroup K}
    (hT : (∀ t ∈ T, t ^ p = 1) ∧ Open.pRank p T ≤ 3) :
    (∀ t ∈ T.map K.subtype, t ^ p = 1) ∧ Open.pRank p (T.map K.subtype) ≤ 3 := by
  refine ⟨?_, by rw [pRank_map_of_injective p hp K.subtype K.subtype_injective]; exact hT.2⟩
  rintro _ ⟨t, ht, rfl⟩
  simpa using congrArg Subtype.val (hT.1 t ht)

theorem exists_map_of_exists_normalizer {p : ℕ} {K : Subgroup G} {T : Subgroup K}
    (hA : ∃ A : Subgroup K, A ≤ T ∧ T ≤ Subgroup.normalizer (A : Set K) ∧ IsElemAbelian p A ∧
      p ^ (p + 1) ≤ Nat.card A) :
    ∃ A : Subgroup G, A ≤ T.map K.subtype ∧
      T.map K.subtype ≤ Subgroup.normalizer (A : Set G) ∧ IsElemAbelian p A ∧
      p ^ (p + 1) ≤ Nat.card A := by
  obtain ⟨A, hAT, hTN, hA, hAcard⟩ := hA
  exact ⟨A.map K.subtype, Subgroup.map_mono hAT,
    (Subgroup.map_mono hTN).trans (Subgroup.le_normalizer_map _), elementary_abelian_map p hA _,
    by rwa [Subgroup.card_map_of_injective K.subtype_injective]⟩

end CFSG.AGLEmbedding
