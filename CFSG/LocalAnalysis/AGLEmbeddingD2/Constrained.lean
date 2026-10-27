module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ : Subgroup X}

theorem le_pRank_of_isElemAbelian_of_pow_le_card (hp : p.Prime) {E H : Subgroup X}
    (hE : IsElemAbelian p E) (hEH : E ≤ H) {n : ℕ} (hn : p ^ n ≤ Nat.card E) :
    n ≤ Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (elementary_isPGroup p E hE)
  have hnk : n ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hk ▸ hn)
  exact hnk.trans (le_csSup (pRank_bddAbove p hp H) ⟨E, hEH, hE, hk⟩)

theorem isElemAbelian_sup_zpowers (hp : p.Prime) {J : Subgroup X} (hJ : IsElemAbelian p J) {t : X}
    (ht : t ^ p = 1) (htC : t ∈ Subgroup.centralizer (J : Set X)) (htJ : t ∉ J) :
    IsElemAbelian p (J ⊔ Subgroup.zpowers t) ∧
      p * Nat.card J ≤ Nat.card (J ⊔ Subgroup.zpowers t : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hJt : IsElemAbelian p (J ⊔ Subgroup.zpowers t) :=
    elementary_abelian_sup_of_commuting p hJ (isElemAbelian_zpowers ht)
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr htC))
  refine ⟨hJt, prime_mul_card_le_of_lt (elementary_isPGroup p _ hJt)
    (lt_of_le_of_ne le_sup_left fun heq => htJ ?_)⟩
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem two_le_pRank_of_commute (hp : p.Prime) {H : Subgroup X} {a b : X} (ha : orderOf a = p)
    (hb : orderOf b = p)
    (hab : b ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X))
    (hbn : b ∉ Subgroup.zpowers a) (haH : a ∈ H) (hbH : b ∈ H) : 2 ≤ Open.pRank p H := by
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  obtain ⟨hE, hcard⟩ := isElemAbelian_sup_zpowers hp (isElemAbelian_zpowers hap) hbp hab hbn
  rw [Nat.card_zpowers, ha] at hcard
  exact le_pRank_of_isElemAbelian_of_pow_le_card hp hE
    (sup_le (Subgroup.zpowers_le.mpr haH) (Subgroup.zpowers_le.mpr hbH))
    (by rw [pow_two]; exact hcard)

theorem exists_mem_centralizer_of_normal {p : ℕ} [Fact p.Prime] {R T : Subgroup X}
    (hR : IsPGroup p R) (hTR : T ≤ R) (hTn : R ≤ Subgroup.normalizer (T : Set X)) (hT : T ≠ ⊥) :
    ∃ z ∈ T, z ∈ Subgroup.centralizer (R : Set X) ∧ orderOf z = p := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hn : (T.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTR).mpr hTn
  have hne : T.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hT
    rw [← Subgroup.map_subgroupOf_eq_of_le hTR, hbot, Subgroup.map_bot]
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hWp : IsPGroup p (T.subgroupOf R ⊓ Subgroup.center R : Subgroup R) :=
    (hR.comap_subtype (K := R)).to_le (by
      intro x _
      exact Subgroup.mem_comap.mpr x.property)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hW (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  have hdvd : p ∣ Nat.card (T.subgroupOf R ⊓ Subgroup.center R : Subgroup R) := by
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((x : R) : X), x.property.1, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hc := Subgroup.mem_center_iff.mp x.property.2 ⟨r, hr⟩
    exact congrArg Subtype.val hc
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

namespace D2Reduced

theorem mem_A_of_mem_center (h : D2Reduced p X R A X₀) {z : X} (hzR : z ∈ (R : Subgroup X))
    (hzc : z ∈ Subgroup.centralizer ((R : Subgroup X) : Set X)) (hz : orderOf z = p) : z ∈ A := by
  by_contra hzA
  have hzA' : z ∈ Subgroup.centralizer (A : Set X) :=
    Subgroup.centralizer_le (show (A : Set X) ⊆ (R : Subgroup X) from h.A_le) hzc
  have h3 := three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer h.prime h.elem h.card_A hz hzA
    hzA' h.A_le hzR
  have h2 := h.pRank_eq
  omega

theorem normalizer_le_of_normal (h : D2Reduced p X R A X₀) {T : Subgroup X}
    (hTR : T ≤ (R : Subgroup X)) (hTn : (R : Subgroup X) ≤ Subgroup.normalizer (T : Set X))
    (hT : T ≠ ⊥) : Subgroup.normalizer (T : Set X) ≤ X₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hrank : 2 ≤ Open.pRank p T
  · exact h.normalizer_le_of_rank T (hTR.trans h.sylow_le) (R.isPGroup'.to_le hTR) hrank
  obtain ⟨z, hzT, hzc, hz⟩ := exists_mem_centralizer_of_normal R.isPGroup' hTR hTn hT
  have hzA := h.mem_A_of_mem_center (hTR hzT) hzc hz
  have hZ1 : Subgroup.zpowers z ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    rintro rfl
    rw [orderOf_one] at hz
    exact hp.one_lt.ne hz
  refine le_trans ?_ (h.normalizer_le_of_le_A _ (Subgroup.zpowers_le.mpr hzA) hZ1)
  intro g hg
  have hwT : g * z * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg z).mp hzT
  have hw : orderOf (g * z * g⁻¹) = p := by
    have hinj := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hinj
    rw [hinj, hz]
  have hwz : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    by_contra hwz
    apply hrank
    refine two_le_pRank_of_commute hp hz hw ?_ hwz hzT hwT
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : z * (g * z * g⁻¹) = (g * z * g⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.mp hzc _ (hTR hwT)).symm
    exact (Commute.zpow_left hc k).eq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwz
    change g * z ^ k * g⁻¹ ∈ Subgroup.zpowers z
    rw [show g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k by
      rw [conj_zpow]]
    exact Subgroup.zpow_mem _ hwz k
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem pCore_eq_bot (h : D2Reduced p X R A X₀) : CFSG.pCore p X = ⊥ := by
  by_contra hne
  have : Fact p.Prime := ⟨h.prime⟩
  have hOn : (CFSG.pCore p X).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  have hOR : CFSG.pCore p X ≤ R :=
    sSup_le fun K ⟨hKn, hKp⟩ => @IsPGroup.le_sylow_of_normal _ _ _ K hKn hKp R
  have hN := h.normalizer_le_of_normal hOR
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hOn]; exact le_top) hne
  rw [Subgroup.normalizer_eq_top_iff.mpr hOn] at hN
  exact h.ne_top (top_le_iff.mp hN)

end D2Reduced

end CFSG.AGLEmbeddingD2
