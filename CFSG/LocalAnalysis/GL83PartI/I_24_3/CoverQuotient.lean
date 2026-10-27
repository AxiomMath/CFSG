module

public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration

public section

namespace GL83.I243.Cover

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

variable {K L : Type*} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ}

omit [Finite K] [Finite L] in
theorem eq_one_of_pow_eq_one_of_mem_ker {ρ : K →* L} (hcop : Nat.Coprime p (Nat.card ρ.ker))
    {n : K} (hn : n ∈ ρ.ker) {a : ℕ} (h : n ^ p ^ a = 1) : n = 1 := by
  have h1 : orderOf n ∣ p ^ a := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf n ∣ Nat.card ρ.ker := Subgroup.orderOf_dvd_natCard ρ.ker hn
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left a hcop)) h2)

omit [Finite L] in
theorem eq_one_of_mem_isPGroup_of_mem_ker {ρ : K →* L}
    (hcop : Nat.Coprime p (Nat.card ρ.ker)) {T : Subgroup K} (hT : IsPGroup p T) {t : K}
    (htT : t ∈ T) (ht : t ∈ ρ.ker) : t = 1 := by
  obtain ⟨a, ha⟩ := isPGroup_iff_exists_pow_pow_eq_one.1 hT
  exact eq_one_of_pow_eq_one_of_mem_ker hcop ht (a := a) (by
    simpa using congrArg Subtype.val (ha ⟨t, htT⟩))

theorem pRank_map_eq_of_ker (hp : p.Prime) (ρ : K →* L) {T U : Subgroup K} (hUT : U ≤ T)
    (hT : ∀ t ∈ T, ρ t = 1 → t = 1) : pRank p (U.map ρ) = pRank p U := by
  have hinj : Function.Injective (ρ.comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hT t t.2 ht)
  have h1 := pRank_map_of_injective p hp (ρ.comp T.subtype) hinj (U.subgroupOf T)
  have h2 := pRank_map_of_injective p hp T.subtype T.subtype_injective (U.subgroupOf T)
  have h3 : (U.subgroupOf T).map T.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUT
  rw [h3] at h2
  rw [h2, ← h1, ← Subgroup.map_map, h3]

theorem map_weakCore_le_weakCore_map (hp : p.Prime) (ρ : K →* L) {T : Subgroup K}
    (hT : ∀ t ∈ T, ρ t = 1 → t = 1) : (GLBWeakCore p T).map ρ ≤ GLBWeakCore p (T.map ρ) := by
  rw [Subgroup.map_le_iff_le_comap, weakCore_le_iff]
  intro Q hQT hQ2 hQ3
  rw [← Subgroup.map_le_iff_le_comap]
  have hmap : (Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set K))).map ρ ≤
      Q.map ρ ⊔ (T.map ρ ⊓ Subgroup.centralizer ((Q.map ρ : Subgroup L) : Set L)) := by
    rw [Subgroup.map_sup]
    refine sup_le_sup_left ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)) _
    rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image _ ρ
  refine (Subgroup.le_normalizer_map ρ).trans
    (normalizer_le_weakCore p (Subgroup.map_mono hQT) ?_ ?_)
  · rwa [pRank_map_eq_of_ker hp ρ hQT hT]
  · refine le_trans ?_ (pRank_mono p hp hmap)
    rwa [pRank_map_eq_of_ker hp ρ (sup_le hQT inf_le_left) hT]

theorem weakCore_map_le_map_weakCore [Fact p.Prime] (ρ : K →* L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (hcop : Nat.Coprime p (Nat.card ρ.ker))
    {T : Subgroup K} (hT : IsPGroup p T) :
    GLBWeakCore p (T.map ρ) ≤ (GLBWeakCore p T).map ρ := by
  have hp : p.Prime := Fact.out
  have hTker : ∀ t ∈ T, ρ t = 1 → t = 1 := fun t htT ht =>
    eq_one_of_mem_isPGroup_of_mem_ker hcop hT htT ht
  obtain ⟨a, ha⟩ := isPGroup_iff_exists_pow_pow_eq_one.1 hT
  have hexp : ∀ t ∈ T, t ^ p ^ a = 1 := fun t ht => by
    simpa using congrArg Subtype.val (ha ⟨t, ht⟩)
  rw [weakCore_le_iff]
  intro Qb hQbT hQb2 hQb3
  obtain ⟨Q, hQT, hQmap⟩ : ∃ Q : Subgroup K, Q ≤ T ∧ Q.map ρ = Qb := by
    refine ⟨T ⊓ Qb.comap ρ, inf_le_left, le_antisymm ?_ ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hq.2
    · intro x hx
      obtain ⟨t, htT, rfl⟩ := hQbT hx
      exact ⟨t, ⟨htT, hx⟩, rfl⟩
  have hQ : ∀ q ∈ Q, ρ q ∈ Qb := fun q hq => hQmap ▸ Subgroup.mem_map_of_mem ρ hq
  have hrankQ : 2 ≤ pRank p Q := by
    rw [← pRank_map_eq_of_ker hp ρ hQT hTker, hQmap]
    exact hQb2
  have hcent : ∀ x ∈ T, ρ x ∈ Subgroup.centralizer (Qb : Set L) →
      x ∈ Subgroup.centralizer (Q : Set K) := by
    intro x hxT hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro q hq
    have h1 : ρ q * ρ x = ρ x * ρ q := hx (ρ q) (hQ q hq)
    have h2 : q * x * (x * q)⁻¹ = 1 := hTker _
      (T.mul_mem (T.mul_mem (hQT hq) hxT) (T.inv_mem (T.mul_mem hxT (hQT hq))))
      (by rw [map_mul, map_mul, map_inv, map_mul, h1, mul_inv_cancel])
    exact mul_inv_eq_one.1 h2
  have hWT : Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set K)) ≤ T := sup_le hQT inf_le_left
  have hWmap : Qb ⊔ (T.map ρ ⊓ Subgroup.centralizer (Qb : Set L)) ≤
      (Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set K))).map ρ := by
    refine sup_le (hQmap.symm.le.trans (Subgroup.map_mono le_sup_left)) ?_
    rintro _ ⟨⟨x, hxT, rfl⟩, hxC⟩
    exact ⟨x, Subgroup.mem_sup_right ⟨hxT, hcent x hxT hxC⟩, rfl⟩
  have hrankW : 3 ≤ pRank p (Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set K))) :=
    hQb3.trans ((pRank_mono p hp hWmap).trans (pRank_map_eq_of_ker hp ρ hWT hTker).le)
  have hnorm : ∀ y : K, ρ y ∈ Subgroup.normalizer (Qb : Set L) → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    intro y hy q hq
    have h1 : ρ (y * q * y⁻¹) ∈ Qb := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hy (ρ q)).1 (hQ q hq)
    obtain ⟨q', hq', hq'eq⟩ : ρ (y * q * y⁻¹) ∈ Q.map ρ := hQmap ▸ h1
    obtain ⟨n, hnker, hyq⟩ : ∃ n ∈ ρ.ker, y * q * y⁻¹ = q' * n := by
      refine ⟨q'⁻¹ * (y * q * y⁻¹), ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hq'eq, inv_mul_cancel]
    have hn1 : n = 1 := by
      refine eq_one_of_pow_eq_one_of_mem_ker hcop hnker (a := a) ?_
      have hcomm : Commute q' n := Subgroup.mem_center_iff.1 (hker hnker) q'
      have h : (q' * n) ^ p ^ a = 1 := by
        rw [← hyq, conj_pow, hexp q (hQT hq), mul_one, mul_inv_cancel]
      rwa [hcomm.mul_pow, hexp q' (hQT hq'), one_mul] at h
    rw [hyq, hn1, mul_one]
    exact hq'
  have hN : Subgroup.normalizer (Qb : Set L) ≤ (Subgroup.normalizer (Q : Set K)).map ρ := by
    intro x hx
    obtain ⟨y, rfl⟩ := hρ x
    refine ⟨y, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm y hx h hh, fun hh => ?_⟩
    have hyinv : ρ y⁻¹ ∈ Subgroup.normalizer (Qb : Set L) := by
      rw [map_inv]
      exact (Subgroup.normalizer (Qb : Set L)).inv_mem hx
    have h2 := hnorm y⁻¹ hyinv _ hh
    rwa [show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at h2
  exact hN.trans (Subgroup.map_mono (normalizer_le_weakCore p hQT hrankQ hrankW))

omit [Finite K] in
theorem eq_top_of_sup_eq_top_of_le_center (hperf : commutator K = ⊤) {Γ N : Subgroup K}
    (hN : N ≤ Subgroup.center K) (h : Γ ⊔ N = ⊤) : Γ = ⊤ := by
  have : N.Normal := Subgroup.normal_of_le_center hN
  have e1 : ∀ a n c : K, n ∈ N → ⁅a * n, c⁆ = ⁅a, c⁆ := by
    intro a n c hn
    rw [commutatorElement_mul_left_eq_conj_mul,
      Commute.commutator_eq (Subgroup.mem_center_iff.1 (hN hn) c).symm, mul_one, mul_inv_cancel,
      one_mul]
  have e2 : ∀ a b n : K, n ∈ N → ⁅a, b * n⁆ = ⁅a, b⁆ := by
    intro a b n hn
    rw [commutatorElement_mul_right_eq_mul_conj,
      Commute.commutator_eq (Subgroup.mem_center_iff.1 (hN hn) a), mul_one, mul_inv_cancel_right]
  have hmem : ∀ g : K, g ∈ Γ ⊔ N := fun g => by
    rw [h]
    exact Subgroup.mem_top g
  rw [eq_top_iff, ← hperf, _root_.commutator_def]
  refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hmem g₁)
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hmem g₂)
  rw [e1 _ _ _ hn₁, e2 _ _ _ hn₂]
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem ha₁ ha₂) (Γ.inv_mem ha₁)) (Γ.inv_mem ha₂)

end GL83.I243.Cover
