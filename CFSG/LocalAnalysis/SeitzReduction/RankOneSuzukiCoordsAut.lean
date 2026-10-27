module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G] {K : Type*} [Field K] [CharP K 2]

namespace SzRCoords2

variable {T₁ R₂ : Subgroup G} {t : G} {a : ℕ} {u v : G → K} {φ : G → K × K × K} {γ c : K}

theorem v_one (h : SzRCoords2 T₁ R₂ t a u v φ γ c) : v 1 = 0 := by
  have h1 := h.v_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h1
  exact add_eq_left.mp h1.symm

theorem map_one (h : SzRCoords2 T₁ R₂ t a u v φ γ c) : φ 1 = 0 :=
  (h.ker 1 (one_mem _)).mpr (one_mem _)

theorem map_inv_mul (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x x' : G} (hx : x ∈ szR T₁ R₂ t)
    (hx' : x' ∈ szR T₁ R₂ t) : φ (x⁻¹ * x') = φ x' - φ x := by
  have h1 := h.mul x hx (x⁻¹ * x') (mul_mem (inv_mem hx) hx')
  rw [mul_inv_cancel_left] at h1
  rw [h1]
  abel

theorem inv_mul_mem_szA₁_of_map_eq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x x' : G}
    (hx : x ∈ szR T₁ R₂ t) (hx' : x' ∈ szR T₁ R₂ t) (he : φ x = φ x') : x⁻¹ * x' ∈ szA₁ T₁ := by
  rw [← h.ker _ (mul_mem (inv_mem hx) hx'), h.map_inv_mul hx hx', he, sub_self]

theorem mem_szA₁_of_forall_commute [Fintype K] (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) {x : G} (hx : x ∈ szR T₁ R₂ t)
    (hxc : ∀ y ∈ szR T₁ R₂ t, x * y = y * x) : x ∈ szA₁ T₁ := by
  refine (h.ker x hx).mp (eq_zero_of_forall_szCommMap_eq_zero (γ := γ) ha hK fun z hz => ?_)
  obtain ⟨y, hy, rfl⟩ := h.surj z hz
  rw [← h.comm x hx y hy, hxc y hy, mul_inv_cancel_right, mul_inv_cancel, h.v_one]

theorem conj_mem_szA₁ [Fintype K] (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {n : G}
    (hn : n ∈ normalizer (szR T₁ R₂ t : Set G)) {b : G} (hb : b ∈ szA₁ T₁) :
    n⁻¹ * b * n ∈ szA₁ T₁ := by
  have hbR : b ∈ szR T₁ R₂ t := le_szR_left T₁ R₂ t (szA₁_le T₁ hb)
  have hconj : ∀ y, y ∈ szR T₁ R₂ t ↔ n⁻¹ * y * n ∈ szR T₁ R₂ t :=
    fun y => mem_normalizer_iff''.mp hn y
  refine h.mem_szA₁_of_forall_commute ha hK ((hconj b).mp hbR) fun y hy => ?_
  have hy' : n * y * n⁻¹ ∈ szR T₁ R₂ t := by
    rw [hconj]
    simpa [mul_assoc] using hy
  have e := h.central _ hy' b hb
  calc n⁻¹ * b * n * y = n⁻¹ * (b * (n * y * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * y * n⁻¹) * b) * n := by rw [e]
    _ = y * (n⁻¹ * b * n) := by group

theorem map_conj_eq_of_map_eq [Fintype K] (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {m : G}
    (hm : m ∈ normalizer (szR T₁ R₂ t : Set G)) {x x' : G} (hx : x ∈ szR T₁ R₂ t)
    (hx' : x' ∈ szR T₁ R₂ t) (he : φ x = φ x') : φ (m⁻¹ * x * m) = φ (m⁻¹ * x' * m) := by
  have hb := h.inv_mul_mem_szA₁_of_map_eq hx hx' he
  have hb' := h.conj_mem_szA₁ ha hK hm hb
  have hconj : ∀ y, y ∈ szR T₁ R₂ t ↔ m⁻¹ * y * m ∈ szR T₁ R₂ t :=
    fun y => mem_normalizer_iff''.mp hm y
  have hxx := mul_mem (inv_mem hx) hx'
  have e : m⁻¹ * x' * m = (m⁻¹ * x * m) * (m⁻¹ * (x⁻¹ * x') * m) := by group
  rw [e, h.mul _ ((hconj x).mp hx) _ ((hconj _).mp hxx), (h.ker _ ((hconj _).mp hxx)).mpr hb',
    add_zero]

theorem exists_addEquiv_of_mem_normalizer [Fintype K] (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) {n : G}
    (hn : n ∈ normalizer (szR T₁ R₂ t : Set G)) :
    ∃ (α : szCoordSpace K ≃+ szCoordSpace K) (β : K ≃+ K),
      (∀ x (hx : x ∈ szR T₁ R₂ t), ((α ⟨φ x, h.mem x hx⟩ : szCoordSpace K) : K × K × K) =
        φ (n⁻¹ * x * n)) ∧
      (∀ b ∈ szA₁ T₁, β (v b) = v (n⁻¹ * b * n)) ∧
      ∀ z z' : szCoordSpace K, szCommMap a γ (α z) (α z') = β (szCommMap a γ z z') := by
  classical
  have hn' : n⁻¹ ∈ normalizer (szR T₁ R₂ t : Set G) := inv_mem hn
  have hconj : ∀ m ∈ normalizer (szR T₁ R₂ t : Set G), ∀ y ∈ szR T₁ R₂ t,
      m⁻¹ * y * m ∈ szR T₁ R₂ t := fun m hm y hy => (mem_normalizer_iff''.mp hm y).mp hy
  choose! sec hsec hφsec using h.surj
  have hf : ∀ m ∈ normalizer (szR T₁ R₂ t : Set G), ∀ x ∈ szR T₁ R₂ t,
      φ (m⁻¹ * sec (φ x) * m) = φ (m⁻¹ * x * m) := fun m hm x hx =>
    h.map_conj_eq_of_map_eq ha hK hm (hsec _ (h.mem x hx)) hx (hφsec _ (h.mem x hx))
  let F : ∀ m ∈ normalizer (szR T₁ R₂ t : Set G), szCoordSpace K → szCoordSpace K :=
    fun m hm z => ⟨φ (m⁻¹ * sec z * m), h.mem _ (hconj m hm _ (hsec z z.2))⟩
  have hF : ∀ m (hm : m ∈ normalizer (szR T₁ R₂ t : Set G)) (z : szCoordSpace K),
      (F m hm z : K × K × K) = φ (m⁻¹ * sec z * m) := fun _ _ _ => rfl
  have hFφ : ∀ m (hm : m ∈ normalizer (szR T₁ R₂ t : Set G)) x (hx : x ∈ szR T₁ R₂ t),
      (F m hm ⟨φ x, h.mem x hx⟩ : K × K × K) = φ (m⁻¹ * x * m) := fun m hm x hx => hf m hm x hx
  have hFF : ∀ (z : szCoordSpace K), F n⁻¹ hn' (F n hn z) = z := by
    intro z
    apply Subtype.ext
    have hy := hconj n hn _ (hsec z z.2)
    show φ (n⁻¹⁻¹ * sec (φ (n⁻¹ * sec z * n)) * n⁻¹) = (z : K × K × K)
    rw [hf n⁻¹ hn' _ hy, show n⁻¹⁻¹ * (n⁻¹ * sec z * n) * n⁻¹ = sec z by group, hφsec z z.2]
  have hFF' : ∀ (z : szCoordSpace K), F n hn (F n⁻¹ hn' z) = z := by
    intro z
    apply Subtype.ext
    have hy := hconj n⁻¹ hn' _ (hsec z z.2)
    show φ (n⁻¹ * sec (φ (n⁻¹⁻¹ * sec z * n⁻¹)) * n) = (z : K × K × K)
    rw [hf n hn _ hy, show n⁻¹ * (n⁻¹⁻¹ * sec z * n⁻¹) * n = sec z by group, hφsec z z.2]
  have hFadd : ∀ z z' : szCoordSpace K, F n hn (z + z') = F n hn z + F n hn z' := by
    intro z z'
    apply Subtype.ext
    have hz := hsec z z.2
    have hz' := hsec z' z'.2
    have he : φ (sec ((z + z' : szCoordSpace K) : K × K × K)) = φ (sec z * sec z') := by
      rw [hφsec _ (z + z').2, h.mul _ hz _ hz', hφsec z z.2, hφsec z' z'.2]
      rfl
    show φ (n⁻¹ * sec ((z + z' : szCoordSpace K) : K × K × K) * n) =
      φ (n⁻¹ * sec z * n) + φ (n⁻¹ * sec z' * n)
    rw [h.map_conj_eq_of_map_eq ha hK hn (hsec _ (z + z').2) (mul_mem hz hz') he,
      show n⁻¹ * (sec z * sec z') * n = (n⁻¹ * sec z * n) * (n⁻¹ * sec z' * n) by group,
      h.mul _ (hconj n hn _ hz) _ (hconj n hn _ hz')]
  let α : szCoordSpace K ≃+ szCoordSpace K :=
    { toFun := F n hn
      invFun := F n⁻¹ hn'
      left_inv := hFF
      right_inv := hFF'
      map_add' := hFadd }
  choose secA hsecA hvsecA using h.v_surj
  have hsecA_eq : ∀ b ∈ szA₁ T₁, secA (v b) = b := by
    intro b hb
    have h1 := h.v_mul b⁻¹ (inv_mem hb) (secA (v b)) (hsecA _)
    have h2 := h.v_mul b⁻¹ (inv_mem hb) b hb
    rw [inv_mul_cancel, h.v_one] at h2
    rw [hvsecA, ← h2] at h1
    have := h.v_inj _ (mul_mem (inv_mem hb) (hsecA _)) h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hAconj : ∀ m ∈ normalizer (szR T₁ R₂ t : Set G), ∀ b ∈ szA₁ T₁, m⁻¹ * b * m ∈ szA₁ T₁ :=
    fun m hm b hb => h.conj_mem_szA₁ ha hK hm hb
  have hβadd : ∀ w w' : K, v (n⁻¹ * secA (w + w') * n) =
      v (n⁻¹ * secA w * n) + v (n⁻¹ * secA w' * n) := by
    intro w w'
    have hb := mul_mem (hsecA w) (hsecA w')
    have e : secA (w + w') = secA w * secA w' := by
      rw [← hsecA_eq _ hb, h.v_mul _ (hsecA w) _ (hsecA w'), hvsecA, hvsecA]
    rw [e, show n⁻¹ * (secA w * secA w') * n = (n⁻¹ * secA w * n) * (n⁻¹ * secA w' * n) by group,
      h.v_mul _ (hAconj n hn _ (hsecA w)) _ (hAconj n hn _ (hsecA w'))]
  let β : K ≃+ K :=
    { toFun := fun w => v (n⁻¹ * secA w * n)
      invFun := fun w => v (n⁻¹⁻¹ * secA w * n⁻¹)
      left_inv := fun w => by
        simp only
        rw [hsecA_eq _ (hAconj n hn _ (hsecA w)),
          show n⁻¹⁻¹ * (n⁻¹ * secA w * n) * n⁻¹ = secA w by group, hvsecA]
      right_inv := fun w => by
        simp only
        rw [hsecA_eq _ (hAconj n⁻¹ hn' _ (hsecA w)),
          show n⁻¹ * (n⁻¹⁻¹ * secA w * n⁻¹) * n = secA w by group, hvsecA]
      map_add' := hβadd }
  have hβ : ∀ b ∈ szA₁ T₁, β (v b) = v (n⁻¹ * b * n) := by
    intro b hb
    show v (n⁻¹ * secA (v b) * n) = v (n⁻¹ * b * n)
    rw [hsecA_eq b hb]
  refine ⟨α, β, fun x hx => hFφ n hn x hx, hβ, fun z z' => ?_⟩
  have hz := hsec z z.2
  have hz' := hsec z' z'.2
  have hαz : (α z : K × K × K) = φ (n⁻¹ * sec z * n) := rfl
  have hαz' : (α z' : K × K × K) = φ (n⁻¹ * sec z' * n) := rfl
  have hcz : szCommMap a γ (z : K × K × K) (z' : K × K × K) = v (sec z * sec z' * (sec z)⁻¹ *
      (sec z')⁻¹) := by
    rw [h.comm _ hz _ hz', hφsec z z.2, hφsec z' z'.2]
  rw [hαz, hαz', hcz, ← h.comm _ (hconj n hn _ hz) _ (hconj n hn _ hz'),
    hβ _ (h.comm_mem _ hz _ hz')]
  congr 1
  group

theorem conj_t_not_mem_sup [Fintype K] (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {n : G}
    (hn : n ∈ normalizer (szR T₁ R₂ t : Set G)) :
    n⁻¹ * t * n ∉ T₁ ⊔ R₂ ∧ (γ ≠ 0 → t⁻¹ * (n⁻¹ * t * n) ∈ szA₁ T₁) := by
  obtain ⟨α, β, hα, -, hB⟩ := h.exists_addEquiv_of_mem_normalizer ha hK hn
  obtain ⟨h1, h2⟩ := szRadical_fixed ha hK γ α β hB
  have htR := mem_szR_right T₁ R₂ t
  have hφt : (⟨φ t, h.mem t htR⟩ : szCoordSpace K) = ⟨(0, 0, 1), Or.inr rfl⟩ :=
    Subtype.ext h.of_t
  have key := hα t htR
  rw [hφt] at key
  have hntR : n⁻¹ * t * n ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp hn t).mp htR
  refine ⟨fun hmem => ?_, fun hγ => ?_⟩
  · have h0 := (h.thd_eq_zero_iff _ hntR).mpr hmem
    rw [← key, h1] at h0
    exact one_ne_zero h0
  · rw [h2 hγ] at key
    exact h.inv_mul_mem_szA₁_of_map_eq htR hntR (h.of_t.trans key)

end SzRCoords2

end CFSG.SeitzReduction.RankOne
