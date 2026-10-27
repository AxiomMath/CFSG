module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {Γ : Type*} [Group Γ]

private noncomputable def ffOutBfsF {n : ℕ} (e : Fin n → Γ) (K : Subgroup Γ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => e i ∈ K

private lemma ffOutBfsF_mem {n : ℕ} (e : Fin n → Γ) {K : Subgroup Γ} {i : Fin n} :
    i ∈ ffOutBfsF e K ↔ e i ∈ K := by
  simp [ffOutBfsF]

private lemma ffOutBfs_card_pos [Finite Γ] (K : Subgroup Γ) : 0 < Nat.card K := by
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  exact Nat.card_pos

private noncomputable def ffOutBfsEquiv {n : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    {K : Subgroup Γ} (hK : ∀ y ∈ K, ∃ i, e i = y) : ↥K ≃ ↥(ffOutBfsF e K) where
  toFun y := ⟨(hK y.1 y.2).choose, by
    rw [ffOutBfsF_mem, (hK y.1 y.2).choose_spec]
    exact y.2⟩
  invFun i := ⟨e i.1, (ffOutBfsF_mem e).mp i.2⟩
  left_inv y := Subtype.ext (hK y.1 y.2).choose_spec
  right_inv i := by
    apply Subtype.ext
    apply he
    exact (hK (e i.1) ((ffOutBfsF_mem e).mp i.2)).choose_spec

private lemma ffOutBfsF_card {n : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    {K : Subgroup Γ} (hK : ∀ y ∈ K, ∃ i, e i = y) :
    Nat.card K = (ffOutBfsF e K).card := by
  rw [Nat.card_congr (ffOutBfsEquiv e he hK), Nat.card_eq_fintype_card, Fintype.card_coe]

private lemma ffOutBfs_relIndex_two [Finite Γ] {K K' : Subgroup Γ} (hle : K' ≤ K)
    (hcard : Nat.card K = 2 * Nat.card K') : K'.relIndex K = 2 := by
  have h := Subgroup.relIndex_mul_card (H := K') (K := K)
  rw [inf_of_le_left hle, hcard] at h
  exact Nat.mul_right_cancel (ffOutBfs_card_pos K') h

private lemma ffOutBfs_coset [Finite Γ] {K K' : Subgroup Γ} (hle : K' ≤ K)
    (hcard : Nat.card K = 2 * Nat.card K') {x : Γ} (hxK : x ∈ K) (hxK' : x ∉ K') :
    (x * x ∈ K') ∧ (∀ y ∈ K, y ∉ K' → x * y ∈ K') := by
  have hrel : (K'.subgroupOf K).index = 2 := ffOutBfs_relIndex_two hle hcard
  have hxx : (⟨x, hxK⟩ : ↥K) * ⟨x, hxK⟩ ∈ K'.subgroupOf K :=
    Subgroup.mul_self_mem_of_index_two hrel ⟨x, hxK⟩
  refine ⟨Subgroup.mem_subgroupOf.mp hxx, ?_⟩
  intro y hyK hyK'
  have h : (⟨x, hxK⟩ : ↥K) * ⟨y, hyK⟩ ∈ K'.subgroupOf K := by
    rw [Subgroup.mul_mem_iff_of_index_two hrel]
    simp only [Subgroup.mem_subgroupOf]
    exact iff_of_false hxK' hyK'
  exact Subgroup.mem_subgroupOf.mp h

private lemma ffOutBfs_union {n : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) {K K' : Subgroup Γ} (hle : K' ≤ K)
    (hK : ∀ y ∈ K, ∃ i, e i = y) {x : Γ} (hxK : x ∈ K) (hxK' : x ∉ K') {j : Fin n}
    (hj : e j = x) (hxx : x * x ∈ K') (hmulmem : ∀ y ∈ K, y ∉ K' → x * y ∈ K') :
    ffOutBfsF e K = ffOutBfsF e K' ∪ (ffOutBfsF e K').image (mul j) := by
  ext i
  constructor
  · intro hi
    have heiK : e i ∈ K := (ffOutBfsF_mem e).mp hi
    rw [Finset.mem_union]
    by_cases hmem : e i ∈ K'
    · left
      rw [ffOutBfsF_mem]; exact hmem
    · right
      have hxy : x * e i ∈ K' := hmulmem (e i) heiK hmem
      have hinv : x⁻¹ * e i ∈ K' := by
        have h : (x * x)⁻¹ * (x * e i) ∈ K' := K'.mul_mem (K'.inv_mem hxx) hxy
        rwa [show (x * x)⁻¹ * (x * e i) = x⁻¹ * e i from by group] at h
      obtain ⟨h, hh⟩ := hK (x⁻¹ * e i) (hle hinv)
      refine Finset.mem_image.mpr ⟨h, ?_, ?_⟩
      · rw [ffOutBfsF_mem, hh]; exact hinv
      · apply he
        rw [hmul, hj, hh]
        group
  · intro hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · rw [ffOutBfsF_mem] at hi ⊢
      exact hle hi
    · rcases Finset.mem_image.mp hi with ⟨h, hh, himg⟩
      rw [ffOutBfsF_mem] at hh ⊢
      have heq : e i = x * e h := by rw [← himg, hmul, hj]
      rw [heq]
      exact K.mul_mem hxK (hle hh)

private lemma ffOutBfs_aux_elemAb [Finite Γ] {n : ℕ} (e : Fin n → Γ)
    (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) {𝓛 : Set (Finset (Fin n))} (h0 : {one} ∈ 𝓛)
    (h2 : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x = one →
      (∀ h ∈ H, mul x h = mul h x) → H ∪ H.image (mul x) ∈ 𝓛) :
    ∀ N, ∀ K : Subgroup Γ, Nat.card K = N → (∀ y ∈ K, ∃ i, e i = y) →
      (∀ y ∈ K, y * y = 1) → ffOutBfsF e K ∈ 𝓛 := by
  intro N
  refine Nat.strongRecOn N (fun m ih => ?_)
  intro K hN hK hKe
  by_cases hbot : K = ⊥
  · have hF : ffOutBfsF e K = {one} := by
      ext i
      rw [ffOutBfsF_mem, Finset.mem_singleton, hbot, Subgroup.mem_bot]
      exact ⟨fun h => he (h.trans hone.symm), fun h => by rw [h]; exact hone⟩
    rw [hF]; exact h0
  · have hcard1 : Nat.card K ≠ 1 :=
      fun h1 => hbot ((Subgroup.eq_bot_iff_card (H := K)).mpr h1)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKp : IsPGroup 2 ↥K := fun g => ⟨1, by
      rw [pow_one, pow_two]
      exact Subtype.ext (hKe g.1 g.2)⟩
    obtain ⟨a, ha⟩ := IsPGroup.exists_card_eq hKp
    have ha0 : a ≠ 0 := fun h0a => hcard1 (by rw [ha, h0a, pow_zero])
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hdvd : 2 ^ b ∣ Nat.card ↥K := by
      rw [ha, pow_succ]
      exact dvd_mul_right _ _
    obtain ⟨K'', hK''card⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    let K' : Subgroup Γ := K''.map K.subtype
    have hK'le : K' ≤ K := Subgroup.map_subtype_le K''
    have hK'card : Nat.card K' = 2 ^ b := by
      show Nat.card (K''.map K.subtype) = 2 ^ b
      rw [Subgroup.card_subtype K K'', hK''card]
    have hcards : Nat.card K = 2 * Nat.card K' := by
      rw [ha, pow_succ, hK'card]; ring
    have hK'lt : Nat.card K' < m := by
      rw [← hN, hcards]
      have := ffOutBfs_card_pos K'
      omega
    have ihK' : ffOutBfsF e K' ∈ 𝓛 :=
      ih (Nat.card K') hK'lt K' rfl (fun y hy => hK y (hK'le hy))
        (fun y hy => hKe y (hK'le hy))
    have hK'ne : K' ≠ K := by
      intro h
      rw [h, hN] at hK'lt
      exact absurd hK'lt (lt_irrefl m)
    have hnotle : ¬ K ≤ K' := fun hle => hK'ne (le_antisymm hle hK'le).symm
    obtain ⟨x, hxK, hxK'⟩ := Set.not_subset.mp hnotle
    obtain ⟨j, hj⟩ := hK x hxK
    obtain ⟨hxx, hmulmem⟩ := ffOutBfs_coset hK'le hcards hxK hxK'
    have hjnot : j ∉ ffOutBfsF e K' := fun hej =>
      hxK' (hj ▸ (ffOutBfsF_mem e).mp hej)
    have hcomm : ∀ y ∈ K, ∀ z ∈ K, y * z = z * y := by
      intro y hy z hz
      have hy2 : y * y = 1 := hKe y hy
      have hz2 : z * z = 1 := hKe z hz
      calc y * z = (y * z)⁻¹ :=
            (inv_eq_of_mul_eq_one_right (hKe (y * z) (K.mul_mem hy hz))).symm
        _ = z⁻¹ * y⁻¹ := mul_inv_rev y z
        _ = z * y := by
            rw [inv_eq_of_mul_eq_one_right hy2, inv_eq_of_mul_eq_one_right hz2]
    have hjj : mul j j = one := by
      apply he
      rw [hmul, hj, hone]
      exact hKe x hxK
    have hcommj : ∀ h ∈ ffOutBfsF e K', mul j h = mul h j := by
      intro h hh
      have heh : e h ∈ K' := (ffOutBfsF_mem e).mp hh
      apply he
      simp only [hmul, hj]
      exact hcomm x hxK (e h) (hK'le heh)
    rw [ffOutBfs_union e he one hone mul hmul hK'le hK hxK hxK' hj hxx hmulmem]
    exact h2 (ffOutBfsF e K') ihK' j hjnot hjj hcommj

private lemma ffOutBfs_aux_abelian [Finite Γ] {n : ℕ} (e : Fin n → Γ)
    (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) {𝓛 : Set (Finset (Fin n))} (h0 : {one} ∈ 𝓛)
    (h2 : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x ∈ H →
      (∀ h ∈ H, mul x h = mul h x) → H ∪ H.image (mul x) ∈ 𝓛) :
    ∀ N, ∀ K : Subgroup Γ, Nat.card K = N → (∀ y ∈ K, ∃ i, e i = y) →
      IsPGroup 2 K → (∀ y ∈ K, ∀ z ∈ K, y * z = z * y) → ffOutBfsF e K ∈ 𝓛 := by
  intro N
  refine Nat.strongRecOn N (fun m ih => ?_)
  intro K hN hK hKp hKc
  by_cases hbot : K = ⊥
  · have hF : ffOutBfsF e K = {one} := by
      ext i
      rw [ffOutBfsF_mem, Finset.mem_singleton, hbot, Subgroup.mem_bot]
      exact ⟨fun h => he (h.trans hone.symm), fun h => by rw [h]; exact hone⟩
    rw [hF]; exact h0
  · have hcard1 : Nat.card K ≠ 1 :=
      fun h1 => hbot ((Subgroup.eq_bot_iff_card (H := K)).mpr h1)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := IsPGroup.exists_card_eq hKp
    have ha0 : a ≠ 0 := fun h0a => hcard1 (by rw [ha, h0a, pow_zero])
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hdvd : 2 ^ b ∣ Nat.card ↥K := by
      rw [ha, pow_succ]
      exact dvd_mul_right _ _
    obtain ⟨K'', hK''card⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    let K' : Subgroup Γ := K''.map K.subtype
    have hK'le : K' ≤ K := Subgroup.map_subtype_le K''
    have hK'card : Nat.card K' = 2 ^ b := by
      show Nat.card (K''.map K.subtype) = 2 ^ b
      rw [Subgroup.card_subtype K K'', hK''card]
    have hcards : Nat.card K = 2 * Nat.card K' := by
      rw [ha, pow_succ, hK'card]; ring
    have hK'lt : Nat.card K' < m := by
      rw [← hN, hcards]
      have := ffOutBfs_card_pos K'
      omega
    have ihK' : ffOutBfsF e K' ∈ 𝓛 :=
      ih (Nat.card K') hK'lt K' rfl (fun y hy => hK y (hK'le hy)) (hKp.to_le hK'le)
        (fun y hy z hz => hKc y (hK'le hy) z (hK'le hz))
    have hK'ne : K' ≠ K := by
      intro h
      rw [h, hN] at hK'lt
      exact absurd hK'lt (lt_irrefl m)
    have hnotle : ¬ K ≤ K' := fun hle => hK'ne (le_antisymm hle hK'le).symm
    obtain ⟨x, hxK, hxK'⟩ := Set.not_subset.mp hnotle
    obtain ⟨j, hj⟩ := hK x hxK
    obtain ⟨hxx, hmulmem⟩ := ffOutBfs_coset hK'le hcards hxK hxK'
    have hjnot : j ∉ ffOutBfsF e K' := fun hej =>
      hxK' (hj ▸ (ffOutBfsF_mem e).mp hej)
    have hcomm : ∀ y ∈ K, ∀ z ∈ K, y * z = z * y := hKc
    have hjj : mul j j ∈ ffOutBfsF e K' := by
      rw [ffOutBfsF_mem, hmul, hj]
      exact hxx
    have hcommj : ∀ h ∈ ffOutBfsF e K', mul j h = mul h j := by
      intro h hh
      have heh : e h ∈ K' := (ffOutBfsF_mem e).mp hh
      apply he
      simp only [hmul, hj]
      exact hcomm x hxK (e h) (hK'le heh)
    rw [ffOutBfs_union e he one hone mul hmul hK'le hK hxK hxK' hj hxx hmulmem]
    exact h2 (ffOutBfsF e K') ihK' j hjnot hjj hcommj

theorem ffRA_bfs_elemAb [Finite Γ] {n : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) {bound : ℕ} (𝓛 : Set (Finset (Fin n)))
    (h0 : {one} ∈ 𝓛) (h1 : ∀ H ∈ 𝓛, H.card ≤ bound)
    (h2 : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x = one → (∀ h ∈ H, mul x h = mul h x) →
      H ∪ H.image (mul x) ∈ 𝓛)
    {K : Subgroup Γ} (hK : ∀ y ∈ K, ∃ i, e i = y) (hKe : ∀ y ∈ K, y * y = 1) :
    Nat.card K ≤ bound := by
  have hmem : ffOutBfsF e K ∈ 𝓛 :=
    ffOutBfs_aux_elemAb e he one hone mul hmul h0 h2 (Nat.card K) K rfl hK hKe
  calc Nat.card K = (ffOutBfsF e K).card := ffOutBfsF_card e he hK
    _ ≤ bound := h1 (ffOutBfsF e K) hmem

theorem ffRA_bfs_abelian [Finite Γ] {n : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) {bound : ℕ} (𝓛 : Set (Finset (Fin n)))
    (h0 : {one} ∈ 𝓛) (h1 : ∀ H ∈ 𝓛, H.card ≤ bound)
    (h2 : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x ∈ H → (∀ h ∈ H, mul x h = mul h x) →
      H ∪ H.image (mul x) ∈ 𝓛)
    {K : Subgroup Γ} (hK : ∀ y ∈ K, ∃ i, e i = y) (hKp : IsPGroup 2 K)
    (hKc : IsMulCommutative K) : Nat.card K ≤ bound := by
  have hmem : ffOutBfsF e K ∈ 𝓛 :=
    ffOutBfs_aux_abelian e he one hone mul hmul h0 h2 (Nat.card K) K rfl hK hKp
      (fun y hy z hz => congrArg Subtype.val (hKc.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩))
  calc Nat.card K = (ffOutBfsF e K).card := ffOutBfsF_card e he hK
    _ ≤ bound := h1 (ffOutBfsF e K) hmem

theorem ffRA_bfs_abelian_mem [Finite Γ] {n : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) (𝓛 : Set (Finset (Fin n))) (h0 : {one} ∈ 𝓛)
    (h2 : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x ∈ H → (∀ h ∈ H, mul x h = mul h x) →
      H ∪ H.image (mul x) ∈ 𝓛)
    {K : Subgroup Γ} (hK : ∀ y ∈ K, ∃ i, e i = y) (hKp : IsPGroup 2 K)
    (hKc : ∀ y ∈ K, ∀ z ∈ K, y * z = z * y) : ∃ F ∈ 𝓛, ∀ i, i ∈ F ↔ e i ∈ K :=
  ⟨ffOutBfsF e K, ffOutBfs_aux_abelian e he one hone mul hmul h0 h2 (Nat.card K) K rfl hK hKp hKc,
    fun _ => ffOutBfsF_mem e⟩

end CFSG.OddStandard.SmallF3.Omega
