module

public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

namespace CFSG.ClassicalInvolution.Asc77.T7DR

open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_gens_of_isQuatSub' {R : Subgroup G} (h : IsQuatSub R) :
    ∃ (a b : G) (n : ℕ), a ∈ R ∧ b ∈ R ∧ Subgroup.closure ({a, b} : Set G) = R ∧
      b * a * b⁻¹ = a⁻¹ ∧ 1 ≤ n ∧ orderOf a = 2 ^ (n + 1) ∧ b * b = a ^ (2 ^ n) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  have hne : NeZero (2 ^ k) := inferInstance
  set a₀ : ↥R := e.symm (QuaternionGroup.a 1) with ha₀
  set b₀ : ↥R := e.symm (QuaternionGroup.xa 0) with hb₀
  have hinv : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k))⁻¹ = QuaternionGroup.a (-1) := by
    apply inv_eq_of_mul_eq_one_right
    simp
  have hq : (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ := by
    apply mul_inv_eq_iff_eq_mul.mpr
    rw [hinv]
    simp
  have hab : b₀ * a₀ * b₀⁻¹ = a₀⁻¹ := by
    simp only [ha₀, hb₀, ← map_mul, ← map_inv]
    exact congrArg e.symm hq
  have hbb : b₀ * b₀ = a₀ ^ (2 ^ k) := by
    have hq2 : (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) * QuaternionGroup.xa 0 =
        (QuaternionGroup.a 1) ^ (2 ^ k) := by
      rw [QuaternionGroup.a_one_pow]
      simp
    simp only [ha₀, hb₀, ← map_mul, ← map_pow]
    exact congrArg e.symm hq2
  have hord : orderOf a₀ = 2 ^ (k + 1) := by
    rw [ha₀, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one, pow_succ]
    ring
  have hgen : Subgroup.closure ({a₀, b₀} : Set ↥R) = ⊤ := by
    rw [eq_top_iff]
    intro r _
    obtain ⟨q, hqr⟩ : ∃ q, e.symm q = r := ⟨e r, by simp⟩
    rw [← hqr]
    cases q with
    | a i =>
      have : (QuaternionGroup.a i : QuaternionGroup (2 ^ k)) = (QuaternionGroup.a 1) ^ i.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [this, map_pow]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [ha₀])) _
    | xa i =>
      have : (QuaternionGroup.xa i : QuaternionGroup (2 ^ k)) =
          QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ i.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
        simp
      rw [this, map_mul, map_pow]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp [hb₀]))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [ha₀])) _)
  refine ⟨(a₀ : G), (b₀ : G), k, a₀.2, b₀.2, ?_, ?_, hk, ?_, ?_⟩
  · have h1 := congrArg (Subgroup.map R.subtype) hgen
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  · have := congrArg Subtype.val hab
    simpa using this
  · rw [← Subgroup.orderOf_coe] at hord
    exact hord
  · have := congrArg Subtype.val hbb
    simpa using this


@[expose] def squaresSub (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ r ∈ R, x = r * r}

theorem square_mem_squaresSub {R : Subgroup G} {r : G} (hr : r ∈ R) : r * r ∈ squaresSub R :=
  Subgroup.subset_closure ⟨r, hr, rfl⟩

section Quat

variable {R : Subgroup G} {a b : G}

theorem conj_zpow_of_inv (hbab : b * a * b⁻¹ = a⁻¹) (n : ℤ) : b * a ^ n * b⁻¹ = a ^ (-n) := by
  rw [← conj_zpow, hbab, inv_zpow, zpow_neg]

theorem zpow_mul_eq_of_inv (hbab : b * a * b⁻¹ = a⁻¹) (i : ℤ) : a ^ i * b = b * a ^ (-i) := by
  have h := conj_zpow_of_inv hbab (-i)
  rw [neg_neg] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem mul_zpow_mul_self_eq (hbab : b * a * b⁻¹ = a⁻¹) (i : ℤ) :
    (b * a ^ i) * (b * a ^ i) = b * b := by
  calc b * a ^ i * (b * a ^ i) = b * (a ^ i * b) * a ^ i := by group
    _ = b * (b * a ^ (-i)) * a ^ i := by rw [zpow_mul_eq_of_inv hbab]
    _ = b * b * (a ^ (-i) * a ^ i) := by group
    _ = b * b := by rw [← zpow_add]; simp

theorem quat_normal_form {k : ℤ} (hbab : b * a * b⁻¹ = a⁻¹) (hk : b * b = a ^ k)
    (hclos : Subgroup.closure ({a, b} : Set G) = R) :
    ∀ r ∈ R, (∃ i : ℤ, r = a ^ i) ∨ ∃ i : ℤ, r = b * a ^ i := by
  intro r hr
  rw [← hclos] at hr
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Or.inl ⟨1, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Or.inr ⟨0, by simp⟩
  | one => exact Or.inl ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨i + j, by rw [zpow_add]⟩
    · right
      refine ⟨-i + j, ?_⟩
      calc a ^ i * (b * a ^ j) = (a ^ i * b) * a ^ j := by group
        _ = b * a ^ (-i) * a ^ j := by rw [zpow_mul_eq_of_inv hbab]
        _ = b * a ^ (-i + j) := by rw [mul_assoc, ← zpow_add]
    · right
      exact ⟨i + j, by rw [mul_assoc, ← zpow_add]⟩
    · left
      refine ⟨k - i + j, ?_⟩
      calc b * a ^ i * (b * a ^ j) = b * (a ^ i * b) * a ^ j := by group
        _ = b * (b * a ^ (-i)) * a ^ j := by rw [zpow_mul_eq_of_inv hbab]
        _ = (b * b) * a ^ (-i) * a ^ j := by group
        _ = a ^ (k - i + j) := by
          rw [hk, ← zpow_add, ← zpow_add]
          congr 1
  | inv x _ hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨-i, by simp⟩
    · right
      refine ⟨i - k, ?_⟩
      have hbinv : b⁻¹ = b * a ^ (-k) := by
        have : b⁻¹ = b * (b * b)⁻¹ := by group
        rw [this, hk, ← zpow_neg]
      calc (b * a ^ i)⁻¹ = a ^ (-i) * b⁻¹ := by group
        _ = a ^ (-i) * (b * a ^ (-k)) := by rw [hbinv]
        _ = (a ^ (-i) * b) * a ^ (-k) := by group
        _ = b * a ^ (-(-i)) * a ^ (-k) := by rw [zpow_mul_eq_of_inv hbab]
        _ = b * a ^ (i - k) := by
          rw [mul_assoc, ← zpow_add, neg_neg]
          congr 2

theorem not_mem_zpowers_of_inv (hbab : b * a * b⁻¹ = a⁻¹) (ha : a * a ≠ 1) :
    b ∉ Subgroup.zpowers a := by
  intro hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h1 : a ^ i * a * (a ^ i)⁻¹ = a := by
    rw [(Commute.zpow_left (Commute.refl a) i).eq]
    group
  rw [h1] at hbab
  exact ha (eq_inv_iff_mul_eq_one.mp hbab)


end Quat

section Adapt

variable {R : Subgroup G} {s a b : G}

theorem sigma_sigma (hs2 : s * s = 1) (x : G) : s * (s * x * s⁻¹) * s⁻¹ = x := by
  calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
    _ = x := by rw [hs2]; group

theorem exists_adjust {k : ℤ} (hs2 : s * s = 1) (hsR : ∀ r ∈ R, s * r * s⁻¹ ∈ R) (haR : a ∈ R)
    (hbR : b ∈ R) (hclos : Subgroup.closure ({a, b} : Set G) = R) (hbab : b * a * b⁻¹ = a⁻¹)
    (hk : b * b = a ^ k) (hnb : b ∉ Subgroup.zpowers a) (hsa : s * a * s⁻¹ = a⁻¹)
    (hnt : ∃ r ∈ R, ⁅s, r⁆ ∉ squaresSub R) :
    ∃ b₁ : G, b₁ ∈ R ∧ Subgroup.closure ({a, b₁} : Set G) = R ∧ b₁ * a * b₁⁻¹ = a⁻¹ ∧
      (∃ k' : ℤ, b₁ * b₁ = a ^ k') ∧ s * b₁ * s⁻¹ = b₁ * a := by
  have hσpow : ∀ n : ℤ, s * a ^ n * s⁻¹ = a ^ (-n) := by
    intro n
    rw [← conj_zpow, hsa, inv_zpow, zpow_neg]
  have hσb : s * b * s⁻¹ ∈ R := hsR b hbR
  have hσb' : s * b * s⁻¹ ∉ Subgroup.zpowers a := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hnb
    have : b = s * (s * b * s⁻¹) * s⁻¹ := (sigma_sigma hs2 b).symm
    rw [this, ← hi, hσpow]
    exact Subgroup.zpow_mem_zpowers a (-i)
  rcases quat_normal_form hbab hk hclos _ hσb with ⟨i, hi⟩ | ⟨j, hj⟩
  · exact absurd (Subgroup.mem_zpowers_iff.mpr ⟨i, hi.symm⟩) hσb'
  · obtain ⟨m, hm⟩ := Int.even_or_odd' j
    rcases hm with rfl | rfl
    · exfalso
      obtain ⟨r, hr, hnr⟩ := hnt
      apply hnr
      rcases quat_normal_form hbab hk hclos r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have : ⁅s, a ^ i⁆ = a ^ (-i) * a ^ (-i) := by
          rw [commutatorElement_def, hσpow]
          group
        rw [this]
        exact square_mem_squaresSub (Subgroup.zpow_mem _ haR _)
      · have h1 : s * (b * a ^ i) * s⁻¹ = (s * b * s⁻¹) * (s * a ^ i * s⁻¹) := by group
        have : ⁅s, b * a ^ i⁆ = a ^ (i - m) * a ^ (i - m) := by
          calc ⁅s, b * a ^ i⁆ = (s * b * s⁻¹) * (s * a ^ i * s⁻¹) * (b * a ^ i)⁻¹ := by
                rw [commutatorElement_def, h1]
            _ = (b * a ^ (2 * m)) * a ^ (-i) * (b * a ^ i)⁻¹ := by rw [hj, hσpow]
            _ = b * a ^ (2 * m - 2 * i) * b⁻¹ := by group
            _ = a ^ (-(2 * m - 2 * i)) := conj_zpow_of_inv hbab _
            _ = a ^ (i - m) * a ^ (i - m) := by
              rw [← zpow_add]
              congr 1
              ring
        rw [this]
        exact square_mem_squaresSub (Subgroup.zpow_mem _ haR _)
    · refine ⟨b * a ^ m, R.mul_mem hbR (Subgroup.zpow_mem _ haR _), ?_, ?_, ⟨k, ?_⟩, ?_⟩
      · apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro x (rfl | rfl)
          · exact haR
          · exact R.mul_mem hbR (Subgroup.zpow_mem _ haR _)
        · have hacl : a ∈ Subgroup.closure ({a, b * a ^ m} : Set G) :=
            Subgroup.subset_closure (by simp)
          have hbacl : b * a ^ m ∈ Subgroup.closure ({a, b * a ^ m} : Set G) :=
            Subgroup.subset_closure (by simp)
          have hb_mem : b ∈ Subgroup.closure ({a, b * a ^ m} : Set G) := by
            have h := Subgroup.mul_mem _ hbacl (Subgroup.zpow_mem _ hacl (-m))
            have e : b * a ^ m * a ^ (-m) = b := by group
            simpa only [e] using h
          rw [← hclos, Subgroup.closure_le]
          rintro x (hx | hx)
          · rw [hx]
            exact hacl
          · rw [Set.mem_singleton_iff] at hx
            rw [hx]
            exact hb_mem
      · calc b * a ^ m * a * (b * a ^ m)⁻¹ = b * a * b⁻¹ := by group
          _ = a⁻¹ := hbab
      · rw [mul_zpow_mul_self_eq hbab m, hk]
      · calc s * (b * a ^ m) * s⁻¹ = (s * b * s⁻¹) * (s * a ^ m * s⁻¹) := by group
          _ = (b * a ^ (2 * m + 1)) * a ^ (-m) := by rw [hj, hσpow]
          _ = b * a ^ m * a := by group

end Adapt

end CFSG.ClassicalInvolution.Asc77.T7DR
