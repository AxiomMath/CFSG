module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRQuat

public section

namespace CFSG.ClassicalInvolution.Asc77.T7DR

open scoped commutatorElement

variable {G : Type} [Group G]

section Adapt

variable {R : Subgroup G} {s a b : G}

theorem conj_commutator_eq_inv (hs2 : s * s = 1) (r : G) : s * ⁅s, r⁆ * s⁻¹ = ⁅s, r⁆⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have h1 : (s * r * s * r⁻¹)⁻¹ = r * s⁻¹ * r⁻¹ * s⁻¹ := by group
  rw [commutatorElement_def, hsinv, h1, hsinv]
  calc s * (s * r * s * r⁻¹) * s = (s * s) * r * s * r⁻¹ * s := by group
    _ = r * s * r⁻¹ * s := by rw [hs2, one_mul]

theorem exists_adapted (hquat : IsQuatSub R) (hs2 : s * s = 1)
    (hsR : ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hnt : ∃ r ∈ R, ⁅s, r⁆ ∉ squaresSub R) :
    ∃ a b : G, a ∈ R ∧ b ∈ R ∧ Subgroup.closure ({a, b} : Set G) = R ∧ b * a * b⁻¹ = a⁻¹ ∧
      (∃ k : ℤ, b * b = a ^ k) ∧ b ∉ Subgroup.zpowers a ∧ s * a * s⁻¹ = a⁻¹ := by
  obtain ⟨a₀, b₀, n, ha₀R, hb₀R, hclos₀, hbab₀, hn1, hord, hbb₀⟩ := exists_gens_of_isQuatSub' hquat
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hk₀ : b₀ * b₀ = a₀ ^ (((2 ^ n : ℕ)) : ℤ) := by rw [zpow_natCast]; exact hbb₀
  have ha₀pow : a₀ ^ (2 ^ (n + 1)) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one a₀
  have hz0 : (b₀ * b₀) * (b₀ * b₀) = 1 := by
    rw [hbb₀, ← pow_add, ← two_mul, ← pow_succ']
    exact ha₀pow
  have hz0ne : b₀ * b₀ ≠ 1 := by
    rw [hbb₀]
    exact pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have ha₀sq : a₀ * a₀ ≠ 1 := by
    rw [← pow_two]
    refine pow_ne_one_of_lt_orderOf (by norm_num) ?_
    rw [hord]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnb₀ : b₀ ∉ Subgroup.zpowers a₀ := not_mem_zpowers_of_inv hbab₀ ha₀sq
  obtain ⟨r, hr, hnr⟩ := hnt
  have hcR : ⁅s, r⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (hsR r hr) (R.inv_mem hr)
  have hσc := conj_commutator_eq_inv hs2 r
  generalize hc : ⁅s, r⁆ = c at hnr hcR hσc
  rcases quat_normal_form hbab₀ hk₀ hclos₀ c hcR with ⟨i, hi⟩ | ⟨i, hi⟩
  ·
    have hodd : Odd i := by
      by_contra hne
      rw [Int.not_odd_iff_even] at hne
      obtain ⟨m, hm⟩ := hne
      apply hnr
      have : c = a₀ ^ m * a₀ ^ m := by rw [hi, hm, zpow_add]
      rw [this]
      exact square_mem_squaresSub (Subgroup.zpow_mem _ ha₀R m)
    obtain ⟨u, v, huv⟩ := (Odd.isCoprime_two hodd).pow_right (n := n + 1)
    have hpowz : a₀ ^ ((2 : ℤ) ^ (n + 1)) = 1 := by
      have : ((2 : ℤ) ^ (n + 1)) = ((2 ^ (n + 1) : ℕ) : ℤ) := by push_cast; ring
      rw [this, zpow_natCast]
      exact ha₀pow
    have hciu : c ^ u = a₀ := by
      rw [hi, ← zpow_mul]
      have h1 : i * u = 1 - 2 ^ (n + 1) * v := by linarith [huv]
      rw [h1, zpow_sub, zpow_one, zpow_mul, hpowz, one_zpow]
      simp
    have hcmem : c ∈ Subgroup.closure ({c, b₀} : Set G) := Subgroup.subset_closure (by simp)
    have hbmem : b₀ ∈ Subgroup.closure ({c, b₀} : Set G) := Subgroup.subset_closure (by simp)
    refine ⟨c, b₀, hcR, hb₀R, ?_, ?_, ⟨u * (((2 ^ n : ℕ)) : ℤ), ?_⟩, ?_, hσc⟩
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · rw [hx]
          exact hcR
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hb₀R
      · rw [← hclos₀, Subgroup.closure_le]
        rintro x (hx | hx)
        · rw [hx, ← hciu]
          exact Subgroup.zpow_mem _ hcmem u
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hbmem
    · rw [hi, conj_zpow_of_inv hbab₀, zpow_neg]
    · rw [zpow_mul, hciu, zpow_natCast]
      exact hbb₀
    · intro hb
      obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hcomm : b₀ * a₀ = a₀ * b₀ := by
        rw [← hp, ← hciu]
        exact (Commute.zpow_zpow_self c p u).eq
      apply ha₀sq
      have : b₀ * a₀ * b₀⁻¹ = a₀ := by rw [hcomm]; group
      rw [this] at hbab₀
      exact eq_inv_iff_mul_eq_one.mp hbab₀
  ·
    have hcc : c * c = b₀ * b₀ := by
      rw [hi]
      exact mul_zpow_mul_self_eq hbab₀ i
    by_cases hn : n = 1
    · subst hn
      have hbb2 : b₀ * b₀ = a₀ * a₀ := by
        rw [hbb₀]
        simp [pow_two]
      have hbinv : b₀⁻¹ = b₀ * a₀ ^ (-2 : ℤ) := by
        have h1 : b₀⁻¹ = b₀ * (b₀ * b₀)⁻¹ := by group
        rw [h1, hbb2]
        group
      have hcinv : c⁻¹ = b₀ * a₀ ^ (i - 2) := by
        calc c⁻¹ = a₀ ^ (-i) * b₀⁻¹ := by rw [hi]; group
          _ = a₀ ^ (-i) * (b₀ * a₀ ^ (-2 : ℤ)) := by rw [hbinv]
          _ = (a₀ ^ (-i) * b₀) * a₀ ^ (-2 : ℤ) := by group
          _ = b₀ * a₀ ^ (-(-i)) * a₀ ^ (-2 : ℤ) := by rw [zpow_mul_eq_of_inv hbab₀]
          _ = b₀ * a₀ ^ (i - 2) := by group
      have hbab' : a₀ * c * a₀⁻¹ = c⁻¹ := by
        have hzp := zpow_mul_eq_of_inv hbab₀ 1
        calc a₀ * c * a₀⁻¹ = a₀ * (b₀ * a₀ ^ i) * a₀⁻¹ := by rw [hi]
          _ = (a₀ ^ (1 : ℤ) * b₀) * a₀ ^ (i - 1) := by group
          _ = b₀ * a₀ ^ (-1 : ℤ) * a₀ ^ (i - 1) := by rw [hzp]
          _ = b₀ * a₀ ^ (i - 2) := by group
          _ = c⁻¹ := hcinv.symm
      have hcmem : c ∈ Subgroup.closure ({c, a₀} : Set G) := Subgroup.subset_closure (by simp)
      have hamem : a₀ ∈ Subgroup.closure ({c, a₀} : Set G) := Subgroup.subset_closure (by simp)
      refine ⟨c, a₀, hcR, ha₀R, ?_, hbab', ⟨2, ?_⟩, ?_, hσc⟩
      · apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro x (hx | hx)
          · rw [hx]
            exact hcR
          · rw [Set.mem_singleton_iff] at hx
            rw [hx]
            exact ha₀R
        · rw [← hclos₀, Subgroup.closure_le]
          have hb₀mem : b₀ ∈ Subgroup.closure ({c, a₀} : Set G) := by
            have h := Subgroup.mul_mem _ hcmem (Subgroup.zpow_mem _ hamem (-i))
            have e : c * a₀ ^ (-i) = b₀ := by rw [hi]; group
            simpa only [e] using h
          rintro x (hx | hx)
          · rw [hx]
            exact hamem
          · rw [Set.mem_singleton_iff] at hx
            rw [hx]
            exact hb₀mem
      · rw [zpow_two, hcc, hbb2]
      · exact not_mem_zpowers_of_inv hbab' (by rw [hcc]; exact hz0ne)
    · exfalso
      have hn2 : 2 ≤ n := by omega
      have hσa₀R : s * a₀ * s⁻¹ ∈ R := hsR a₀ ha₀R
      have hσa₀ : ∃ j : ℤ, s * a₀ * s⁻¹ = a₀ ^ j := by
        rcases quat_normal_form hbab₀ hk₀ hclos₀ _ hσa₀R with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨j, hj⟩
        · exfalso
          have hx2 : (s * a₀ * s⁻¹) * (s * a₀ * s⁻¹) = b₀ * b₀ := by
            rw [hj]
            exact mul_zpow_mul_self_eq hbab₀ j
          have hx4 : (s * a₀ * s⁻¹) ^ 4 = 1 := by
            have hp4 : ∀ x : G, x ^ 4 = (x * x) * (x * x) := fun x => by
              rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
            rw [hp4, hx2]
            exact hz0
          have hdvd : orderOf (s * a₀ * s⁻¹) ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
          have horder : orderOf (s * a₀ * s⁻¹) = 2 ^ (n + 1) := by
            rw [← hord]
            exact (MulAut.conj s).orderOf_eq a₀
          rw [horder] at hdvd
          have h1 : 2 ^ (n + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
          have h2 : 2 ^ 3 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      obtain ⟨j₁, hj₁⟩ := hσa₀
      have hσpow : ∀ x : ℤ, s * a₀ ^ x * s⁻¹ = a₀ ^ (j₁ * x) := by
        intro x
        rw [← conj_zpow, hj₁, ← zpow_mul]
      have hσb₀R : s * b₀ * s⁻¹ ∈ R := hsR b₀ hb₀R
      have hσb₀ : ∃ j₂ : ℤ, s * b₀ * s⁻¹ = b₀ * a₀ ^ j₂ := by
        rcases quat_normal_form hbab₀ hk₀ hclos₀ _ hσb₀R with ⟨j, hj⟩ | ⟨j, hj⟩
        · exfalso
          apply hnb₀
          have : b₀ = s * (s * b₀ * s⁻¹) * s⁻¹ := (sigma_sigma hs2 b₀).symm
          rw [this, hj, hσpow]
          exact Subgroup.zpow_mem_zpowers a₀ _
        · exact ⟨j, hj⟩
      obtain ⟨j₂, hj₂⟩ := hσb₀
      have hallc : ∀ r' ∈ R, ⁅s, r'⁆ ∈ Subgroup.zpowers a₀ := by
        intro r' hr'
        rcases quat_normal_form hbab₀ hk₀ hclos₀ r' hr' with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · have : ⁅s, a₀ ^ x⁆ = a₀ ^ (j₁ * x - x) := by
            rw [commutatorElement_def, hσpow]
            group
          rw [this]
          exact Subgroup.zpow_mem_zpowers a₀ _
        · have h1 : s * (b₀ * a₀ ^ x) * s⁻¹ = (s * b₀ * s⁻¹) * (s * a₀ ^ x * s⁻¹) := by group
          have : ⁅s, b₀ * a₀ ^ x⁆ = a₀ ^ (-(j₂ + j₁ * x - x)) := by
            calc ⁅s, b₀ * a₀ ^ x⁆
                = (s * b₀ * s⁻¹) * (s * a₀ ^ x * s⁻¹) * (b₀ * a₀ ^ x)⁻¹ := by
                  rw [commutatorElement_def, h1]
              _ = (b₀ * a₀ ^ j₂) * a₀ ^ (j₁ * x) * (b₀ * a₀ ^ x)⁻¹ := by rw [hj₂, hσpow]
              _ = b₀ * a₀ ^ (j₂ + j₁ * x - x) * b₀⁻¹ := by group
              _ = a₀ ^ (-(j₂ + j₁ * x - x)) := conj_zpow_of_inv hbab₀ _
          rw [this]
          exact Subgroup.zpow_mem_zpowers a₀ _
      have hcA := hallc r hr
      rw [hc] at hcA
      apply hnb₀
      have : b₀ = c * a₀ ^ (-i) := by rw [hi]; group
      rw [this]
      exact Subgroup.mul_mem _ hcA (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a₀) _)


theorem exists_coord (hquat : IsQuatSub R) (hs2 : s * s = 1)
    (hsR : ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hnt : ∃ r ∈ R, ⁅s, r⁆ ∉ squaresSub R) :
    ∃ a b : G, a ∈ R ∧ b ∈ R ∧ Subgroup.closure ({a, b} : Set G) = R ∧ b * a * b⁻¹ = a⁻¹ ∧
      (∃ k : ℤ, b * b = a ^ k) ∧ s * a * s⁻¹ = a⁻¹ ∧ s * b * s⁻¹ = b * a := by
  obtain ⟨a, b, haR, hbR, hclos, hbab, ⟨k, hk⟩, hnb, hsa⟩ := exists_adapted hquat hs2 hsR hnt
  obtain ⟨b₁, hb₁R, hclos₁, hbab₁, hk₁, hsb₁⟩ :=
    exists_adjust hs2 hsR haR hbR hclos hbab hk hnb hsa hnt
  exact ⟨a, b₁, haR, hb₁R, hclos₁, hbab₁, hk₁, hsa, hsb₁⟩

end Adapt

end CFSG.ClassicalInvolution.Asc77.T7DR
