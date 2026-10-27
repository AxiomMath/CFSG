module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8

open Subgroup

section

section Central
variable {K : Type*} [Group K] {A B : Subgroup K} {ζ : K}

theorem pow_two_pow_add_eq_one {x : K} {m n : ℕ} (h : x ^ 2 ^ m = 1) :
    x ^ 2 ^ (m + n) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

theorem exists_mul_of_mem_sup (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ s ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hsup : A ⊔ B = Subgroup.closure ((A : Set K) ∪ (B : Set K)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  intro s hs
  rw [hsup] at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem B, (mul_one x).symm⟩
    · exact ⟨1, one_mem A, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem A, 1, one_mem B, (mul_one (1 : K)).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    have h1 : b * a' = a' * b := (hcomm a' ha' b hb).symm
    refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
      _ = a * (a' * b) * b' := by rw [h1]
      _ = a * a' * (b * b') := by simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hc : Commute a b := hcomm a ha b hb
    refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    rw [mul_inv_rev, hc.inv_inv.eq]

theorem mem_B_of_centralizes (hA : Q8Like A ζ) (hBζ : ζ ∈ B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {s : K} (hs : s ∈ A ⊔ B)
    (hc : ∀ a ∈ A, s * a = a * s) : s ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm s hs
  have hcen : ∀ a' ∈ A, a * a' = a' * a := by
    intro a' ha'
    have h1 : a * b * a' = a' * (a * b) := hc a' ha'
    have h2 : b * a' = a' * b := (hcomm a' ha' b hb).symm
    have h3 : a * a' * b = a' * a * b := by
      calc a * a' * b = a * (a' * b) := mul_assoc a a' b
        _ = a * (b * a') := by rw [h2]
        _ = a * b * a' := (mul_assoc a b a').symm
        _ = a' * (a * b) := h1
        _ = a' * a * b := (mul_assoc a' a b).symm
    exact mul_right_cancel h3
  rcases hA.center a ha hcen with h1 | h1
  · rw [h1, one_mul]
    exact hb
  · rw [h1]
    exact mul_mem hBζ hb

theorem isPGroup_sup (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 2 ↥(A ⊔ B) := by
  intro g
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hcomm (g : K) g.2
  obtain ⟨k₁, hk₁⟩ := hA ⟨a, ha⟩
  obtain ⟨k₂, hk₂⟩ := hB ⟨b, hb⟩
  have ha1 : a ^ 2 ^ k₁ = 1 := by
    have h := congrArg Subtype.val hk₁
    simpa using h
  have hb1 : b ^ 2 ^ k₂ = 1 := by
    have h := congrArg Subtype.val hk₂
    simpa using h
  have hc : Commute a b := hcomm a ha b hb
  have ha2 : a ^ 2 ^ (k₁ + k₂) = 1 := pow_two_pow_add_eq_one ha1
  have hb2 : b ^ 2 ^ (k₁ + k₂) = 1 := by
    rw [Nat.add_comm]
    exact pow_two_pow_add_eq_one hb1
  refine ⟨k₁ + k₂, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [hab, hc.mul_pow, ha2, hb2, one_mul]

end Central

end

section

variable {K : Type*} [Group K]

theorem commutator_identity {a₁ a₂ b₁ b₂ : K} (h11 : Commute a₁ b₁) (h12 : Commute a₁ b₂)
    (h21 : Commute a₂ b₁) (h22 : Commute a₂ b₂)
    (h : (a₂ * b₂) * (a₁ * b₁) * (a₂ * b₂)⁻¹ = (a₁ * b₁)⁻¹) :
    (a₂ * a₁ * a₂⁻¹ * a₁⁻¹) * (b₂ * b₁ * b₂⁻¹ * b₁⁻¹) = ((a₁ * b₁) ^ 2)⁻¹ := by
  have hb : Commute a₂ (b₂ * b₁ * b₂⁻¹) := (h22.mul_right h21).mul_right h22.inv_right
  have hb' : (b₂ * b₁ * b₂⁻¹) * a₂⁻¹ = a₂⁻¹ * (b₂ * b₁ * b₂⁻¹) := (hb.inv_left).symm.eq
  have hvu : (a₂ * b₂) * (a₁ * b₁) * (a₂ * b₂)⁻¹ = (a₂ * a₁ * a₂⁻¹) * (b₂ * b₁ * b₂⁻¹) := by
    calc a₂ * b₂ * (a₁ * b₁) * (a₂ * b₂)⁻¹
        = a₂ * (b₂ * a₁) * (b₁ * b₂⁻¹) * a₂⁻¹ := by group
      _ = a₂ * (a₁ * b₂) * (b₁ * b₂⁻¹) * a₂⁻¹ := by rw [h12.symm.eq]
      _ = a₂ * a₁ * ((b₂ * b₁ * b₂⁻¹) * a₂⁻¹) := by group
      _ = a₂ * a₁ * (a₂⁻¹ * (b₂ * b₁ * b₂⁻¹)) := by rw [hb']
      _ = (a₂ * a₁ * a₂⁻¹) * (b₂ * b₁ * b₂⁻¹) := by group
  have h1 : Commute a₁⁻¹ (b₂ * b₁ * b₂⁻¹) :=
    ((h12.mul_right h11).mul_right h12.inv_right).inv_left
  calc (a₂ * a₁ * a₂⁻¹ * a₁⁻¹) * (b₂ * b₁ * b₂⁻¹ * b₁⁻¹)
      = (a₂ * a₁ * a₂⁻¹) * (a₁⁻¹ * (b₂ * b₁ * b₂⁻¹)) * b₁⁻¹ := by group
    _ = (a₂ * a₁ * a₂⁻¹) * ((b₂ * b₁ * b₂⁻¹) * a₁⁻¹) * b₁⁻¹ := by rw [h1.eq]
    _ = ((a₂ * a₁ * a₂⁻¹) * (b₂ * b₁ * b₂⁻¹)) * (a₁⁻¹ * b₁⁻¹) := by group
    _ = ((a₂ * a₁ * a₂⁻¹) * (b₂ * b₁ * b₂⁻¹)) * (b₁⁻¹ * a₁⁻¹) := by rw [h11.inv_inv.eq]
    _ = ((a₂ * b₂) * (a₁ * b₁) * (a₂ * b₂)⁻¹) * (a₁ * b₁)⁻¹ := by rw [hvu]; group
    _ = (a₁ * b₁)⁻¹ * (a₁ * b₁)⁻¹ := by rw [h]
    _ = ((a₁ * b₁) ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev (a₁ * b₁) (a₁ * b₁)]

end

section

variable {K : Type*} [Group K] {A B Y : Subgroup K} {ζ : K}

theorem Q8Like.sq_cases (hA : Q8Like A ζ) {a : K} (ha : a ∈ A) : a ^ 2 = 1 ∨ a ^ 2 = ζ := by
  have h4 : (a ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hA.pow4 a ha
  exact hA.uniq (a ^ 2) (A.pow_mem ha 2) h4

theorem QuatLike.sq_cases (hB : QuatLike B Y ζ) {b : K} (hb : b ∈ B) (h4 : b ^ 4 = 1) :
    b ^ 2 = 1 ∨ b ^ 2 = ζ := by
  have h4' : (b ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  exact hB.uniq (b ^ 2) (B.pow_mem hb 2) h4'

theorem central_of_unique_involution {G : Subgroup K} {ζ : K} (hζG : ζ ∈ G) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ^ 2 = 1) (huniq : ∀ g ∈ G, g ^ 2 = 1 → g = 1 ∨ g = ζ) {g : K} (hg : g ∈ G) :
    g * ζ = ζ * g := by
  have hmem : g * ζ * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hg hζG) (G.inv_mem hg)
  have hsq : (g * ζ * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hζ2]; group
  have hne : g * ζ * g⁻¹ ≠ 1 := by
    intro h
    apply hζ1
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  rcases huniq _ hmem hsq with h | h
  · exact absurd h hne
  · calc g * ζ = g * ζ * g⁻¹ * g := by group
      _ = ζ * g := by rw [h]

theorem mem_of_sq_eq_one {G H : Subgroup K} {ζ : K} (hζH : ζ ∈ H)
    (huniq : ∀ g ∈ G, g ^ 2 = 1 → g = 1 ∨ g = ζ) {g : K} (hg : g ∈ G) (hg2 : g ^ 2 = 1) :
    g ∈ H := by
  rcases huniq g hg hg2 with rfl | rfl
  · exact H.one_mem
  · exact hζH

theorem comm_of_sq_eq_one {G : Subgroup K} {ζ : K} (hζG : ζ ∈ G) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ^ 2 = 1) (huniq : ∀ g ∈ G, g ^ 2 = 1 → g = 1 ∨ g = ζ) {g : K} (hg : g ∈ G)
    (hg2 : g ^ 2 = 1) {g' : K} (hg' : g' ∈ G) : g * g' = g' * g := by
  rcases huniq g hg hg2 with rfl | rfl
  · simp
  · exact (central_of_unique_involution hζG hζ1 hζ2 huniq hg').symm

theorem comm4_eq_one {x y : K} (h : x * y = y * x) : x * y * x⁻¹ * y⁻¹ = 1 := by
  rw [h]; group

theorem pair_sq (hA : Q8Like A ζ) (hB : QuatLike B Y ζ) {a b : K} (ha : a ∈ A) (hb : b ∈ B)
    (hab : Commute a b) (h4 : (a * b) ^ 4 = 1) (hne : (a * b) ^ 2 ≠ 1) :
    (a ^ 2 = ζ ∧ b ^ 2 = 1) ∨ (a ^ 2 = 1 ∧ b ^ 2 = ζ) := by
  have h4' : a ^ 4 * b ^ 4 = 1 := by rw [← hab.mul_pow]; exact h4
  have hb4 : b ^ 4 = 1 := by rw [hA.pow4 a ha, one_mul] at h4'; exact h4'
  have hsq : (a * b) ^ 2 = a ^ 2 * b ^ 2 := hab.mul_pow 2
  rcases hA.sq_cases ha with h1 | h1 <;> rcases hB.sq_cases hb hb4 with h2 | h2
  · exact absurd (by rw [hsq, h1, h2, one_mul]) hne
  · right; exact ⟨h1, h2⟩
  · left; exact ⟨h1, h2⟩
  · exfalso; apply hne; rw [hsq, h1, h2, ← sq]; exact hB.ζ_sq

theorem qpair_dichotomy (hA : Q8Like A ζ) (hB : QuatLike B Y ζ)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {u v : K} (hu : u ∈ A ⊔ B) (hv : v ∈ A ⊔ B)
    (h : QPair u v) : (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup hcomm u hu
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup hcomm v hv
  have c11 : Commute a₁ b₁ := hcomm a₁ ha₁ b₁ hb₁
  have c12 : Commute a₁ b₂ := hcomm a₁ ha₁ b₂ hb₂
  have c21 : Commute a₂ b₁ := hcomm a₂ ha₂ b₁ hb₁
  have c22 : Commute a₂ b₂ := hcomm a₂ ha₂ b₂ hb₂
  obtain ⟨h4, hne, hsq, hconj⟩ := h
  have hζA : ζ ∈ A := hA.ζ_mem
  have hζB : ζ ∈ B := hB.Y_le hB.ζ_mem
  have P1 := pair_sq hA hB ha₁ hb₁ c11 h4 hne
  have h4v : (a₂ * b₂) ^ 4 = 1 := by
    have : (a₂ * b₂) ^ 4 = ((a₂ * b₂) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hsq, ← pow_mul]; exact h4
  have hnev : (a₂ * b₂) ^ 2 ≠ 1 := by rw [hsq]; exact hne
  have P2 := pair_sq hA hB ha₂ hb₂ c22 h4v hnev
  have hu2 : (a₁ * b₁) ^ 2 = ζ := by
    rw [c11.mul_pow]; rcases P1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hid := commutator_identity c11 c12 c21 c22 hconj
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hB.ζ_sq)
  rw [hu2, hζinv] at hid
  rcases hA.comm a₂ ha₂ a₁ ha₁ with hc1 | hc1
  ·
    rw [hc1, one_mul] at hid
    have hb1 : b₁ ^ 2 ≠ 1 := by
      intro h2
      have := comm_of_sq_eq_one hζB hB.ζ_ne hB.ζ_sq hB.uniq hb₁ h2 hb₂
      have h3 := comm4_eq_one this.symm
      rw [h3] at hid
      exact hB.ζ_ne hid.symm
    have hb2 : b₂ ^ 2 ≠ 1 := by
      intro h2
      have := comm_of_sq_eq_one hζB hB.ζ_ne hB.ζ_sq hB.uniq hb₂ h2 hb₁
      have h3 := comm4_eq_one this
      rw [h3] at hid
      exact hB.ζ_ne hid.symm
    right
    have ha1 : a₁ ^ 2 = 1 := by
      rcases P1 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h2 hb1
      · exact h1
    have ha2 : a₂ ^ 2 = 1 := by
      rcases P2 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h2 hb2
      · exact h1
    exact ⟨B.mul_mem (mem_of_sq_eq_one hζB hA.uniq ha₁ ha1) hb₁,
      B.mul_mem (mem_of_sq_eq_one hζB hA.uniq ha₂ ha2) hb₂⟩
  ·
    have ha1 : a₁ ^ 2 ≠ 1 := by
      intro h2
      have := comm_of_sq_eq_one hζA hA.ζ_ne hA.ζ_sq hA.uniq ha₁ h2 ha₂
      have h3 := comm4_eq_one this.symm
      rw [h3] at hc1
      exact hA.ζ_ne hc1.symm
    have ha2 : a₂ ^ 2 ≠ 1 := by
      intro h2
      have := comm_of_sq_eq_one hζA hA.ζ_ne hA.ζ_sq hA.uniq ha₂ h2 ha₁
      have h3 := comm4_eq_one this
      rw [h3] at hc1
      exact hA.ζ_ne hc1.symm
    left
    have hb1 : b₁ ^ 2 = 1 := by
      rcases P1 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd h1 ha1
    have hb2 : b₂ ^ 2 = 1 := by
      rcases P2 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd h1 ha2
    exact ⟨A.mul_mem ha₁ (mem_of_sq_eq_one hζA hB.uniq hb₁ hb1),
      A.mul_mem ha₂ (mem_of_sq_eq_one hζA hB.uniq hb₂ hb2)⟩

end

section

section Cyc
variable {K : Type*} [Group K]

theorem exists_zpowers_inf_of_isCyclic {Y : Subgroup K} (hY : IsCyclic Y) (H : Subgroup K) :
    ∃ c : K, H ⊓ Y = Subgroup.zpowers c := by
  obtain ⟨y, hy⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).mp hY
  have hle : H ⊓ Y ≤ Subgroup.zpowers y := inf_le_right.trans_eq hy.symm
  obtain ⟨n, hn⟩ := (Subgroup.le_zpowers_iff y (H ⊓ Y)).mp hle
  exact ⟨y ^ n, hn⟩

end Cyc

section Central4
variable {K : Type*} [Group K] {B Y : Subgroup K} {ζ : K}

theorem aux_eq_or_inv_of_sq (hB : QuatLike B Y ζ) {t s : K} (ht : t ∈ B) (ht2 : t ^ 2 = ζ)
    (hcomm : t * s = s * t) (hs : s ∈ B) (hs2 : s ^ 2 = ζ) : s = t ∨ s = t⁻¹ := by
  have hζζ : ζ * ζ = 1 := by
    rw [← pow_two]
    exact hB.ζ_sq
  have hts : (t * s) ^ 2 = 1 := by
    rw [Commute.mul_pow (show Commute t s from hcomm) 2, ht2, hs2]
    exact hζζ
  have hmem : t * s ∈ B := Subgroup.mul_mem B ht hs
  rcases hB.uniq (t * s) hmem hts with h | h
  · exact Or.inr (eq_inv_of_mul_eq_one_right h)
  · left
    have h' : t * t = t * s := by
      rw [h, ← ht2, pow_two]
    exact (mul_left_cancel h').symm

theorem no_commuting_qpairs_in_B (hB : QuatLike B Y ζ) {u₁ u₂ v₂ : K} (h1 : u₁ ∈ B)
    (h2 : u₂ ∈ B) (h3 : v₂ ∈ B) (hu₁ : u₁ ^ 4 = 1 ∧ u₁ ^ 2 ≠ 1) (hq : QPair u₂ v₂)
    (c2 : u₁ * u₂ = u₂ * u₁) (c3 : u₁ * v₂ = v₂ * u₁) : False := by
  obtain ⟨hu₂4, hu₂2, hv₂2, hconj⟩ :
      u₂ ^ 4 = 1 ∧ u₂ ^ 2 ≠ 1 ∧ v₂ ^ 2 = u₂ ^ 2 ∧ v₂ * u₂ * v₂⁻¹ = u₂⁻¹ := hq
  have hsq1 : (u₁ ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hu₁.1
  have hsq2 : (u₂ ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hu₂4
  have hζ1 : u₁ ^ 2 = ζ := (hB.uniq (u₁ ^ 2) (pow_mem h1 2) hsq1).resolve_left hu₁.2
  have hζ2 : u₂ ^ 2 = ζ := (hB.uniq (u₂ ^ 2) (pow_mem h2 2) hsq2).resolve_left hu₂2
  have hζ3 : v₂ ^ 2 = ζ := hv₂2.trans hζ2
  have hu : u₂ = u₁ ∨ u₂ = u₁⁻¹ := aux_eq_or_inv_of_sq hB h1 hζ1 c2 h2 hζ2
  have hv : v₂ = u₁ ∨ v₂ = u₁⁻¹ := aux_eq_or_inv_of_sq hB h1 hζ1 c3 h3 hζ3
  have hcomm : v₂ * u₂ = u₂ * v₂ := by
    rcases hu with h | h <;> rcases hv with h' | h' <;> simp [h, h']
  have hfix : u₂ = u₂⁻¹ := by
    rw [← hconj, hcomm, mul_inv_cancel_right]
  have hsq : u₂ ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hfix
  exact hu₂2 hsq

theorem two_gen_of_quatLike (hB : QuatLike B Y ζ) (H : Subgroup K) (hH : H ≤ B) :
    ∃ u v : K, H = Subgroup.closure {u, v} := by
  obtain ⟨c, hc⟩ := exists_zpowers_inf_of_isCyclic hB.Y_cyc H
  have hcH : c ∈ H := by
    have hcHY : c ∈ H ⊓ Y := by
      rw [hc]
      exact Subgroup.mem_zpowers c
    exact (Subgroup.mem_inf.mp hcHY).1
  by_cases hHY : H ≤ Y
  · refine ⟨c, c, ?_⟩
    rw [Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure, ← hc, inf_eq_left.mpr hHY]
  · obtain ⟨g, hgH, hgY⟩ := SetLike.not_le_iff_exists.mp hHY
    refine ⟨c, g, le_antisymm ?_ ?_⟩
    · intro h hh
      by_cases hhY : h ∈ Y
      · have hmem : h ∈ H ⊓ Y := Subgroup.mem_inf.mpr ⟨hh, hhY⟩
        rw [hc] at hmem
        exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c {g}))) hmem
      · have hmemY : h * g⁻¹ ∈ Y := hB.idx h (hH hh) g (hH hgH) hhY hgY
        have hmemH : h * g⁻¹ ∈ H := Subgroup.mul_mem H hh (Subgroup.inv_mem H hgH)
        have hmem : h * g⁻¹ ∈ H ⊓ Y := Subgroup.mem_inf.mpr ⟨hmemH, hmemY⟩
        rw [hc] at hmem
        have hA : h * g⁻¹ ∈ Subgroup.closure {c, g} :=
          (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c {g}))) hmem
        have hG : g ∈ Subgroup.closure {c, g} :=
          Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton g))
        have key := Subgroup.mul_mem _ hA hG
        rwa [inv_mul_cancel_right] at key
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hcH, hgH⟩

end Central4

end

section

section Target
variable {K : Type*} [Group K] {B Y : Subgroup K} {ζ : K}

theorem le_closure_qpairs_of_quatLike (hB : QuatLike B Y ζ) (H : Subgroup K) (hH : H ≤ B)
    {u v : K} (hu : u ∈ H) (hv : v ∈ H) (huv : QPair u v) :
    H ≤ Subgroup.closure {g | g ∈ H ∧ ∃ w ∈ H, QPair g w} := by
  have huB : u ∈ B := hH hu
  have hvB : v ∈ B := hH hv
  have hu2 : u ^ 2 = ζ := by
    have hmem : u ^ 2 ∈ B := by
      rw [pow_two]
      exact B.mul_mem huB huB
    have h4 : (u ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact huv.1
    rcases hB.uniq (u ^ 2) hmem h4 with h | h
    · exact absurd h huv.2.1
    · exact h
  have hv2 : v ^ 2 = ζ := huv.2.2.1.trans hu2
  have hy1 : ∃ y₁ ∈ H, y₁ ∈ Y ∧ y₁ ^ 2 = ζ := by
    by_cases hu' : u ∈ Y
    · exact ⟨u, hu, hu', hu2⟩
    by_cases hv' : v ∈ Y
    · exact ⟨v, hv, hv', hv2⟩
    refine ⟨u * v, H.mul_mem hu hv, ?_, ?_⟩
    · have hidx : u * v⁻¹ ∈ Y := hB.idx u huB v hvB hu' hv'
      have hsplit : u * v = u * v⁻¹ * ζ := by
        rw [← hv2]
        group
      rw [hsplit]
      exact Y.mul_mem hidx hB.ζ_mem
    · have hvu : v * u = u⁻¹ * v := by
        calc v * u = v * u * v⁻¹ * v := by group
          _ = u⁻¹ * v := by rw [huv.2.2.2]
      rw [pow_two]
      calc u * v * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
        _ = u * (u⁻¹ * v) * v := by rw [hvu]
        _ = v ^ 2 := by rw [pow_two]; group
        _ = ζ := hv2
  obtain ⟨y₁, hy₁H, hy₁Y, hy₁sq⟩ := hy1
  have hg0 : ∃ g₀ ∈ H, g₀ ∉ Y := by
    by_contra hcon
    push_neg at hcon
    have hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
      intro a ha b hb
      haveI := hB.Y_cyc
      letI : CommGroup Y := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Y) ⟨b, hb⟩)
    have hcomm : v * u = u * v := hYc v (hcon v hv) u (hcon u hu)
    have h1 : u * v * v⁻¹ = u⁻¹ := by
      rw [← hcomm]
      exact huv.2.2.2
    rw [mul_inv_cancel_right] at h1
    apply huv.2.1
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 h1
  obtain ⟨g₀, hg₀H, hg₀Y⟩ := hg0
  have hΘ : ∀ g ∈ H, g ∉ Y → g ∈ Subgroup.closure {g | g ∈ H ∧ ∃ w ∈ H, QPair g w} := by
    intro g hgH hgY
    have hgB : g ∈ B := hH hgH
    have hg2 : g ^ 2 = ζ := hB.out_sq g hgB hgY
    have hg4 : g ^ 4 = 1 := by
      have e4 : g ^ 4 = (g ^ 2) ^ 2 := by
        rw [← pow_mul] <;> norm_num
      rw [e4, hg2, hB.ζ_sq]
    have hy1g : y₁ ^ 2 = g ^ 2 := hy₁sq.trans hg2.symm
    have hinv : y₁⁻¹ ∈ Y := Y.inv_mem hy₁Y
    have e : g * y₁⁻¹ * g⁻¹ = y₁ := by
      have h := hB.out_inv g hgB hgY y₁⁻¹ hinv
      rwa [inv_inv] at h
    have hconj : y₁ * g * y₁⁻¹ = g⁻¹ := by
      calc y₁ * g * y₁⁻¹ = (g * y₁⁻¹ * g⁻¹) * g * y₁⁻¹ := by rw [e]
        _ = g * y₁⁻¹ * y₁⁻¹ := by group
        _ = g * (y₁ ^ 2)⁻¹ := by group
        _ = g * ζ⁻¹ := by rw [hy₁sq]
        _ = g * (g ^ 2)⁻¹ := by rw [hg2]
        _ = g⁻¹ := by group
    have hmem : g ∈ {x : K | x ∈ H ∧ ∃ w ∈ H, QPair x w} := by
      show g ∈ H ∧ ∃ w ∈ H, QPair g w
      refine ⟨hgH, y₁, hy₁H, ?_⟩
      unfold QPair
      refine ⟨hg4, ?_, hy1g, hconj⟩
      rw [hg2]
      exact hB.ζ_ne
    exact Subgroup.subset_closure hmem
  intro h hh
  by_cases hhY : h ∈ Y
  · have h1 : h * g₀ ∈ H := H.mul_mem hh hg₀H
    have h1Y : h * g₀ ∉ Y := by
      intro hc
      apply hg₀Y
      simpa using Y.mul_mem (Y.inv_mem hhY) hc
    have h2 : g₀⁻¹ ∈ H := H.inv_mem hg₀H
    have h2Y : g₀⁻¹ ∉ Y := by
      intro hc
      apply hg₀Y
      simpa using Y.inv_mem hc
    have hC := Subgroup.mul_mem _ (hΘ _ h1 h1Y) (hΘ _ h2 h2Y)
    rwa [mul_inv_cancel_right] at hC
  · exact hΘ h hh hhY

end Target

end

section

section RelIndexInfLe

variable {K : Type*} [Group K] {A B : Subgroup K}

theorem relIndex_sup_le_of_comm [Finite K] (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B.relIndex (A ⊔ B) ≤ B.relIndex A := by
  have hmap : ∀ a b : ↥A, QuotientGroup.leftRel (B.subgroupOf A) a b →
      QuotientGroup.leftRel (B.subgroupOf (A ⊔ B))
        (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B) a)
        (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B) b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf]
    simpa using hab
  have hf : Function.Surjective
      (Quotient.map' (s₁ := QuotientGroup.leftRel (B.subgroupOf A))
        (s₂ := QuotientGroup.leftRel (B.subgroupOf (A ⊔ B)))
        (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B) : ↥A → ↥(A ⊔ B)) hmap) := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, b, hb, hs⟩ := exists_mul_of_mem_sup hcomm (s : K) s.2
    refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : ↥A) : ↥A ⧸ B.subgroupOf A), ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B) (⟨a, ha⟩ : ↥A)) :
      ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) = QuotientGroup.mk s
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [hs] using hb
  haveI : Finite (Quotient (QuotientGroup.leftRel (B.subgroupOf A))) :=
    Finite.of_surjective _ (QuotientGroup.mk_surjective (s := B.subgroupOf A))
  show Nat.card (↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) ≤ Nat.card (↥A ⧸ B.subgroupOf A)
  exact Nat.card_le_card_of_surjective _ hf

theorem relIndex_inf_le_four [Finite K] (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : Nat.card A = 8) (hAB : Nat.card (A ⊓ B : Subgroup K) = 2) {Q : Subgroup K}
    (hQ : Q ≤ A ⊔ B) : (Q ⊓ B).relIndex Q ≤ 4 := by
  have h3 : B.relIndex A = 4 := by
    have h := relIndex_mul_card (H := B) (K := A)
    have hBA : Nat.card (B ⊓ A : Subgroup K) = 2 := by
      rw [inf_comm]
      exact hAB
    rw [hBA, hA] at h
    omega
  have h1 : (Q ⊓ B).relIndex Q = B.relIndex Q := inf_relIndex_left (H := Q) (K := B)
  have hne : B.relIndex (A ⊔ B) ≠ 0 := by
    intro h0
    have hd := relIndex_dvd_card (H := B) (K := A ⊔ B)
    rw [h0, zero_dvd_iff] at hd
    haveI : Nonempty ↥(A ⊔ B) := ⟨1⟩
    have hpos : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    omega
  have h2 : B.relIndex Q ≤ B.relIndex (A ⊔ B) := relIndex_le_of_le_right hQ hne
  have h4 : B.relIndex (A ⊔ B) ≤ B.relIndex A := relIndex_sup_le_of_comm hcomm
  omega

end RelIndexInfLe

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8
