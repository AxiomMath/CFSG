module

public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.Action

public section

namespace CFSG.GH74.QTGen4.Leaves

section Rank5

variable {G : Type} [Group G]

theorem rank5_sq_comm {a b z : G} (h : a * b = z * (b * a)) (haz : a * z = z * a)
    (hzz : z * z = 1) : a ^ 2 * b = b * a ^ 2 := by
  calc a ^ 2 * b = a * (a * b) := by rw [pow_two, mul_assoc]
    _ = a * (z * (b * a)) := by rw [h]
    _ = (a * z) * (b * a) := by simp only [mul_assoc]
    _ = (z * a) * (b * a) := by rw [haz]
    _ = z * (a * b) * a := by simp only [mul_assoc]
    _ = z * (z * (b * a)) * a := by rw [h]
    _ = (z * z) * b * (a * a) := by simp only [mul_assoc]
    _ = b * a ^ 2 := by rw [hzz, one_mul, pow_two]

theorem rank5_qr_pow {z r q : G} (hqr : q * r = z * (r * q))
    (hrz : r * z = z * r) (hqz : q * z = z * q) :
    ∀ b c : ℕ, q ^ b * r ^ c = z ^ (b * c) * (r ^ c * q ^ b) := by
  have hcr : Commute r z := hrz
  have hcq : Commute q z := hqz
  have hzr : ∀ n : ℕ, r ^ n * z = z * r ^ n := fun n => (hcr.pow_left n).eq
  have hzq : ∀ n : ℕ, q * z ^ n = z ^ n * q := fun n => (hcq.pow_right n).eq
  have hzr' : ∀ n : ℕ, r * z ^ n = z ^ n * r := fun n => (hcr.pow_right n).eq
  have step1 : ∀ c : ℕ, q * r ^ c = z ^ c * (r ^ c * q) := by
    intro c
    induction c with
    | zero => simp
    | succ c ih =>
      calc q * r ^ (c + 1) = (q * r ^ c) * r := by rw [pow_succ, mul_assoc]
        _ = (z ^ c * (r ^ c * q)) * r := by rw [ih]
        _ = z ^ c * (r ^ c * (q * r)) := by simp only [mul_assoc]
        _ = z ^ c * (r ^ c * (z * (r * q))) := by rw [hqr]
        _ = z ^ c * ((r ^ c * z) * (r * q)) := by simp only [mul_assoc]
        _ = z ^ c * ((z * r ^ c) * (r * q)) := by rw [hzr]
        _ = z ^ (c + 1) * (r ^ (c + 1) * q) := by rw [pow_succ z c, pow_succ r c]; simp only [mul_assoc]
  intro b c
  induction b with
  | zero => simp
  | succ b ih =>
    calc q ^ (b + 1) * r ^ c = q * (q ^ b * r ^ c) := by rw [pow_succ', mul_assoc]
      _ = q * (z ^ (b * c) * (r ^ c * q ^ b)) := by rw [ih]
      _ = z ^ (b * c) * (q * (r ^ c * q ^ b)) := by rw [← mul_assoc, hzq, mul_assoc]
      _ = z ^ (b * c) * ((q * r ^ c) * q ^ b) := by simp only [mul_assoc]
      _ = z ^ (b * c) * ((z ^ c * (r ^ c * q)) * q ^ b) := by rw [step1]
      _ = z ^ (b * c + c) * (r ^ c * q ^ (b + 1)) := by
        rw [pow_add, pow_succ' q b]; simp only [mul_assoc]
      _ = z ^ ((b + 1) * c) * (r ^ c * q ^ (b + 1)) := by rw [Nat.succ_mul]


theorem rank5_false [Finite G] (hG : CFSG.GH74.Gen4 G)
    {Q V C : Subgroup G} {z r q : G}
    (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hV16 : Nat.card V = 2 ^ 4) (hz : orderOf z = 2) (hVC : V ⊓ C = Subgroup.zpowers z)
    (hr : r ∈ Q) (hq : q ∈ Q) (hrV : ∀ v ∈ V, r * v = v * r) (hqV : ∀ v ∈ V, q * v = v * q)
    (hr2 : r ^ 2 ∈ C) (hq2 : q ^ 2 ∈ C) (hrq : r * q * r⁻¹ * q⁻¹ = z) : False := by
  classical
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzVC : z ∈ V ⊓ C := hVC ▸ Subgroup.mem_zpowers z
  have hzV : z ∈ V := hzVC.1
  have hzC : z ∈ C := hzVC.2
  have hrz : r * z = z * r := hrV z hzV
  have hqz : q * z = z * q := hqV z hzV
  have h1 : r * q = z * (q * r) := by
    calc r * q = (r * q * r⁻¹ * q⁻¹) * (q * r) := by group
      _ = z * (q * r) := by rw [hrq]
  have h2 : q * r = z * (r * q) := by
    calc q * r = (z * z) * (q * r) := by rw [hzz, one_mul]
      _ = z * (z * (q * r)) := by rw [mul_assoc]
      _ = z * (r * q) := by rw [← h1]
  have hnc : r * q ≠ q * r := by
    intro h
    have : z * (q * r) = 1 * (q * r) := by rw [← h1, h, one_mul]
    exact hz1 (mul_right_cancel this)
  let M : Subgroup G := Subgroup.closure ({z, r ^ 2, q ^ 2} : Set G)
  have hzM : z ∈ M := Subgroup.subset_closure (by simp)
  have hr2M : r ^ 2 ∈ M := Subgroup.subset_closure (by simp)
  have hq2M : q ^ 2 ∈ M := Subgroup.subset_closure (by simp)
  have hMC : M ≤ C := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> rw [hx] <;> assumption
  have hr2q : r ^ 2 * q = q * r ^ 2 := rank5_sq_comm h1 hrz hzz
  have hq2r : q ^ 2 * r = r * q ^ 2 := rank5_sq_comm h2 hqz hzz
  have hMcent : M ≤ Subgroup.centralizer ({r, q} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hg
    rcases hx with hx | hx | hx <;> rcases hg with hg | hg <;> rw [hx, hg]
    · exact hrz
    · exact hqz
    · exact (Commute.refl r).pow_right 2 |>.eq
    · exact hr2q.symm
    · exact hq2r.symm
    · exact (Commute.refl q).pow_right 2 |>.eq
  have hMx : ∀ m ∈ M, ∀ a b : ℕ, m * (r ^ a * q ^ b) = (r ^ a * q ^ b) * m := by
    intro m hm a b
    have hmr : m * r = r * m := (Subgroup.mem_centralizer_iff.1 (hMcent hm) r (by simp)).symm
    have hmq : m * q = q * m := (Subgroup.mem_centralizer_iff.1 (hMcent hm) q (by simp)).symm
    have hmr' : Commute m (r ^ a) := Commute.pow_right (show Commute m r from hmr) a
    have hmq' : Commute m (q ^ b) := Commute.pow_right (show Commute m q from hmq) b
    exact (hmr'.mul_right hmq').eq
  have hrzp : ∀ a n : ℕ, r ^ a * z ^ n = z ^ n * r ^ a := fun a n =>
    (Commute.pow_pow (show Commute r z from hrz) a n).eq
  let S : Set G := {x | ∃ m ∈ M, ∃ a b : ℕ, x = m * (r ^ a * q ^ b)}
  have hSone : (1 : G) ∈ S := ⟨1, M.one_mem, 0, 0, by simp⟩
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨m₁, hm₁, a, b, rfl⟩ _ ⟨m₂, hm₂, c, d, rfl⟩
    refine ⟨m₁ * m₂ * z ^ (b * c), M.mul_mem (M.mul_mem hm₁ hm₂) (M.pow_mem hzM _), a + c,
      b + d, ?_⟩
    have hqr := rank5_qr_pow h2 hrz hqz b c
    calc m₁ * (r ^ a * q ^ b) * (m₂ * (r ^ c * q ^ d))
        = m₁ * ((r ^ a * q ^ b) * m₂) * (r ^ c * q ^ d) := by simp only [mul_assoc]
      _ = m₁ * (m₂ * (r ^ a * q ^ b)) * (r ^ c * q ^ d) := by rw [← hMx m₂ hm₂ a b]
      _ = m₁ * m₂ * (r ^ a * (q ^ b * r ^ c) * q ^ d) := by simp only [mul_assoc]
      _ = m₁ * m₂ * (r ^ a * (z ^ (b * c) * (r ^ c * q ^ b)) * q ^ d) := by rw [hqr]
      _ = m₁ * m₂ * ((r ^ a * z ^ (b * c)) * (r ^ c * q ^ b) * q ^ d) := by simp only [mul_assoc]
      _ = m₁ * m₂ * ((z ^ (b * c) * r ^ a) * (r ^ c * q ^ b) * q ^ d) := by rw [hrzp]
      _ = m₁ * m₂ * z ^ (b * c) * (r ^ (a + c) * q ^ (b + d)) := by
        rw [pow_add r a c, pow_add q b d]; simp only [mul_assoc]
  have hSpow : ∀ x ∈ S, ∀ n : ℕ, x ^ n ∈ S := by
    intro x hx n
    induction n with
    | zero => simpa using hSone
    | succ n ih => rw [pow_succ]; exact hSmul _ ih _ hx
  have hSinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro x hx
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x)]
      exact pow_orderOf_eq_one x
    rw [this]
    exact hSpow x hx _
  have hHS : ∀ x ∈ Subgroup.closure ({r, q} : Set G), x ∈ S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · exact ⟨1, M.one_mem, 1, 0, by simp [hy]⟩
      · exact ⟨1, M.one_mem, 0, 1, by simp [hy]⟩
    | one => exact hSone
    | mul a b _ _ ha hb => exact hSmul _ ha _ hb
    | inv a _ ha => exact hSinv _ ha
  have hVHM : ∀ x ∈ V, x ∈ Subgroup.closure ({r, q} : Set G) → x ∈ M := by
    intro x hxV hxH
    obtain ⟨m, hm, a, b, rfl⟩ := hHS x hxH
    have hha : r ^ a = (r ^ 2) ^ (a / 2) * r ^ (a % 2) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hhb : q ^ b = (q ^ 2) ^ (b / 2) * q ^ (b % 2) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hq2j : (q ^ 2) ^ (b / 2) ∈ M := M.pow_mem hq2M _
    have hr2i : (r ^ 2) ^ (a / 2) ∈ M := M.pow_mem hr2M _
    have hcom : r ^ (a % 2) * (q ^ 2) ^ (b / 2) = (q ^ 2) ^ (b / 2) * r ^ (a % 2) := by
      have := hMx _ hq2j (a % 2) 0
      simpa using this.symm
    obtain ⟨m', hm', e, f, he, hf, hx⟩ : ∃ m' ∈ M, ∃ e f : ℕ, e ≤ 1 ∧ f ≤ 1 ∧
        m * (r ^ a * q ^ b) = m' * (r ^ e * q ^ f) := by
      refine ⟨m * (r ^ 2) ^ (a / 2) * (q ^ 2) ^ (b / 2),
        M.mul_mem (M.mul_mem hm hr2i) hq2j, a % 2, b % 2, by omega, by omega, ?_⟩
      rw [hha, hhb]
      calc m * ((r ^ 2) ^ (a / 2) * r ^ (a % 2) * ((q ^ 2) ^ (b / 2) * q ^ (b % 2)))
          = m * (r ^ 2) ^ (a / 2) * (r ^ (a % 2) * (q ^ 2) ^ (b / 2)) * q ^ (b % 2) := by
            simp only [mul_assoc]
        _ = m * (r ^ 2) ^ (a / 2) * ((q ^ 2) ^ (b / 2) * r ^ (a % 2)) * q ^ (b % 2) := by
            rw [hcom]
        _ = _ := by simp only [mul_assoc]
    rw [hx] at hxV ⊢
    have hm'r : m' * r = r * m' :=
      (Subgroup.mem_centralizer_iff.1 (hMcent hm') r (by simp)).symm
    have hm'q : m' * q = q * m' :=
      (Subgroup.mem_centralizer_iff.1 (hMcent hm') q (by simp)).symm
    have hrx := hrV _ hxV
    have hqx := hqV _ hxV
    interval_cases e <;> interval_cases f
    · simpa using hm'
    · exfalso
      simp only [pow_zero, pow_one, one_mul] at hrx hqx
      apply hnc
      have : m' * (r * q) = m' * (q * r) := by
        calc m' * (r * q) = (m' * r) * q := by rw [mul_assoc]
          _ = (r * m') * q := by rw [hm'r]
          _ = r * (m' * q) := by rw [mul_assoc]
          _ = (m' * q) * r := hrx
          _ = m' * (q * r) := by rw [mul_assoc]
      exact mul_left_cancel this
    · exfalso
      simp only [pow_zero, pow_one, mul_one] at hrx hqx
      apply hnc
      have : m' * (q * r) = m' * (r * q) := by
        calc m' * (q * r) = (m' * q) * r := by rw [mul_assoc]
          _ = (q * m') * r := by rw [hm'q]
          _ = q * (m' * r) := by rw [mul_assoc]
          _ = (m' * r) * q := hqx
          _ = m' * (r * q) := by rw [mul_assoc]
      exact (mul_left_cancel this).symm
    · exfalso
      simp only [pow_one] at hrx hqx
      apply hnc
      have : (m' * r) * (r * q) = (m' * r) * (q * r) := by
        calc (m' * r) * (r * q) = (r * m') * (r * q) := by rw [hm'r]
          _ = r * (m' * (r * q)) := by simp only [mul_assoc]
          _ = (m' * (r * q)) * r := hrx
          _ = (m' * r) * (q * r) := by simp only [mul_assoc]
      exact mul_left_cancel this
  let H : Subgroup G := Subgroup.closure ({r, q} : Set G)
  have hrH : r ∈ H := Subgroup.subset_closure (by simp)
  have hqH : q ∈ H := Subgroup.subset_closure (by simp)
  have hHQ : H ≤ Q := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> rw [hx] <;> assumption
  have hHV : H ≤ Subgroup.centralizer (V : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> intro g hg <;> rw [hx]
    · exact (hrV g hg).symm
    · exact (hqV g hg).symm
  have hVp : IsPGroup 2 V := hQ.to_le hVQ
  have hHp : IsPGroup 2 H := hQ.to_le hHQ
  have hcomm : ∀ v ∈ V, ∀ h ∈ H, v * h = h * v := fun v hv h hh =>
    (Subgroup.mem_centralizer_iff.1 (hHV hh) v hv)
  have key := CFSG.GH74.E2.gen4_rank_add_le hG V H hVp hHp hcomm
  have hrV4 : Group.rank ↥V = 4 := by
    have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2)⟩⟩
    have h := CFSG.GH74.E2.two_pow_rank_eq_card_of_exponent_two (Y := ↥V)
      (fun y => Subtype.ext (hV2 y.1 y.2))
    rw [hV16] at h
    exact Nat.pow_right_injective le_rfl h
  have hKle : V ⊓ H ≤ Subgroup.zpowers z := by
    intro x hx
    rw [← hVC]
    exact ⟨hx.1, hMC (hVHM x hx.1 hx.2)⟩
  have hcardK : Nat.card ↥(V ⊓ H) ≤ 2 := by
    refine (Subgroup.card_le_of_le hKle).trans ?_
    rw [Nat.card_zpowers, hz]
  have hrK : Group.rank ↥(V ⊓ H) ≤ 1 := CFSG.GH74.E2.rank_le_one_of_card_le_two hcardK
  have hrH2 : 2 ≤ Group.rank ↥H := by
    by_contra hlt
    push Not at hlt
    obtain ⟨S₀, hS₀, hcl⟩ := Group.rank_spec ↥H
    have hcard : S₀.card ≤ 1 := by omega
    have hcommH : ∀ x y : ↥H, x * y = y * x := by
      rcases Finset.eq_empty_or_nonempty S₀ with h0 | ⟨s, hs⟩
      · have hone : ∀ x : ↥H, x = 1 := by
          intro x
          have hx : x ∈ Subgroup.closure (S₀ : Set ↥H) := hcl ▸ Subgroup.mem_top x
          rw [h0] at hx
          simpa using hx
        intro x y
        rw [hone x, hone y]
      · have hall : ∀ t ∈ S₀, t = s := fun t ht => Finset.card_le_one.1 hcard t ht s hs
        have hle : Subgroup.closure (S₀ : Set ↥H) ≤ Subgroup.zpowers s :=
          (Subgroup.closure_le _).2 (fun t ht => by
            rw [Finset.mem_coe] at ht
            rw [hall t ht]
            exact Subgroup.mem_zpowers s)
        intro x y
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hle (hcl ▸ Subgroup.mem_top x))
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hle (hcl ▸ Subgroup.mem_top y))
        rw [← hi, ← hj]
        exact ((Commute.refl s).zpow_zpow i j).eq
    exact hnc (congrArg Subtype.val (hcommH ⟨r, hrH⟩ ⟨q, hqH⟩))
  omega

end Rank5

end CFSG.GH74.QTGen4.Leaves
