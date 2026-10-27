module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoC2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

open Subgroup

variable {G : Type*} [Group G]

theorem not_comm_of_inv {a b : G} (hab : b * a * b⁻¹ = a⁻¹) (ha2 : a ^ 2 ≠ 1) :
    a * b ≠ b * a := by
  intro h
  have h1 : b * a * b⁻¹ = a := by rw [← h]; group
  rw [h1] at hab
  apply ha2
  rw [pow_two]
  exact inv_eq_iff_mul_eq_one.mp hab.symm

theorem order16_of_central {M : Subgroup G} {y w m : G} (c : Config M y w m) {z : G} (hz : z ∈ M)
    (hz4 : orderOf z = 4) (hzy : z * y = y * z) (hzw : z * w = w * z) (hzm : z * m = m * z)
    {a b : G} (ha : a ∈ M) (hb : b ∈ M) (hab : a * b ≠ b * a) : Sec622Order16 M := by
  refine ⟨c.card, ⟨a, ha, b, hb, hab⟩, z, hz, hz4, fun g hg => ?_⟩
  rw [c.eq_closure] at hg
  refine (commute_of_mem_closure (S := {y, w, m}) ?_ hg).symm
  intro s hs
  rcases hs with rfl | rfl | rfl
  · exact hzy
  · exact hzw
  · exact hzm

theorem conj_eq_inv_of_mem {M : Subgroup G} {y v m : G} (c : Config M y v m) (hyv : y * v = v * y)
    (hy1 : m * y * m⁻¹ = y⁻¹) (hv1 : m * v * m⁻¹ = v⁻¹) {τ : G}
    (hτ : τ ∈ closure ({y, v} : Set G)) : m * τ * m⁻¹ = τ⁻¹ := by
  obtain ⟨i, j, -, -, rfl⟩ := (c.t0.mem_closure_iff c.wy).mp hτ
  have hsc : SemiconjBy m y y⁻¹ := mul_inv_eq_iff_eq_mul.mp hy1
  have hsd : SemiconjBy m v v⁻¹ := mul_inv_eq_iff_eq_mul.mp hv1
  have h1 : m * (y ^ i * v ^ j) = (y⁻¹ ^ i * v⁻¹ ^ j) * m :=
    ((hsc.pow_right i).mul_right (hsd.pow_right j)).eq
  have hc : Commute (y ^ i) (v ^ j) := Commute.pow_pow (show Commute y v from hyv) i j
  have h2 : (y ^ i * v ^ j)⁻¹ = y⁻¹ ^ i * v⁻¹ ^ j :=
    calc (y ^ i * v ^ j)⁻¹ = (v ^ j)⁻¹ * (y ^ i)⁻¹ := mul_inv_rev _ _
      _ = (y ^ i)⁻¹ * (v ^ j)⁻¹ := hc.inv_inv.eq.symm
      _ = y⁻¹ ^ i * v⁻¹ ^ j := by rw [inv_pow, inv_pow]
  rw [mul_inv_eq_iff_eq_mul, h1, h2]

theorem sq_eq_of_mem_closure {M : Subgroup G} {y v m : G} (c : Config M y v m)
    (hyv : y * v = v * y) {τ : G} (hτ : τ ∈ closure ({y, v} : Set G)) :
    τ ^ 2 = 1 ∨ τ ^ 2 = y ^ 2 := by
  obtain ⟨i, j, -, -, rfl⟩ := (c.t0.mem_closure_iff c.wy).mp hτ
  have hc : Commute (y ^ i) (v ^ j) := Commute.pow_pow (show Commute y v from hyv) i j
  have hz : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact c.t0.y_pow_four
  have : (y ^ i * v ^ j) ^ 2 = (y ^ 2) ^ (i + j) := by
    rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i 2, pow_mul, mul_comm j 2, pow_mul,
      c.t0.sq, pow_add]
  rw [this]
  exact pow_eq_one_or_self hz _

theorem eq_closure_prod {M : Subgroup G} {y v m : G} (c : Config M y v m) :
    M = closure ({y * v, y, m} : Set G) := by
  rw [c.eq_closure]
  apply le_antisymm
  · rw [closure_le]
    intro x hx
    have hy : y ∈ closure ({y * v, y, m} : Set G) := subset_closure (by simp)
    have hb : y * v ∈ closure ({y * v, y, m} : Set G) := subset_closure (by simp)
    rcases hx with rfl | rfl | rfl
    · exact hy
    · have := mul_mem (inv_mem hy) hb
      simpa using this
    · exact subset_closure (by simp)
  · rw [closure_le]
    intro x hx
    have hy : y ∈ closure ({y, v, m} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({y, v, m} : Set G) := subset_closure (by simp)
    rcases hx with rfl | rfl | rfl
    · exact mul_mem hy hv
    · exact hy
    · exact subset_closure (by simp)

theorem prod_not_mem_closure {M : Subgroup G} {y v m : G} (c : Config M y v m)
    (hy1 : m * y * m⁻¹ = y⁻¹) (hm2 : m ^ 2 = 1) : y * v ∉ closure ({y, m} : Set G) := by
  intro h
  have hsr : m * y * m⁻¹ ∈ zpowers y := by rw [hy1]; exact inv_mem (mem_zpowers y)
  have hs2 : m ^ 2 ∈ zpowers y := by rw [hm2]; exact one_mem _
  have hyT : zpowers y ≤ closure ({y, v} : Set G) :=
    (zpowers_le).mpr (subset_closure (by simp))
  rcases mem_closure_pair_cases hsr hs2 h with h1 | ⟨ρ, hρ, h1⟩
  · apply c.t0.not_mem
    have := mul_mem (inv_mem (mem_zpowers y)) h1
    simpa using this
  · apply c.m_not
    have hρ' : ρ ∈ closure ({y, v} : Set G) := hyT hρ
    have hb : y * v ∈ closure ({y, v} : Set G) :=
      mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have := mul_mem (inv_mem hρ') hb
    rwa [h1, inv_mul_cancel_left] at this

theorem prodDihedral_of_sq_eq_one {M : Subgroup G} {y v m : G} (c : Config M y v m)
    (hyv : y * v = v * y) (hy1 : m * y * m⁻¹ = y⁻¹) (hv1 : m * v * m⁻¹ = v⁻¹)
    (hm2 : m ^ 2 = 1) : Sec622ProdDihedral M 3 := by
  have ht0 := c.t0
  have hy4 := ht0.y_pow_four
  have hsc : SemiconjBy m y y⁻¹ := mul_inv_eq_iff_eq_mul.mp hy1
  have hsd : SemiconjBy m v v⁻¹ := mul_inv_eq_iff_eq_mul.mp hv1
  have hb2 : (y * v) ^ 2 = 1 := by
    rw [(show Commute y v from hyv).mul_pow, ht0.sq, ← pow_add]; exact hy4
  have hb1 : y * v ≠ 1 := by
    intro h
    apply ht0.not_mem
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem (mem_zpowers y)
  have hbinv : (y * v)⁻¹ = y * v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
  have hinvb : y⁻¹ * v⁻¹ = y * v :=
    calc y⁻¹ * v⁻¹ = (v * y)⁻¹ := (mul_inv_rev v y).symm
      _ = (y * v)⁻¹ := by rw [hyv]
      _ = y * v := hbinv
  have hbm : (y * v) * m = m * (y * v) := by
    have := (hsc.mul_right hsd).eq
    rw [hinvb] at this
    exact this.symm
  have hm1 : m ≠ 1 := fun h => c.m_not (h ▸ one_mem _)
  refine ⟨le_rfl, y * v, y, m, orderOf_eq_prime hb2 hb1, by simpa using ht0.ord,
    orderOf_eq_prime hm2 hm1, hy1, ?_, hbm, eq_closure_prod c, prod_not_mem_closure c hy1 hm2⟩
  rw [mul_assoc, ← hyv]

theorem centralInv_of_sq_eq {M : Subgroup G} {y v m : G} (c : Config M y v m)
    (hyv : y * v = v * y) (hy1 : m * y * m⁻¹ = y⁻¹) (hv1 : m * v * m⁻¹ = v⁻¹)
    (hm2 : m ^ 2 = y ^ 2) : Sec622CentralInv M := by
  have ht0 := c.t0
  have hz2 : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact ht0.y_pow_four
  have hcoset : ∀ g : G, g * m⁻¹ ∈ closure ({y, v} : Set G) → g ^ 2 = y ^ 2 := by
    intro g hg
    obtain ⟨τ, rfl⟩ : ∃ τ, g = τ * m := ⟨g * m⁻¹, by group⟩
    have hτ : τ ∈ closure ({y, v} : Set G) := by simpa using hg
    have e1 := conj_eq_inv_of_mem c hyv hy1 hv1 hτ
    calc (τ * m) ^ 2 = τ * (m * τ * m⁻¹) * m ^ 2 := by rw [pow_two (τ * m), pow_two m]; group
      _ = τ * τ⁻¹ * m ^ 2 := by rw [e1]
      _ = y ^ 2 := by rw [mul_inv_cancel, one_mul, hm2]
  have hsq : ∀ g ∈ M, g ^ 2 = 1 ∨ g ^ 2 = y ^ 2 := by
    intro g hg
    rcases c.span g hg with h | h
    · exact sq_eq_of_mem_closure c hyv h
    · exact Or.inr (hcoset g h)
  refine ⟨?_, y ^ 2, orderOf_eq_prime hz2 ht0.y_sq_ne_one, hsq, y, c.y_mem, rfl⟩
  intro e he he2 g hg
  rcases c.span e he with h | h
  · have e1 := conj_eq_inv_of_mem c hyv hy1 hv1 h
    have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact he2)
    rw [hinv] at e1
    have hem : m * e = e * m := mul_inv_eq_iff_eq_mul.mp e1
    have hey : e * y = y * e := comm_of_mem_closure_pair hyv h (subset_closure (by simp))
    have hev : e * v = v * e := comm_of_mem_closure_pair hyv h (subset_closure (by simp))
    rw [c.eq_closure] at hg
    refine (commute_of_mem_closure (S := {y, v, m}) (c := e) ?_ hg).symm
    intro s hs
    rcases hs with rfl | rfl | rfl
    · exact hey
    · exact hev
    · exact hem.symm
  · exact absurd ((hcoset e h).symm.trans he2) ht0.y_sq_ne_one

theorem case_one_inv {M : Subgroup G} {t y v m : G} (c : Config M y v m) (hyv : y * v = v * y)
    (hty : t * y * t⁻¹ = y⁻¹) (htv : t * v = v * t) {ε : ℕ} (hε : ε % 2 = 1)
    (hmt : m * t * m⁻¹ = y ^ ε * t) (hy1 : m * y * m⁻¹ = y⁻¹) (hv1 : m * v * m⁻¹ = v⁻¹) :
    Sec622ProdDihedral M 3 ∨ Sec622CentralInv M := by
  have ht0 := c.t0
  have hy4 := ht0.y_pow_four
  have hv4 := ht0.w_pow_four
  obtain ⟨α, β, hα, hβ, hm2⟩ := (ht0.mem_closure_iff c.wy).mp c.m_sq
  have hpar := (parity ht0.ord hty htv hε hmt hm2).2 hy1
  have hsc : SemiconjBy m y y⁻¹ := mul_inv_eq_iff_eq_mul.mp hy1
  have hsd : SemiconjBy m v v⁻¹ := mul_inv_eq_iff_eq_mul.mp hv1
  have hfix : y ^ α * v ^ β = y ^ (3 * α) * v ^ (3 * β) := by
    have h1 : m * (y ^ α * v ^ β) = (y⁻¹ ^ α * v⁻¹ ^ β) * m :=
      ((hsc.pow_right α).mul_right (hsd.pow_right β)).eq
    have h2 : m * (y ^ α * v ^ β) = (y ^ α * v ^ β) * m := by
      rw [← hm2]; group
    rw [h2] at h1
    have := mul_right_cancel h1
    rw [this, inv_eq_pow_three hy4, inv_eq_pow_three hv4, ← pow_mul, ← pow_mul]
  obtain ⟨h1, h2⟩ := ht0.mul_eq_iff.mp hfix
  have hβ0 : β = 0 := by omega
  subst hβ0
  have hα' : α = 0 ∨ α = 2 := by omega
  rcases hα' with rfl | rfl
  · exact Or.inl (prodDihedral_of_sq_eq_one c hyv hy1 hv1 (by simpa using hm2))
  · exact Or.inr (centralInv_of_sq_eq c hyv hy1 hv1 (by simpa using hm2))

theorem case_one {M : Subgroup G} {t y v m : G} (c : Config M y v m) (hyv : y * v = v * y)
    (hty : t * y * t⁻¹ = y⁻¹) (htv : t * v = v * t) {ε : ℕ} (hε : ε % 2 = 1)
    (hmt : m * t * m⁻¹ = y ^ ε * t) (hmy : m * y * m⁻¹ = y ∨ m * y * m⁻¹ = y⁻¹)
    (hmv : m * v * m⁻¹ = v ∨ m * v * m⁻¹ = v⁻¹) :
    IsMulCommutative M ∨ Sec622ProdDihedral M 3 ∨ Sec622CentralInv M ∨ Sec622Order16 M := by
  have ht0 := c.t0
  rcases hmy with hy1 | hy1 <;> rcases hmv with hv1 | hv1
  · left
    have hym : y * m = m * y := (mul_inv_eq_iff_eq_mul.mp hy1).symm
    have hvm : v * m = m * v := (mul_inv_eq_iff_eq_mul.mp hv1).symm
    have hpw : ({y, v, m} : Set G).Pairwise Commute := by
      intro a ha b hb _
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact Commute.refl _
          | exact hyv
          | exact hyv.symm
          | exact hym
          | exact hym.symm
          | exact hvm
          | exact hvm.symm
    have := Subgroup.isMulCommutative_closure hpw
    rwa [← c.eq_closure] at this
  · right; right; right
    have hym : y * m = m * y := (mul_inv_eq_iff_eq_mul.mp hy1).symm
    refine order16_of_central c c.y_mem ht0.ord rfl hyv hym (a := v) (b := m) c.w_mem c.m_mem ?_
    exact not_comm_of_inv hv1 (by rw [ht0.sq]; exact ht0.y_sq_ne_one)
  · right; right; right
    have hvm : v * m = m * v := (mul_inv_eq_iff_eq_mul.mp hv1).symm
    refine order16_of_central c c.w_mem ht0.orderOf_w hyv.symm rfl hvm (a := y) (b := m) c.y_mem
      c.m_mem ?_
    exact not_comm_of_inv hy1 ht0.y_sq_ne_one
  · rcases case_one_inv c hyv hty htv hε hmt hy1 hv1 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC
