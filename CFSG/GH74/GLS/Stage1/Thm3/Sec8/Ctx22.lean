module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx19

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem V₁_inf_V_bot (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Vof S K₁ W₂ ⊓ conjugate (Vof S K₁ W₂) h = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ conjugate (Vof S K₁ W₂) h ⊓ Qof S K₂ :=
    Subgroup.mem_inf.2 ⟨hx.2, hs.P₁_le_Q₂ hII hx.1.2⟩
  rw [hs.V₁h_inf_Q hII hq (Or.inr rfl)] at this
  exact this

theorem V₁_inf_V₂_sq (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ g ∈ Vof S K₁ W₂ ⊓ Vof S K₂ W₁, g * g = 1 := by
  intro g hg
  have hgP : g ∈ Pof S K₁ ⊓ Pof S K₂ := Subgroup.mem_inf.2 ⟨hg.1.2, hg.2.2⟩
  rw [hs.P_inf hII] at hgP
  rcases (M.mem_zpowers_of_sq hs.z_sq).1 hgP with h0 | hz
  · rw [h0, one_mul]
  · rw [hz]; exact hs.z_sq

theorem A_inv_mem_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {b : G} (hbA : b ∈ Aof S K₁ W₂ h) (hb2 : b * b = 1) :
    b ∈ U := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec hbA
  have ha₁A : a₁ ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left ha₁
  have ha₂A : a₂ ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_right ha₂
  have hc : a₁ * a₂ = a₂ * a₁ := hs.A_comm hII hq hrec a₁ ha₁A a₂ ha₂A
  have h1 : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [hc]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := hb2
  have hsq₁ : a₁ * a₁ ∈ Vof S K₁ W₂ ⊓ conjugate (Vof S K₁ W₂) h := by
    refine Subgroup.mem_inf.2 ⟨mul_mem ha₁ ha₁, ?_⟩
    have : a₁ * a₁ = (a₂ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem (mul_mem ha₂ ha₂)
  rw [hs.V₁_inf_V_bot hII hq] at hsq₁
  have ha₁sq : a₁ * a₁ = 1 := hsq₁
  have ha₂sq : a₂ * a₂ = 1 := by rw [ha₁sq, one_mul] at h1; exact h1
  have hz1 : a₁ = 1 ∨ a₁ = z := (hs.gq_P hII hq (Or.inl rfl)).uniq a₁ ha₁.2 ha₁sq
  have hv : h * a₂ * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 ha₂
  have hv2 : (h * a₂ * h⁻¹) * (h * a₂ * h⁻¹) = 1 := by
    calc (h * a₂ * h⁻¹) * (h * a₂ * h⁻¹) = h * (a₂ * a₂) * h⁻¹ := by group
      _ = 1 := by rw [ha₂sq]; group
  have h2z : h * a₂ * h⁻¹ = 1 ∨ h * a₂ * h⁻¹ = z :=
    (hs.gq_P hII hq (Or.inl rfl)).uniq _ hv.2 hv2
  have ha₂' : a₂ = 1 ∨ a₂ = h⁻¹ * z * h := by
    have e : a₂ = h⁻¹ * (h * a₂ * h⁻¹) * h := by group
    rcases h2z with h2 | h2
    · left
      rw [e, h2]; group
    · right
      rw [e, h2]
  have hzU := hs.z_mem
  have hz1U := hs.hz_inv_mem_U
  rcases hz1 with e1 | e1 <;> rcases ha₂' with e2 | e2 <;> rw [e1, e2]
  · rw [one_mul]; exact one_mem _
  · rw [one_mul]; exact hz1U
  · rw [mul_one]; exact hzU
  · exact mul_mem hzU hz1U

theorem psi_fixed_U (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {b : G}
    (hbU : b ∈ U) (hb1 : b ≠ 1) (hbfix : h⁻¹ * b * h = b) : False := by
  have hz₁U : h⁻¹ * z * h ∈ U := hs.hz_inv_mem_U
  have hz₁1 : h⁻¹ * z * h ≠ 1 := by
    intro h'
    apply hs.z_ne
    have e : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
    rw [e, h']; group
  have hz₁z : h⁻¹ * z * h ≠ z := hs.h_move
  have hz₂U : h⁻¹ * (h⁻¹ * z * h) * h ∈ U := hs.U_conj_h hz₁U
  have hzW : z ∈ Wsub S U := Subgroup.mem_inf.2 ⟨hs.U_le_S hII hs.z_mem,
    Subgroup.mem_centralizer_iff.2 (fun y hy => (hs.four_comm z hs.z_mem y hy).symm)⟩
  have hcube : h⁻¹ * (h⁻¹ * (h⁻¹ * z * h) * h) * h = z := by
    have h3 := hs.h_cube z hzW
    rw [pow_three] at h3
    have e : h⁻¹ * (h⁻¹ * (h⁻¹ * z * h) * h) * h = (h * (h * h))⁻¹ * (z * (h * (h * h))) := by
      group
    rw [e, ← h3]
    group
  have hnot : h⁻¹ * z * h ∉ zpowers z := by
    intro hmem
    rcases (M.mem_zpowers_of_sq hs.z_sq).1 hmem with h' | h'
    · exact hz₁1 h'
    · exact hz₁z h'
  have hU4 := Basic.four_elems hs.z_sq hs.U_four.2 hs.z_mem hz₁U hs.z_ne hnot
  have hz₂ : h⁻¹ * (h⁻¹ * z * h) * h = (h⁻¹ * z * h) * z := by
    rcases hU4 _ hz₂U with h' | h' | h' | h'
    · exfalso
      apply hs.z_ne
      rw [h'] at hcube
      rw [← hcube]; group
    · exfalso
      rw [h'] at hcube
      exact hz₁z hcube
    · exfalso
      have e := congrArg (fun t => h * t * h⁻¹) h'
      have e1 : h * (h⁻¹ * (h⁻¹ * z * h) * h) * h⁻¹ = h⁻¹ * z * h := by group
      have e2 : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
      rw [e1, e2] at e
      exact hz₁z e
    · exact h'
  have hz₁zz : h⁻¹ * ((h⁻¹ * z * h) * z) * h = z := by
    have e : h⁻¹ * ((h⁻¹ * z * h) * z) * h =
        (h⁻¹ * (h⁻¹ * z * h) * h) * (h⁻¹ * z * h) := by group
    rw [e, hz₂]
    have hc : (h⁻¹ * z * h) * z = z * (h⁻¹ * z * h) := hs.four_comm _ hz₁U z hs.z_mem
    have hsq : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := hs.four_sq _ hz₁U
    calc (h⁻¹ * z * h) * z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) := by group
      _ = (h⁻¹ * z * h) * ((h⁻¹ * z * h) * z) := by rw [hc]
      _ = ((h⁻¹ * z * h) * (h⁻¹ * z * h)) * z := by group
      _ = z := by rw [hsq, one_mul]
  rcases hU4 b hbU with h' | h' | h' | h'
  · exact hb1 h'
  · rw [h'] at hbfix
    exact hz₁z hbfix
  · rw [h'] at hbfix
    rw [hz₂] at hbfix
    apply hs.z_ne
    exact (mul_eq_left.1 hbfix)
  · rw [h'] at hbfix
    rw [hz₁zz] at hbfix
    apply hz₁1
    exact (mul_eq_right.1 hbfix.symm)

theorem A_fixed_trivial (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {n : G}
    (hnA : n ∈ Aof S K₁ W₂ h) (hfix : h⁻¹ * n * h = n) : n = 1 := by
  by_contra hn1
  have hpow := Basic.pow_card_of_mem hnA
  rw [hs.card_A hII hq hrec hk] at hpow
  have hdvd : orderOf n ∣ 2 ^ (k + k) := by
    have := orderOf_dvd_of_pow_eq_one hpow
    rwa [← pow_add] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hj
    exact hn1 (orderOf_eq_one_iff.1 hj)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hb2 : n ^ (2 ^ i) * n ^ (2 ^ i) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hj ▸ pow_orderOf_eq_one n
  have hb1 : n ^ (2 ^ i) ≠ 1 := by
    intro h'
    have h2 := orderOf_dvd_of_pow_eq_one h'
    rw [hj] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hbU : n ^ (2 ^ i) ∈ U := hs.A_inv_mem_U hII hq hrec (pow_mem hnA _) hb2
  have hbfix : h⁻¹ * n ^ (2 ^ i) * h = n ^ (2 ^ i) := by
    have := conj_pow (a := h⁻¹) (b := n) (i := 2 ^ i)
    rw [inv_inv, hfix] at this
    exact this.symm
  exact hs.psi_fixed_U hII hbU hb1 hbfix

theorem psi_rel (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {x : G}
    (hxV : x ∈ Vof S K₁ W₂) :
    x * (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h) = 1 := by
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hx'A : h⁻¹ * x * h ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec hk hxA).2
  have hx''A : h⁻¹ * (h⁻¹ * x * h) * h ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec hk hx'A).2
  have hxW : x ∈ Wsub S U := hs.V₁_le_W hII hq hxV
  have hcube : h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = x := by
    have h3 := hs.h_cube x hxW
    rw [pow_three] at h3
    have e : h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = (h * (h * h))⁻¹ * (x * (h * (h * h))) := by
      group
    rw [e, ← h3]
    group
  have hnA : x * (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h) ∈ Aof S K₁ W₂ h :=
    mul_mem (mul_mem hxA hx'A) hx''A
  apply hs.A_fixed_trivial hII hq hrec hk hnA
  have e : h⁻¹ * (x * (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h)) * h =
      (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h) * (h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h) := by
    group
  rw [e, hcube]
  have c1 : x * (h⁻¹ * x * h) = (h⁻¹ * x * h) * x := hs.A_comm hII hq hrec _ hxA _ hx'A
  have c2 : x * (h⁻¹ * (h⁻¹ * x * h) * h) = (h⁻¹ * (h⁻¹ * x * h) * h) * x :=
    hs.A_comm hII hq hrec _ hxA _ hx''A
  calc (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h) * x
      = (h⁻¹ * x * h) * ((h⁻¹ * (h⁻¹ * x * h) * h) * x) := by group
    _ = (h⁻¹ * x * h) * (x * (h⁻¹ * (h⁻¹ * x * h) * h)) := by rw [c2]
    _ = ((h⁻¹ * x * h) * x) * (h⁻¹ * (h⁻¹ * x * h) * h) := by group
    _ = (x * (h⁻¹ * x * h)) * (h⁻¹ * (h⁻¹ * x * h) * h) := by rw [c1]

theorem gen_V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {m : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) :
    ∃ x : G, x ∈ Vof S K₁ W₂ ∧ Vof S K₁ W₂ = zpowers x ∧ orderOf x = 2 ^ (m + 1) ∧
      x ^ (2 ^ m) = z := by
  have hm : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have := hs.four_le_V₁ hII hq
    rw [hk, hm0] at this
    norm_num at this
  obtain ⟨x, hxV, hVx⟩ := Basic.exists_generator_of_cyclic hs.V₁_cyclic
  have hxo : orderOf x = 2 ^ (m + 1) := by rw [← Nat.card_zpowers, ← hVx]; exact hk
  have hx2m : x ^ (2 ^ (m + 1)) = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxsq : x ^ (2 ^ m) * x ^ (2 ^ m) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hx2m
  have hz : x ^ (2 ^ m) = z := by
    have hzV : z ∈ Vof S K₁ W₂ := hs.z_mem_V₁ hII hq (by omega) hk
    have h1 : x ^ (2 ^ m) ∈ Vof S K₁ W₂ := by rw [hVx]; exact Subgroup.npow_mem_zpowers x _
    have hne : x ^ (2 ^ m) ≠ 1 := by
      intro h'
      have h2 := orderOf_dvd_of_pow_eq_one h'
      rw [hxo] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    exact Basic.cyc_inv_unique hs.V₁_cyclic h1 hzV hxsq hs.z_sq hne hs.z_ne
  exact ⟨x, by rw [hVx]; exact Subgroup.mem_zpowers x, hVx, hxo, hz⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
