module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnC
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermFacts4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnStmt

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

section Generic

variable {H : Type} [Group H]

theorem mem_sup_iff_mul_of_commute {A B : Subgroup H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : H} :
    y ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hle : A ≤ normalizer (B : Set H) := fun a ha =>
    Subgroup.centralizer_le_normalizer (B : Set H)
      (mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  constructor
  · intro hy
    have hy' : y ∈ ((A ⊔ B : Subgroup H) : Set H) := hy
    rw [hset] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem mem_sup_iff_mul_of_le_normalizer {A B : Subgroup H} (hB : B ≤ normalizer (A : Set H)) {y : H} :
    y ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  constructor
  · intro hy
    have hy' : y ∈ ((A ⊔ B : Subgroup H) : Set H) := hy
    rw [hset] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem mem_of_sq_mem {M : Subgroup H} {y : H} (hy : y * y ∈ M) (hodd : Odd (orderOf y)) : y ∈ M := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  have h2 : y = (y * y) ^ (k + 1) := by
    calc y = y ^ (2 * k + 1) * y := by rw [h1, one_mul]
      _ = y ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (y * y) ^ (k + 1) := by rw [pow_mul, pow_two]
  rw [h2]
  exact pow_mem hy _

theorem eq_one_of_odd_of_pow_two_pow {o : H} (hodd : Odd (orderOf o)) {k : ℕ} (h : o ^ (2 ^ k) = 1) :
    o = 1 := by
  have h1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : Nat.Coprime (orderOf o) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem eq_one_of_sq_of_odd {j : H} (hj : j * j = 1) (hodd : Odd (orderOf j)) : j = 1 := by
  apply eq_one_of_odd_of_pow_two_pow hodd (k := 1)
  rw [pow_one, pow_two]
  exact hj

theorem mem_O2res_of_odd {C : Subgroup H} {y : H} (hy : y ∈ C) (hodd : Odd (orderOf y)) : y ∈ O2res C := by
  refine ⟨⟨y, hy⟩, subset_closure ?_, rfl⟩
  show Nat.Coprime (orderOf (⟨y, hy⟩ : ↥C)) 2
  rw [← Subgroup.orderOf_coe]
  exact Nat.coprime_two_right.mpr hodd

theorem O2res_le {C M : Subgroup H} (h : ∀ y ∈ C, Odd (orderOf y) → y ∈ M) : O2res C ≤ M := by
  show Subgroup.map C.subtype (Subgroup.closure {x : ↥C | Nat.Coprime (orderOf x) 2}) ≤ M
  rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  intro x hx
  have hx' : Nat.Coprime (orderOf x) 2 := hx
  have : Odd (orderOf (x : H)) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.coprime_two_right.mp hx'
  exact h x x.2 this

theorem O2core_eq_of {M Q : Subgroup H} (hQM : Q ≤ M) (hQn : ∀ y ∈ M, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hQ2 : IsPGroup 2 Q) (hmax : ∀ y ∈ M, (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ∈ Q) : O2core M = Q := by
  have hsub : pCore 2 ↥M = Q.subgroupOf M := by
    apply le_antisymm
    · apply sSup_le
      rintro N ⟨hNn, hNp⟩ x hx
      obtain ⟨k, hk⟩ := hNp ⟨x, hx⟩
      have hk' : ((x : ↥M) ^ (2 ^ k) : ↥M) = 1 := congrArg Subtype.val hk
      have hk'' : ((x : ↥M) : H) ^ (2 ^ k) = 1 := by
        have := congrArg Subtype.val hk'
        simpa using this
      exact Subgroup.mem_subgroupOf.mpr (hmax x x.2 ⟨k, hk''⟩)
    · apply le_sSup
      refine ⟨⟨fun n hn g => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hQn g g.2 n hn
      · intro x
        obtain ⟨k, hk⟩ := hQ2 ⟨(x : ↥M), Subgroup.mem_subgroupOf.mp x.2⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
  show (pCore 2 ↥M).map M.subtype = Q
  rw [hsub, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQM]

theorem pPrimeCoreOf_eq_of {C O : Subgroup H} (hOC : O ≤ C) (hOn : ∀ y ∈ C, ∀ o ∈ O, y * o * y⁻¹ ∈ O)
    (hOc : Nat.Coprime 2 (Nat.card O))
    (hmax : ∀ N : Subgroup H, N ≤ C → (∀ y ∈ C, ∀ x ∈ N, y * x * y⁻¹ ∈ N) →
      Nat.Coprime 2 (Nat.card N) → N ≤ O) :
    pPrimeCoreOf 2 C = O := by
  have hsub : pPrimeCore 2 ↥C = O.subgroupOf C := by
    apply le_antisymm
    · apply sSup_le
      rintro N ⟨hNn, hNc⟩
      have hle : N.map C.subtype ≤ O := by
        apply hmax
        · rintro _ ⟨x, hx, rfl⟩
          exact x.2
        · rintro y hy _ ⟨x, hx, rfl⟩
          exact ⟨⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹, hNn.conj_mem x hx ⟨y, hy⟩, rfl⟩
        · rw [Subgroup.card_map_of_injective C.subtype_injective]
          exact hNc
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hle ⟨x, hx, rfl⟩)
    · apply le_sSup
      refine ⟨⟨fun n hn g => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hOn g g.2 n hn
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
        exact hOc
  show (pPrimeCore 2 ↥C).map C.subtype = O
  rw [hsub, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hOC]

end Generic

theorem Sfun_gens (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) :
    Sfun m ⟨1, 0, 0⟩ = ub m ∧ Sfun m ⟨omegaC, 0, 0⟩ = vb m ∧ Sfun m ⟨0, 1, 0⟩ = xb1 m ∧
      Sfun m ⟨0, omegaC, 0⟩ = xb2 m ∧ Sfun m ⟨0, 0, 1⟩ = tb m := by
  interval_cases m <;> decide

section CfgFacts

variable {H : Type} [Group H] {K : Subgroup H} {m : ℕ}

namespace Cfg

variable {R : PermRep K (m + 1)} {z : H} (Γ : Cfg R z)

include Γ

theorem Q_le_J : Γ.Q ≤ Γ.J := le_sup_left

theorem X_le_J : Γ.X ≤ Γ.J := le_sup_right

theorem J_norm_Q : ∀ j ∈ Γ.J, ∀ q ∈ Γ.Q, j * q * j⁻¹ ∈ Γ.Q := by
  intro j hj q hq
  have := Γ.Q_normal_in_J.conj_mem ⟨q, Γ.Q_le_J hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨j, hj⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem mem_J_iff {y : H} : y ∈ Γ.J ↔ ∃ q ∈ Γ.Q, ∃ x ∈ Γ.X, y = q * x :=
  mem_sup_iff_mul_of_le_normalizer Γ.X_le_norm_Q

theorem X_pow_three {x : H} (hx : x ∈ Γ.X) : x ^ 3 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard Γ.X hx
  rw [Γ.X_card] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem X_odd {x : H} (hx : x ∈ Γ.X) : Odd (orderOf x) := by
  have h : orderOf x ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard Γ.X hx
    rwa [Γ.X_card] at this
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h1 | h1 <;> rw [h1] <;> decide

theorem u_mem_Q : Γ.L.u ∈ Γ.Q :=
  Γ.mem_Q_of_rho (x := ⟨1, 0, 0⟩) (by rw [Γ.L.hu, (Sfun_gens m Γ.h7 Γ.h10).1])

theorem v_mem_Q : Γ.L.v ∈ Γ.Q :=
  Γ.mem_Q_of_rho (x := ⟨omegaC, 0, 0⟩) (by rw [Γ.L.hv, (Sfun_gens m Γ.h7 Γ.h10).2.1])

theorem x1_mem_Q : Γ.L.x1 ∈ Γ.Q :=
  Γ.mem_Q_of_rho (x := ⟨0, 1, 0⟩) (by rw [Γ.L.hx1, (Sfun_gens m Γ.h7 Γ.h10).2.2.1])

theorem x2_mem_Q : Γ.L.x2 ∈ Γ.Q :=
  Γ.mem_Q_of_rho (x := ⟨0, omegaC, 0⟩) (by rw [Γ.L.hx2, (Sfun_gens m Γ.h7 Γ.h10).2.2.2.1])

theorem t_mem_Q : Γ.t ∈ Γ.Q :=
  Γ.mem_Q_of_rho (x := ⟨0, 0, 1⟩) (by rw [Γ.rho_t', (Sfun_gens m Γ.h7 Γ.h10).2.2.2.2])

theorem rho_J_form {y : H} (hy : y ∈ Γ.J) :
    ∃ x : UT3 F4c, R.ρ y = Sfun m x ∨ R.ρ y = Sfun m x * c3 m ∨
      R.ρ y = Sfun m x * (c3 m * c3 m) := by
  obtain ⟨q, hq, x, hx, rfl⟩ := Γ.mem_J_iff.mp hy
  obtain ⟨s, hs⟩ := Γ.rho_of_mem_Q hq
  rcases mem_zpowers_cube Γ.L.hc3 hx with h | h | h
  · exact ⟨s, Or.inl (by rw [map_mul, hs, h, map_one, mul_one])⟩
  · exact ⟨s, Or.inr (Or.inl (by rw [map_mul, hs, h, Γ.L.hc]))⟩
  · exact ⟨s, Or.inr (Or.inr (by rw [map_mul, hs, h, map_mul, Γ.L.hc]))⟩

theorem rho_commutes_of_cent {j : H} (hc : ∀ q ∈ Γ.Q, j * q = q * j) :
    R.ρ j * ub m = ub m * R.ρ j ∧ R.ρ j * vb m = vb m * R.ρ j ∧ R.ρ j * xb1 m = xb1 m * R.ρ j ∧
      R.ρ j * xb2 m = xb2 m * R.ρ j := by
  have h1 := congrArg R.ρ (hc _ Γ.u_mem_Q)
  have h2 := congrArg R.ρ (hc _ Γ.v_mem_Q)
  have h3 := congrArg R.ρ (hc _ Γ.x1_mem_Q)
  have h4 := congrArg R.ρ (hc _ Γ.x2_mem_Q)
  rw [map_mul, map_mul, Γ.L.hu] at h1
  rw [map_mul, map_mul, Γ.L.hv] at h2
  rw [map_mul, map_mul, Γ.L.hx1] at h3
  rw [map_mul, map_mul, Γ.L.hx2] at h4
  exact ⟨h1, h2, h3, h4⟩

theorem cent_J_Q {j : H} (hj : j ∈ Γ.J) (hc : ∀ q ∈ Γ.Q, j * q = q * j) :
    j = 1 ∨ j = z ∨ j = Γ.t ∨ j = Γ.t * z := by
  obtain ⟨h1, h2, h3, h4⟩ := Γ.rho_commutes_of_cent hc
  obtain ⟨x, hx⟩ := Γ.rho_J_form hj
  have hρ : R.ρ j = 1 ∨ R.ρ j = tb m := by
    rcases hx with h | h | h
    · rw [h] at h1 h2 h3 h4 ⊢
      exact Sfun_cent0 m Γ.h7 Γ.h10 x h1 h2 h3 h4
    · rw [h] at h1 h2 h3 h4
      exact (Sfun_cent1 m Γ.h7 Γ.h10 x h1 h2 h3 h4).elim
    · rw [h] at h1 h2 h3 h4
      exact (Sfun_cent2 m Γ.h7 Γ.h10 x h1 h2 h3 h4).elim
  rcases hρ with h | h
  · rcases Γ.hz.ker j h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have h5 : R.ρ (Γ.t⁻¹ * j) = 1 := by
      rw [map_mul, map_inv, Γ.rho_t', h, inv_mul_cancel]
    rcases Γ.hz.ker _ h5 with h' | h'
    · right; right; left
      calc j = Γ.t * (Γ.t⁻¹ * j) := by group
        _ = Γ.t := by rw [h', mul_one]
    · right; right; right
      calc j = Γ.t * (Γ.t⁻¹ * j) := by group
        _ = Γ.t * z := by rw [h']

theorem cent_J_Q_odd {j : H} (hj : j ∈ Γ.J) (hc : ∀ q ∈ Γ.Q, j * q = q * j) (hodd : Odd (orderOf j)) :
    j = 1 := by
  have hzz : z * z = 1 := Γ.hz.sq
  have htt : Γ.t * Γ.t = 1 := Γ.L.sq_t Γ.h7 Γ.h10
  rcases Γ.cent_J_Q hj hc with h | h | h | h
  · exact h
  · rw [h] at hodd ⊢; exact eq_one_of_sq_of_odd hzz hodd
  · rw [h] at hodd ⊢; exact eq_one_of_sq_of_odd htt hodd
  · rw [h] at hodd ⊢
    refine eq_one_of_sq_of_odd ?_ hodd
    calc Γ.t * z * (Γ.t * z) = Γ.t * (z * Γ.t) * z := by group
      _ = Γ.t * (Γ.t * z) * z := by rw [Γ.hz.central Γ.t]
      _ = (Γ.t * Γ.t) * (z * z) := by group
      _ = 1 := by rw [htt, hzz, mul_one]

theorem mem_Q_of_two_power {j : H} (hj : j ∈ Γ.J) {k : ℕ} (h : j ^ (2 ^ k) = 1) : j ∈ Γ.Q := by
  have : (Γ.Q.subgroupOf Γ.J).Normal := Γ.Q_normal_in_J
  have hN : Nat.card ↥(Γ.Q.subgroupOf Γ.J) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Γ.Q_le_J).toEquiv]
    exact Γ.Q_card
  have hidx : (Γ.Q.subgroupOf Γ.J).index = 3 := by
    have h1 := Subgroup.index_mul_card (Γ.Q.subgroupOf Γ.J)
    rw [hN, Γ.J_card] at h1
    omega
  have hcard : Nat.card (↥Γ.J ⧸ Γ.Q.subgroupOf Γ.J) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  set g : ↥Γ.J ⧸ Γ.Q.subgroupOf Γ.J := ((⟨j, hj⟩ : ↥Γ.J) : ↥Γ.J ⧸ Γ.Q.subgroupOf Γ.J) with hg
  have h3 : g ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Γ.J ⧸ Γ.Q.subgroupOf Γ.J) (x := g)
    rwa [hcard] at this
  have h2k : g ^ (2 ^ k) = 1 := by
    rw [hg, ← QuotientGroup.mk_pow]
    have : (⟨j, hj⟩ : ↥Γ.J) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      simpa using h
    rw [this]
    rfl
  have hodd : Odd (orderOf g) := by
    have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h' | h' <;> rw [h'] <;> decide
  have hg1 : g = 1 := eq_one_of_odd_of_pow_two_pow hodd h2k
  have : (⟨j, hj⟩ : ↥Γ.J) ∈ Γ.Q.subgroupOf Γ.J := (QuotientGroup.eq_one_iff _).mp hg1
  exact Subgroup.mem_subgroupOf.mp this

theorem Q_le_O2res : Γ.Q ≤ O2res Γ.C := by
  calc Γ.Q = ⁅Γ.Q, Γ.X⁆ := Γ.comm_QX.symm
    _ ≤ O2res Γ.C := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨q, hq, x, hx, rfl⟩
      have h1 : q * x * q⁻¹ ∈ O2res Γ.C := by
        refine mem_O2res_of_odd ?_ ?_
        · exact mul_mem (mul_mem (Γ.Q_le_C hq) (Γ.X_le_C hx)) (inv_mem (Γ.Q_le_C hq))
        · have h3 : (q * x * q⁻¹) ^ 3 = 1 := by rw [conj_pow, Γ.X_pow_three hx]; group
          have hd : orderOf (q * x * q⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h | h <;> rw [h] <;> decide
      have h2 : x⁻¹ ∈ O2res Γ.C := inv_mem (mem_O2res_of_odd (Γ.X_le_C hx) (Γ.X_odd hx))
      show ⁅q, x⁆ ∈ O2res Γ.C
      rw [commutatorElement_def]
      exact mul_mem h1 h2

theorem X_le_O2res : Γ.X ≤ O2res Γ.C := fun _ hx => mem_O2res_of_odd (Γ.X_le_C hx) (Γ.X_odd hx)

end Cfg

namespace Cfg.Decomp

variable {R : PermRep K (m + 1)} {z : H} {Γ : Cfg R z} (d : Decomp Γ)

include d

theorem mem_M {y : H} : y ∈ Γ.J ⊔ d.O ↔ ∃ j ∈ Γ.J, ∃ o ∈ d.O, y = j * o :=
  mem_sup_iff_mul_of_commute d.O_comm

theorem M_norm_v : ∀ y ∈ Γ.J ⊔ d.O, d.v * y * d.v⁻¹ ∈ Γ.J ⊔ d.O := by
  intro y hy
  obtain ⟨j, hj, o, ho, rfl⟩ := d.mem_M.mp hy
  have e : d.v * (j * o) * d.v⁻¹ = (d.v * j * d.v⁻¹) * (d.v * o * d.v⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (d.v_norm_J j hj)) (Subgroup.mem_sup_right (d.v_norm_O o ho))

theorem v_le_normalizer_M : zpowers d.v ≤ normalizer ((Γ.J ⊔ d.O : Subgroup H) : Set H) := by
  rw [zpowers_le]
  exact mem_normalizer_of_invol d.v_sq d.M_norm_v

theorem mem_C {y : H} : y ∈ Γ.C ↔ ∃ m ∈ Γ.J ⊔ d.O, ∃ w ∈ zpowers d.v, y = m * w := by
  rw [d.C_eq]
  exact mem_sup_iff_mul_of_le_normalizer d.v_le_normalizer_M

theorem sq_mem_M {y : H} (hy : y ∈ Γ.C) : y * y ∈ Γ.J ⊔ d.O := by
  obtain ⟨m, hm, w, hw, rfl⟩ := d.mem_C.mp hy
  rcases mem_zpowers_involution d.v_sq hw with rfl | rfl
  · rw [mul_one]; exact mul_mem hm hm
  · have e : m * d.v * (m * d.v) = m * (d.v * m * d.v⁻¹) * (d.v * d.v) := by group
    rw [e, d.v_sq, mul_one]
    exact mul_mem hm (d.M_norm_v m hm)

theorem odd_mem_M {y : H} (hy : y ∈ Γ.C) (hodd : Odd (orderOf y)) : y ∈ Γ.J ⊔ d.O :=
  mem_of_sq_mem (d.sq_mem_M hy) hodd

theorem C_le_normalizer_O : Γ.C ≤ normalizer (d.O : Set H) := by
  rw [d.C_eq]
  refine sup_le (sup_le ?_ (Subgroup.le_normalizer)) ?_
  · intro j hj
    exact Subgroup.centralizer_le_normalizer (d.O : Set H)
      (mem_centralizer_iff.mpr fun o ho => (d.O_comm j hj o ho).symm)
  · rw [zpowers_le]
    exact mem_normalizer_of_invol d.v_sq d.v_norm_O

theorem O_le_O2res : d.O ≤ O2res Γ.C := fun o ho => mem_O2res_of_odd (d.O_le_C ho) (d.O_odd o ho)

theorem O2res_eq : O2res Γ.C = Γ.J ⊔ d.O := by
  apply le_antisymm
  · exact O2res_le fun y hy hodd => d.odd_mem_M hy hodd
  · exact sup_le (sup_le Γ.Q_le_O2res Γ.X_le_O2res) d.O_le_O2res

theorem O2core_eq : O2core (O2res Γ.C) = Γ.Q := by
  refine O2core_eq_of ?_ ?_ ?_ ?_
  · rw [d.O2res_eq]
    exact le_trans Γ.Q_le_J le_sup_left
  · intro y hy q hq
    rw [d.O2res_eq] at hy
    obtain ⟨j, hj, o, ho, rfl⟩ := d.mem_M.mp hy
    have hoq : o * q = q * o := (d.O_comm q (Γ.Q_le_J hq) o ho).symm
    have e : j * o * q * (j * o)⁻¹ = j * q * j⁻¹ := by
      calc j * o * q * (j * o)⁻¹ = j * (o * q) * o⁻¹ * j⁻¹ := by group
        _ = j * (q * o) * o⁻¹ * j⁻¹ := by rw [hoq]
        _ = j * q * j⁻¹ := by group
    rw [e]
    exact Γ.J_norm_Q j hj q hq
  · exact IsPGroup.of_card (n := 6) (by rw [Γ.Q_card]; norm_num)
  · intro y hy ⟨k, hk⟩
    rw [d.O2res_eq] at hy
    obtain ⟨j, hj, o, ho, rfl⟩ := d.mem_M.mp hy
    have hcomm : Commute j o := d.O_comm j hj o ho
    rw [hcomm.mul_pow] at hk
    have h1 : j ^ (2 ^ k) = (o ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hk
    have hOk : o ^ (2 ^ k) ∈ d.O := pow_mem ho _
    have h2 : j ^ (2 ^ k) ∈ Γ.J ⊓ d.O :=
      Subgroup.mem_inf.mpr ⟨pow_mem hj _, by rw [h1]; exact inv_mem hOk⟩
    rw [d.O_disj, mem_bot] at h2
    have h3 : o ^ (2 ^ k) = 1 := by
      rw [h2] at h1
      exact inv_eq_one.mp h1.symm
    have h4 : o = 1 := eq_one_of_odd_of_pow_two_pow (d.O_odd o ho) h3
    rw [h4, one_pow, mul_one] at hk
    rw [h4, mul_one]
    exact Γ.mem_Q_of_two_power hj hk

theorem pPrimeCoreOf_eq : pPrimeCoreOf 2 Γ.C = d.O := by
  refine pPrimeCoreOf_eq_of d.O_le_C ?_ ?_ ?_
  · intro y hy o ho
    exact (mem_normalizer_iff.mp (d.C_le_normalizer_O hy) o).mp ho
  · rw [d.O_card]
    split_ifs <;> decide
  · intro N hNC hNn hNc y hyN
    have hyC : y ∈ Γ.C := hNC hyN
    have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp hNc
    have hyodd : Odd (orderOf y) :=
      Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hyN)
    obtain ⟨j, hj, o, ho, rfl⟩ := d.mem_M.mp (d.odd_mem_M hyC hyodd)
    have hjc : ∀ q ∈ Γ.Q, j * q = q * j := by
      intro q hq
      have hqC : q ∈ Γ.C := Γ.Q_le_C hq
      have hn1 : q * (j * o) * q⁻¹ ∈ N := hNn q hqC _ hyN
      have hw : q * (j * o) * q⁻¹ * (j * o)⁻¹ ∈ N := mul_mem hn1 (inv_mem hyN)
      have hoq : o * q⁻¹ = q⁻¹ * o := (d.O_comm q⁻¹ (inv_mem (Γ.Q_le_J hq)) o ho).symm
      have e : q * (j * o) * q⁻¹ * (j * o)⁻¹ = q * (j * q⁻¹ * j⁻¹) := by
        calc q * (j * o) * q⁻¹ * (j * o)⁻¹ = q * j * (o * q⁻¹) * (o⁻¹ * j⁻¹) := by group
          _ = q * j * (q⁻¹ * o) * (o⁻¹ * j⁻¹) := by rw [hoq]
          _ = q * (j * q⁻¹ * j⁻¹) := by group
      have hwQ : q * (j * q⁻¹ * j⁻¹) ∈ Γ.Q := mul_mem hq (Γ.J_norm_Q j hj q⁻¹ (inv_mem hq))
      rw [e] at hw
      have hwodd : Odd (orderOf (q * (j * q⁻¹ * j⁻¹))) :=
        Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hw)
      have hwdvd : orderOf (q * (j * q⁻¹ * j⁻¹)) ∣ 2 ^ 6 := by
        have := Subgroup.orderOf_dvd_natCard Γ.Q hwQ
        rwa [Γ.Q_card] at this
      have hw1 : q * (j * q⁻¹ * j⁻¹) = 1 := by
        have h2 : Nat.Coprime (orderOf (q * (j * q⁻¹ * j⁻¹))) (2 ^ 6) :=
          Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr hwodd)
        exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 hwdvd)
      have : q * j * q⁻¹ * j⁻¹ = 1 := by rw [← hw1]; group
      calc j * q = (q * j * q⁻¹ * j⁻¹)⁻¹ * (q * j) := by group
        _ = q * j := by rw [this]; group
    have hjodd : Odd (orderOf j) := by
      have hcomm : Commute j o := d.O_comm j hj o ho
      have hpow : (j * o) ^ (orderOf (j * o)) = 1 := pow_orderOf_eq_one _
      rw [hcomm.mul_pow] at hpow
      have h1 : j ^ orderOf (j * o) = (o ^ orderOf (j * o))⁻¹ := eq_inv_of_mul_eq_one_left hpow
      have hOk : o ^ orderOf (j * o) ∈ d.O := pow_mem ho _
      have h2 : j ^ orderOf (j * o) ∈ Γ.J ⊓ d.O :=
        Subgroup.mem_inf.mpr ⟨pow_mem hj _, by rw [h1]; exact inv_mem hOk⟩
      rw [d.O_disj, mem_bot] at h2
      exact Odd.of_dvd_nat hyodd (orderOf_dvd_of_pow_eq_one h2)
    have hj1 : j = 1 := Γ.cent_J_Q_odd hj hjc hjodd
    rw [hj1, one_mul]
    exact ho

end Cfg.Decomp

end CfgFacts

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
