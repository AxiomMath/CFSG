module

public import CFSG.CGT.PushingUpLit.Orth.OrthDef

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv
open scoped commutatorElement

variable {G : Type*} [Group G] {M Q : Subgroup G}

theorem pow_four_of_pow_eight : ∀ x : Perm (Fin 5), x ^ 8 = 1 → x ^ 4 = 1 := by decide +kernel

theorem pow_four_of_pow_two_pow (x : Perm (Fin 5)) (j : ℕ) (h : x ^ (2 ^ j) = 1) : x ^ 4 = 1 := by
  have h1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf x ∣ 120 := by
    have := orderOf_dvd_card (G := Perm (Fin 5)) (x := x)
    simpa [Fintype.card_perm, Nat.factorial] using this
  have h3 : 2 ^ i ∣ 120 := hio ▸ h2
  have h4 : i ≤ 3 := by
    by_contra hlt
    have h5 : 2 ^ 4 ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
    have := h5.trans h3
    omega
  have h6 : x ^ 8 = 1 := by
    have : orderOf x ∣ 8 := by
      rw [hio]
      exact (pow_dvd_pow 2 h4).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.1 this
  exact pow_four_of_pow_eight x h6

namespace OrthCfg

variable (C : OrthCfg G M Q)

include C

@[expose] def T : Subgroup G := C.pre (Subgroup.zpowers tau)

@[expose] def Q1 : Subgroup G := C.T ⊓ Subgroup.centralizer (C.T : Set G)

theorem mem_T {x : G} : x ∈ C.T ↔ x ∈ M ∧ (C.th x = 1 ∨ C.th x = tau) := by
  rw [T, C.mem_pre, mem_zpowers_tau]

theorem T_le_M : C.T ≤ M := C.pre_le_M _

theorem Q_le_T : Q ≤ C.T := C.Q_le_pre _

theorem isPGroup_T : IsPGroup 2 C.T := C.isPGroup_pre isPGroup_zpowers_tau

theorem card_T : Nat.card C.T = 64 := by
  rw [T, C.card_pre, card_zpowers_tau]

theorem mem_Q1_iff {x : G} : x ∈ C.Q1 ↔ ∃ v : Vec5, v 0 = v 1 ∧ C.elt v = x := by
  constructor
  · rintro ⟨hxT, hxc⟩
    have hxM : x ∈ M := C.T_le_M hxT
    have hxQ : x ∈ Q := by
      by_contra hxQ
      have h1 : C.th x = tau := by
        rcases (C.mem_T.1 hxT).2 with h | h
        · exact absurd ((C.th_eq_one_iff hxM).1 h) hxQ
        · exact h
      have hc := Subgroup.mem_centralizer_iff.1 hxc (C.elt ![1, 0, 0, 0, 0])
        (C.Q_le_T (C.elt_mem _))
      have h2 : x * C.elt ![1, 0, 0, 0, 0] * x⁻¹ = C.elt ![1, 0, 0, 0, 0] := by
        calc x * C.elt ![1, 0, 0, 0, 0] * x⁻¹ = (C.elt ![1, 0, 0, 0, 0] * x) * x⁻¹ := by rw [hc]
          _ = C.elt ![1, 0, 0, 0, 0] := by group
      rw [C.conj_elt hxM, h1] at h2
      have h3 := C.elt_inj h2
      revert h3
      decide +kernel
    obtain ⟨v, hv⟩ := (C.mem_Q_iff x).1 hxQ
    refine ⟨v, ?_, hv⟩
    obtain ⟨t, htM, htτ⟩ := C.th_surj tau
    have htT : t ∈ C.T := C.mem_T.2 ⟨htM, Or.inr htτ⟩
    have hc := Subgroup.mem_centralizer_iff.1 hxc t htT
    have h2 : t * x * t⁻¹ = x := by
      calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [hc]
        _ = x := by group
    rw [← hv, C.conj_elt htM, htτ] at h2
    exact (permAct_tau_iff v).1 (C.elt_inj h2)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨C.Q_le_T (C.elt_mem v), ?_⟩
    show C.elt v ∈ Subgroup.centralizer (C.T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htT := C.mem_T.1 ht
    have h1 : t * C.elt v * t⁻¹ = C.elt v := by
      rw [C.conj_elt htT.1]
      rcases htT.2 with h | h
      · rw [h, permAct_one]
      · rw [h, permAct_tau_zero v hv]
    calc t * C.elt v = (t * C.elt v * t⁻¹) * t := by group
      _ = C.elt v * t := by rw [h1]

theorem Q1_le_Q : C.Q1 ≤ Q := fun _ hx => by
  obtain ⟨v, -, rfl⟩ := C.mem_Q1_iff.1 hx
  exact C.elt_mem v

theorem Q1_comm_T {y t : G} (hy : y ∈ C.Q1) (ht : t ∈ C.T) : t * y = y * t :=
  Subgroup.mem_centralizer_iff.1 hy.2 t ht

theorem card_Q1 : Nat.card C.Q1 = 16 := by
  have : Nat.card C.Q1 = Nat.card {v : Vec5 // v 0 = v 1} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨C.vec x, ?_⟩
        invFun := fun v => ⟨C.elt v, C.mem_Q1_iff.2 ⟨v, v.2, rfl⟩⟩
        left_inv := fun x => Subtype.ext (C.elt_vec (C.Q1_le_Q x.2))
        right_inv := fun v => Subtype.ext (C.vec_elt v) }
    obtain ⟨v, hv, hvx⟩ := C.mem_Q1_iff.1 x.2
    rw [← hvx, C.vec_elt]
    exact hv
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem eq_or_eq_of_between_Q_T [Finite G] {P : Subgroup G} (h1 : Q ≤ P) (h2 : P ≤ C.T) :
    P = Q ∨ P = C.T := by
  have hQ : Nat.card Q = 32 := C.card_Q
  have hd1 : Nat.card Q ∣ Nat.card P := Subgroup.card_dvd_of_le h1
  have hd2 : Nat.card P ∣ Nat.card C.T := Subgroup.card_dvd_of_le h2
  rw [hQ] at hd1
  rw [C.card_T] at hd2
  obtain ⟨k, hk⟩ := hd1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      exact absurd hk Nat.card_pos.ne'
    · exact h
  have hle : 32 * k ≤ 64 := by
    have := Nat.le_of_dvd (by norm_num) hd2
    omega
  have hk2 : k = 1 ∨ k = 2 := by omega
  rcases hk2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hk, hQ])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hk, C.card_T])

theorem eq_or_eq_of_between_Q1_Q [Finite G] {P : Subgroup G} (h1 : C.Q1 ≤ P) (h2 : P ≤ Q) :
    P = C.Q1 ∨ P = Q := by
  have hQ : Nat.card Q = 32 := C.card_Q
  have hd1 : Nat.card C.Q1 ∣ Nat.card P := Subgroup.card_dvd_of_le h1
  have hd2 : Nat.card P ∣ Nat.card Q := Subgroup.card_dvd_of_le h2
  rw [C.card_Q1] at hd1
  rw [hQ] at hd2
  obtain ⟨k, hk⟩ := hd1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      exact absurd hk Nat.card_pos.ne'
    · exact h
  have hle : 16 * k ≤ 32 := by
    have := Nat.le_of_dvd (by norm_num) hd2
    omega
  have hk2 : k = 1 ∨ k = 2 := by omega
  rcases hk2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hk, C.card_Q1])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hk, hQ])

theorem le_T_of_normal {N : Subgroup G} (hNK : N ≤ C.pre H2)
    (hnorm : ∀ k ∈ C.pre H2, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hN : IsPGroup 2 N) : N ≤ C.T := by
  intro n hn
  have hnH := C.th_mem_of_mem_pre (hNK hn)
  have hnM := C.pre_le_M _ (hNK hn)
  have hρ : isH2 (C.th n) := hnH
  have key : ∀ σ : Perm (Fin 5), isH2 σ → ⁅σ, C.th n⁆ ^ 4 = 1 := by
    intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := C.pre_surj (A := H2) hσ
    have hkM := C.pre_le_M _ hk
    have hc : k * n * k⁻¹ * n⁻¹ ∈ N := N.mul_mem (hnorm k hk n hn) (N.inv_mem hn)
    obtain ⟨j, hj⟩ := hN ⟨_, hc⟩
    have hj' : (k * n * k⁻¹ * n⁻¹) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    have hcM : k * n * k⁻¹ * n⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hkM hnM) (M.inv_mem hkM)) (M.inv_mem hnM)
    have h1 := congrArg C.th hj'
    rw [C.th_pow hcM, C.th_one] at h1
    have h2 : C.th (k * n * k⁻¹ * n⁻¹) = ⁅σ, C.th n⁆ := by
      rw [C.th_mul (M.mul_mem (M.mul_mem hkM hnM) (M.inv_mem hkM)) (M.inv_mem hnM),
        C.th_mul (M.mul_mem hkM hnM) (M.inv_mem hkM), C.th_mul hkM hnM, C.th_inv hkM,
        C.th_inv hnM, hkσ, commutatorElement_def]
    rw [h2] at h1
    exact pow_four_of_pow_two_pow _ j h1
  exact C.mem_T.2 ⟨hnM, normal2 _ hρ key⟩

theorem relIndex_inf_Q {P : Subgroup G} (hPT : P ≤ C.T) (hPQ : ¬ P ≤ Q) :
    (P ⊓ Q).relIndex P = 2 := by
  let f : ↥P →* Perm (Fin 5) :=
    { toFun := fun x => C.th x
      map_one' := C.th_one
      map_mul' := fun x y => C.th_mul (C.T_le_M (hPT x.2)) (C.T_le_M (hPT y.2)) }
  have hker : f.ker = (P ⊓ Q).subgroupOf P := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show C.th x = 1 ↔ _
    rw [C.th_eq_one_iff (C.T_le_M (hPT x.2))]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : f.range ≤ Subgroup.zpowers tau := by
    rintro _ ⟨x, rfl⟩
    rcases (C.mem_T.1 (hPT x.2)).2 with h | h
    · show C.th x ∈ _
      rw [h]; exact Subgroup.one_mem _
    · show C.th x ∈ _
      rw [h]; exact Subgroup.mem_zpowers _
  have hrange_card : Nat.card f.range ≤ 2 := by
    have := Subgroup.card_le_of_le hrange
    rwa [card_zpowers_tau] at this
  have hne : Nat.card f.range ≠ 1 := by
    intro h1
    apply hPQ
    intro x hx
    have h3 : f ⟨x, hx⟩ ∈ f.range := ⟨⟨x, hx⟩, rfl⟩
    have h2 : f.range = ⊥ := Subgroup.card_eq_one.1 h1
    rw [h2, Subgroup.mem_bot] at h3
    exact (C.th_eq_one_iff (C.T_le_M (hPT hx))).1 h3
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  omega

end OrthCfg

end CFSG.CGT.PushingUpLit.Orth
