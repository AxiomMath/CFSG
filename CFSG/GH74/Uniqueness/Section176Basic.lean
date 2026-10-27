module

public import CFSG.Walter.W67.Section5.Prop56N
public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.GH74.Uniqueness.Theorem4

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem eq_two_mul_of_two_pow_sub_one_dvd {n k : ℕ} (hnk : n < k) (hk : k ≤ 2 * n)
    (hdvd : 2 ^ n - 1 ∣ 2 ^ k - 1) : k = 2 * n := by
  obtain ⟨r, rfl⟩ : ∃ r, k = n + r := ⟨k - n, by omega⟩
  have h1n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h1r : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h1 : 2 ^ (n + r) - 1 = (2 ^ n - 1) * 2 ^ r + (2 ^ r - 1) := by
    rw [pow_add]
    have h1nr : 1 ≤ 2 ^ n * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    zify [h1n, h1r, h1nr]
    ring
  rw [h1] at hdvd
  have h2 : 2 ^ n - 1 ∣ 2 ^ r - 1 := (Nat.dvd_add_right (dvd_mul_right _ _)).mp hdvd
  by_contra hne
  have hrn : r < n := by omega
  have h3 : 2 ^ r < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hrn
  have h4 : 0 < 2 ^ r - 1 := by
    have := Nat.one_lt_two_pow (n := r) (by omega)
    omega
  have := Nat.le_of_dvd h4 h2
  omega

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.card_eq_ncard_omega_sub_one_mul
    (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) :
    Nat.card M = ((omega M).ncard - 1) * Nat.card ↥(M ⊓ conjugate M t) := by
  have hβ : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have hβM : conjugate M t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr htM
  let α₀ : omega M := ⟨M, self_mem_omega M⟩
  let β₀ : omega M := ⟨conjugate M t, hβ⟩
  have hfixα : ∀ m : ↥M, m • α₀ = α₀ := fun m => Subtype.ext (by
    change conjugate M (m : X)⁻¹ = M
    exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (M.inv_mem m.2))
  have hstab : MulAction.stabilizer ↥M β₀ = (M ⊓ conjugate M t).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have h1 : (m • β₀ : omega M) = β₀ ↔ conjugate (conjugate M t) (m : X)⁻¹ = conjugate M t :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, S.prodDisc.conjugate_eq_iff_mem hβ, (conjugate M t).inv_mem_iff]
    exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
  have horb : MulAction.orbit ↥M β₀ = {α₀}ᶜ := by
    ext γ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, rfl⟩ h
      apply hβM
      have h2 : m⁻¹ • (m • β₀) = m⁻¹ • α₀ := congrArg (fun γ => m⁻¹ • γ) h
      rw [inv_smul_smul, hfixα] at h2
      exact congrArg Subtype.val h2
    · intro hγ
      have hγM : (γ : Subgroup X) ≠ M := fun h => hγ (Subtype.ext h)
      obtain ⟨m, hm, hmγ⟩ :=
        S.prodDisc.exists_mem_conjugate_of_doublyTransitive S.theorem4.1 hβ γ.2 hβM hγM
      refine ⟨⟨m, hm⟩⁻¹, Subtype.ext ?_⟩
      change conjugate (conjugate M t) ((⟨m, hm⟩⁻¹ : ↥M) : X)⁻¹ = γ
      simpa using hmγ
  have hidx := MulAction.index_stabilizer (↥M) β₀
  rw [hstab, horb, Set.compl_eq_univ_sdiff, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _),
    Set.ncard_univ, Nat.card_coe_set_eq] at hidx
  have hcard := Subgroup.card_mul_index ((M ⊓ conjugate M t).subgroupOf M)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  rw [← hcard, mul_comm]

omit [Finite X] in
theorem isPGroup_oTwoIn (H : Subgroup X) : IsPGroup 2 (oTwoIn H) :=
  CFSG.pCore_isPGroup.map H.subtype

omit [Finite X] in
theorem eq_one_of_mem_oTwoIn_of_odd {H : Subgroup X} {x : X} (hx : x ∈ oTwoIn H)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (isPGroup_oTwoIn H) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem exists_pow_orderOf_eq_two_of_mem_oTwoIn {H : Subgroup X} {v : X} (hv : v ∈ oTwoIn H)
    (hv1 : v ≠ 1) : ∃ k : ℕ, orderOf (v ^ k) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp (isPGroup_oTwoIn H) ⟨v, hv⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hv1 (orderOf_eq_one_iff.mp hj)
  have hdvd : 2 ∣ orderOf v := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  exact ⟨orderOf v / 2, orderOf_pow_orderOf_div (orderOf_pos v).ne' hdvd⟩

theorem card_mul_card_le_card_sup {V D : Subgroup X} (h : V ⊓ D = ⊥) :
    Nat.card V * Nat.card D ≤ Nat.card ↥(V ⊔ D) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : ↥V × ↥D => (⟨(p.1 : X) * p.2,
    mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ : ↥(V ⊔ D))) ?_
  rintro ⟨v, d⟩ ⟨v', d'⟩ hvd
  have h1 : (v : X) * d = v' * d' := congrArg Subtype.val hvd
  have h2 : (v' : X)⁻¹ * v = d' * (d : X)⁻¹ := by
    calc (v' : X)⁻¹ * v = (v' : X)⁻¹ * (v * d) * (d : X)⁻¹ := by group
      _ = (v' : X)⁻¹ * (v' * d') * (d : X)⁻¹ := by rw [h1]
      _ = d' * (d : X)⁻¹ := by group
  have h3 : (v' : X)⁻¹ * v ∈ V ⊓ D :=
    Subgroup.mem_inf.mpr ⟨V.mul_mem (V.inv_mem v'.2) v.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
  rw [h, mem_bot] at h3
  have hv : (v : X) = v' := (inv_mul_eq_one.mp h3).symm
  have hd : (d : X) = d' := by
    rw [hv] at h1
    exact (mul_left_cancel h1)
  exact Prod.ext (Subtype.ext hv) (Subtype.ext hd)

theorem card_dvd_card_sub_one_of_semiregular {A V : Subgroup X}
    (hAV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (hfree : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a → a = 1 ∨ v = 1) :
    Nat.card A ∣ Nat.card V - 1 := by
  let _ : MulAction ↥A ↥V :=
    { smul := fun a v => ⟨(a : X) * v * (a : X)⁻¹, hAV a a.2 v v.2⟩
      one_smul := fun v => Subtype.ext
        (show ((1 : ↥A) : X) * (v : X) * ((1 : ↥A) : X)⁻¹ = v by simp)
      mul_smul := fun a b v => Subtype.ext
        (show ((a * b : ↥A) : X) * (v : X) * ((a * b : ↥A) : X)⁻¹ =
          (a : X) * ((b : X) * v * (b : X)⁻¹) * (a : X)⁻¹ by
            simp only [Subgroup.coe_mul, mul_inv_rev]
            group) }
  refine CFSG.Walter.W67.Sec56.card_dvd_card_sub_one_of_fpf (1 : ↥V)
    (fun b => Subtype.ext (show (b : X) * ((1 : ↥V) : X) * (b : X)⁻¹ = ((1 : ↥V) : X) by simp))
    fun b hb y hy => ?_
  have h1 : (b : X) * y * (b : X)⁻¹ = y := congrArg Subtype.val hy
  have h2 : (b : X) * y = y * b := by
    calc (b : X) * y = (b : X) * y * (b : X)⁻¹ * b := by group
      _ = y * b := by rw [h1]
  rcases hfree b b.2 y y.2 h2 with h | h
  · exact absurd (Subtype.ext h) hb
  · exact Subtype.ext h

end CFSG.GH74.Uniqueness
