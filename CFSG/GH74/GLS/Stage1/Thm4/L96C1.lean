module

public import CFSG.GH74.GLS.Stage1.Thm4.L96Inner
public import CFSG.GH74.GLS.Stage1.Thm4.L96Lift
public import CFSG.GH74.GLS.Stage1.Thm4.L96Perm

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement
open Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  {h : Ctx98 G Lh z t S K} {n : ℕ}

omit [Finite G] in
@[expose] def conjC {g : G} (hg : g * z * g⁻¹ = t) : ↥(Cz t) →* ↥(Cz z) where
  toFun y := ⟨g⁻¹ * (y : G) * g, by
    have hy : (y : G) * t = t * (y : G) := Subgroup.mem_centralizer_singleton_iff.1 y.2
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hz : z = g⁻¹ * t * g := by rw [← hg]; group
    calc g⁻¹ * (y : G) * g * z = g⁻¹ * (y : G) * g * (g⁻¹ * t * g) := by rw [← hz]
      _ = g⁻¹ * ((y : G) * t) * g := by group
      _ = g⁻¹ * (t * (y : G)) * g := by rw [hy]
      _ = (g⁻¹ * t * g) * (g⁻¹ * (y : G) * g) := by group
      _ = z * (g⁻¹ * (y : G) * g) := by rw [← hz]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

omit [Finite G] in
theorem conjC_coe {g : G} (hg : g * z * g⁻¹ = t) (y : ↥(Cz t)) :
    ((conjC hg y : ↥(Cz z)) : G) = g⁻¹ * (y : G) * g := rfl

section Ker

variable (A : Act h n)

include A

theorem Act.ker_unique {y y' : HatT K} (hy : y ∈ A.π.ker) (hy' : y' ∈ A.π.ker) (hy1 : y ≠ 1)
    (hy1' : y' ≠ 1) : y = y' := by
  obtain ⟨zz, -, -, -, hzk⟩ := A.cover.exists_z
  rcases hzk y hy with h1 | h1
  · exact absurd h1 hy1
  rcases hzk y' hy' with h2 | h2
  · exact absurd h2 hy1'
  rw [h1, h2]

theorem Act.π_z (hn4 : 4 ≤ n) : A.π (QuotientGroup.mk (⟨z, h.z_mem⟩ : ↥K)) = 1 := by
  have hn4' : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn4
  have hmem : A.π (QuotientGroup.mk (⟨z, h.z_mem⟩ : ↥K)) ∈ center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := A.cover.surj g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    have : k * ⟨z, h.z_mem⟩ = (⟨z, h.z_mem⟩ : ↥K) * k := Subtype.ext (h.z_comm k.2)
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  rw [alternatingGroup.center_eq_bot hn4'] at hmem
  exact hmem

omit A in
theorem Act.mk_z_ne_one : (QuotientGroup.mk (⟨z, h.z_mem⟩ : ↥K) : HatT K) ≠ 1 :=
  mk'_ne_one_of_orderOf_two (N := pPrimeCore 2 ↥K) odd_card_pPrimeCore
    (by rw [Subgroup.orderOf_mk]; exact h.z_ord)

end Ker

theorem z_mem_Cz_t (h : Ctx98 G Lh z t S K) : z ∈ Cz t := by
  have : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.1 h.std.t_cen
  exact Subgroup.mem_centralizer_singleton_iff.2 this.symm

@[expose] noncomputable def Theta (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t) :
    ↥(K ⊓ Cz t) →* Equiv.Perm (Fin n) :=
  A.ρ.comp ((conjC hg).comp (Subgroup.inclusion inf_le_right))

theorem commute_swap_of_fixes {m : ℕ} (γ : Perm (Fin m)) {a b : Fin m} (ha : γ a = a) (hb : γ b = b) :
    Commute γ (swap a b) := by
  have hdis : Disjoint γ (swap a b) := by
    intro x
    by_cases hxa : x = a
    · left; rw [hxa]; exact ha
    by_cases hxb : x = b
    · left; rw [hxb]; exact hb
    · right; exact swap_apply_of_ne_of_ne hxa hxb
  exact hdis.commute

section Zeta

variable (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t)

include A

theorem sign_zeta (hn : 8 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (htρ : A.ρ ⟨t, h.std.t_cen⟩ = swap a b) :
    Equiv.Perm.sign (Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩) = 1 := by
  classical
  obtain ⟨γ₁, γ₂, h₁, h₂, ha₁, hb₁, ha₂, hb₂, hct⟩ := exists_two_threeCycles (n := n) (by omega) a b hab
  have hodd3 : Odd (orderOf γ₁) := by rw [h₁]; decide
  have hodd3' : Odd (orderOf γ₂) := by rw [h₂]; decide
  have hs₁ : γ₁ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hodd3)
  have hs₂ : γ₂ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hodd3')
  set G₁ : alternatingGroup (Fin n) := ⟨γ₁, hs₁⟩ with hG₁
  set G₂ : alternatingGroup (Fin n) := ⟨γ₂, hs₂⟩ with hG₂
  have hG₁o : Odd (orderOf G₁) := by rw [← Subgroup.orderOf_coe]; exact hodd3
  have hG₂o : Odd (orderOf G₂) := by rw [← Subgroup.orderOf_coe]; exact hodd3'
  have hc₁ : (G₁ : Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ = A.ρ ⟨t, h.std.t_cen⟩ * (G₁ : Perm (Fin n)) := by
    rw [htρ]; exact (commute_swap_of_fixes γ₁ ha₁ hb₁).eq
  have hc₂ : (G₂ : Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ = A.ρ ⟨t, h.std.t_cen⟩ * (G₂ : Perm (Fin n)) := by
    rw [htρ]; exact (commute_swap_of_fixes γ₂ ha₂ hb₂).eq
  obtain ⟨x₁, hx₁t, hx₁o, hx₁π⟩ := A.exists_lift_odd G₁ hG₁o hc₁
  obtain ⟨x₂, hx₂t, hx₂o, hx₂π⟩ := A.exists_lift_odd G₂ hG₂o hc₂
  let mem : ∀ x : ↥K, (x : G) * t = t * (x : G) → (x : G) ∈ K ⊓ Cz t := fun x hx =>
    ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 hx⟩
  let y₁ : ↥(K ⊓ Cz t) := ⟨x₁, mem x₁ hx₁t⟩
  let y₂ : ↥(K ⊓ Cz t) := ⟨x₂, mem x₂ hx₂t⟩
  let yz : ↥(K ⊓ Cz t) := ⟨z, h.z_mem, z_mem_Cz_t h⟩
  let w : ↥(K ⊓ Cz t) := y₁ * y₂
  let o : ↥(K ⊓ Cz t) := yz⁻¹ * w ^ 2
  have hyz : yz = w ^ 2 * o⁻¹ := by simp [o]
  have hwK : ((w : ↥(K ⊓ Cz t)) : G) = (x₁ : G) * (x₂ : G) := rfl
  have hπw : ((A.π (QuotientGroup.mk (x₁ * x₂)) : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType
      = {2, 2} := by
    rw [QuotientGroup.mk_mul, map_mul, hx₁π, hx₂π]
    exact hct
  obtain ⟨hk, hne⟩ := A.cover.sq_mem_ker_ne_one_of_cycleType_two_two (by omega)
    (x := QuotientGroup.mk (x₁ * x₂)) hπw
  have hzk : (QuotientGroup.mk (⟨z, h.z_mem⟩ : ↥K) : HatT K) ∈ A.π.ker := A.π_z (by omega)
  have hsq : (QuotientGroup.mk (x₁ * x₂) : HatT K) ^ 2 = QuotientGroup.mk ⟨z, h.z_mem⟩ :=
    A.ker_unique hk hzk hne (Act.mk_z_ne_one (h := h))
  have hoK : (⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2 ∈ pPrimeCore 2 ↥K := by
    have : (QuotientGroup.mk ((x₁ * x₂) ^ 2) : HatT K) = QuotientGroup.mk ⟨z, h.z_mem⟩ := by
      rw [QuotientGroup.mk_pow]; exact hsq
    exact QuotientGroup.eq.1 this.symm
  have hodd_o : Odd (orderOf (o : G)) := by
    have h1 : orderOf (⟨(⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2, hoK⟩ : pPrimeCore 2 ↥K) ∣
        Nat.card (pPrimeCore 2 ↥K) := orderOf_dvd_natCard _
    have h2 : Odd (orderOf ((⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2)) := by
      rw [← Subgroup.orderOf_mk _ hoK]
      exact Odd.of_dvd_nat odd_card_pPrimeCore h1
    have h3 : (o : G) = (((⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2 : ↥K) : G) := by
      simp [o, yz, w, y₁, y₂]
    rw [h3, Subgroup.orderOf_coe]
    exact h2
  have hodd_Θo : Odd (orderOf (Theta A hg o)) := by
    have h1 : orderOf (Theta A hg o) ∣ orderOf o := orderOf_map_dvd _ _
    have h2 : Odd (orderOf o) := by rw [← Subgroup.orderOf_coe]; exact hodd_o
    exact Odd.of_dvd_nat h2 h1
  have hso : Equiv.Perm.sign (Theta A hg o) = 1 := sign_eq_one_of_odd_orderOf hodd_Θo
  rw [show (⟨z, h.z_mem, z_mem_Cz_t h⟩ : ↥(K ⊓ Cz t)) = yz from rfl, hyz, map_mul, map_pow, map_inv,
    map_mul, map_pow, map_inv, hso]
  simp

end Zeta

omit [Finite G] in
theorem orderOf_conj_inv (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
  exact this

section Final

variable (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t)

include A hg

theorem zeta_ne_one : Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ ≠ 1 := by
  intro h1
  have h2 : A.ρ (conjC hg ⟨z, z_mem_Cz_t h⟩) = 1 := h1
  have h3 : ((conjC hg ⟨z, z_mem_Cz_t h⟩ : ↥(Cz z)) : G) = g⁻¹ * z * g := rfl
  have hz2 : (g⁻¹ * z * g) ^ (2 ^ 1) = 1 := by
    have : (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by
      rw [pow_two, pow_two]; group
    rw [pow_one, this, ← h.z_ord, pow_orderOf_eq_one]; group
  have hzp : g⁻¹ * z * g ∈ zpowers z := by
    have := A.mem_zpowers_of_ker h2 (m := 1) (by rw [h3]; exact hz2)
    rw [h3] at this
    exact this
  have hord : orderOf (g⁻¹ * z * g) = 2 := by rw [orderOf_conj_inv]; exact h.z_ord
  have heq : g⁻¹ * z * g = z := eq_of_mem_zpowers_of_orderOf_two h.z_ord hzp hord
  apply t_ne_z h
  rw [← hg]
  calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [heq]
    _ = z := by group

theorem exists_pElement_theta_ne_one {p : ℕ} (hnp : (n = 8 ∧ p = 5) ∨ (n = 9 ∧ p = 7))
    {a b : Fin n} (hab : a ≠ b) (htρ : A.ρ ⟨t, h.std.t_cen⟩ = swap a b) :
    ∃ x : ↥(K ⊓ Cz t), (∃ m : ℕ, (x : G) ^ (p ^ m) = 1) ∧ Theta A hg x ≠ 1 := by
  classical
  have hp : p.Prime := by rcases hnp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hp2 : p ≠ 2 := by rcases hnp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨γ₁, γ₂, ho₁, ho₂, ha₁, hb₁, ha₂, hb₂, hev⟩ := exists_two_pElements hnp a b hab
  have hodd₁ : Odd (orderOf γ₁) := by rw [ho₁]; exact hpodd
  have hodd₂ : Odd (orderOf γ₂) := by rw [ho₂]; exact hpodd
  have hs₁ : γ₁ ∈ alternatingGroup (Fin n) :=
    Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hodd₁)
  have hs₂ : γ₂ ∈ alternatingGroup (Fin n) :=
    Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hodd₂)
  set G₁ : alternatingGroup (Fin n) := ⟨γ₁, hs₁⟩ with hG₁
  set G₂ : alternatingGroup (Fin n) := ⟨γ₂, hs₂⟩ with hG₂
  have hG₁o : orderOf G₁ = p := by rw [← Subgroup.orderOf_coe]; exact ho₁
  have hG₂o : orderOf G₂ = p := by rw [← Subgroup.orderOf_coe]; exact ho₂
  have hc₁ : (G₁ : Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ =
      A.ρ ⟨t, h.std.t_cen⟩ * (G₁ : Perm (Fin n)) := by
    rw [htρ]; exact (commute_swap_of_fixes γ₁ ha₁ hb₁).eq
  have hc₂ : (G₂ : Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ =
      A.ρ ⟨t, h.std.t_cen⟩ * (G₂ : Perm (Fin n)) := by
    rw [htρ]; exact (commute_swap_of_fixes γ₂ ha₂ hb₂).eq
  obtain ⟨x₁, hx₁t, ⟨m₁, hx₁o⟩, hx₁π⟩ := A.exists_lift_pElement hp hp2 G₁ hG₁o hc₁
  obtain ⟨x₂, hx₂t, ⟨m₂, hx₂o⟩, hx₂π⟩ := A.exists_lift_pElement hp hp2 G₂ hG₂o hc₂
  let mem : ∀ x : ↥K, (x : G) * t = t * (x : G) → (x : G) ∈ K ⊓ Cz t := fun x hx =>
    ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 hx⟩
  let y₁ : ↥(K ⊓ Cz t) := ⟨x₁, mem x₁ hx₁t⟩
  let y₂ : ↥(K ⊓ Cz t) := ⟨x₂, mem x₂ hx₂t⟩
  by_contra hcon
  push Not at hcon
  have key : ∀ (y : ↥(K ⊓ Cz t)) (m : ℕ), (y : G) ^ (p ^ m) = 1 →
      g⁻¹ * (y : G) * g ∈ Oz z := by
    intro y m hym
    have h1 := hcon y ⟨m, hym⟩
    have h2 : A.ρ (conjC hg ⟨(y : G), y.2.2⟩) = 1 := h1
    refine A.mem_Oz_of_ker h2 (m := p ^ m) (hpodd.pow) ?_
    have : ((conjC hg ⟨(y : G), y.2.2⟩ : ↥(Cz z)) : G) = g⁻¹ * (y : G) * g := rfl
    rw [this]
    have e : (g⁻¹ * (y : G) * g) ^ (p ^ m) = g⁻¹ * (y : G) ^ (p ^ m) * g := by
      have e' : (g⁻¹ * (y : G) * g⁻¹⁻¹) ^ (p ^ m) = g⁻¹ * (y : G) ^ (p ^ m) * g⁻¹⁻¹ := conj_pow
      simpa using e'
    rw [e, hym]; group
  have h1 := key y₁ m₁ hx₁o
  have h2 := key y₂ m₂ hx₂o
  have h12 : g⁻¹ * ((x₁ : G) * (x₂ : G)) * g ∈ Oz z := by
    have : g⁻¹ * ((x₁ : G) * (x₂ : G)) * g = (g⁻¹ * (x₁ : G) * g) * (g⁻¹ * (x₂ : G) * g) := by group
    rw [this]
    exact (Oz z).mul_mem h1 h2
  have hw_odd : Odd (orderOf (x₁ * x₂ : ↥K)) := by
    have h3 : Odd (orderOf (g⁻¹ * ((x₁ : G) * (x₂ : G)) * g)) := by
      have := orderOf_dvd_natCard (⟨g⁻¹ * ((x₁ : G) * (x₂ : G)) * g, h12⟩ : Oz z)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat (Nat.coprime_two_left.1 card_Oz_coprime) this
    rw [orderOf_conj_inv] at h3
    rw [← Subgroup.orderOf_coe]
    exact h3
  have hw_even : Even (orderOf (x₁ * x₂ : ↥K)) := by
    have h4 : orderOf (A.π (QuotientGroup.mk (x₁ * x₂))) ∣ orderOf (x₁ * x₂ : ↥K) :=
      orderOf_map_dvd (A.π.comp (QuotientGroup.mk' _)) _
    rw [QuotientGroup.mk_mul, map_mul, hx₁π, hx₂π] at h4
    have h5 : orderOf (G₁ * G₂) = orderOf (γ₁ * γ₂) := by rw [← Subgroup.orderOf_coe]; rfl
    rw [h5] at h4
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans h4)
  exact (Nat.not_even_iff_odd.2 hw_odd) hw_even

theorem false_of_transposition (hnp : n = 8 ∨ n = 9) {a b : Fin n} (hab : a ≠ b)
    (htρ : A.ρ ⟨t, h.std.t_cen⟩ = swap a b) : False := by
  classical
  obtain ⟨p, hnp'⟩ : ∃ p : ℕ, (n = 8 ∧ p = 5) ∨ (n = 9 ∧ p = 7) := by
    rcases hnp with h8 | h9
    · exact ⟨5, Or.inl ⟨h8, rfl⟩⟩
    · exact ⟨7, Or.inr ⟨h9, rfl⟩⟩
  have hp : p.Prime := by rcases hnp' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hp2 : p ≠ 2 := by rcases hnp' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hn8 : 8 ≤ n := by omega
  obtain ⟨x, ⟨m, hxm⟩, hΘx⟩ := exists_pElement_theta_ne_one A hg hnp' hab htρ
  set w : Perm (Fin n) := Theta A hg x with hw
  have hwp : w ^ (p ^ m) = 1 := by
    rw [hw, ← map_pow]
    have : x ^ (p ^ m) = 1 := Subtype.ext (by simpa using hxm)
    rw [this, map_one]
  obtain ⟨b', hb'm, hb'⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hwp)
  have hb'1 : 1 ≤ b' := by
    by_contra hb0
    have : b' = 0 := by omega
    rw [this, pow_zero] at hb'
    exact hΘx (orderOf_eq_one_iff.1 hb')
  set w' : Perm (Fin n) := w ^ (p ^ (b' - 1)) with hw'
  have hw'o : orderOf w' = p := by
    rw [hw', orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (by rw [hb']; exact pow_dvd_pow p (by omega)),
      hb']
    rw [Nat.pow_div (by omega : b' - 1 ≤ b') hp.pos]
    have : b' - (b' - 1) = 1 := by omega
    rw [this, pow_one]
  set ζ : Perm (Fin n) := Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ with hζ
  have hζ1 : ζ ≠ 1 := zeta_ne_one A hg
  have hζ2 : ζ ^ 2 = 1 := by
    rw [hζ, ← map_pow]
    have : (⟨z, h.z_mem, z_mem_Cz_t h⟩ : ↥(K ⊓ Cz t)) ^ 2 = 1 := by
      apply Subtype.ext
      have h2 : z ^ 2 = 1 := by rw [← h.z_ord]; exact pow_orderOf_eq_one z
      simpa using h2
    rw [this, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hζo : orderOf ζ = 2 := orderOf_eq_prime hζ2 hζ1
  have hζs : Equiv.Perm.sign ζ = 1 := sign_zeta A hg hn8 hab htρ
  have hcomm : Commute w' ζ := by
    have h1 : Commute w ζ := by
      rw [hw, hζ]
      apply Commute.map
      apply Subtype.ext
      have hk : (x : G) * z = z * (x : G) := h.z_comm x.2.1
      exact hk
    rw [hw']
    exact h1.pow_left _
  have hcop : Nat.Coprime (orderOf w') (orderOf ζ) := by
    rw [hw'o, hζo]; exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hu : orderOf (w' * ζ) = p * 2 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hw'o, hζo]
  have hw's : Equiv.Perm.sign w' = 1 :=
    sign_eq_one_of_odd_orderOf (by rw [hw'o]; exact hp.odd_of_ne_two hp2)
  have hus : Equiv.Perm.sign (w' * ζ) = 1 := by rw [map_mul, hw's, hζs, one_mul]
  rcases hnp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact no_order_ten_alt8 _ hus hu
  · exact no_order_fourteen_alt9 _ hus hu

end Final

end CFSG.GH74.GLS.Stage1.Thm4.L96
