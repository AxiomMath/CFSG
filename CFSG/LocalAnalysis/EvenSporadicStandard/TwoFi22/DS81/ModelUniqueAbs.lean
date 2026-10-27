module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueLin
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

structure AbsData (G : Type*) [Group G] (S : Subgroup G) (b u w : ℕ → G)
    (cu cw : Array (Array ℕ)) : Prop where
  card_S : Nat.card S = 2 ^ 17
  b_mem : ∀ i < 10, b i ∈ S
  b_sq : ∀ i < 10, b i * b i = 1
  b_comm : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i
  card_E : Nat.card (Subgroup.closure (b '' Set.Iio 10)) = 2 ^ 10
  gen : ∀ s ∈ S, ∃ k₀ < cu.size, ∃ k₁ < cw.size, s = u k₀ * w k₁
  u_mem : ∀ k < cu.size, u k ∈ S
  w_mem : ∀ k < cw.size, w k ∈ S
  cu_lt : ∀ k < cu.size, ∀ i < 10, cu[k]![i]! < 1024
  cw_lt : ∀ k < cw.size, ∀ i < 10, cw[k]![i]! < 1024
  act_u : ∀ k < cu.size, ∀ i < 10, u k * b i * (u k)⁻¹ = phi b cu[k]![i]!
  act_w : ∀ k < cw.size, ∀ i < 10, w k * b i * (w k)⁻¹ = phi b cw[k]![i]!
  fc : fcSpec cu cw

theorem mul_comm_of_mul_self_eq_one {G : Type*} [Group G] {g h : G} (hg : g * g = 1)
    (hh : h * h = 1) (hgh : g * h * (g * h) = 1) : g * h = h * g := by
  have e1 : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have e2 : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
    _ = h * g := by rw [mul_inv_rev, e1, e2]

namespace AbsData

variable {G : Type*} [Group G] {S : Subgroup G} {b u w : ℕ → G} {cu cw : Array (Array ℕ)}
  (D : AbsData G S b u w cu cw)

include D

theorem phi_xor' (v v' : ℕ) : phi b (v ^^^ v') = phi b v * phi b v' := phi_xor D.b_comm D.b_sq v v'

theorem phi_comm (v v' : ℕ) : phi b v * phi b v' = phi b v' * phi b v := by
  rw [← D.phi_xor', ← D.phi_xor', Nat.xor_comm]

theorem mem_E_comm {x y : G} (hx : x ∈ Subgroup.closure (b '' Set.Iio 10))
    (hy : y ∈ Subgroup.closure (b '' Set.Iio 10)) : x * y = y * x := by
  obtain ⟨v, -, rfl⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq hx
  obtain ⟨v', -, rfl⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq hy
  exact D.phi_comm v v'

theorem E_le : Subgroup.closure (b '' Set.Iio 10) ≤ S := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact D.b_mem i hi

theorem phi_inj {v v' : Fin 1024} (h : phi b v.val = phi b v'.val) : v = v' := by
  let e : Fin 1024 → Subgroup.closure (b '' Set.Iio 10) := fun v => ⟨phi b v.val, phi_mem _⟩
  have hs : Function.Surjective e := fun x => by
    obtain ⟨v, hv, hx⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq x.2
    exact ⟨⟨v, hv⟩, Subtype.ext hx⟩
  have hb : Function.Bijective e :=
    hs.bijective_of_nat_card_le
      (by rw [D.card_E, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact hb.1 (Subtype.ext h)

theorem exists_phi {x : G} (hx : x ∈ Subgroup.closure (b '' Set.Iio 10)) :
    ∃ v : Fin 1024, phi b v.val = x := by
  obtain ⟨v, hv, h⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq hx
  exact ⟨⟨v, hv⟩, h⟩

theorem conj_uw {k₀ k₁ : ℕ} (h₀ : k₀ < cu.size) (h₁ : k₁ < cw.size) (v : Fin 1024) :
    (u k₀ * w k₁) * phi b v.val * (u k₀ * w k₁)⁻¹ =
      phi b (fn (compose cu[k₀]! cw[k₁]!) v).val := by
  have e1 := conj_phi D.b_comm D.b_sq (w k₁) cw[k₁]! (D.act_w k₁ h₁) v.val
  have e2 := conj_phi D.b_comm D.b_sq (u k₀) cu[k₀]! (D.act_u k₀ h₀) (lin cw[k₁]! v.val)
  have e3 : (u k₀ * w k₁) * phi b v.val * (u k₀ * w k₁)⁻¹ =
      u k₀ * (w k₁ * phi b v.val * (w k₁)⁻¹) * (u k₀)⁻¹ := by group
  rw [e3, e1, e2, fn_val (compose_lt (D.cu_lt k₀ h₀) _) v, lin_compose]

theorem exists_conj {s : G} (hs : s ∈ S) (v : Fin 1024) :
    ∃ v' : Fin 1024, s * phi b v.val * s⁻¹ = phi b v'.val := by
  obtain ⟨k₀, h₀, k₁, h₁, rfl⟩ := D.gen s hs
  exact ⟨_, D.conj_uw h₀ h₁ v⟩

@[expose] noncomputable def act (s : S) (v : Fin 1024) : Fin 1024 := (D.exists_conj s.2 v).choose

theorem act_spec (s : S) (v : Fin 1024) :
    s.1 * phi b v.val * s.1⁻¹ = phi b (D.act s v).val :=
  (D.exists_conj s.2 v).choose_spec

theorem act_eq {s : S} {v v' : Fin 1024} (h : s.1 * phi b v.val * s.1⁻¹ = phi b v'.val) :
    D.act s v = v' :=
  D.phi_inj ((D.act_spec s v).symm.trans h)

theorem act_one (v : Fin 1024) : D.act 1 v = v := D.act_eq (by simp)

theorem act_mul (s s' : S) (v : Fin 1024) : D.act (s * s') v = D.act s (D.act s' v) := by
  refine D.act_eq ?_
  rw [← D.act_spec s (D.act s' v), ← D.act_spec s' v]
  simp only [Subgroup.coe_mul, mul_inv_rev]
  group

@[expose] noncomputable def rho : S →* Equiv.Perm (Fin 1024) where
  toFun s :=
    ⟨D.act s, D.act s⁻¹, fun v => by rw [← D.act_mul, inv_mul_cancel, D.act_one],
      fun v => by rw [← D.act_mul, mul_inv_cancel, D.act_one]⟩
  map_one' := Equiv.ext (D.act_one)
  map_mul' s s' := Equiv.ext (D.act_mul s s')

theorem rho_uw {k₀ k₁ : ℕ} (h₀ : k₀ < cu.size) (h₁ : k₁ < cw.size)
    (hs : u k₀ * w k₁ ∈ S) :
    ⇑(D.rho ⟨u k₀ * w k₁, hs⟩) = fn (compose cu[k₀]! cw[k₁]!) :=
  funext fun v => D.act_eq (D.conj_uw h₀ h₁ v)

theorem rho_mem_mset (s : S) : ⇑(D.rho s) ∈ mset cu cw := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨k₀, h₀, k₁, h₁, rfl⟩ := D.gen s hs
  exact ⟨k₀, h₀, k₁, h₁, D.rho_uw h₀ h₁ hs⟩

theorem two_pow_seven_le_card_range : 2 ^ 7 ≤ Nat.card D.rho.range := by
  have h1 := D.fc.1
  have hsub : mset cu cw ⊆ (fun g : Equiv.Perm (Fin 1024) => ⇑g) '' (D.rho.range : Set _) := by
    rintro f ⟨k₀, h₀, k₁, h₁, rfl⟩
    have hs : u k₀ * w k₁ ∈ S := S.mul_mem (D.u_mem k₀ h₀) (D.w_mem k₁ h₁)
    exact ⟨D.rho ⟨_, hs⟩, ⟨_, rfl⟩, D.rho_uw h₀ h₁ hs⟩
  calc 2 ^ 7 ≤ (mset cu cw).ncard := h1
    _ ≤ ((fun g : Equiv.Perm (Fin 1024) => ⇑g) '' (D.rho.range : Set _)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (D.rho.range : Set (Equiv.Perm (Fin 1024))).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card D.rho.range := (Nat.card_coe_set_eq _).symm

theorem ker_eq : D.rho.ker = (Subgroup.closure (b '' Set.Iio 10)).subgroupOf S := by
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [D.card_S]; norm_num)
  have hle : (Subgroup.closure (b '' Set.Iio 10)).subgroupOf S ≤ D.rho.ker := by
    intro s hs
    have hsE : s.1 ∈ Subgroup.closure (b '' Set.Iio 10) := Subgroup.mem_subgroupOf.1 hs
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun v => ?_
    refine D.act_eq ?_
    show s.1 * phi b v.val * s.1⁻¹ = phi b v.val
    rw [D.mem_E_comm hsE (phi_mem v.val), mul_inv_cancel_right]
  have hcardE : Nat.card ((Subgroup.closure (b '' Set.Iio 10)).subgroupOf S) = 2 ^ 10 := by
    rw [← D.card_E]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.E_le).toEquiv
  have hk : Nat.card D.rho.ker ≤ 2 ^ 10 := by
    have h := Subgroup.card_ker_mul_card_range D.rho
    rw [D.card_S] at h
    have hr := D.two_pow_seven_le_card_range
    by_contra hlt
    push Not at hlt
    nlinarith
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE]; exact hk)).symm

theorem le_of_card {A : Subgroup G} (hAS : A ≤ S) (hsq : ∀ a ∈ A, a ^ 2 = 1)
    (hcard : 2 ^ 10 ≤ Nat.card A) : A ≤ Subgroup.closure (b '' Set.Iio 10) := by
  classical
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [D.card_S]; norm_num)
  have hAfin : Finite A :=
    Finite.of_injective (Subgroup.inclusion hAS) (Subgroup.inclusion_injective hAS)
  let ρA : A →* Equiv.Perm (Fin 1024) := D.rho.comp (Subgroup.inclusion hAS)
  have hAsq : ∀ a : A, a.1 * a.1 = 1 := fun a => by rw [← pow_two]; exact hsq _ a.2
  have hAcomm : ∀ a a' : A, a.1 * a'.1 = a'.1 * a.1 := fun a a' =>
    mul_comm_of_mul_self_eq_one (hAsq a) (hAsq a') (hAsq (a * a'))
  let X : Finset (Fin 1024 → Fin 1024) := (Set.finite_range (fun a : A => ⇑(ρA a))).toFinset
  have hX : ∀ x, x ∈ X ↔ ∃ a : A, ⇑(ρA a) = x := fun x => by simp [X]
  have hXsub : (X : Set (Fin 1024 → Fin 1024)) ⊆ mset cu cw := by
    intro x hx
    obtain ⟨a, rfl⟩ := (hX x).1 hx
    exact D.rho_mem_mset ⟨a.1, hAS a.2⟩
  have hXmul : ∀ x ∈ X, ∀ y ∈ X, x ∘ y ∈ X := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (hX x).1 hx
    obtain ⟨a', rfl⟩ := (hX y).1 hy
    exact (hX _).2 ⟨a * a', by rw [map_mul, Equiv.Perm.coe_mul]⟩
  have hXsq : ∀ x ∈ X, x ∘ x = id := by
    intro x hx
    obtain ⟨a, rfl⟩ := (hX x).1 hx
    have h1 : a * a = 1 := Subtype.ext (hAsq a)
    rw [← Equiv.Perm.coe_mul, ← map_mul, h1, map_one, Equiv.Perm.coe_one]
  have hXne : X.Nonempty := ⟨_, (hX _).2 ⟨1, rfl⟩⟩
  rcases D.fc.2 X hXsub hXmul hXsq hXne with hid | hle
  · intro a ha
    have h1 : ρA ⟨a, ha⟩ = 1 := Equiv.ext fun v => congrFun (hid _ ((hX _).2 ⟨⟨a, ha⟩, rfl⟩)) v
    have h2 : (⟨a, hAS ha⟩ : S) ∈ D.rho.ker := h1
    rw [D.ker_eq] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  · exfalso
    have hAc := Subgroup.card_ker_mul_card_range ρA
    have hr : Nat.card ρA.range ≤ X.card := by
      let f : ρA.range → X := fun g =>
        ⟨⇑g.1, (hX _).2 (by obtain ⟨a, ha⟩ := g.2; exact ⟨a, by rw [ha]⟩)⟩
      have hf : Function.Injective f := fun g g' h =>
        Subtype.ext (DFunLike.coe_injective (congrArg Subtype.val h))
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_eq_fintype_card (α := X), Fintype.card_coe] at this
    have hkE : ∀ a : ρA.ker, a.1.1 ∈ Subgroup.closure (b '' Set.Iio 10) := by
      intro a
      have h2 : (⟨a.1.1, hAS a.1.2⟩ : S) ∈ D.rho.ker := a.2
      rw [D.ker_eq] at h2
      exact Subgroup.mem_subgroupOf.1 h2
    choose f hf using fun a : ρA.ker => D.exists_phi (hkE a)
    have hk : Nat.card ρA.ker ≤ (fixSet X).card := by
      have hmem : ∀ a : ρA.ker, f a ∈ fixSet X := by
        intro a
        simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro x hx
        obtain ⟨a', rfl⟩ := (hX x).1 hx
        refine D.act_eq ?_
        show a'.1 * phi b (f a).val * a'.1⁻¹ = phi b (f a).val
        rw [hf a, hAcomm a' a.1, mul_inv_cancel_right]
      let g : ρA.ker → fixSet X := fun a => ⟨f a, hmem a⟩
      have hg : Function.Injective g := by
        intro a a' h
        have h1 : f a = f a' := congrArg Subtype.val h
        apply Subtype.ext
        apply Subtype.ext
        rw [← hf a, ← hf a', h1]
      have := Nat.card_le_card_of_injective g hg
      rwa [Nat.card_eq_fintype_card (α := fixSet X), Fintype.card_coe] at this
    have h3 : Nat.card A ≤ (fixSet X).card * X.card := by
      rw [← hAc]
      exact Nat.mul_le_mul hk hr
    nlinarith [hle, hcard, h3]

end AbsData

end CFSG.EvenSporadicStandard.TwoFi22.DS81
