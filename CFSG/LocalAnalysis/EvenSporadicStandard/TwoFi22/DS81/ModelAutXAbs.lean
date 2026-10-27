module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXSpec
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

structure AbsX (G : Type*) [Group G] (S T : Subgroup G) (b u : ℕ → G) (ms : Array (Array ℕ))
    (q : ℕ → Bool) : Prop where
  card_S : Nat.card S = 2 ^ 18
  T_le : T ≤ S
  b_mem : ∀ i < 10, b i ∈ T
  b_sq : ∀ i < 10, b i * b i = 1
  b_comm : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i
  phi_inj : ∀ v < 1024, ∀ v' < 1024, phi b v = phi b v' → v = v'
  size_ms : ms.size = 2 ^ 8
  u_mem : ∀ k < ms.size, u k ∈ S
  u_T : ∀ k < ms.size, q k = true → u k ∈ T
  ms_lt : ∀ k < ms.size, ∀ i < 10, ms[k]![i]! < 1024
  ms_inj : ∀ k < ms.size, ∀ k' < ms.size, fn ms[k]! = fn ms[k']! → k = k'
  act_u : ∀ k < ms.size, ∀ i < 10, u k * b i * (u k)⁻¹ = phi b ms[k]![i]!
  fc : axSpec ms q

theorem mul_comm_of_mul_self_eq_one' {G : Type*} [Group G] {g h : G} (hg : g * g = 1)
    (hh : h * h = 1) (hgh : g * h * (g * h) = 1) : g * h = h * g := by
  have e1 : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have e2 : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
    _ = h * g := by rw [mul_inv_rev, e1, e2]

namespace AbsX

variable {G : Type*} [Group G] {S T : Subgroup G} {b u : ℕ → G} {ms : Array (Array ℕ)}
  {q : ℕ → Bool} (D : AbsX G S T b u ms q)

include D

theorem phi_xor' (v v' : ℕ) : phi b (v ^^^ v') = phi b v * phi b v' := phi_xor D.b_comm D.b_sq v v'

theorem phi_comm (v v' : ℕ) : phi b v * phi b v' = phi b v' * phi b v := by
  rw [← D.phi_xor', ← D.phi_xor', Nat.xor_comm]

theorem mem_E_comm {x y : G} (hx : x ∈ Subgroup.closure (b '' Set.Iio 10))
    (hy : y ∈ Subgroup.closure (b '' Set.Iio 10)) : x * y = y * x := by
  obtain ⟨v, -, rfl⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq hx
  obtain ⟨v', -, rfl⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq hy
  exact D.phi_comm v v'

theorem E_le_T : Subgroup.closure (b '' Set.Iio 10) ≤ T := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact D.b_mem i hi

theorem E_le : Subgroup.closure (b '' Set.Iio 10) ≤ S := D.E_le_T.trans D.T_le

theorem phi_mem_T (v : ℕ) : phi b v ∈ T := D.E_le_T (phi_mem v)

theorem phi_mem_S (v : ℕ) : phi b v ∈ S := D.T_le (D.phi_mem_T v)

theorem phi_inj' {v v' : Fin 1024} (h : phi b v.val = phi b v'.val) : v = v' :=
  Fin.ext (D.phi_inj v.val v.isLt v'.val v'.isLt h)

theorem card_E : Nat.card (Subgroup.closure (b '' Set.Iio 10)) = 2 ^ 10 := by
  let e : Fin 1024 → Subgroup.closure (b '' Set.Iio 10) := fun v => ⟨phi b v.val, phi_mem _⟩
  have hinj : Function.Injective e := fun v v' h => D.phi_inj' (congrArg Subtype.val h)
  have hs : Function.Surjective e := fun x => by
    obtain ⟨v, hv, hx⟩ := exists_phi_of_mem_closure D.b_comm D.b_sq x.2
    exact ⟨⟨v, hv⟩, Subtype.ext hx⟩
  rw [← Nat.card_congr (Equiv.ofBijective e ⟨hinj, hs⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

theorem conj_uphi {k : ℕ} (hk : k < ms.size) (v w : ℕ) :
    (u k * phi b v) * phi b w * (u k * phi b v)⁻¹ = phi b (lin ms[k]! w) := by
  have e1 := conj_phi D.b_comm D.b_sq (u k) ms[k]! (D.act_u k hk) w
  have e3 : (u k * phi b v) * phi b w * (u k * phi b v)⁻¹ =
      u k * (phi b v * phi b w * (phi b v)⁻¹) * (u k)⁻¹ := by group
  rw [e3, D.phi_comm v w, mul_inv_cancel_right, e1]

theorem gen {s : G} (hs : s ∈ S) : ∃ k < ms.size, ∃ v < 1024, s = u k * phi b v := by
  classical
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [D.card_S]; norm_num)
  let f : Fin ms.size × Fin 1024 → S := fun p =>
    ⟨u p.1 * phi b p.2, S.mul_mem (D.u_mem _ p.1.isLt) (D.phi_mem_S _)⟩
  have hinj : Function.Injective f := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ h
    have h1 : u k * phi b v = u k' * phi b v' := congrArg Subtype.val h
    have h2 : ∀ w : ℕ, phi b (lin ms[k.val]! w) = phi b (lin ms[k'.val]! w) := fun w => by
      rw [← D.conj_uphi k.isLt v w, ← D.conj_uphi k'.isLt v' w, h1]
    have h3 : fn ms[k.val]! = fn ms[k'.val]! := by
      funext w
      apply Fin.ext
      rw [fn_val (D.ms_lt _ k.isLt), fn_val (D.ms_lt _ k'.isLt)]
      exact D.phi_inj _ (lin_lt _ (D.ms_lt _ k.isLt) _) _ (lin_lt _ (D.ms_lt _ k'.isLt) _)
        (h2 w.val)
    have hkk : k = k' := Fin.ext (D.ms_inj _ k.isLt _ k'.isLt h3)
    subst hkk
    have h4 : phi b v.val = phi b v'.val := mul_left_cancel h1
    rw [D.phi_inj' h4]
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [D.card_S, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin ms.size),
      Nat.card_eq_fintype_card (α := Fin 1024), Fintype.card_fin, Fintype.card_fin, D.size_ms]
    norm_num
  obtain ⟨⟨k, v⟩, hkv⟩ := hbij.2 ⟨s, hs⟩
  exact ⟨k, k.isLt, v, v.isLt, (congrArg Subtype.val hkv).symm⟩

theorem exists_conj {s : G} (hs : s ∈ S) (v : Fin 1024) :
    ∃ v' : Fin 1024, s * phi b v.val * s⁻¹ = phi b v'.val := by
  obtain ⟨k, hk, v0, -, rfl⟩ := D.gen hs
  exact ⟨fn ms[k]! v, by rw [D.conj_uphi hk v0 v.val, fn_val (D.ms_lt k hk) v]⟩

@[expose] noncomputable def act (s : S) (v : Fin 1024) : Fin 1024 := (D.exists_conj s.2 v).choose

theorem act_spec (s : S) (v : Fin 1024) :
    s.1 * phi b v.val * s.1⁻¹ = phi b (D.act s v).val :=
  (D.exists_conj s.2 v).choose_spec

theorem act_eq {s : S} {v v' : Fin 1024} (h : s.1 * phi b v.val * s.1⁻¹ = phi b v'.val) :
    D.act s v = v' :=
  D.phi_inj' ((D.act_spec s v).symm.trans h)

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

theorem rho_uphi {k : ℕ} (hk : k < ms.size) (v₀ : ℕ) (hs : u k * phi b v₀ ∈ S) :
    ⇑(D.rho ⟨u k * phi b v₀, hs⟩) = fn ms[k]! :=
  funext fun v => D.act_eq (by rw [D.conj_uphi hk v₀ v.val, fn_val (D.ms_lt k hk) v])

theorem rho_mem_axSet (s : S) : ⇑(D.rho s) ∈ axSet ms := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨k, hk, v₀, -, rfl⟩ := D.gen hs
  exact ⟨k, hk, D.rho_uphi hk v₀ hs⟩

theorem two_pow_eight_le_card_range : 2 ^ 8 ≤ Nat.card D.rho.range := by
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [D.card_S]; norm_num)
  have hs : ∀ k : Fin ms.size, u k * phi b 0 ∈ S := fun k =>
    S.mul_mem (D.u_mem _ k.isLt) (D.phi_mem_S _)
  let f : Fin ms.size → D.rho.range := fun k => ⟨D.rho ⟨u k * phi b 0, hs k⟩, ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro k k' h
    have h1 : ⇑(D.rho ⟨u k * phi b 0, hs k⟩) = ⇑(D.rho ⟨u k' * phi b 0, hs k'⟩) :=
      congrArg (fun g : D.rho.range => ⇑g.1) h
    rw [D.rho_uphi k.isLt 0, D.rho_uphi k'.isLt 0] at h1
    exact Fin.ext (D.ms_inj _ k.isLt _ k'.isLt h1)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := Fin ms.size), Fintype.card_fin, D.size_ms] at this

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
    have hr := D.two_pow_eight_le_card_range
    by_contra hlt
    push Not at hlt
    nlinarith
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE]; exact hk)).symm

theorem card_le {A : Subgroup G} (hAS : A ≤ S) (hsq : ∀ a ∈ A, a ^ 2 = 1) (hAT : ¬ A ≤ T) :
    Nat.card A ≤ 2 ^ 8 := by
  classical
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [D.card_S]; norm_num)
  have hAfin : Finite A :=
    Finite.of_injective (Subgroup.inclusion hAS) (Subgroup.inclusion_injective hAS)
  let ρA : A →* Equiv.Perm (Fin 1024) := D.rho.comp (Subgroup.inclusion hAS)
  have hAsq : ∀ a : A, a.1 * a.1 = 1 := fun a => by rw [← pow_two]; exact hsq _ a.2
  have hAcomm : ∀ a a' : A, a.1 * a'.1 = a'.1 * a.1 := fun a a' =>
    mul_comm_of_mul_self_eq_one' (hAsq a) (hAsq a') (hAsq (a * a'))
  let X : Finset (Fin 1024 → Fin 1024) := (Set.finite_range (fun a : A => ⇑(ρA a))).toFinset
  have hX : ∀ x, x ∈ X ↔ ∃ a : A, ⇑(ρA a) = x := fun x => by simp [X]
  have hXsub : (X : Set (Fin 1024 → Fin 1024)) ⊆ axSet ms := by
    intro x hx
    obtain ⟨a, rfl⟩ := (hX x).1 hx
    exact D.rho_mem_axSet ⟨a.1, hAS a.2⟩
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
  rcases D.fc X hXsub hXmul hXsq hXne with hQ | hle
  · exfalso
    refine hAT fun a ha => ?_
    obtain ⟨k, hk, hqk, hfk⟩ := hQ _ ((hX _).2 ⟨⟨a, ha⟩, rfl⟩)
    obtain ⟨k', hk', v₀, -, ha'⟩ := D.gen (hAS ha)
    have hρ : ⇑(ρA ⟨a, ha⟩) = fn ms[k']! := by
      subst ha'
      exact D.rho_uphi hk' v₀ _
    have hkk : k = k' := D.ms_inj _ hk _ hk' (hfk.symm.trans hρ)
    subst hkk
    rw [ha']
    exact T.mul_mem (D.u_T _ hk hqk) (D.phi_mem_T _)
  · have hAc := Subgroup.card_ker_mul_card_range ρA
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
    choose f hf using fun a : ρA.ker =>
      (exists_phi_of_mem_closure D.b_comm D.b_sq (hkE a))
    have hk : Nat.card ρA.ker ≤ (fixSet X).card := by
      have hmem : ∀ a : ρA.ker, (⟨f a, (hf a).1⟩ : Fin 1024) ∈ fixSet X := by
        intro a
        simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro x hx
        obtain ⟨a', rfl⟩ := (hX x).1 hx
        refine D.act_eq ?_
        show a'.1 * phi b (f a) * a'.1⁻¹ = phi b (f a)
        rw [(hf a).2, hAcomm a' a.1, mul_inv_cancel_right]
      let g : ρA.ker → fixSet X := fun a => ⟨⟨f a, (hf a).1⟩, hmem a⟩
      have hg : Function.Injective g := by
        intro a a' h
        have h1 : f a = f a' := congrArg (fun y : fixSet X => y.1.val) h
        apply Subtype.ext
        apply Subtype.ext
        rw [← (hf a).2, ← (hf a').2, h1]
      have := Nat.card_le_card_of_injective g hg
      rwa [Nat.card_eq_fintype_card (α := fixSet X), Fintype.card_coe] at this
    have h3 : Nat.card A ≤ (fixSet X).card * X.card := by
      rw [← hAc]
      exact Nat.mul_le_mul hk hr
    calc Nat.card A ≤ (fixSet X).card * X.card := h3
      _ = X.card * (fixSet X).card := mul_comm _ _
      _ ≤ 2 ^ 8 := hle

end AbsX

end CFSG.EvenSporadicStandard.TwoFi22.DS81
