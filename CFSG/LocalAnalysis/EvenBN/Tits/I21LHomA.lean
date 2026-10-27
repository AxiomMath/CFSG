module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.IntegralDomain

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

namespace Hom

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {G : Type*} [Group G]

@[expose] def er (ρ : G →* (V ≃ₗ[ZMod 2] V)) : G →* Module.End (ZMod 2) V :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp ρ

theorem er_apply (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g : G) (v : V) : er ρ g v = ρ g v := rfl

@[expose] def comm (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  Subalgebra.centralizer (ZMod 2) (er ρ '' (M : Set G))

theorem mem_comm (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) (z : Module.End (ZMod 2) V) :
    z ∈ comm ρ M ↔ ∀ m ∈ M, er ρ m * z = z * er ρ m := by
  simp [comm, Subalgebra.mem_centralizer_iff]

@[expose] def cz (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  comm ρ M ⊓ Subalgebra.centralizer (ZMod 2) (comm ρ M : Set (Module.End (ZMod 2) V))

theorem mem_cz (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) (z : Module.End (ZMod 2) V) :
    z ∈ cz ρ M ↔ z ∈ comm ρ M ∧ ∀ f ∈ comm ρ M, f * z = z * f := by
  simp [cz, Subalgebra.mem_centralizer_iff]

@[expose] def cj (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g : G) :
    Module.End (ZMod 2) V ≃ₐ[ZMod 2] Module.End (ZMod 2) V :=
  (ρ g).conjAlgEquiv (ZMod 2)

theorem cj_apply (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g : G) (f : Module.End (ZMod 2) V) :
    cj ρ g f = er ρ g * f * er ρ g⁻¹ := by
  ext v
  simp [cj, er_apply, LinearEquiv.conjAlgEquiv_apply]

theorem cj_er (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g h : G) : cj ρ g (er ρ h) = er ρ (g * h * g⁻¹) := by
  rw [cj_apply, ← map_mul, ← map_mul]

theorem er_inv_mul_cancel_left (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g : G) (x : Module.End (ZMod 2) V) :
    er ρ g⁻¹ * (er ρ g * x) = x := by
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem er_mul_inv_cancel_left (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g : G) (x : Module.End (ZMod 2) V) :
    er ρ g * (er ρ g⁻¹ * x) = x := by
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem cj_mul (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g h : G) (f : Module.End (ZMod 2) V) :
    cj ρ (g * h) f = cj ρ g (cj ρ h f) := by
  simp only [cj_apply, mul_inv_rev, map_mul, mul_assoc, er_inv_mul_cancel_left]

theorem cj_one (ρ : G →* (V ≃ₗ[ZMod 2] V)) (f : Module.End (ZMod 2) V) : cj ρ 1 f = f := by
  simp [cj_apply]

theorem cj_mem_comm (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) [M.Normal] (g : G)
    {z : Module.End (ZMod 2) V} (hz : z ∈ comm ρ M) : cj ρ g z ∈ comm ρ M := by
  rw [mem_comm] at hz ⊢
  intro m hm
  have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ M := Subgroup.Normal.conj_mem inferInstance m hm g⁻¹
  have e1 : er ρ m = cj ρ g (er ρ (g⁻¹ * m * g⁻¹⁻¹)) := by
    rw [cj_er]; congr 1; group
  rw [e1, ← map_mul, ← map_mul, hz _ hm']

theorem cj_mem_cz (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) [M.Normal] (g : G)
    {z : Module.End (ZMod 2) V} (hz : z ∈ cz ρ M) : cj ρ g z ∈ cz ρ M := by
  rw [mem_cz] at hz ⊢
  refine ⟨cj_mem_comm ρ M g hz.1, fun f hf => ?_⟩
  have hf' : cj ρ g⁻¹ f ∈ comm ρ M := cj_mem_comm ρ M g⁻¹ hf
  have e1 : f = cj ρ g (cj ρ g⁻¹ f) := by rw [← cj_mul]; simp [cj_one]
  rw [e1, ← map_mul, ← map_mul, hz.2 _ hf']

theorem exists_inv_compl (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) (hodd : Odd (Nat.card M))
    (U : Submodule (ZMod 2) V) (hU : ∀ m ∈ M, ∀ u ∈ U, ρ m u ∈ U) :
    ∃ C : Submodule (ZMod 2) V, IsCompl U C ∧ ∀ m ∈ M, ∀ u ∈ C, ρ m u ∈ C := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (by
    intro h; rw [h] at hodd; exact absurd hodd (by decide))
  haveI : Fintype M := Fintype.ofFinite M
  obtain ⟨π₀, hπ₀⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (by simp)
  let X : Module.End (ZMod 2) V := U.subtype ∘ₗ π₀
  let P : Module.End (ZMod 2) V := ∑ m : M, er ρ m * X * er ρ (m : G)⁻¹
  have hXU : ∀ v, X v ∈ U := fun v => (π₀ v).2
  have hXu : ∀ u ∈ U, X u = u := fun u hu => by
    have := congrArg Subtype.val (LinearMap.congr_fun hπ₀ ⟨u, hu⟩)
    simpa [X] using this
  have hP1 : ∀ v, P v ∈ U := by
    intro v
    simp only [P, LinearMap.sum_apply, Module.End.mul_apply]
    exact U.sum_mem fun m _ => hU m m.2 _ (hXU _)
  have hP2 : ∀ u ∈ U, P u = u := by
    intro u hu
    simp only [P, LinearMap.sum_apply, Module.End.mul_apply]
    have : ∀ m : M, er ρ m (X (er ρ (m : G)⁻¹ u)) = u := by
      intro m
      have hm : er ρ (m : G)⁻¹ u ∈ U := hU _ (M.inv_mem m.2) u hu
      rw [hXu _ hm]
      have := congrArg (fun y => y u) (er_mul_inv_cancel_left ρ (m : G) 1)
      simpa using this
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      ZMod.natCast_eq_one_iff_odd.mpr hodd, one_smul]
  have hP3 : ∀ g ∈ M, er ρ g * P = P * er ρ g := by
    intro g hg
    simp only [P, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : M)) _ _ ?_
    intro m
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, mul_assoc, map_inv, mul_inv_rev]
    have h1 : er ρ g⁻¹ * er ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [h1, mul_one]
  let f : V →ₗ[ZMod 2] U := P.codRestrict U hP1
  have hf : ∀ x : U, f x = x := fun x => Subtype.ext (hP2 x x.2)
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf, ?_⟩
  intro m hm u hu
  have hPu : P u = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
  have hcomm : P (ρ m u) = ρ m (P u) := congrArg (fun y => y u) (hP3 m hm).symm
  refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
  show P (ρ m u) = 0
  rw [hcomm, hPu, map_zero]

@[expose] noncomputable def proj {K R : Submodule (ZMod 2) V} (h : IsCompl K R) :
    Module.End (ZMod 2) V :=
  K.subtype ∘ₗ K.linearProjOfIsCompl R h

theorem proj_mem {K R : Submodule (ZMod 2) V} (h : IsCompl K R) (v : V) : proj h v ∈ K :=
  (K.linearProjOfIsCompl R h v).2

theorem proj_left {K R : Submodule (ZMod 2) V} (h : IsCompl K R) {x : V} (hx : x ∈ K) :
    proj h x = x := by
  have := Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem proj_right {K R : Submodule (ZMod 2) V} (h : IsCompl K R) {x : V} (hx : x ∈ R) :
    proj h x = 0 := by
  have := Submodule.linearProjOfIsCompl_apply_right h ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem proj_idem {K R : Submodule (ZMod 2) V} (h : IsCompl K R) : proj h * proj h = proj h := by
  ext v
  exact proj_left h (proj_mem h v)

theorem exists_add {K R : Submodule (ZMod 2) V} (h : IsCompl K R) (v : V) :
    ∃ k ∈ K, ∃ r ∈ R, k + r = v := by
  have : v ∈ K ⊔ R := by rw [h.sup_eq_top]; trivial
  exact Submodule.mem_sup.mp this

theorem proj_comm {K R : Submodule (ZMod 2) V} (h : IsCompl K R) (f : Module.End (ZMod 2) V)
    (hK : ∀ k ∈ K, f k ∈ K) (hR : ∀ r ∈ R, f r ∈ R) : f * proj h = proj h * f := by
  ext v
  obtain ⟨k, hk, r, hr, rfl⟩ := exists_add h v
  simp only [Module.End.mul_apply, map_add, proj_left h hk, proj_right h hr, add_zero,
    proj_left h (hK k hk), proj_right h (hR r hr), map_zero]

theorem mem_of_proj_eq_zero {K R : Submodule (ZMod 2) V} (h : IsCompl K R) {w : V}
    (hw : proj h w = 0) : w ∈ R := by
  obtain ⟨k, hk, r, hr, rfl⟩ := exists_add h w
  rw [map_add, proj_left h hk, proj_right h hr, add_zero] at hw
  rw [hw, zero_add]; exact hr

theorem eq_zero_of_nilpotent (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G)
    (hodd : Odd (Nat.card M)) {z : Module.End (ZMod 2) V} (hz : z ∈ cz ρ M) (hn : IsNilpotent z) :
    z = 0 := by
  obtain ⟨hzc, hzz⟩ := (mem_cz ρ M z).mp hz
  have hzc' := (mem_comm ρ M z).mp hzc
  have hKinv : ∀ m ∈ M, ∀ u ∈ LinearMap.ker z, ρ m u ∈ LinearMap.ker z := by
    intro m hm u hu
    rw [LinearMap.mem_ker] at hu ⊢
    have := congrArg (fun y => y u) (hzc' m hm)
    simp only [Module.End.mul_apply, hu, map_zero] at this
    exact this.symm
  obtain ⟨C, hC, hCinv⟩ := exists_inv_compl ρ M hodd (LinearMap.ker z) hKinv
  have hpcomm : proj hC ∈ comm ρ M := by
    rw [mem_comm]
    intro m hm
    exact proj_comm hC (er ρ m) (hKinv m hm) (hCinv m hm)
  have hpz : proj hC * z = z * proj hC := hzz _ hpcomm
  have hzC : ∀ v, z v ∈ C := by
    intro v
    apply mem_of_proj_eq_zero hC
    have hz0 : z (proj hC v) = 0 := LinearMap.mem_ker.mp (proj_mem hC v)
    have := congrArg (fun y => y v) hpz
    simp only [Module.End.mul_apply, hz0] at this
    exact this
  have key : ∀ k : ℕ, z ^ (k + 2) = 0 → z ^ (k + 1) = 0 := by
    intro k hk
    ext v
    have hw : (z ^ (k + 1)) v ∈ C := by
      rw [pow_succ', Module.End.mul_apply]; exact hzC _
    have hw0 : z ((z ^ (k + 1)) v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ', hk]; rfl
    have hmem : (z ^ (k + 1)) v ∈ LinearMap.ker z ⊓ C :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hw0, hw⟩
    rw [hC.disjoint.eq_bot] at hmem
    simpa using hmem
  have hall : ∀ n : ℕ, z ^ (n + 1) = 0 → z = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact fun h => ih (key n h)
  obtain ⟨n, hn⟩ := hn
  cases n with
  | zero =>
    have h1 : (1 : Module.End (ZMod 2) V) = 0 := by simpa using hn
    calc z = z * 1 := (mul_one z).symm
      _ = 0 := by rw [h1, mul_zero]
  | succ n => exact hall n hn

@[expose] def Simple (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) : Prop :=
  ∀ z ∈ cz ρ M, z * z = z → z = 0 ∨ z = 1

@[expose] def InjZ (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) : Prop :=
  ∀ z ∈ cz ρ M, z ≠ 0 → Function.Injective z

theorem preserve_of_comm (z f : Module.End (ZMod 2) V) (hf : f * z = z * f) (n : ℕ) :
    (∀ k ∈ LinearMap.ker (z ^ n), f k ∈ LinearMap.ker (z ^ n)) ∧
      (∀ r ∈ LinearMap.range (z ^ n), f r ∈ LinearMap.range (z ^ n)) := by
  have h : f * z ^ n = z ^ n * f := (Commute.pow_right (show Commute f z from hf) n).eq
  refine ⟨fun k hk => ?_, fun r hr => ?_⟩
  · rw [LinearMap.mem_ker] at hk ⊢
    have := congrArg (fun y => y k) h
    simp only [Module.End.mul_apply, hk, map_zero] at this
    exact this.symm
  · obtain ⟨w, rfl⟩ := hr
    exact ⟨f w, by simpa using (congrArg (fun y => y w) h).symm⟩

theorem injZ_of_simple (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) (hodd : Odd (Nat.card M))
    (hs : Simple ρ M) : InjZ ρ M := by
  intro z hz hz0
  obtain ⟨hzc, hzz⟩ := (mem_cz ρ M z).mp hz
  have hzc' := (mem_comm ρ M z).mp hzc
  obtain ⟨n, hn, hn1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow z).and
    (Filter.eventually_ge_atTop 1)).exists
  have hpc : proj hn ∈ cz ρ M := by
    rw [mem_cz]
    refine ⟨?_, fun f hf => ?_⟩
    · rw [mem_comm]
      intro m hm
      have := preserve_of_comm z (er ρ m) (hzc' m hm) n
      exact proj_comm hn _ this.1 this.2
    · have := preserve_of_comm z f (hzz f hf) n
      exact proj_comm hn _ this.1 this.2
  rcases hs _ hpc (proj_idem hn) with h0 | h1
  · have hker : LinearMap.ker (z ^ n) = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      have := proj_left hn hk
      rw [h0] at this
      simpa using this.symm
    intro v w hvw
    have hzz0 : z (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have : v - w ∈ LinearMap.ker (z ^ n) := by
      rw [LinearMap.mem_ker]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
      rw [pow_succ, Module.End.mul_apply, hzz0, map_zero]
    rw [hker] at this
    exact sub_eq_zero.mp (by simpa using this)
  · exfalso
    have hrange : LinearMap.range (z ^ n) = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      have := proj_right hn hr
      rw [h1] at this
      simpa using this
    have hzn : z ^ n = 0 := by
      ext v
      have : (z ^ n) v ∈ LinearMap.range (z ^ n) := ⟨v, rfl⟩
      rw [hrange] at this
      simpa using this
    exact hz0 (eq_zero_of_nilpotent ρ M hodd hz ⟨n, hzn⟩)

theorem simple_of_irreducible (ρ : G →* (V ≃ₗ[ZMod 2] V))
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g : G, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    Simple ρ ⊤ := by
  intro z hz hzz
  have hzc := (mem_comm ρ ⊤ z).mp ((mem_cz ρ ⊤ z).mp hz).1
  rcases hirr (LinearMap.range z) (by
      rintro g _ ⟨w, rfl⟩
      refine ⟨ρ g w, ?_⟩
      have := congrArg (fun y => y w) (hzc g trivial)
      simp only [Module.End.mul_apply] at this
      exact this.symm) with h | h
  · exact Or.inl (LinearMap.range_eq_bot.mp h)
  · refine Or.inr ?_
    ext v
    obtain ⟨w, rfl⟩ : v ∈ LinearMap.range z := by rw [h]; trivial
    have := congrArg (fun y => y w) hzz
    simpa using this

theorem isField_cz (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) [Nontrivial V]
    (hinj : InjZ ρ M) : IsField (cz ρ M) := by
  have : Finite (Module.End (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => Subtype.ext ?_, fun {a} ha => ?_⟩
  · show (a : Module.End (ZMod 2) V) * b = b * a
    exact (((mem_cz ρ M _).mp a.2).2 b (((mem_cz ρ M _).mp b.2).1)).symm
  · have ha0 : (a : Module.End (ZMod 2) V) ≠ 0 := fun h => ha (Subtype.ext h)
    have hai := hinj a a.2 ha0
    have hunit : IsUnit (a : Module.End (ZMod 2) V) :=
      (LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot.mpr hai)
    obtain ⟨u, hu⟩ := hunit
    have : Finite (Module.End (ZMod 2) V)ˣ := Finite.of_injective _ Units.val_injective
    have hpos := orderOf_pos u
    have hpow : (a : Module.End (ZMod 2) V) ^ orderOf u = 1 := by
      rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    refine ⟨⟨(a : Module.End (ZMod 2) V) ^ (orderOf u - 1), Subalgebra.pow_mem _ a.2 _⟩,
      Subtype.ext ?_⟩
    show (a : Module.End (ZMod 2) V) * (a : Module.End (ZMod 2) V) ^ (orderOf u - 1) = 1
    rw [← pow_succ', Nat.sub_add_cancel hpos, hpow]

theorem er_mem_cz (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G)
    (hab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) {g : G} (hg : g ∈ M) : er ρ g ∈ cz ρ M := by
  rw [mem_cz]
  refine ⟨(mem_comm ρ M _).mpr fun m hm => ?_, fun f hf => ?_⟩
  · rw [← map_mul, ← map_mul, hab m hm g hg]
  · exact ((mem_comm ρ M f).mp hf g hg).symm

theorem isCyclic_of_injZ (ρ : G →* (V ≃ₗ[ZMod 2] V)) [Finite G] [Nontrivial V]
    (hinj : InjZ ρ ⊤) (hρ : Function.Injective ρ) (hab : ∀ a b : G, a * b = b * a) :
    IsCyclic G := by
  letI : Field (cz ρ ⊤) := (isField_cz ρ ⊤ hinj).toField
  let f : G →* cz ρ ⊤ :=
    { toFun := fun g => ⟨er ρ g, er_mem_cz ρ ⊤ (fun a _ b _ => hab a b) (Subgroup.mem_top g)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  refine isCyclic_of_injective_ringHom f ?_
  intro a b hab'
  apply hρ
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun y : cz ρ ⊤ => (y : Module.End (ZMod 2) V) v) hab'
  exact this

end Hom

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
