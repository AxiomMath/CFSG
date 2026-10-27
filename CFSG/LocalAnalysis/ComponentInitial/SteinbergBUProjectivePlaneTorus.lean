module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {K : Type*} [Field K] {p : ℕ}

@[expose] def torusHom (P : GL (Fin p) K) : (Fin p → Kˣ) →* ProjGenLinGroup (Fin p) K :=
  mk.comp ((MulAut.conj P).toMonoidHom.comp TauCeti.diagGL)

theorem torusHom_apply (P : GL (Fin p) K) (x : Fin p → Kˣ) :
    torusHom P x = mk (P * TauCeti.diagGL x * P⁻¹) :=
  rfl

theorem diagGL_eq_scalar_iff (x : Fin p → Kˣ) (u : Kˣ) :
    TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) u ↔ ∀ i, x i = u := by
  constructor
  · intro h i
    have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K) i i) h
    simp only [TauCeti.diagGL_coe, diagonal_apply_eq, GeneralLinearGroup.coe_scalar,
      scalar_apply] at h1
    exact Units.ext h1
  · intro h
    rw [show x = fun _ => u from funext h, TauCeti.diagGL_const]

theorem torusHom_eq_one_iff [NeZero p] (P : GL (Fin p) K) (x : Fin p → Kˣ) :
    torusHom P x = 1 ↔ ∀ i j, x i = x j := by
  rw [torusHom_apply, mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, hu⟩ i j
    have h : TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) u := by
      have hc := (Subgroup.mem_center_iff.1 (by
        rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩ :
          GeneralLinearGroup.scalar (Fin p) u ∈ Subgroup.center (GL (Fin p) K)) P).symm
      calc TauCeti.diagGL x = P⁻¹ * (P * TauCeti.diagGL x * P⁻¹) * P := by group
        _ = GeneralLinearGroup.scalar (Fin p) u := by rw [← hu, mul_assoc, hc, inv_mul_cancel_left]
    have hx := (diagGL_eq_scalar_iff x u).1 h
    rw [hx i, hx j]
  · intro h
    refine ⟨x 0, ?_⟩
    rw [show TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) (x 0) from
      (diagGL_eq_scalar_iff x (x 0)).2 fun i => h i 0]
    have hc := (Subgroup.mem_center_iff.1 (by
      rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨x 0, rfl⟩ :
        GeneralLinearGroup.scalar (Fin p) (x 0) ∈ Subgroup.center (GL (Fin p) K)) P)
    rw [hc]
    group

@[expose] def powEqSubgroup (p : ℕ) (K : Type*) [Field K] : Subgroup (Fin p → Kˣ) where
  carrier := {x | ∀ i j, x i ^ p = x j ^ p}
  mul_mem' {x y} hx hy i j := by
    simp only [Pi.mul_apply, mul_pow, hx i j, hy i j]
  one_mem' i j := by simp
  inv_mem' {x} hx i j := by
    simp only [Pi.inv_apply, inv_pow, hx i j]

theorem mem_powEqSubgroup {x : Fin p → Kˣ} : x ∈ powEqSubgroup p K ↔ ∀ i j, x i ^ p = x j ^ p :=
  Iff.rfl

@[expose] def omegaTorus (P : GL (Fin p) K) : Subgroup (ProjGenLinGroup (Fin p) K) :=
  (powEqSubgroup p K).map (torusHom P)

theorem mem_omegaTorus {P : GL (Fin p) K} {y : ProjGenLinGroup (Fin p) K} :
    y ∈ omegaTorus P ↔ ∃ x ∈ powEqSubgroup p K, torusHom P x = y :=
  Subgroup.mem_map

theorem torusHom_mem_omegaTorus (P : GL (Fin p) K) {x : Fin p → Kˣ}
    (hx : x ∈ powEqSubgroup p K) : torusHom P x ∈ omegaTorus P :=
  mem_omegaTorus.2 ⟨x, hx, rfl⟩

theorem torusHom_comm (P : GL (Fin p) K) (x y : Fin p → Kˣ) :
    torusHom P x * torusHom P y = torusHom P y * torusHom P x := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem omegaTorus_comm (P : GL (Fin p) K) :
    ∀ x ∈ omegaTorus P, ∀ y ∈ omegaTorus P, x * y = y * x := by
  intro _ hx _ hy
  obtain ⟨x, -, rfl⟩ := mem_omegaTorus.1 hx
  obtain ⟨y, -, rfl⟩ := mem_omegaTorus.1 hy
  exact torusHom_comm P x y

theorem omegaTorus_pow [NeZero p] (P : GL (Fin p) K) : ∀ x ∈ omegaTorus P, x ^ p = 1 := by
  intro _ hy
  obtain ⟨x, hx, rfl⟩ := mem_omegaTorus.1 hy
  rw [← map_pow, torusHom_eq_one_iff]
  exact fun i j => hx i j

theorem mem_omegaTorus_of_pow [NeZero p] (P : GL (Fin p) K) {x : Fin p → Kˣ}
    (hx : torusHom P x ^ p = 1) : torusHom P x ∈ omegaTorus P := by
  rw [← map_pow, torusHom_eq_one_iff] at hx
  exact torusHom_mem_omegaTorus P fun i j => hx i j

@[expose] def rootTorusHom (P : GL (Fin p) K) :
    (Fin p → rootsOfUnity p K) →* ProjGenLinGroup (Fin p) K :=
  (torusHom P).comp (MonoidHom.compLeft (rootsOfUnity p K).subtype (Fin p))

theorem rootTorusHom_apply (P : GL (Fin p) K) (f : Fin p → rootsOfUnity p K) :
    rootTorusHom P f = torusHom P fun i => (f i : Kˣ) :=
  rfl

theorem range_rootTorusHom [NeZero p] (P : GL (Fin p) K) :
    (rootTorusHom P).range = omegaTorus P := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [rootTorusHom_apply]
    refine torusHom_mem_omegaTorus P fun i j => ?_
    rw [(mem_rootsOfUnity _ _).1 (f i).2, (mem_rootsOfUnity _ _).1 (f j).2]
  · intro _ hy
    obtain ⟨x, hx, rfl⟩ := mem_omegaTorus.1 hy
    have hf : ∀ i, x i * (x 0)⁻¹ ∈ rootsOfUnity p K := fun i => by
      rw [mem_rootsOfUnity, mul_pow, inv_pow, hx i 0, mul_inv_cancel]
    refine ⟨fun i => ⟨_, hf i⟩, ?_⟩
    have hfx : (fun i => ((⟨_, hf i⟩ : rootsOfUnity p K) : Kˣ)) = x * fun _ => (x 0)⁻¹ := rfl
    rw [rootTorusHom_apply, hfx, map_mul,
      (torusHom_eq_one_iff P (fun _ => (x 0)⁻¹)).2 fun _ _ => rfl, mul_one]

theorem ker_rootTorusHom [NeZero p] (P : GL (Fin p) K) (f : Fin p → rootsOfUnity p K) :
    f ∈ (rootTorusHom P).ker ↔ ∀ i j, f i = f j := by
  rw [MonoidHom.mem_ker, rootTorusHom_apply, torusHom_eq_one_iff]
  exact ⟨fun h i j => Subtype.ext (h i j), fun h i j => congrArg Subtype.val (h i j)⟩

theorem card_omegaTorus [NeZero p] (P : GL (Fin p) K) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Nat.card (omegaTorus P) = p ^ (p - 1) := by
  have hμ : Nat.card (rootsOfUnity p K) = p := hζ.card_rootsOfUnity
  have hker : Nat.card (rootTorusHom P).ker = Nat.card (rootsOfUnity p K) := by
    refine Nat.card_congr
      { toFun := fun f => (f : Fin p → rootsOfUnity p K) 0
        invFun := fun c => ⟨fun _ => c, (ker_rootTorusHom P _).2 fun _ _ => rfl⟩
        left_inv := fun f => Subtype.ext (funext fun i =>
          ((ker_rootTorusHom P _).1 f.2 0 i))
        right_inv := fun c => rfl }
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (rootTorusHom P).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (rootTorusHom P)).toEquiv,
    range_rootTorusHom, hker, Nat.card_fun, hμ, Nat.card_fin] at h
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have h2 : p ^ p = p ^ (p - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_right hp h).symm

@[expose] def rootProdHom (p : ℕ) (K : Type*) [Field K] :
    (Fin p → rootsOfUnity p K) →* rootsOfUnity p K where
  toFun f := ∏ i, f i
  map_one' := by simp
  map_mul' f g := by simp [Finset.prod_mul_distrib]

@[expose] def detOneTorus (P : GL (Fin p) K) : Subgroup (ProjGenLinGroup (Fin p) K) :=
  (rootProdHom p K).ker.map (rootTorusHom P)

theorem mem_detOneTorus_iff {P : GL (Fin p) K} {y : ProjGenLinGroup (Fin p) K} :
    y ∈ detOneTorus P ↔ ∃ f ∈ (rootProdHom p K).ker, rootTorusHom P f = y :=
  Subgroup.mem_map

theorem detOneTorus_le [NeZero p] (P : GL (Fin p) K) : detOneTorus P ≤ omegaTorus P := by
  rw [← range_rootTorusHom]
  intro _ hy
  obtain ⟨f, -, rfl⟩ := mem_detOneTorus_iff.1 hy
  exact ⟨f, rfl⟩

theorem mem_detOneTorus {P : GL (Fin p) K} {y : ProjGenLinGroup (Fin p) K}
    (hy : y ∈ detOneTorus P) : ∃ f : Fin p → rootsOfUnity p K,
      (∏ i, ((f i : Kˣ) : K)) = 1 ∧ y = mk (P * TauCeti.diagGL (fun i => (f i : Kˣ)) * P⁻¹) := by
  obtain ⟨f, hf, rfl⟩ := mem_detOneTorus_iff.1 hy
  refine ⟨f, ?_, rfl⟩
  have h := congrArg (fun z : rootsOfUnity p K => ((z : Kˣ) : K)) (MonoidHom.mem_ker.1 hf)
  simp only [rootProdHom, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one,
    Units.val_one] at h
  rw [← h]
  push_cast
  rfl

theorem card_detOneTorus [NeZero p] (P : GL (Fin p) K) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp2 : 2 ≤ p) : Nat.card (detOneTorus P) = p ^ (p - 2) := by
  classical
  have hμ : Nat.card (rootsOfUnity p K) = p := hζ.card_rootsOfUnity
  have hp : 0 < p := by omega
  have hsurj : Function.Surjective (rootProdHom p K) := by
    intro c
    refine ⟨Pi.mulSingle 0 c, ?_⟩
    simp [rootProdHom, Finset.prod_pi_mulSingle']
  have hprod : Nat.card (rootProdHom p K).ker = p ^ (p - 1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (rootProdHom p K).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (rootProdHom p K)).toEquiv,
      MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_fun, hμ, Nat.card_fin] at h
    have h2 : p ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hp]
    rw [h2] at h
    exact (Nat.eq_of_mul_eq_mul_left hp h).symm
  let φ := (rootTorusHom P).comp (rootProdHom p K).ker.subtype
  have hrange : φ.range = detOneTorus P := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Nat.card φ.ker = Nat.card (rootsOfUnity p K) := by
    refine Nat.card_congr
      { toFun := fun f => ((f : (rootProdHom p K).ker) : Fin p → rootsOfUnity p K) 0
        invFun := fun c => ⟨⟨fun _ => c, by
            rw [MonoidHom.mem_ker]
            apply Subtype.ext
            simp only [rootProdHom, MonoidHom.coe_mk, OneHom.coe_mk, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin, OneMemClass.coe_one]
            exact (mem_rootsOfUnity _ _).1 c.2⟩,
          by
            rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
            exact (ker_rootTorusHom P _).2 fun _ _ => rfl⟩
        left_inv := fun f => by
          refine Subtype.ext (Subtype.ext (funext fun i => ?_))
          exact (ker_rootTorusHom P _).1 f.2 0 i
        right_inv := fun c => rfl }
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker, hμ, hprod] at h
  have h2 : p ^ (p - 1) = p ^ (p - 2) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_right hp h).symm

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
