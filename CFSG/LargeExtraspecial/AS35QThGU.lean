module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.LargeExtraspecial.AS35QThCoordA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

@[expose] noncomputable def detGU : GU3 →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp GU3.subtype

theorem card_SUid_three : Nat.card (SUid frob 3) = 216 := by
  obtain ⟨P, hP⟩ := exists_wittMatrix (p := 2) (f := 1) card_K 3
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv, CFSG.LieType.Steinberg.card_SU_three card_K]
  norm_num

theorem card_units_K : Nat.card Kˣ = 3 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, card_K]
  norm_num

theorem card_ker_detGU_le : Nat.card detGU.ker ≤ 216 := by
  rw [← card_SUid_three]
  refine Nat.card_le_card_of_injective
    (fun A => ⟨(A : GU3), ?_⟩) (fun A B h => ?_)
  · have h1 : detGU (A : GU3) = 1 := A.2
    refine mem_SUid.mpr ⟨?_, mem_GU3.1 (A : GU3).2⟩
    exact congrArg Units.val h1
  · have h' := congrArg (fun x : SUid frob 3 => (x : GL (Fin 3) K)) h
    exact Subtype.ext (Subtype.ext h')

theorem card_GU3_le : Nat.card GU3 ≤ 648 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup detGU.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange detGU).toEquiv]
  have h1 : Nat.card detGU.range ≤ 3 := (Subgroup.card_le_card_group _).trans card_units_K.le
  have h2 := card_ker_detGU_le
  calc Nat.card detGU.range * Nat.card detGU.ker ≤ 3 * 216 := Nat.mul_le_mul h1 h2
    _ = 648 := by norm_num

theorem eq_zero_of_tr2 {c : K} (h1 : tr2 c = 0) (h2 : tr2 (ω * c) = 0) : c = 0 := by
  rcases K_cases c with rfl | rfl | rfl | rfl
  · rfl
  · rw [mul_one, tr2_omega] at h2; exact absurd h2 (by decide)
  · rw [tr2_omega] at h1; exact absurd h1 (by decide)
  · rw [tr2_frob_omega] at h1; exact absurd h1 (by decide)

theorem eq_of_tr2 {c d : K} (h1 : tr2 c = tr2 d) (h2 : tr2 (ω * c) = tr2 (ω * d)) : c = d := by
  have e : c + d = 0 := eq_zero_of_tr2 (by rw [tr2_add, h1, zmod2_add_self])
    (by rw [mul_add, tr2_add, h2, zmod2_add_self])
  rw [← neg_K d]
  exact eq_neg_of_add_eq_zero_left e

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {ζ : V →ₗ[ZMod 2] V} {l : (Fin 3 → K) → V}

structure HermCoords (q : QuadraticForm (ZMod 2) V) (ζ : V →ₗ[ZMod 2] V)
    (l : (Fin 3 → K) → V) : Prop where
  add : ∀ x y, l (x + y) = l x + l y
  bij : Function.Bijective l
  omega : ∀ x, l (ω • x) = ζ (l x)
  polar : ∀ x y, polar q (l x) (l y) = tr2 (herm frob x y)

namespace HermCoords

variable (hl : HermCoords q ζ l)
include hl

@[expose] noncomputable def inv (v : V) : Fin 3 → K := (Equiv.ofBijective l hl.bij).symm v

theorem l_inv (v : V) : l (hl.inv v) = v := (Equiv.ofBijective l hl.bij).apply_symm_apply v

theorem inv_l (x : Fin 3 → K) : hl.inv (l x) = x := (Equiv.ofBijective l hl.bij).symm_apply_apply x

theorem inv_add (u v : V) : hl.inv (u + v) = hl.inv u + hl.inv v := by
  apply hl.bij.1
  rw [hl.l_inv, hl.add, hl.l_inv, hl.l_inv]

theorem l_zero : l 0 = 0 := by
  have h := hl.add 0 0
  rw [add_zero] at h
  exact (left_eq_add.mp h)

theorem l_frob_omega (x : Fin 3 → K) : l (frob ω • x) = ζ (l x) + l x := by
  rw [frob_omega, add_smul, one_smul, hl.add, hl.omega]

@[expose] noncomputable def fK (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v)) :
    (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun x := hl.inv (σ (l x))
  map_add' x y := by rw [hl.add, map_add, hl.inv_add]
  map_smul' c x := by
    have hω : ∀ x, hl.inv (σ (l (ω • x))) = ω • hl.inv (σ (l x)) := by
      intro x
      apply hl.bij.1
      rw [hl.l_inv, hl.omega, hl.omega, hl.l_inv, hσ]
    have hadd : ∀ x y, hl.inv (σ (l (x + y))) = hl.inv (σ (l x)) + hl.inv (σ (l y)) := by
      intro x y
      rw [hl.add, map_add, hl.inv_add]
    simp only [RingHom.id_apply]
    rcases K_cases c with rfl | rfl | rfl | rfl
    · rw [zero_smul, zero_smul, hl.l_zero, map_zero]
      apply hl.bij.1
      rw [hl.l_inv, hl.l_zero]
    · rw [one_smul, one_smul]
    · exact hω x
    · rw [frob_omega, add_smul, one_smul, hadd, hω, add_smul, one_smul]

theorem fK_apply (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v)) (x : Fin 3 → K) :
    hl.fK σ hσ x = hl.inv (σ (l x)) := rfl

@[expose] noncomputable def thetaMat (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v)) :
    Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrix' (hl.fK σ hσ)

theorem l_thetaMat_mulVec (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v)) (x : Fin 3 → K) :
    l (hl.thetaMat σ hσ *ᵥ x) = σ (l x) := by
  rw [thetaMat, LinearMap.toMatrix'_mulVec, fK_apply, hl.l_inv]

theorem herm_thetaMat (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v))
    (hq : ∀ v, q (σ v) = q v) (x y : Fin 3 → K) :
    herm frob (hl.thetaMat σ hσ *ᵥ x) (hl.thetaMat σ hσ *ᵥ y) = herm frob x y := by
  refine eq_of_tr2 ?_ ?_
  · rw [← hl.polar, ← hl.polar, hl.l_thetaMat_mulVec, hl.l_thetaMat_mulVec,
      polar_map_map q hq]
  · rw [← herm_smul_right, ← herm_smul_right, ← Matrix.mulVec_smul, ← hl.polar, ← hl.polar,
      hl.l_thetaMat_mulVec, hl.l_thetaMat_mulVec, polar_map_map q hq]

theorem conjTr_thetaMat (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v))
    (hq : ∀ v, q (σ v) = q v) :
    conjTr frob (hl.thetaMat σ hσ) * hl.thetaMat σ hσ = 1 :=
  conjTr_mul_self_of_isometry frob (hl.herm_thetaMat σ hσ hq)

theorem thetaMat_injective {σ τ : V →ₗ[ZMod 2] V} (hσ : ∀ v, σ (ζ v) = ζ (σ v))
    (hτ : ∀ v, τ (ζ v) = ζ (τ v)) (h : hl.thetaMat σ hσ = hl.thetaMat τ hτ) : σ = τ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := hl.bij.2 v
  rw [← hl.l_thetaMat_mulVec σ hσ, h, hl.l_thetaMat_mulVec]

end HermCoords

end CFSG.LargeExtraspecial.AS35QTh
