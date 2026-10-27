module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullAffine
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixRadicalLabels
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientTools

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBM

open Subgroup Matrix Module SymplecticFlag BinarySymplecticSix FusionOrbits RadicalLabels
open LinearMap (BilinForm)

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type} [Group G]

theorem card_inf_centralizer_le_sq [Finite G] {C A : Subgroup G} {z : G}
    (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (hzC : ∀ c ∈ C, z⁻¹ * c * z ∈ C)
    (hfix : ∀ c ∈ C, c * z = z * c ↔ c ∈ A)
    (hcomm : ∀ c ∈ C, z⁻¹ * c⁻¹ * z * c ∈ A) {M : Set G} (hMz : ∀ m ∈ M, m * z = z * m) :
    Nat.card ↥(C ⊓ centralizer M) ≤ Nat.card ↥(A ⊓ centralizer M) ^ 2 := by
  set D := C ⊓ centralizer M with hD
  have hmul : ∀ c d : D, z⁻¹ * ((c * d : D) : G)⁻¹ * z * ((c * d : D) : G) =
      z⁻¹ * (c : G)⁻¹ * z * c * (z⁻¹ * (d : G)⁻¹ * z * d) := by
    intro c d
    have hc := (mem_inf.1 c.2).1
    have hd := (mem_inf.1 d.2).1
    have hd' : z⁻¹ * (d : G)⁻¹ * z ∈ C := hzC _ (inv_mem hd)
    have hc' : z⁻¹ * (c : G)⁻¹ * z * c ∈ C := mul_mem (hzC _ (inv_mem hc)) hc
    calc z⁻¹ * ((c * d : D) : G)⁻¹ * z * ((c * d : D) : G) =
        (z⁻¹ * (d : G)⁻¹ * z) * (z⁻¹ * (c : G)⁻¹ * z * c) * d := by
          rw [Subgroup.coe_mul]
          group
      _ = (z⁻¹ * (c : G)⁻¹ * z * c) * (z⁻¹ * (d : G)⁻¹ * z) * d := by
          rw [hCab _ hd' _ hc']
      _ = _ := by group
  let ψ : D →* G :=
    { toFun := fun c => z⁻¹ * (c : G)⁻¹ * z * c
      map_one' := by simp
      map_mul' := hmul }
  have hψ : ∀ c : D, ψ c = z⁻¹ * (c : G)⁻¹ * z * c := fun _ => rfl
  have hrange : ψ.range ≤ A ⊓ centralizer M := by
    rintro _ ⟨c, rfl⟩
    refine mem_inf.2 ⟨hcomm _ (mem_inf.1 c.2).1, ?_⟩
    rw [mem_centralizer_iff]
    intro m hm
    have hmz : Commute m z := hMz m hm
    have hmc : Commute m (c : G) := ((mem_centralizer_iff.1 (mem_inf.1 c.2).2) m hm)
    exact (((hmz.inv_right.mul_right hmc.inv_right).mul_right hmz).mul_right hmc).eq
  have hker : ∀ c : D, ψ c = 1 → (c : G) ∈ A := by
    intro c hc
    rw [hψ] at hc
    apply (hfix _ (mem_inf.1 c.2).1).1
    have h1 : (c : G)⁻¹ * z * c = z := by
      calc (c : G)⁻¹ * z * c = z * (z⁻¹ * (c : G)⁻¹ * z * c) := by group
        _ = z := by rw [hc, mul_one]
    calc (c : G) * z = (c : G) * ((c : G)⁻¹ * z * c) := by rw [h1]
      _ = z * c := by group
  let ι : ψ.ker → ↥(A ⊓ centralizer M) := fun c =>
    ⟨((c : D) : G), mem_inf.2 ⟨hker c c.2, (mem_inf.1 (c : D).2).2⟩⟩
  have hι : Function.Injective ι := fun c d h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at hcard
  rw [hcard, pow_two]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hrange) (Nat.card_le_card_of_injective ι hι)

theorem fix_glTransThreeOne : ∀ B : ↥(binarySymMatrices 3),
    symThreeCongr glTransThreeOne B = B → (B : M₃) 1 2 = 0 ∧ (B : M₃) 2 2 = 0 := by
  decide +kernel

theorem fix_glTransTwoOne : ∀ B : ↥(binarySymMatrices 3),
    symThreeCongr glTransTwoOne B = B → (B : M₃) 1 1 = 0 ∧ (B : M₃) 1 2 = 0 := by
  decide +kernel

theorem fix_glTransThreeTwo : ∀ B : ↥(binarySymMatrices 3),
    symThreeCongr glTransThreeTwo B = B → (B : M₃) 0 2 = 0 ∧ (B : M₃) 2 2 = 0 := by
  decide +kernel

theorem eq_of_upper_eq {B B' : ↥(binarySymMatrices 3)}
    (h00 : (B : M₃) 0 0 = (B' : M₃) 0 0) (h01 : (B : M₃) 0 1 = (B' : M₃) 0 1)
    (h02 : (B : M₃) 0 2 = (B' : M₃) 0 2) (h11 : (B : M₃) 1 1 = (B' : M₃) 1 1)
    (h12 : (B : M₃) 1 2 = (B' : M₃) 1 2) (h22 : (B : M₃) 2 2 = (B' : M₃) 2 2) : B = B' := by
  have hs : ∀ (X : ↥(binarySymMatrices 3)) (i j : Fin 3), (X : M₃) j i = (X : M₃) i j :=
    fun X i j => congrFun (congrFun X.2 i) j
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h02
  · simpa [hs B 0 1, hs B' 0 1] using h01
  · exact h11
  · exact h12
  · simpa [hs B 0 2, hs B' 0 2] using h02
  · simpa [hs B 1 2, hs B' 1 2] using h12
  · exact h22

theorem card_fix_glTransThreeOne_le :
    Nat.card {B : ↥(binarySymMatrices 3) // symThreeCongr glTransThreeOne B = B} ≤ 2 ^ 4 := by
  let f : {B : ↥(binarySymMatrices 3) // symThreeCongr glTransThreeOne B = B} →
      ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 := fun B =>
    ((B.1 : M₃) 0 0, (B.1 : M₃) 0 1, (B.1 : M₃) 0 2, (B.1 : M₃) 1 1)
  have hf : Function.Injective f := by
    intro B B' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h00, h01, h02, h11⟩ := h
    obtain ⟨h12, h22⟩ := fix_glTransThreeOne B.1 B.2
    obtain ⟨h12', h22'⟩ := fix_glTransThreeOne B'.1 B'.2
    exact Subtype.ext (eq_of_upper_eq h00 h01 h02 h11 (h12.trans h12'.symm)
      (h22.trans h22'.symm))
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, Nat.card_zmod] using this

theorem card_fix_glTransTwoOne_le :
    Nat.card {B : ↥(binarySymMatrices 3) //
      symThreeCongr glTransTwoOne B = B ∧ symThreeCongr glTransThreeOne B = B} ≤ 2 ^ 3 := by
  let f : {B : ↥(binarySymMatrices 3) //
      symThreeCongr glTransTwoOne B = B ∧ symThreeCongr glTransThreeOne B = B} →
      ZMod 2 × ZMod 2 × ZMod 2 := fun B => ((B.1 : M₃) 0 0, (B.1 : M₃) 0 1, (B.1 : M₃) 0 2)
  have hf : Function.Injective f := by
    intro B B' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h00, h01, h02⟩ := h
    obtain ⟨h11, h12⟩ := fix_glTransTwoOne B.1 B.2.1
    obtain ⟨h11', h12'⟩ := fix_glTransTwoOne B'.1 B'.2.1
    obtain ⟨-, h22⟩ := fix_glTransThreeOne B.1 B.2.2
    obtain ⟨-, h22'⟩ := fix_glTransThreeOne B'.1 B'.2.2
    exact Subtype.ext (eq_of_upper_eq h00 h01 h02 (h11.trans h11'.symm) (h12.trans h12'.symm)
      (h22.trans h22'.symm))
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, Nat.card_zmod] using this

theorem card_fix_glTransThreeTwo_le :
    Nat.card {B : ↥(binarySymMatrices 3) //
      symThreeCongr glTransThreeTwo B = B ∧ symThreeCongr glTransThreeOne B = B} ≤ 2 ^ 3 := by
  let f : {B : ↥(binarySymMatrices 3) //
      symThreeCongr glTransThreeTwo B = B ∧ symThreeCongr glTransThreeOne B = B} →
      ZMod 2 × ZMod 2 × ZMod 2 := fun B => ((B.1 : M₃) 0 0, (B.1 : M₃) 0 1, (B.1 : M₃) 1 1)
  have hf : Function.Injective f := by
    intro B B' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h00, h01, h11⟩ := h
    obtain ⟨h02, h22⟩ := fix_glTransThreeTwo B.1 B.2.1
    obtain ⟨h02', h22'⟩ := fix_glTransThreeTwo B'.1 B'.2.1
    obtain ⟨h12, -⟩ := fix_glTransThreeOne B.1 B.2.2
    obtain ⟨h12', -⟩ := fix_glTransThreeOne B'.1 B'.2.2
    exact Subtype.ext (eq_of_upper_eq h00 h01 (h02.trans h02'.symm) h11 (h12.trans h12'.symm)
      (h22.trans h22'.symm))
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, Nat.card_zmod] using this

section Levi

variable {L : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e)

theorem card_tauHom_fixed_le [Finite G] {S : Set (GL (Fin 3) (ZMod 2))} {n : ℕ}
    (hS : Nat.card {B : ↥(binarySymMatrices 3) // ∀ g ∈ S, symThreeCongr g B = B} ≤ 2 ^ n) :
    Nat.card ↥(pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊓
      centralizer (leviHom φ he '' S)) ≤ 2 ^ n := by
  classical
  have key : ∀ x : ↥(pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊓
      centralizer (leviHom φ he '' S)),
      ∃ B : {B : ↥(binarySymMatrices 3) // ∀ g ∈ S, symThreeCongr g B = B},
        tauHom φ he (Multiplicative.ofAdd B.1) = x := by
    intro x
    obtain ⟨B, hB⟩ := (mem_pullSub_iff φ he).1 (mem_inf.1 x.2).1
    refine ⟨⟨Multiplicative.toAdd B, fun g hg => ?_⟩, hB⟩
    have hc := mem_centralizer_iff.1 (mem_inf.1 x.2).2 (leviHom φ he g) ⟨g, hg, rfl⟩
    apply Multiplicative.ofAdd.injective
    apply tauHom_injective φ he
    rw [← leviHom_conj_tauHom', ofAdd_toAdd, hB, hc, mul_inv_cancel_right]
  choose f hf using key
  have hinj : Function.Injective f := fun x y h => Subtype.ext (by rw [← hf x, ← hf y, h])
  exact (Nat.card_le_card_of_injective f hinj).trans hS

end Levi

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
