module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cASimple

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex

section Trivial

variable {F L : Type} [Field F] [Field L] [Algebra F L]

theorem funRep_eq_of_mem_zero {f : (Fin 2 → F) → L} (hf : f ∈ steinbergSub F L 0) (g : SLm F) :
    funRep F L g f = f := by
  obtain ⟨c, hc⟩ := isHomPoly_of_mem hf
  funext v
  rw [funRep_apply, hc, hc]
  simp

theorem steinbergRep_trivial_zero (g : SLm F) (z : steinbergSub F L 0) :
    steinbergRep F L 0 g z = z :=
  Subtype.ext (funRep_eq_of_mem_zero z.2 g)

theorem steinbergRep_sl2D_yVec {A : ℕ} (t : Fˣ) :
    steinbergRep F L A (sl2D t) (yVec F L A) = (algebraMap F L (t : F)) ^ A • yVec F L A :=
  Subtype.ext (funRep_sl2D_y t A)

theorem steinbergRep_ne_self {A : ℕ} (hA : A ≠ 0) (hA1 : (-1 : F) ^ A = 1) :
    steinbergRep F L A (sl2U 1) (xVec F L A) ≠ xVec F L A := by
  intro h
  have h1 := congrFun (congrArg Subtype.val h) ![0, 1]
  have h2 : (-1 : L) ^ A = 1 := by
    have := congrArg (algebraMap F L) hA1
    simpa using this
  simp [steinbergRep_val, xVec, funRep_sl2U, monoFun, hA, h2] at h1

theorem trivial_transfer {A A' : ℕ} (Ψ : steinbergSub F L A ≃ₗ[L] steinbergSub F L A')
    (hΨ : ∀ (g : SLm F) (z : steinbergSub F L A),
      Ψ (steinbergRep F L A g z) = steinbergRep F L A' g (Ψ z))
    (h : ∀ (g : SLm F) (z : steinbergSub F L A), steinbergRep F L A g z = z) :
    ∀ (g : SLm F) (z : steinbergSub F L A'), steinbergRep F L A' g z = z := by
  intro g z'
  obtain ⟨z, rfl⟩ := Ψ.surjective z'
  rw [← hΨ, h]

theorem equivariant_symm {A A' : ℕ} (Ψ : steinbergSub F L A ≃ₗ[L] steinbergSub F L A')
    (hΨ : ∀ (g : SLm F) (z : steinbergSub F L A),
      Ψ (steinbergRep F L A g z) = steinbergRep F L A' g (Ψ z)) (g : SLm F)
    (z : steinbergSub F L A') :
    Ψ.symm (steinbergRep F L A' g z) = steinbergRep F L A g (Ψ.symm z) := by
  rw [LinearEquiv.symm_apply_eq, hΨ, LinearEquiv.apply_symm_apply]

theorem exists_equivariant_of_iso {A A' : ℕ}
    (ψ : (steinbergRep F L A).asModule ≃ₗ[MonoidAlgebra L (SLm F)] (steinbergRep F L A').asModule) :
    ∃ Ψ : steinbergSub F L A ≃ₗ[L] steinbergSub F L A', ∀ (g : SLm F) (z : steinbergSub F L A),
      Ψ (steinbergRep F L A g z) = steinbergRep F L A' g (Ψ z) := by
  let ρ := steinbergRep F L A
  let ρ' := steinbergRep F L A'
  let e : ρ.asModule ≃ₗ[L] steinbergSub F L A := ρ.asModuleEquiv
  let e' : ρ'.asModule ≃ₗ[L] steinbergSub F L A' := ρ'.asModuleEquiv
  refine ⟨e.symm.trans ((ψ.restrictScalars L).trans e'), fun g z => ?_⟩
  show e' (ψ (e.symm (ρ g z))) = ρ' g (e' (ψ (e.symm z)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]

end Trivial

section Weights

variable {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]

theorem iso_yVec {A A' : ℕ} (hA' : A' < Nat.card F) (Ψ : steinbergSub F L A ≃ₗ[L] steinbergSub F L A')
    (hΨ : ∀ (g : SLm F) (z : steinbergSub F L A),
      Ψ (steinbergRep F L A g z) = steinbergRep F L A' g (Ψ z)) :
    ∃ c : L, c ≠ 0 ∧ Ψ (yVec F L A) = c • yVec F L A' := by
  have hfix : ∀ b : F, steinbergRep F L A' (sl2U b) (Ψ (yVec F L A)) = Ψ (yVec F L A) := by
    intro b
    rw [← hΨ, steinbergRep_sl2U_yVec]
  obtain ⟨c, hc⟩ := fixed_eq_smul hA' hfix
  refine ⟨c, ?_, hc⟩
  rintro rfl
  rw [zero_smul] at hc
  exact yVec_ne_zero (Ψ.injective (by rw [hc, map_zero]))

theorem units_pow_eq {A A' : ℕ} (hA' : A' < Nat.card F) (Ψ : steinbergSub F L A ≃ₗ[L] steinbergSub F L A')
    (hΨ : ∀ (g : SLm F) (z : steinbergSub F L A),
      Ψ (steinbergRep F L A g z) = steinbergRep F L A' g (Ψ z)) (t : Fˣ) :
    t ^ A = t ^ A' := by
  obtain ⟨c, hc0, hc⟩ := iso_yVec hA' Ψ hΨ
  have h1 := hΨ (sl2D t) (yVec F L A)
  rw [steinbergRep_sl2D_yVec, map_smul, hc, map_smul, steinbergRep_sl2D_yVec, smul_smul,
    smul_smul] at h1
  have h2 := smul_left_injective L (yVec_ne_zero (F := F) (L := L) (A := A')) h1
  have h3 : (algebraMap F L (t : F)) ^ A * c = (algebraMap F L (t : F)) ^ A' * c := by
    rw [h2, mul_comm]
  have h4 := mul_right_cancel₀ hc0 h3
  apply Units.ext
  apply (algebraMap F L).injective
  simpa using h4

theorem modEq_of_iso {A A' : ℕ} (hA' : A' < Nat.card F) (Ψ : steinbergSub F L A ≃ₗ[L] steinbergSub F L A')
    (hΨ : ∀ (g : SLm F) (z : steinbergSub F L A),
      Ψ (steinbergRep F L A g z) = steinbergRep F L A' g (Ψ z)) :
    A ≡ A' [MOD Nat.card F - 1] := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g₀ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, Nat.card_units]
  rw [← hord]
  exact pow_eq_pow_iff_modEq.mp (units_pow_eq hA' Ψ hΨ g₀)

end Weights

section Main

theorem steinberg_inj_holds : SteinbergInjStmt := by
  intro p n F L _ _ _ _ hp hp2 hF A A' hA hA' ⟨ψ⟩
  have hA1 : A < Nat.card F := hF ▸ hA
  have hA1' : A' < Nat.card F := hF ▸ hA'
  obtain ⟨Ψ, hΨ⟩ := exists_equivariant_of_iso ψ
  have hmod := modEq_of_iso hA1' Ψ hΨ
  by_contra hne
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hneg : (-1 : F) ^ (Nat.card F - 1) = 1 := by
    classical
    have := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one (-1 : F) (neg_ne_zero.mpr one_ne_zero)
    rwa [← Nat.card_eq_fintype_card] at h1
  have hcase : (A = 0 ∧ A' = Nat.card F - 1) ∨ (A = Nat.card F - 1 ∧ A' = 0) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd : Nat.card F - 1 ∣ A' - A := (Nat.modEq_iff_dvd' hlt.le).mp hmod
      have hpos : 0 < A' - A := Nat.sub_pos_of_lt hlt
      have := Nat.le_of_dvd hpos hd
      left
      omega
    · have hd : Nat.card F - 1 ∣ A - A' := (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm
      have hpos : 0 < A - A' := Nat.sub_pos_of_lt hgt
      have := Nat.le_of_dvd hpos hd
      right
      omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have htriv := trivial_transfer Ψ hΨ (fun g z => steinbergRep_trivial_zero g z)
    exact steinbergRep_ne_self (A := Nat.card F - 1) (by omega) hneg (htriv _ _)
  · have htriv := trivial_transfer Ψ.symm (equivariant_symm Ψ hΨ)
      (fun g z => steinbergRep_trivial_zero g z)
    exact steinbergRep_ne_self (A := Nat.card F - 1) (by omega) hneg (htriv _ _)

end Main

end CFSG.GH74.GLS.Stage4.Rest
