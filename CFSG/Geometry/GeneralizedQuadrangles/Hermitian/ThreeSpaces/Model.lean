module

public import CFSG.Geometry.ProjectiveSpaces.Counting
public import Mathlib.RingTheory.LittleWedderburn
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Veblen
public import CFSG.Geometry.ProjectiveSpaces.VeblenYoung

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.ProjectiveSpaces Module
open scoped LinearAlgebra.Projectivization

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

private theorem ncard_preimage_of_mem_isThreeBundle {β : Set (Set V)}
    (hβ : IsThreeBundle Γ c q β) :
    (Subtype.val ⁻¹' β : Set {E : Set V // IsThreespace Γ c q E}).ncard = β.ncard := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' β :
      Set {E : Set V // IsThreespace Γ c q E}) = β := by
    ext E
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hE
      exact ⟨⟨E, isThreespace_of_mem_isThreeBundle hβ hE⟩, hE, rfl⟩
  calc (Subtype.val ⁻¹' β : Set {E : Set V // IsThreespace Γ c q E}).ncard
      = (Subtype.val '' (Subtype.val ⁻¹' β :
          Set {E : Set V // IsThreespace Γ c q E})).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = β.ncard := by rw [himg]

theorem exists_projectiveSpace (hΓ : IsThasQuadrangle Γ c q) :
    ∃ G : ProjectiveSpace {E : Set V // IsThreespace Γ c q E},
      G.lines = {ℓ | ∃ β, IsThreeBundle Γ c q β ∧ ℓ = Subtype.val ⁻¹' β} ∧
        G.HasDimension 4 := by
  classical
  haveI : Finite V := Finite.of_fintype V
  haveI : Finite (Set V) := Finite.of_fintype (Set V)
  let P := {E : Set V // IsThreespace Γ c q E}
  haveI : Finite P := Subtype.finite
  let lines : Set (Set P) := {ℓ | ∃ β, IsThreeBundle Γ c q β ∧ ℓ = Subtype.val ⁻¹' β}
  have hline_ncard : ∀ ℓ ∈ lines, ℓ.ncard = q ^ 2 + 1 := by
    rintro ℓ ⟨β, hβ, rfl⟩
    exact (ncard_preimage_of_mem_isThreeBundle hβ).trans (ncard_of_isThreeBundle hΓ hβ)
  let G : ProjectiveSpace P :=
  { lines := lines
    existsUnique_line := by
      intro p r hpr
      have hpr' : (p : Set V) ≠ (r : Set V) := fun h => hpr (Subtype.ext h)
      obtain ⟨β, ⟨hβ, hpβ, hrβ⟩, huniq⟩ :=
        existsUnique_isThreeBundle (Γ := Γ) (c := c) (q := q) hΓ p.2 r.2 hpr'
      refine ⟨Subtype.val ⁻¹' β, ⟨⟨β, hβ, rfl⟩, hpβ, hrβ⟩, ?_⟩
      rintro ℓ ⟨⟨β', hβ', hℓ⟩, hp', hq'⟩
      have hpβ' : (p : Set V) ∈ β' := by rw [hℓ] at hp'; exact hp'
      have hrβ' : (r : Set V) ∈ β' := by rw [hℓ] at hq'; exact hq'
      rw [hℓ, huniq β' ⟨hβ', hpβ', hrβ'⟩]
    exists_three := by
      intro ℓ hℓ
      obtain ⟨β, hβ, rfl⟩ := hℓ
      have h3 : 2 < β.ncard := by
        rw [ncard_of_isThreeBundle hΓ hβ]
        nlinarith [hΓ.two_le]
      obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ :=
        (Set.two_lt_ncard (s := β)).mp h3
      exact ⟨⟨a, isThreespace_of_mem_isThreeBundle hβ ha⟩,
        ⟨b, isThreespace_of_mem_isThreeBundle hβ hb⟩,
        ⟨d, isThreespace_of_mem_isThreeBundle hβ hd⟩, ha, hb, hd,
        fun h => hab (congrArg Subtype.val h),
        fun h => had (congrArg Subtype.val h),
        fun h => hbd (congrArg Subtype.val h)⟩
    veblen := by
      intro a b d e hab had hae hbd hbe hde ℓ₁ hℓ₁ ℓ₂ hℓ₂ ℓ₃ hℓ₃ ℓ₄ hℓ₄
        ha₁ hb₁ hd₂ he₂ ha₃ hd₃ hb₄ he₄ hmeet
      obtain ⟨β₁, hβ₁, rℓ₁⟩ := hℓ₁
      obtain ⟨β₂, hβ₂, rℓ₂⟩ := hℓ₂
      obtain ⟨β₃, hβ₃, rℓ₃⟩ := hℓ₃
      obtain ⟨β₄, hβ₄, rℓ₄⟩ := hℓ₄
      obtain ⟨x, hx₁, hx₂⟩ := hmeet
      have hxβ₁ : (x : Set V) ∈ β₁ := by rw [rℓ₁] at hx₁; exact hx₁
      have hxβ₂ : (x : Set V) ∈ β₂ := by rw [rℓ₂] at hx₂; exact hx₂
      have haβ₁ : (a : Set V) ∈ β₁ := by rw [rℓ₁] at ha₁; exact ha₁
      have hbβ₁ : (b : Set V) ∈ β₁ := by rw [rℓ₁] at hb₁; exact hb₁
      have hdβ₂ : (d : Set V) ∈ β₂ := by rw [rℓ₂] at hd₂; exact hd₂
      have heβ₂ : (e : Set V) ∈ β₂ := by rw [rℓ₂] at he₂; exact he₂
      have hγ₁ : (a : Set V) ∈ β₃ ∧ (d : Set V) ∈ β₃ := by
        constructor
        · rw [rℓ₃] at ha₃; exact ha₃
        · rw [rℓ₃] at hd₃; exact hd₃
      have hγ₂ : (b : Set V) ∈ β₄ ∧ (e : Set V) ∈ β₄ := by
        constructor
        · rw [rℓ₄] at hb₄; exact hb₄
        · rw [rℓ₄] at he₄; exact he₄
      obtain ⟨E, hE₃, hE₄⟩ :=
        threeBundle_veblen hΓ hβ₁ hβ₂ hβ₃ hβ₄ ⟨x.1, hxβ₁, hxβ₂⟩
          haβ₁ hbβ₁ hdβ₂ heβ₂
          (fun h => had (Subtype.ext h)) (fun h => hbe (Subtype.ext h)) hγ₁ hγ₂
      refine ⟨⟨E, isThreespace_of_mem_isThreeBundle hβ₃ hE₃⟩, ?_, ?_⟩
      · rw [rℓ₃]; exact hE₃
      · rw [rℓ₄]; exact hE₄ }
  refine ⟨G, rfl, ?_⟩
  apply ProjectiveSpace.hasDimension_of_card G (s := q ^ 2) (n := 4)
  · nlinarith [hΓ.two_le]
  · intro ℓ hℓ
    exact hline_ncard ℓ hℓ
  · have hcardP : Nat.card P = q ^ 8 + q ^ 6 + q ^ 4 + q ^ 2 + 1 := by
      have h' : Nat.card P = {E : Set V | IsThreespace Γ c q E}.ncard :=
        Nat.card_coe_set_eq _
      rw [h', ncard_threespaces hΓ]
    have hsum : (∑ i ∈ Finset.range (4 + 1), (q ^ 2) ^ i) =
        q ^ 8 + q ^ 6 + q ^ 4 + q ^ 2 + 1 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
      ring
    rw [hcardP, hsum]

theorem exists_isModel_threespaces (hΓ : IsThasQuadrangle Γ c q) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K)
      (ψ : {E : Set V // IsThreespace Γ c q E} ≃ ℙ K (Fin 5 → K)),
      Fintype.card K = q ^ 2 ∧
      (∀ β, IsThreeBundle Γ c q β → ∃ W : Submodule K (Fin 5 → K), finrank K W = 2 ∧
        ψ '' (Subtype.val ⁻¹' β) = {x | x.submodule ≤ W}) ∧
      ∀ W : Submodule K (Fin 5 → K), finrank K W = 2 →
        ∃ β, IsThreeBundle Γ c q β ∧
          ψ '' (Subtype.val ⁻¹' β) = {x | x.submodule ≤ W} := by
  classical
  haveI : Finite V := Finite.of_fintype V
  haveI : Finite (Set V) := Finite.of_fintype (Set V)
  let P := {E : Set V // IsThreespace Γ c q E}
  haveI hPfin : Finite P := Subtype.finite
  obtain ⟨G, hGlines, hdim⟩ := exists_projectiveSpace (Γ := Γ) (c := c) (q := q) hΓ
  obtain ⟨D, hD, φ, hφline, hφW, hφfin⟩ :=
    G.veblen_young (n := 4) (by norm_num) hdim
  letI : DivisionRing D := hD
  obtain ⟨hDfin, hlinecardD, -⟩ := hφfin hPfin
  let K := Dᵐᵒᵖ
  let hKfin : Finite K := Finite.of_equiv D MulOpposite.opEquiv
  let hKfield : Field K := littleWedderburn K
  let hKfintype : Fintype K := Fintype.ofFinite K
  letI : Finite K := hKfin
  letI : Field K := hKfield
  letI : Fintype K := hKfintype
  let L₀ : (Fin 5 → D) ≃ₗ[K] (Fin 5 → K) :=
  { toFun := fun v i => MulOpposite.op (v i)
    invFun := fun w i => MulOpposite.unop (w i)
    left_inv := by intro v; ext i; simp
    right_inv := by intro w; ext i; simp
    map_add' := by intro v w; ext i; simp
    map_smul' := by
      intro a v
      ext i
      simp [MulOpposite.smul_eq_mul_unop, MulOpposite.op_mul] }
  let eSub : Submodule K (Fin 5 → D) ≃o Submodule K (Fin 5 → K) :=
    Submodule.orderIsoMapComap L₀
  have hfin : ∀ U, finrank K (eSub U) = finrank K U := fun U =>
    LinearEquiv.finrank_map_eq L₀ U
  let eL : {U : Submodule K (Fin 5 → D) // finrank K U = 1} ≃
      {H : Submodule K (Fin 5 → K) // finrank K H = 1} :=
  { toFun := fun U => ⟨eSub U.1, by rw [hfin U.1]; exact U.2⟩
    invFun := fun H => ⟨eSub.symm H.1, by
      rw [← hfin (eSub.symm H.1), eSub.apply_symm_apply]
      exact H.2⟩
    left_inv := fun U => Subtype.ext (eSub.symm_apply_apply U.1)
    right_inv := fun H => Subtype.ext (eSub.apply_symm_apply H.1) }
  let e := Projectivization.equivSubmodule K (Fin 5 → K)
  let ψ : P ≃ ℙ K (Fin 5 → K) := φ.trans (eL.trans e.symm)
  have hψe : ∀ p, e (ψ p) = eL (φ p) := fun p => e.apply_symm_apply (eL (φ p))
  have hline : ∀ β, IsThreeBundle Γ c q β →
      ∃ W : Submodule K (Fin 5 → K), finrank K W = 2 ∧
        ψ '' (Subtype.val ⁻¹' β) = {x | x.submodule ≤ W} := by
    intro β hβ
    have hℓmem : (Subtype.val ⁻¹' β : Set P) ∈ G.lines := by
      rw [hGlines]
      exact ⟨β, hβ, rfl⟩
    obtain ⟨W, hW, hφβ⟩ := hφline _ hℓmem
    refine ⟨eSub W, ?_, ?_⟩
    · rw [hfin W]; exact hW
    · ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hle : (φ p).1 ≤ W := by
          have hmem : φ p ∈ {U | U.1 ≤ W} := by
            rw [← hφβ]
            exact ⟨p, hp, rfl⟩
          exact hmem
        show (e (ψ p)).1 ≤ eSub W
        rw [hψe p]
        show eSub (φ p).1 ≤ eSub W
        exact eSub.le_iff_le.2 hle
      · intro hx
        let U : {H : Submodule K (Fin 5 → K) // finrank K H = 1} := e x
        have hUle : eSub.symm U.1 ≤ W := by
          apply eSub.le_iff_le.1
          rw [eSub.apply_symm_apply]
          exact hx
        have hfin' : finrank K (eSub.symm U.1) = 1 := by
          rw [← hfin (eSub.symm U.1), eSub.apply_symm_apply]
          exact U.2
        have hmem : (⟨eSub.symm U.1, hfin'⟩ :
            {H : Submodule K (Fin 5 → D) // finrank K H = 1}) ∈ {U | U.1 ≤ W} := hUle
        rw [← hφβ] at hmem
        obtain ⟨p, hp, hpe⟩ := hmem
        refine ⟨p, hp, ?_⟩
        apply e.injective
        calc e (ψ p) = eL (φ p) := hψe p
          _ = eL ⟨eSub.symm U.1, hfin'⟩ := congrArg eL hpe
          _ = U := by
              apply Subtype.ext
              rw [show (eL ⟨eSub.symm U.1, hfin'⟩).1 = eSub (eSub.symm U.1) from rfl,
                eSub.apply_symm_apply]
          _ = e x := rfl
  have hconverse : ∀ W : Submodule K (Fin 5 → K), finrank K W = 2 →
      ∃ β, β ∈ G.lines ∧ ψ '' β = {x | x.submodule ≤ W} := by
    intro W hW
    have hW' : finrank K (eSub.symm W) = 2 := by
      rw [← hfin (eSub.symm W), eSub.apply_symm_apply]
      exact hW
    obtain ⟨β, ⟨hβ, hφβ⟩, -⟩ := hφW (eSub.symm W) hW'
    refine ⟨β, hβ, ?_⟩
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hle : (φ p).1 ≤ eSub.symm W := by
        have hmem : φ p ∈ {U | U.1 ≤ eSub.symm W} := by
          rw [← hφβ]
          exact ⟨p, hp, rfl⟩
        exact hmem
      show (e (ψ p)).1 ≤ W
      rw [hψe p]
      show eSub (φ p).1 ≤ W
      rw [← eSub.apply_symm_apply W]
      exact eSub.le_iff_le.2 hle
    · intro hx
      let U : {H : Submodule K (Fin 5 → D) // finrank K H = 1} := eL.symm (e x)
      have hUle : U.1 ≤ eSub.symm W := by
        apply eSub.le_iff_le.1
        rw [eSub.apply_symm_apply]
        calc eSub U.1 = (eL U).1 := rfl
          _ = (e x).1 := congrArg Subtype.val (eL.apply_symm_apply (e x))
          _ = x.submodule := rfl
          _ ≤ W := hx
      have hmem : U ∈ {U | U.1 ≤ eSub.symm W} := hUle
      rw [← hφβ] at hmem
      obtain ⟨p, hp, hpe⟩ := hmem
      refine ⟨p, hp, ?_⟩
      apply e.injective
      calc e (ψ p) = eL (φ p) := hψe p
        _ = eL U := congrArg eL hpe
        _ = e x := eL.apply_symm_apply (e x)
  have hKcard : Fintype.card K = q ^ 2 := by
    obtain ⟨L, hL⟩ := exists_line (Γ := Γ) hΓ.gp hΓ.thick c
    let β : Set (Set V) := lineBundle Γ c L
    have hβ : IsThreeBundle Γ c q β := Or.inr ⟨L, hL, rfl⟩
    let ℓ : Set P := Subtype.val ⁻¹' β
    have hℓmem : ℓ ∈ G.lines := by
      rw [hGlines]
      exact ⟨β, hβ, rfl⟩
    have hℓncard : ℓ.ncard = q ^ 2 + 1 :=
      (ncard_preimage_of_mem_isThreeBundle hβ).trans (ncard_of_isThreeBundle hΓ hβ)
    have hℓnat : Nat.card ℓ = q ^ 2 + 1 := by
      rw [Nat.card_coe_set_eq]
      exact hℓncard
    have hline := hlinecardD ℓ hℓmem
    have hDcard : Nat.card D = q ^ 2 := by omega
    have hKD : Nat.card K = Nat.card D := by
      dsimp only [K]
      exact (Nat.card_congr MulOpposite.opEquiv).symm
    rw [← Nat.card_eq_fintype_card, hKD, hDcard]
  have hconverse' : ∀ W : Submodule K (Fin 5 → K), finrank K W = 2 →
      ∃ β, IsThreeBundle Γ c q β ∧
        ψ '' (Subtype.val ⁻¹' β) = {x | x.submodule ≤ W} := by
    intro W hW
    obtain ⟨β, hβ, hβeq⟩ := hconverse W hW
    rw [hGlines] at hβ
    obtain ⟨γ, hγ, hβγ⟩ := hβ
    refine ⟨γ, hγ, ?_⟩
    rw [← hβγ]
    exact hβeq
  exact ⟨K, hKfield, hKfintype, ψ, hKcard, hline, hconverse'⟩

end CFSG.Geometry.GeneralizedQuadrangles
