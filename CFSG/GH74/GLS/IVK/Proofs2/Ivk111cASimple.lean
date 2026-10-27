module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cAFun
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cAFix
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex

section Basic

variable {F L : Type} [Field F] [Field L] [Algebra F L]

@[expose] def uHom (F : Type) [Field F] : Multiplicative F →* SLm F where
  toFun b := sl2U (Multiplicative.toAdd b)
  map_one' := by simp [sl2U_zero]
  map_mul' a b := by simp [sl2U_add]

@[expose] noncomputable def yVec (F L : Type) [Field F] [Field L] [Algebra F L] (A : ℕ) :
    steinbergSub F L A := ⟨monoFun F L 0 A, monoFun_y_mem A⟩

@[expose] noncomputable def xVec (F L : Type) [Field F] [Field L] [Algebra F L] (A : ℕ) :
    steinbergSub F L A := ⟨monoFun F L A 0, monoFun_x_mem A⟩

theorem steinbergRep_val {A : ℕ} (g : SLm F) (z : steinbergSub F L A) :
    ((steinbergRep F L A g z : steinbergSub F L A) : (Fin 2 → F) → L) = funRep F L g z := rfl

theorem steinbergRep_sl2U_yVec {A : ℕ} (b : F) :
    steinbergRep F L A (sl2U b) (yVec F L A) = yVec F L A :=
  Subtype.ext (funRep_sl2U_y b A)

theorem steinbergRep_sl2W_yVec {A : ℕ} :
    steinbergRep F L A (sl2W F) (yVec F L A) = xVec F L A :=
  Subtype.ext (funRep_sl2W_y A)

theorem yVec_ne_zero {A : ℕ} : yVec F L A ≠ 0 := fun h =>
  monoFun_y_ne_zero (F := F) (L := L) A (congrArg Subtype.val h)

end Basic

section Core

variable {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]

theorem fixed_eq_smul {A : ℕ} (hA : A < Nat.card F) {z : steinbergSub F L A}
    (hz : ∀ b : F, steinbergRep F L A (sl2U b) z = z) : ∃ c : L, z = c • yVec F L A := by
  obtain ⟨c, hc⟩ := eq_smul_of_fixed hA (isHomPoly_of_mem z.2) (fun b => congrArg Subtype.val (hz b))
  exact ⟨c, Subtype.ext hc⟩

theorem eq_top_of_mem_ne_zero {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) {A : ℕ}
    (hA : A < Nat.card F) (σ : Subrepresentation (steinbergRep F L A)) {s : steinbergSub F L A}
    (hs : s ∈ σ) (hs0 : s ≠ 0) : σ = ⊤ := by
  obtain ⟨w, hw, hw0, hwfix⟩ :=
    exists_fixed_ne_zero_span hp hF ((steinbergRep F L A).comp (uHom F)) hs0
  have hwσ : w ∈ σ.toSubmodule :=
    (Submodule.span_le.mpr (by
      rintro _ ⟨b, rfl⟩
      exact σ.apply_mem_toSubmodule _ hs)) hw
  obtain ⟨c, hc⟩ := fixed_eq_smul hA (z := w) (fun b => hwfix (Multiplicative.ofAdd b))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [hc, zero_smul])
  have hy : yVec F L A ∈ σ.toSubmodule := by
    have h1 : yVec F L A = c⁻¹ • w := by rw [hc, inv_smul_smul₀ hc0]
    rw [h1]
    exact σ.toSubmodule.smul_mem _ hwσ
  have hx : xVec F L A ∈ σ.toSubmodule := by
    rw [← steinbergRep_sl2W_yVec]
    exact σ.apply_mem_toSubmodule _ hy
  have hle : steinbergSub F L A ≤ σ.toSubmodule.map (steinbergSub F L A).subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨steinbergRep F L A g (xVec F L A), σ.apply_mem_toSubmodule g hx, rfl⟩
  refine eq_top_iff.mpr fun t _ => ?_
  obtain ⟨t', ht', htt⟩ := hle t.2
  have : t' = t := Subtype.ext htt
  exact this ▸ ht'


theorem schur_core {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < Nat.card F)
    (Φ : steinbergSub F L A →ₗ[L] steinbergSub F L A)
    (hΦ : ∀ (g : SLm F) (z : steinbergSub F L A),
      Φ (steinbergRep F L A g z) = steinbergRep F L A g (Φ z)) :
    ∃ c : L, ∀ z, Φ z = c • z := by
  have hfix : ∀ b : F, steinbergRep F L A (sl2U b) (Φ (yVec F L A)) = Φ (yVec F L A) := by
    intro b
    rw [← hΦ, steinbergRep_sl2U_yVec]
  obtain ⟨c, hc⟩ := fixed_eq_smul hA hfix
  refine ⟨c, ?_⟩
  let K : Subrepresentation (steinbergRep F L A) :=
    ⟨LinearMap.ker (Φ - c • LinearMap.id), fun g z hz => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hz ⊢
      rw [hΦ, hz, map_smul]⟩
  have hK : K = ⊤ := by
    refine eq_top_of_mem_ne_zero hp hF hA K (s := yVec F L A) ?_ yVec_ne_zero
    show yVec F L A ∈ LinearMap.ker (Φ - c • LinearMap.id)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    exact hc
  intro z
  have hz : z ∈ K := by rw [hK]; trivial
  have hz' : z ∈ LinearMap.ker (Φ - c • LinearMap.id) := hz
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] using hz'

end Core

section Main

theorem steinberg_simple_holds : SteinbergSimpleStmt := by
  intro p n F L _ _ _ _ hp hp2 hF A hA
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hA' : A < Nat.card F := hF ▸ hA
  have hne : (⊥ : Subrepresentation (steinbergRep F L A)) ≠ ⊤ := by
    intro h
    have h1 : xVec F L A ∈ (⊥ : Subrepresentation (steinbergRep F L A)).toSubmodule := by
      rw [h]; trivial
    have h2 : xVec F L A = 0 := (Submodule.mem_bot L).mp h1
    exact monoFun_x_ne_zero (F := F) (L := L) A (congrArg Subtype.val h2)
  exact
    { exists_pair_ne := ⟨⊥, ⊤, hne⟩
      eq_bot_or_eq_top := fun σ => by
        by_cases h : σ = ⊥
        · exact Or.inl h
        · refine Or.inr ?_
          have h1 : σ.toSubmodule ≠ ⊥ := fun h0 => h (Subrepresentation.ext h0)
          obtain ⟨s, hs, hs0⟩ := Submodule.ne_bot_iff _ |>.mp h1
          exact eq_top_of_mem_ne_zero hp hF hA' σ hs hs0 }

theorem steinberg_negOne_holds : SteinbergNegOneStmt := by
  intro p n F L _ _ _ _ hp hp2 hF A hA f
  apply Subtype.ext
  exact funRep_negOne_of_isHomPoly (isHomPoly_of_mem f.2)

theorem steinberg_end_holds : SteinbergEndStmt := by
  intro p n F L _ _ _ _ hp hp2 hF A hA φ
  have hA' : A < Nat.card F := hF ▸ hA
  let ρ := steinbergRep F L A
  let e : ρ.asModule ≃ₗ[L] steinbergSub F L A := ρ.asModuleEquiv
  let Φ : steinbergSub F L A →ₗ[L] steinbergSub F L A :=
    (e : ρ.asModule →ₗ[L] steinbergSub F L A) ∘ₗ (φ.restrictScalars L) ∘ₗ
      (e.symm : steinbergSub F L A →ₗ[L] ρ.asModule)
  have hΦx : ∀ x : ρ.asModule, Φ (e x) = e (φ x) := by
    intro x
    simp [Φ]
  have hΦ : ∀ (g : SLm F) (z : steinbergSub F L A), Φ (ρ g z) = ρ g (Φ z) := by
    intro g z
    have h0 : e.symm (ρ g z) = MonoidAlgebra.of L (SLm F) g • e.symm z :=
      Representation.asModuleEquiv_symm_map_rho ρ g z
    have h1 : ρ g z = e (MonoidAlgebra.of L (SLm F) g • e.symm z) := by
      rw [← h0]
      simp
    rw [h1, hΦx, map_smul]
    show e (MonoidAlgebra.of L (SLm F) g • φ (e.symm z)) = ρ g (Φ z)
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    rfl
  obtain ⟨c, hc⟩ := schur_core hp hF hA' Φ hΦ
  refine ⟨c, fun x => e.injective ?_⟩
  rw [← hΦx, hc, map_smul]

end Main

end CFSG.GH74.GLS.Stage4.Rest
