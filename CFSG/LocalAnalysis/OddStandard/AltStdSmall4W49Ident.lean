module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49Main
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarCases
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Struct
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49Excl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup ModIso
open scoped Matrix

theorem exists_gl_of_add {f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2)}
    (hadd : ∀ a a', f (a + a') = f a + f a') (hinj : Function.Injective f) :
    ∃ A : GL (Fin 3) (ZMod 2), ∀ a, mv A a = f a := by
  let fA : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) := AddMonoidHom.mk' f hadd
  let fL : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) := fA.toZModLinearMap 2
  have hbij : Function.Bijective fL := ⟨hinj, Finite.surjective_of_injective hinj⟩
  let eL : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearEquiv.ofBijective fL hbij
  let u : LinearMap.GeneralLinearGroup (ZMod 2) (Fin 3 → ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm eL
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm u, fun a => ?_⟩
  have h := congrArg (fun L : LinearMap.GeneralLinearGroup (ZMod 2) (Fin 3 → ZMod 2) =>
    (L : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) a)
    (Matrix.GeneralLinearGroup.toLin.apply_symm_apply u)
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h
  exact h

section Shape

variable {G : Type} [Group G] {z : G} {T : Subgroup G} {κ : GL (Fin 3) (ZMod 2) →* G}
  {E₀ : Subgroup G} {e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} (he : PairCoords z T κ E₀ e)
include he

private theorem exists_gl_of_conj₁ {g : G} {f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2)}
    (hf : ∀ a, g * e a 0 * g⁻¹ = e (f a) 0) : ∃ A : GL (Fin 3) (ZMod 2), ∀ a, mv A a = f a := by
  refine exists_gl_of_add (fun a a' => ?_) (fun a a' h => ?_)
  · have h1 : e (f (a + a')) 0 = e (f a + f a') 0 := by
      rw [← hf, show (0 : Fin 3 → ZMod 2) = 0 + 0 from (add_zero 0).symm, he.add, he.add, ← hf,
        ← hf]
      group
    exact ((he.eq_iff).1 h1).1
  · have h1 : e a 0 = e a' 0 := by
      have h2 : g * e a 0 * g⁻¹ = g * e a' 0 * g⁻¹ := by rw [hf, hf, h]
      simpa using h2
    exact ((he.eq_iff).1 h1).1

private theorem exists_gl_of_conj₂ {g : G} {f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2)}
    (hf : ∀ b, g * e 0 b * g⁻¹ = e 0 (f b)) : ∃ A : GL (Fin 3) (ZMod 2), ∀ b, mv A b = f b := by
  refine exists_gl_of_add (fun b b' => ?_) (fun b b' h => ?_)
  · have h1 : e 0 (f (b + b')) = e 0 (f b + f b') := by
      rw [← hf, show (0 : Fin 3 → ZMod 2) = 0 + 0 from (add_zero 0).symm, he.add, he.add, ← hf,
        ← hf]
      group
    exact ((he.eq_iff).1 h1).2
  · have h1 : e 0 b = e 0 b' := by
      have h2 : g * e 0 b * g⁻¹ = g * e 0 b' * g⁻¹ := by rw [hf, hf, h]
      simpa using h2
    exact ((he.eq_iff).1 h1).2

theorem shape_of_pointwise {g : G}
    (hg : ((∀ a, ∃ a', g * e a 0 * g⁻¹ = e a' 0) ∧ (∀ b, ∃ b', g * e 0 b * g⁻¹ = e 0 b')) ∨
      ((∀ a, ∃ b', g * e a 0 * g⁻¹ = e 0 b') ∧ (∀ b, ∃ a', g * e 0 b * g⁻¹ = e a' 0))) :
    ∃ A B : GL (Fin 3) (ZMod 2), (∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv B b)) ∨
      (∀ a b, g * e a b * g⁻¹ = e (mv B b) (mv A a)) := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · choose f hf using h1
    choose f' hf' using h2
    obtain ⟨A, hA⟩ := exists_gl_of_conj₁ he hf
    obtain ⟨B, hB⟩ := exists_gl_of_conj₂ he hf'
    refine ⟨A, B, Or.inl fun a b => ?_⟩
    rw [he.split a b, show g * (e a 0 * e 0 b) * g⁻¹ = (g * e a 0 * g⁻¹) * (g * e 0 b * g⁻¹) by
      group, hf, hf', hA, hB, ← he.split]
  · choose f hf using h1
    choose f' hf' using h2
    have hadd₁ : ∀ a a', f (a + a') = f a + f a' := fun a a' => by
      have h1 : e 0 (f (a + a')) = e 0 (f a + f a') := by
        rw [← hf, show (0 : Fin 3 → ZMod 2) = 0 + 0 from (add_zero 0).symm, he.add, he.add, ← hf,
          ← hf]
        group
      exact ((he.eq_iff).1 h1).2
    have hinj₁ : Function.Injective f := fun a a' h => by
      have h1 : e a 0 = e a' 0 := by
        have h2 : g * e a 0 * g⁻¹ = g * e a' 0 * g⁻¹ := by rw [hf, hf, h]
        simpa using h2
      exact ((he.eq_iff).1 h1).1
    have hadd₂ : ∀ b b', f' (b + b') = f' b + f' b' := fun b b' => by
      have h1 : e (f' (b + b')) 0 = e (f' b + f' b') 0 := by
        rw [← hf', show (0 : Fin 3 → ZMod 2) = 0 + 0 from (add_zero 0).symm, he.add, he.add, ← hf',
          ← hf']
        group
      exact ((he.eq_iff).1 h1).1
    have hinj₂ : Function.Injective f' := fun b b' h => by
      have h1 : e 0 b = e 0 b' := by
        have h2 : g * e 0 b * g⁻¹ = g * e 0 b' * g⁻¹ := by rw [hf', hf', h]
        simpa using h2
      exact ((he.eq_iff).1 h1).2
    obtain ⟨A, hA⟩ := exists_gl_of_add hadd₁ hinj₁
    obtain ⟨B, hB⟩ := exists_gl_of_add hadd₂ hinj₂
    refine ⟨A, B, Or.inr fun a b => ?_⟩
    rw [he.split a b, show g * (e a 0 * e 0 b) * g⁻¹ = (g * e a 0 * g⁻¹) * (g * e 0 b * g⁻¹) by
      group, hf, hf', hA, hB, he.comm, ← he.split]

end Shape

section Ident

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}

theorem shape_of_MW (c : Config G L Q n θ z)
    {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}
    (hc : TCoords z T (kap θ c.hn8) (E θ c.hn8) cT) (Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2))
    (hconj : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
      (g : G) * cT v w * (g : G)⁻¹ =
        cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w))
          (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w)))
    (hMW : (Hbar T).map Ψ.toMonoidHom ≤ GL62.MW) :
    ∃ e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G,
      PairCoords z T (kap θ c.hn8) (E θ c.hn8) e ∧
      ∀ g ∈ normalizer (T : Set G), ∃ A B : GL (Fin 3) (ZMod 2),
        (∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv B b)) ∨
          (∀ a b, g * e a b * g⁻¹ = e (mv B b) (mv A a)) := by
  have he := pairCoords_of_tCoords hc
  refine ⟨_, he, fun g hg => shape_of_pointwise he ?_⟩
  set M := Ψ (AltStdBal.normAct T ⟨g, hg⟩) with hM
  have hMmem : M ∈ GL62.MW := hMW ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
  have hc' : ∀ v w, g * cT v w * g⁻¹ =
      cT (GL62.fst ((M : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w))
        (GL62.snd ((M : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w)) :=
    hconj ⟨g, hg⟩
  rcases GL62.mulVec_of_mem_MW hMmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨fun a => ?_, fun b => ?_⟩
    · obtain ⟨w', hw'⟩ := h1 a
      refine ⟨w', ?_⟩
      simp only [add_zero]
      rw [hc', hw', GL62.fst_append, GL62.snd_append]
    · obtain ⟨w', hw'⟩ := h2 b
      refine ⟨w', ?_⟩
      simp only [zero_add]
      rw [hc', hw', GL62.fst_append, GL62.snd_append]
  · refine Or.inr ⟨fun a => ?_, fun b => ?_⟩
    · obtain ⟨w', hw'⟩ := h1 a
      refine ⟨w', ?_⟩
      simp only [add_zero, zero_add]
      rw [hc', hw', GL62.fst_append, GL62.snd_append]
    · obtain ⟨w', hw'⟩ := h2 b
      refine ⟨w', ?_⟩
      simp only [add_zero, zero_add]
      rw [hc', hw', GL62.fst_append, GL62.snd_append]

end Ident

theorem sec4Wreath49_of_ident (hI : HbarCoords.Sec4HbarIdent) : Sec4Wreath49 := by
  apply sec4Wreath49_of_shape
  intro G _ _ L Q n θ z c T hH hcard
  obtain ⟨cT, Ψ, hc, hconj, hX⟩ := hI G L Q n θ z c T hH
  have hcardX : Nat.card ((Hbar T).map Ψ.toMonoidHom) = 56448 := by
    rw [card_map_of_injective Ψ.injective, hcard]
  obtain ⟨hMN, hMS, hMG⟩ := card_ne_56448
  have hle : (Hbar T).map Ψ.toMonoidHom ≤ GL62.MW := by
    rcases hX with h | h | h | h | h
    · rw [h]
      exact le_sup_left
    · rw [h] at hcardX
      exact absurd hcardX hMN
    · exact h.le
    · rw [h] at hcardX
      exact absurd hcardX hMS
    · rw [h] at hcardX
      exact absurd hcardX hMG
  exact shape_of_MW c hc Ψ hconj hle

end CFSG.OddStandard.AltStdSmall4.W49
