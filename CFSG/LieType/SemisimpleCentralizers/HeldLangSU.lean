module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangUnitary
public import CFSG.LieType.SemisimpleCentralizers.HeldLangSL

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.HardMathSupport.Foote.ModuleExclusions CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

variable {K : Type} [Field K] {d : ℕ}

@[expose] def IsIso (bar : K ≃+* K) (A : GL (Fin d) K) : Prop :=
  conjTr bar (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) = 1

section Iso

variable {bar : K ≃+* K}

theorem IsIso.conjTr_eq_inv {A : GL (Fin d) K} (h : IsIso bar A) :
    conjTr bar (A : Matrix (Fin d) (Fin d) K) = ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  calc conjTr bar (A : Matrix (Fin d) (Fin d) K)
      = conjTr bar (A : Matrix (Fin d) (Fin d) K) *
          ((A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (conjTr bar (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K)) *
          ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [Matrix.mul_assoc]
    _ = ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [h, Matrix.one_mul]

theorem IsIso.inv (hbb : ∀ x, bar (bar x) = x) {A : GL (Fin d) K} (h : IsIso bar A) : IsIso bar A⁻¹ := by
  unfold IsIso
  have h2 : conjTr bar ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (A : Matrix (Fin d) (Fin d) K) := by
    rw [← h.conjTr_eq_inv, conjTr_conjTr' bar hbb]
  rw [h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem IsIso.mul {A B : GL (Fin d) K} (hA : IsIso bar A) (hB : IsIso bar B) : IsIso bar (A * B) := by
  unfold IsIso at *
  rw [Units.val_mul, conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr bar (A : Matrix (Fin d) (Fin d) K)),
    hA, Matrix.one_mul, hB]

theorem IsIso.one : IsIso bar (1 : GL (Fin d) K) := by
  unfold IsIso
  simp [conjTr_one]

theorem IsIso.glMap {σ : K ≃+* K} (hcomm : ∀ x, σ (bar x) = bar (σ x)) {x : GL (Fin d) K}
    (h : IsIso bar x) : IsIso bar (glMap σ x) := by
  unfold IsIso at *
  rw [coe_glMap, ← map_conjTr bar σ hcomm, ← Matrix.map_mul, h]
  simp

theorem IsIso.det_mul_det {A : GL (Fin d) K} (h : IsIso bar A) :
    bar (A : Matrix (Fin d) (Fin d) K).det * (A : Matrix (Fin d) (Fin d) K).det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one, conjTr, Matrix.det_transpose] at h1
  have h2 : ((A : Matrix (Fin d) (Fin d) K).map bar).det = bar (A : Matrix (Fin d) (Fin d) K).det :=
    (RingHom.map_det (bar : K →+* K) (A : Matrix (Fin d) (Fin d) K)).symm
  rwa [h2] at h1

theorem IsIso.normProd {σ : K ≃+* K} (hcomm : ∀ x, σ (bar x) = bar (σ x)) {A : GL (Fin d) K}
    (hA : IsIso bar A) (k : ℕ) : IsIso bar (normProd σ A k) := by
  induction k with
  | zero => exact IsIso.one
  | succ k ih => exact hA.mul (ih.glMap hcomm)

theorem IsIso.conj {A x : GL (Fin d) K} (hbb : ∀ x, bar (bar x) = x) (hA : IsIso bar A) (hx : IsIso bar x) :
    IsIso bar (A * x * A⁻¹) :=
  (hA.mul hx).mul (hA.inv hbb)

theorem isIso_of_mem_SUid {x : GL (Fin d) K} (hx : x ∈ SUid bar d) : IsIso bar x := (mem_SUid.1 hx).2

theorem mem_SUid_of_isIso {x : GL (Fin d) K} (h1 : (x : Matrix (Fin d) (Fin d) K).det = 1)
    (h2 : IsIso bar x) : x ∈ SUid bar d := mem_SUid.2 ⟨h1, h2⟩

theorem glMap_mem_SUid {σ : K ≃+* K} (hcomm : ∀ x, σ (bar x) = bar (σ x)) {x : GL (Fin d) K}
    (hx : x ∈ SUid bar d) : glMap σ x ∈ SUid bar d := by
  refine mem_SUid_of_isIso ?_ ((isIso_of_mem_SUid hx).glMap hcomm)
  rw [det_glMap, (mem_SUid.1 hx).1, map_one]

theorem conj_mem_SUid {A x : GL (Fin d) K} (hbb : ∀ x, bar (bar x) = x) (hA : IsIso bar A)
    (hx : x ∈ SUid bar d) : A * x * A⁻¹ ∈ SUid bar d := by
  refine mem_SUid_of_isIso ?_ (hA.conj hbb (isIso_of_mem_SUid hx))
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, (mem_SUid.1 hx).1, mul_one,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

end Iso

section Twist

variable {bar σ : K ≃+* K}

theorem suTwist_mem (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x) {A : GL (Fin d) K}
    (hA : IsIso bar A) {x : GL (Fin d) K} (hx : x ∈ SUid bar d) : A * glMap σ x * A⁻¹ ∈ SUid bar d :=
  conj_mem_SUid hbb hA (glMap_mem_SUid hcomm hx)

@[expose] def suTwist (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x) (A : GL (Fin d) K)
    (hA : IsIso bar A) : SUid bar d →* SUid bar d :=
  twistHom (SUid bar d) σ A fun _ hx => suTwist_mem hcomm hbb hA hx

theorem mem_SUid_inf_glFix_iff (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x)
    {w : GL (Fin d) K} :
    w ∈ SUid bar d ⊓ glFix σ ↔ ∃ x₀ : SUid (barFix σ bar hcomm hbb) d, glFixEmb σ x₀ = w := by
  have hinj : Function.Injective fun N : Matrix (Fin d) (Fin d) (fixField σ) => N.map (fixField σ).subtype :=
    Matrix.map_injective (fixField σ).subtype_injective
  have hcoe : ∀ x₀ : GL (Fin d) (fixField σ), ((glFixEmb σ x₀ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (x₀ : Matrix (Fin d) (Fin d) (fixField σ)).map (fixField σ).subtype := fun x₀ => by
    ext i j
    rw [glFixEmb_apply]
    rfl
  constructor
  · intro hw
    obtain ⟨hs, hf⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨x₀, hx₀⟩ : w ∈ (glFixEmb (ι := Fin d) σ).range := by rwa [glFixEmb_range]
    obtain ⟨hdet, hiso⟩ := mem_SUid.1 hs
    refine ⟨⟨x₀, mem_SUid.2 ⟨?_, ?_⟩⟩, hx₀⟩
    · apply (fixField σ).subtype_injective
      rw [← hx₀, hcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
      simpa using hdet
    · have hX : (x₀ : Matrix (Fin d) (Fin d) (fixField σ)).map (fixField σ).subtype =
          (w : Matrix (Fin d) (Fin d) K) := by
        rw [← hcoe x₀, hx₀]
      have key : (conjTr (barFix σ bar hcomm hbb) (x₀ : Matrix (Fin d) (Fin d) (fixField σ)) *
            (x₀ : Matrix (Fin d) (Fin d) (fixField σ))).map (fixField σ).subtype =
          (1 : Matrix (Fin d) (Fin d) (fixField σ)).map (fixField σ).subtype := by
        rw [Matrix.map_mul, map_conjTr_fix, hX]
        exact hiso.trans (by simp)
      exact hinj key
  · rintro ⟨x₀, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, glFixEmb_mem σ (x₀ : GL (Fin d) (fixField σ))⟩
    obtain ⟨hdet, hiso⟩ := mem_SUid.1 x₀.2
    refine mem_SUid.2 ⟨?_, ?_⟩
    · rw [hcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
      simp
    · have h2 := congrArg (fun N : Matrix (Fin d) (Fin d) (fixField σ) => N.map (fixField σ).subtype) hiso
      simp only [Matrix.map_mul, map_conjTr_fix] at h2
      rw [hcoe]
      simpa using h2

end Twist

variable {bar σ : K ≃+* K}

theorem exists_suTwist_fix {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hodd : Odd (orderOf σ))
    [NeZero d] (A : GL (Fin d) K) (hA : IsIso bar A) {c : K}
    (hc : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K)) :
    ∃ u : GL (Fin d) K, IsIso bar u ∧
      (∀ x : GL (Fin d) K, A * glMap σ x * A⁻¹ = u⁻¹ * glMap σ (u * x * u⁻¹) * u) ∧
      ∀ x : SUid bar d, x ∈ fixHom (suTwist hcomm hbar.invol A hA) ↔
        ∃ x₀ : SUid (barFix σ bar hcomm hbar.invol) d, (x : GL (Fin d) K) = u⁻¹ * glFixEmb σ x₀ * u := by
  obtain ⟨u, l, hu, hl⟩ := exists_unitary_cocycle hp he hK hbar hcomm hodd A (μ := 1) (c := c)
    (map_one bar) one_ne_zero (by rw [one_smul]; exact hA) hc
  have hconj := twist_eq_conj_of_smul σ l hl
  refine ⟨u, hu, hconj, fun x => ?_⟩
  refine (mem_fixHom_twistHom_iff (SUid bar d) σ A u
    (fun _ hx => suTwist_mem hcomm hbar.invol hA hx) hconj x).trans ?_
  have hux : u * (x : GL (Fin d) K) * u⁻¹ ∈ SUid bar d := conj_mem_SUid hbar.invol hu x.2
  constructor
  · intro h
    obtain ⟨x₀, hx₀⟩ := (mem_SUid_inf_glFix_iff hcomm hbar.invol).1 (Subgroup.mem_inf.2 ⟨hux, h⟩)
    refine ⟨x₀, ?_⟩
    rw [hx₀]
    group
  · rintro ⟨x₀, hx₀⟩
    have h1 : u * (x : GL (Fin d) K) * u⁻¹ = glFixEmb σ x₀ := by
      rw [hx₀]
      group
    rw [h1]
    exact (Subgroup.mem_inf.1 ((mem_SUid_inf_glFix_iff hcomm hbar.invol).2 ⟨x₀, rfl⟩)).2

theorem exists_fix_of_eq {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hodd : Odd (orderOf σ))
    [NeZero d] (S : Subgroup (GL (Fin d) K)) (hS : S = SUid bar d) (A : GL (Fin d) K) (hA : IsIso bar A)
    {c : K} (hc : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K))
    (β₀ : S →* S) (hβ₀ : ∀ x : S, (β₀ x : GL (Fin d) K) = A * glMap σ x * A⁻¹) :
    ∃ u : GL (Fin d) K, IsIso bar u ∧
      ∀ x : S, x ∈ fixHom β₀ ↔
        ∃ x₀ : SUid (barFix σ bar hcomm hbar.invol) d, (x : GL (Fin d) K) = u⁻¹ * glFixEmb σ x₀ * u := by
  subst hS
  have hβ : β₀ = suTwist hcomm hbar.invol A hA := MonoidHom.ext fun x => Subtype.ext (hβ₀ x)
  subst hβ
  obtain ⟨u, hu, -, hfix⟩ := exists_suTwist_fix hp he hK hbar hcomm hodd A hA hc
  exact ⟨u, hu, hfix⟩

end CFSG.LieType.SemisimpleCentralizers.HeldLang
