module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Fix

variable {Ω X : Type*} [Group Ω] [Group X] {B : Subgroup Ω}

@[expose] def actFix (α : ↥B → MulAut X) (D : Subgroup Ω) : Subgroup X where
  carrier := {g | ∀ x : ↥B, (x : Ω) ∈ D → α x g = g}
  mul_mem' := fun {a b} ha hb x hx => by rw [map_mul, ha x hx, hb x hx]
  one_mem' := fun x _ => map_one _
  inv_mem' := fun {a} ha x hx => by rw [map_inv, ha x hx]

theorem mem_actFix {α : ↥B → MulAut X} {D : Subgroup Ω} {g : X} :
    g ∈ actFix α D ↔ ∀ x : ↥B, (x : Ω) ∈ D → α x g = g :=
  Iff.rfl

theorem inf_centralizer_eq_map_actFix (φ : X →* Ω) (hφ : Function.Injective φ) {S : Subgroup Ω}
    (hφS : φ.range = S) (α : ↥B → MulAut X)
    (hα : ∀ (x : ↥B) (g : X), (x : Ω) * φ g * (x : Ω)⁻¹ = φ (α x g)) {D : Subgroup Ω}
    (hDB : D ≤ B) : S ⊓ Subgroup.centralizer (D : Set Ω) = (actFix α D).map φ := by
  ext y
  constructor
  · rintro ⟨hyS, hyC⟩
    rw [← hφS] at hyS
    obtain ⟨g, rfl⟩ := hyS
    refine ⟨g, fun x hx => hφ ?_, rfl⟩
    rw [← hα, (Subgroup.mem_centralizer_iff.1 hyC) x hx, mul_inv_cancel_right]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨hφS ▸ ⟨g, rfl⟩, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
    have h := hα ⟨d, hDB hd⟩ g
    rw [hg ⟨d, hDB hd⟩ hd] at h
    calc d * φ g = d * φ g * d⁻¹ * d := by group
      _ = φ g * d := by rw [h]

end Fix

section Transport

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_action (hp : p.Prime) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {X : Type} [Group X] [Finite X] (φ : X →* Ω) (hφ : Function.Injective φ) (hφS : φ.range = S)
    (α : ↥B → MulAut X) (hα : ∀ (x : ↥B) (g : X), (x : Ω) * φ g * (x : Ω)⁻¹ = φ (α x g))
    {D E : Subgroup Ω} (hDB : D ≤ B) (hEB : E ≤ B) (hDE : D ≤ E) (hDc : p ^ 2 ≤ Nat.card D)
    (hDBc : p ^ 2 * Nat.card D ≤ Nat.card B) (hEc : Nat.card D = p ^ 2 → Nat.card E = p ^ 3)
    {J : Subgroup X} (hJ : GLAPComponent p (actFix α D) J)
    (hJB : ∀ x : ↥B, J.map (α x).toMonoidHom = J)
    (hJD : ∀ x : ↥B, (∀ j ∈ J, j * (α x j)⁻¹ ∈ GLAPPrimeCoreOf p J) → (x : Ω) ∈ D)
    (hJE : Nat.card D = p ^ 2 → GLAPLayer p (J ⊓ actFix α E) ≠ ⊥)
    {t : X} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htJ : J ≤ Subgroup.centralizer ({t} : Set X))
    (htD : ∀ x : ↥B, (x : Ω) ∈ D → α x t = t) : S267ConcA p S B := by
  set Jφ := J.map φ with hJφ
  have hJX : J ≤ actFix α D := hJ.1
  have hBN : B ≤ Subgroup.normalizer (Jφ : Set Ω) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hα ⟨b, hb⟩ j]
      have hj' : (α ⟨b, hb⟩) j ∈ J := by
        rw [← hJB ⟨b, hb⟩]
        exact ⟨j, hj, rfl⟩
      exact ⟨_, hj', rfl⟩
    · rintro ⟨j, hj, hjy⟩
      have hj' : j ∈ J.map (α ⟨b, hb⟩).toMonoidHom := (hJB ⟨b, hb⟩).symm ▸ hj
      obtain ⟨j₀, hj₀, rfl⟩ := hj'
      have e : y = φ j₀ := by
        have h2 : b * y * b⁻¹ = b * φ j₀ * b⁻¹ := by
          rw [hα ⟨b, hb⟩ j₀]
          exact hjy.symm
        exact mul_left_cancel (mul_right_cancel h2)
      rw [e]
      exact ⟨j₀, hj₀, rfl⟩
  have hDcent : ∀ d ∈ D, ∀ j ∈ J, d * φ j = φ j * d := by
    intro d hd j hj
    have h := hα ⟨d, hDB hd⟩ j
    rw [(hJX hj) ⟨d, hDB hd⟩ hd] at h
    calc d * φ j = d * φ j * d⁻¹ * d := by group
      _ = φ j * d := by rw [h]
  have hcentD : ∀ b ∈ B, CentMod p Jφ b ↔ b ∈ D := by
    intro b hb
    constructor
    · intro hc
      apply hJD ⟨b, hb⟩
      intro j hj
      have hmem := (centMod_iff.1 hc).2 (φ j) ⟨j, hj, rfl⟩
      rw [hJφ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPPrimeCoreOf_map hφ] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      have e : ⁅φ j, b⁆ = φ (j * ((α ⟨b, hb⟩) j)⁻¹) := by
        rw [commutatorElement_def, map_mul, map_inv, ← hα ⟨b, hb⟩ j]
        group
      rw [e] at hwe
      rw [hφ hwe] at hw
      exact hw
    · intro hbD
      refine centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 ?_)
      rintro _ ⟨j, hj, rfl⟩
      exact (hDcent b hbD j hj).symm
  have hSD : S ⊓ Subgroup.centralizer (D : Set Ω) = (actFix α D).map φ :=
    inf_centralizer_eq_map_actFix φ hφ hφS α hα hDB
  have hJE' : Jφ ⊓ Subgroup.centralizer (E : Set Ω) = (J ⊓ actFix α E).map φ := by
    have hJS : Jφ ≤ S := by
      rw [← hφS]
      exact Subgroup.map_le_range φ J
    have h1 : Jφ ⊓ Subgroup.centralizer (E : Set Ω) =
        Jφ ⊓ (S ⊓ Subgroup.centralizer (E : Set Ω)) := by
      rw [← inf_assoc, inf_eq_left.2 hJS]
    rw [h1, inf_centralizer_eq_map_actFix φ hφ hφS α hα hEB, hJφ, Subgroup.map_inf_eq _ _ φ hφ]
  refine ⟨B, D, Jφ, hB, ⟨⟨hDB, hDc, hDBc⟩,
    ⟨by rw [hSD, hJφ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hφ]; exact hJ,
      hBN, hcentD⟩,
    fun hD2 => ⟨E, hEB, hB.mono hEB, hEc hD2, hDE, ?_⟩⟩, Or.inl rfl, hBC, φ t, ?_, ?_, ?_, ?_⟩
  · rw [hJE']
    exact CFSG.LocalAnalysis.GLTheoremA.I2611.glaPLayer_map_ne_bot hp φ hφ (hJE hD2)
  · exact fun h => ht1 (hφ (h.trans (map_one φ).symm))
  · rw [← map_pow, ht2, map_one]
  · intro d hd
    have h := hα ⟨d, hDB hd⟩ t
    rw [htD ⟨d, hDB hd⟩ hd] at h
    calc d * φ t = d * φ t * d⁻¹ * d := by group
      _ = φ t * d := by rw [h]
  · rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (htJ hj)]

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
