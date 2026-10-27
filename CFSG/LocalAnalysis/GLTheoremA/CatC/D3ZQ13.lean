module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ12

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Data

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem degSeries_le_adjointGroup (d : ℤ) : degSeries τ K J d ≤ adjointGroup τ K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem lconj_congr_conj {g g' : ModGL τ K} (hg : NormAll J g) (hg' : NormAll J g') {d : ℤ}
    (hd : 1 ≤ d) (h : ∀ x ∈ degSeries τ K J d, g * x * g⁻¹ = g' * x * g'⁻¹)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) : lconj hg hd z = lconj hg' hd z := by
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lconj_mk, lconj_mk]
  congr 1
  exact Subtype.ext (h x.1 x.2)

structure A4Grp (J : Set (Fin τ.rank)) (φ : ModGL τ K →* ModGL τ K) (Γ₁ Γ₂ : ModGL τ K) : Prop where
  φ_mem : ∀ d : ℤ, ∀ x ∈ degSeries τ K J d, φ x ∈ degSeries τ K J d
  φ_cube : ∀ x ∈ adjointGroup τ K, φ (φ (φ x)) = x
  n₁ : NormAll J Γ₁
  n₂ : NormAll J Γ₂
  sq₁ : ∀ x ∈ adjointGroup τ K, Γ₁ * Γ₁ * x * (Γ₁ * Γ₁)⁻¹ = x
  sq₂ : ∀ x ∈ adjointGroup τ K, Γ₂ * Γ₂ * x * (Γ₂ * Γ₂)⁻¹ = x
  comm : ∀ x ∈ adjointGroup τ K, Γ₁ * (Γ₂ * x * Γ₂⁻¹) * Γ₁⁻¹ = Γ₂ * (Γ₁ * x * Γ₁⁻¹) * Γ₂⁻¹
  rel₁ : ∀ x ∈ adjointGroup τ K, φ (Γ₁ * x * Γ₁⁻¹) = Γ₂ * φ x * Γ₂⁻¹
  rel₂ : ∀ x ∈ adjointGroup τ K, φ (Γ₂ * x * Γ₂⁻¹) = (Γ₁ * Γ₂) * φ x * (Γ₁ * Γ₂)⁻¹

variable {φ : ModGL τ K →* ModGL τ K} {Γ₁ Γ₂ : ModGL τ K}

@[expose] def A4Grp.layerB (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d) :
    Lyr (isLayer_degSeries (K := K) (J := J) hd) ≃ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
  lmapEquiv G.φ_mem hd (fun x hx => G.φ_cube x (degSeries_le_adjointGroup d hx))

theorem A4Grp.layer_inv₁ (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj G.n₁ hd (lconj G.n₁ hd z) = z :=
  lconj_involutive G.n₁ hd (fun x hx => G.sq₁ x (degSeries_le_adjointGroup d hx)) z

theorem A4Grp.layer_inv₂ (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj G.n₂ hd (lconj G.n₂ hd z) = z :=
  lconj_involutive G.n₂ hd (fun x hx => G.sq₂ x (degSeries_le_adjointGroup d hx)) z

theorem A4Grp.layer_comm (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj G.n₁ hd (lconj G.n₂ hd z) = lconj G.n₂ hd (lconj G.n₁ hd z) := by
  rw [← lconj_mul G.n₁ G.n₂ hd z, ← lconj_mul G.n₂ G.n₁ hd z]
  exact lconj_congr_conj (G.n₁.mul G.n₂) (G.n₂.mul G.n₁) hd
    (fun x hx => by
      have := G.comm x (degSeries_le_adjointGroup d hx)
      simpa [mul_assoc] using this) z

theorem A4Grp.layer_B₁ (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    G.layerB hd (lconj G.n₁ hd z) = lconj G.n₂ hd (G.layerB hd z) :=
  lmap_lconj G.φ_mem G.n₁ G.n₂ hd (fun x hx => G.rel₁ x (degSeries_le_adjointGroup d hx)) z

theorem A4Grp.layer_B₂ (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    G.layerB hd (lconj G.n₂ hd z) =
      lconj G.n₁ hd (lconj G.n₂ hd (G.layerB hd z)) := by
  rw [← lconj_mul G.n₁ G.n₂ hd]
  exact lmap_lconj G.φ_mem G.n₂ (G.n₁.mul G.n₂) hd
    (fun x hx => G.rel₂ x (degSeries_le_adjointGroup d hx)) z

theorem A4Grp.card_fix_le (G : A4Grp J φ Γ₁ Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (c₁ : Nat.card (fixSp (lconj G.n₁ hd)) ^ 2 ≤
      Nat.card (Lyr (isLayer_degSeries (K := K) (J := J) hd))) :
    Nat.card (fixSp (lconj G.n₁ hd) ⊓ fixSp (lconj G.n₂ hd) :
        Submodule (ZMod 3) (Lyr (isLayer_degSeries (K := K) (J := J) hd))) ^ 4 ≤
      Nat.card (Lyr (isLayer_degSeries (K := K) (J := J) hd)) :=
  card_inf_klein_le_of_conj _ _ (G.layer_inv₁ hd) (G.layer_inv₂ hd) (G.layer_comm hd) (G.layerB hd)
    (G.layer_B₁ hd) (G.layer_B₂ hd) c₁

end Data

end CFSG.LocalAnalysis.GLTheoremA
