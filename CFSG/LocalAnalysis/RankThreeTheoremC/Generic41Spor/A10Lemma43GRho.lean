module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10t1_conj_hom (J H : Subgroup G) (hH : H ≤ Subgroup.normalizer (J : Set G)) :
    ∃ ι : H →* MulAut J, ∀ (c : H) (j : J), ((ι c j : J) : G) = (c : G) * j * (c : G)⁻¹ := by
  let f : ∀ c : G, c ∈ Subgroup.normalizer (J : Set G) → MulAut J := fun c hc =>
    { toFun := fun j => ⟨c * j * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc j).mp j.2⟩
      invFun := fun j => ⟨c⁻¹ * j * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hc) j).mp j.2⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  refine ⟨{ toFun := fun c => f c (hH c.2), map_one' := ?_, map_mul' := ?_ }, fun c j => rfl⟩
  · ext j; simp [f]
  · intro a b; ext j; simp [f, mul_assoc]

theorem a10t1_descent {J Q H : Type} [Group J] [Group Q] [Group H] (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (ι : H →* MulAut J)
    (h : ∀ c j, ψ j = 1 → ψ (ι c j) = 1) :
    ∃ θ : H →* MulAut Q, ∀ c j, θ c (ψ j) = ψ (ι c j) := by
  have key : ∀ c : H, ∃ f : Q →* Q, ∀ j, f (ψ j) = ψ (ι c j) := by
    intro c
    refine ⟨ψ.liftOfSurjective hψ ⟨ψ.comp (ι c).toMonoidHom, fun j hj => h c j hj⟩, fun j => ?_⟩
    simp
  choose F hF using key
  have hmul : ∀ c d : H, ∀ q, F (c * d) q = F c (F d q) := by
    intro c d q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF, hF, hF]
    simp
  have hone : ∀ q, F 1 q = q := by
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF]
    simp
  let θ' : ∀ c : H, MulAut Q := fun c =>
    { toFun := F c
      invFun := F c⁻¹
      left_inv := fun q => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := (F c).map_mul }
  refine ⟨{ toFun := θ', map_one' := ?_, map_mul' := ?_ }, fun c j => hF c j⟩
  · ext q; exact hone q
  · intro a b; ext q; exact hmul a b q

theorem a10_rho (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q]
    (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ ρ : ↥W →* MulAut Q,
      (∀ (w : ↥W) (j : ↥J) (hj : (w : G) * (j : G) * (w : G)⁻¹ ∈ J),
        ρ w (ψ j) = ψ ⟨(w : G) * (j : G) * (w : G)⁻¹, hj⟩) ∧
      ∀ w : ↥W, ρ w = 1 → (w : G) ∈ u3K0 5 x J := by
  have hPN : W ≤ Subgroup.normalizer (J : Set G) := hW.trans hc.cent_le
  obtain ⟨ι, hι⟩ := a10t1_conj_hom J W hPN
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore 5 J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hιker : ∀ (c : W) (j : J), ψ j = 1 → ψ (ι c j) = 1 := by
    intro c j hj
    rw [hOker] at hj ⊢
    rw [hι]
    exact Generic49U3.u3_core_conj (hPN c.2) hj
  obtain ⟨θ, hθ⟩ := a10t1_descent ψ hψ ι hιker
  refine ⟨θ, fun w j hj => ?_, fun w hw1 => ?_⟩
  · rw [hθ]
    congr 1
    exact Subtype.ext (hι w j)
  · refine ⟨hW w.2, hPN w.2, fun j hj => ?_⟩
    have h1 : ψ (ι w ⟨j, hj⟩) = ψ ⟨j, hj⟩ := by
      rw [← hθ, hw1]; rfl
    have h2 : ψ ((ι w ⟨j, hj⟩) * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hOker _).mp h2
    simpa [hι] using h3

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
