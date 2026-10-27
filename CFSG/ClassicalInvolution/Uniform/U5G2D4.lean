module

public import CFSG.ClassicalInvolution.Uniform.U5Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Abstract

theorem compGen3_of_pairGen (c : Q3.CompData)
    (hinj : ∀ (X : Type) [Group X] (ψ : c.G →* X), ψ.ker ≤ Subgroup.center c.G →
      Function.Injective ψ)
    (hpair : ∀ u v : c.G, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v → u * v = v * u →
      Subgroup.centralizer ({u} : Set c.G) ⊔ Subgroup.centralizer ({v} : Set c.G) = ⊤) :
    CompGen3 c := by
  intro X _ _ ψ hker R₁ _ R₂ _ _ _ _ _ _ _ z hz A hA hAKJ hzA
  have hψ : Function.Injective ψ := hinj X ψ hker
  have hA4 : Nat.card A = 4 := by simpa using hA.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h := hA.2 (x * y) (A.mul_mem hx hy)
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA.2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA.2 y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxi, hyi]
  obtain ⟨a, haA, ha1, haz⟩ := thm5IH_exists_ne hA4 1 z
  have hrange : R₁.map ψ ⊔ R₂.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  obtain ⟨u₀, hu₀⟩ := MonoidHom.mem_range.mp (hrange (hAKJ hzA))
  obtain ⟨v₀, hv₀⟩ := MonoidHom.mem_range.mp (hrange (hAKJ haA))
  have hz1 : z ≠ 1 := hz.ne_one
  have hzz : z * z = 1 := hA.2 z hzA
  have haa : a * a = 1 := hA.2 a haA
  have hu2 : u₀ * u₀ = 1 := hψ (by rw [map_mul, hu₀, map_one, hzz])
  have hv2 : v₀ * v₀ = 1 := hψ (by rw [map_mul, hv₀, map_one, haa])
  have hu1 : u₀ ≠ 1 := fun h => hz1 (by rw [← hu₀, h, map_one])
  have hv1 : v₀ ≠ 1 := fun h => ha1 (by rw [← hv₀, h, map_one])
  have huv : u₀ ≠ v₀ := fun h => haz.symm (by rw [← hu₀, ← hv₀, h])
  have hcomm : u₀ * v₀ = v₀ * u₀ :=
    hψ (by rw [map_mul, map_mul, hu₀, hv₀]; exact hAc z hzA a haA)
  have hpair' := hpair u₀ v₀ hu2 hv2 hu1 hv1 huv hcomm
  set T : Subgroup X := ⨆ a' ∈ A, ⨆ (_ : a' ≠ 1),
    Subgroup.centralizer ({a'} : Set X) ⊓ ψ.range with hT
  have hle : ∀ (w : X) (u : c.G), w ∈ A → w ≠ 1 → ψ u = w →
      (Subgroup.centralizer ({u} : Set c.G)).map ψ ≤ T := by
    intro w u hw hw1 hu y hy
    obtain ⟨g, hg, rfl⟩ := hy
    have hgc : ψ g * w = w * ψ g := by
      rw [← hu, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
    have hS : Subgroup.centralizer ({w} : Set X) ⊓ ψ.range ≤ T :=
      le_iSup₂_of_le w hw (le_iSup_of_le hw1 le_rfl)
    exact hS ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgc, ⟨g, rfl⟩⟩
  rw [MonoidHom.range_eq_map, ← hpair', Subgroup.map_sup]
  exact sup_le (hle z u₀ hzA hz1 hu₀) (hle a v₀ haA ha1 hv₀)

end Abstract

section Models


@[expose] def G2NonToralGenerate3 : Prop :=
  ∀ z z' : (modelUniv .G2 0 3 1 Nat.prime_three).K, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 →
    z ≠ z' → z * z' = z' * z → ¬ G2D4Models.ToralPair (F := GaloisField 3 1) z z' →
      Subgroup.centralizer ({z} : Set (modelUniv .G2 0 3 1 Nat.prime_three).K) ⊔
        Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 3 1 Nat.prime_three).K) = ⊤

theorem g2_pairGen3 (h : G2NonToralGenerate3) (u v : (modelUniv .G2 0 3 1 Nat.prime_three).K)
    (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hcomm : u * v = v * u) :
    Subgroup.centralizer ({u} : Set (modelUniv .G2 0 3 1 Nat.prime_three).K) ⊔
      Subgroup.centralizer ({v} : Set (modelUniv .G2 0 3 1 Nat.prime_three).K) = ⊤ := by
  by_cases hT : G2D4Models.ToralPair (F := GaloisField 3 1) u v
  · exact G2D4Models.centralizer_sup_eq_top_of_toralPair_model (p := 3) (e := 1) (by norm_num)
      ⟨Nat.prime_three, le_refl 1, rfl, by norm_num⟩ hT
  · exact h u v hu hv hu1 hv1 huv hcomm hT

theorem g2D4Gen3_of_g2NonToral (h : G2NonToralGenerate3) : G2D4Gen3 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  intro t k ht hfund hadm
  have he : 1 ≤ 1 := le_refl 1
  rcases ht with rfl | rfl
  · obtain ⟨hk, -⟩ := hadm.2.2
    subst hk
    refine compGen3_of_pairGen _ ?_ ?_
    · intro X _ ψ hker
      exact RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inl rfl) 0 he ψ hker
    · exact g2_pairGen3 h
  · have hk : k = 0 := hadm.2.2
    subst hk
    refine compGen3_of_pairGen _ ?_ ?_
    · intro X _ ψ hker
      exact RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr rfl) 0 he ψ hker
    · intro u v hu hv hu1 hv1 huv hcomm
      exact G2D4Models.sup_centralizer_eq_top_model_td4 hp2 hadm hu hv hu1 hv1 huv hcomm

theorem thm5NonGenBelowU_of_twin_and_g2 (hTwin : TwinGen3) (hG2 : G2NonToralGenerate3) {n : ℕ}
    (hn : CITBelowT (.sl2 3 1) n) : Q3.Disc3.Thm5NonGenBelowU n :=
  thm5NonGenBelowU_of_modelFacts hTwin (g2D4Gen3_of_g2NonToral hG2) hn

end Models

end CFSG.ClassicalInvolution.Uniform
