module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperRad

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_stable_compl_su [Finite K] {A : Subgroup (SUid σ n)} (hA : (Nat.card A : K) ≠ 0)
    {X : Submodule K (Fin n → K)} (hX : ∀ g ∈ A, ∀ x ∈ X, g • x ∈ X) :
    ∃ X' : Submodule K (Fin n → K), IsCompl X X' ∧ ∀ g ∈ A, ∀ x ∈ X', g • x ∈ X' := by
  have : NeZero (Nat.card A : K) := ⟨hA⟩
  let ρ : Representation K A (Fin n → K) :=
    { toFun := fun h => actU σ n h.1
      map_one' := map_one _
      map_mul' := fun a b => map_mul (actU σ n) a.1 b.1 }
  let τ : Subrepresentation ρ := ⟨X, fun g v hv => hX g g.2 v hv⟩
  obtain ⟨τ', hτ'⟩ := exists_isCompl τ
  refine ⟨τ'.toSubmodule, ⟨?_, ?_⟩, fun x hx w hw => τ'.apply_mem_toSubmodule ⟨x, hx⟩ hw⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hτ'.1)
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hτ'.2)
    exact this

theorem stable_hermOrth {A : Subgroup (SUid σ n)} {X : Submodule K (Fin n → K)}
    (hX : ∀ g ∈ A, ∀ x ∈ X, g • x ∈ X) :
    ∀ g ∈ A, ∀ v ∈ hermOrth σ X, g • v ∈ hermOrth σ X := fun g hg _ hv =>
  smul_mem_hermOrth (e := g) (fun w hw => hX g⁻¹ (A.inv_mem hg) w hw) hv

theorem exists_opposite [Finite K] (hσ : IsUnitaryInvolution σ) {A : Subgroup (SUid σ n)}
    (hA : (Nat.card A : K) ≠ 0) {W : Submodule K (Fin n → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) (hWs : ∀ g ∈ A, ∀ w ∈ W, g • w ∈ W) :
    ∃ W' : Submodule K (Fin n → K), (∀ x ∈ W', ∀ y ∈ W', herm σ x y = 0) ∧
      IsCompl (hermOrth σ W) W' ∧ ∀ g ∈ A, ∀ w ∈ W', g • w ∈ W' := by
  classical
  have hWP : ∀ w ∈ W, w ∈ hermOrth σ W := fun w hw x hx => hW x hx w hw
  obtain ⟨C₀, hC₀, hC₀s⟩ := exists_stable_compl_su hA (stable_hermOrth hWs)
  have hC₀P := stable_hermOrth hC₀s
  have hfin1 := finrank_hermOrth_add σ hσ.invol W
  have hfin2 := finrank_hermOrth_add σ hσ.invol C₀
  have hfin3 : Module.finrank K (hermOrth σ W) + Module.finrank K C₀ = n := by
    simpa using Submodule.finrank_add_eq_of_isCompl hC₀
  have hdisj : Disjoint W (hermOrth σ C₀) := by
    rw [Submodule.disjoint_def]
    intro w hw hwC
    refine eq_zero_of_herm σ fun y => ?_
    have hy : y ∈ hermOrth σ W ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    rw [herm_add_right, hu w hw, herm_eq_zero_comm σ hσ.invol (hwC c hc), add_zero]
  have hWC : IsCompl W (hermOrth σ C₀) := by
    refine (Submodule.isCompl_iff_disjoint W (hermOrth σ C₀) ?_).2 hdisj
    simp only [Module.finrank_fin_fun]
    omega
  set P : (Fin n → K) →ₗ[K] (Fin n → K) := W.projection (hermOrth σ C₀) hWC with hPdef
  have hP1 : ∀ v, P v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hP2 : ∀ v, v - P v ∈ hermOrth σ C₀ := fun v => Submodule.sub_projection_mem hWC v
  have hPW : ∀ w ∈ W, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  have hPC : ∀ z ∈ hermOrth σ C₀, P z = 0 := fun z hz =>
    Submodule.projection_apply_of_mem_right hWC hz
  have hPg : ∀ g ∈ A, ∀ v, P (g • v) = g • P v := by
    intro g hg v
    have hv : g • v = g • P v + g • (v - P v) := by rw [← smul_add]; congr 1; abel
    rw [hv, map_add, hPW _ (hWs g hg _ (hP1 v)), hPC _ (hC₀P g hg _ (hP2 v)), add_zero]
  obtain ⟨κ, hκ⟩ := hσ.trace_surj 1 (map_one σ)
  have hcc : ∀ c₁ ∈ C₀, ∀ c₂ ∈ C₀, herm σ c₁ (P c₂) = herm σ c₁ c₂ := by
    intro c₁ hc₁ c₂ _
    have := hP2 c₂ c₁ hc₁
    rw [herm_sub_right, sub_eq_zero] at this
    exact this.symm
  refine ⟨C₀.map (LinearMap.id - κ • P), ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    have e1 := hcc c₁ hc₁ c₂ hc₂
    have e2 : herm σ (P c₁) c₂ = herm σ c₁ c₂ := by
      rw [herm_conj σ hσ.invol c₂ (P c₁), hcc c₂ hc₂ c₁ hc₁, ← herm_conj σ hσ.invol c₂ c₁]
    have e3 := hW _ (hP1 c₁) _ (hP1 c₂)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, herm_sub_left,
      herm_sub_right, herm_smul_left, herm_smul_right, e1, e2, e3]
    linear_combination (-(herm σ c₁ c₂)) * hκ
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro x ⟨hx, c, hc, rfl⟩
    have hcP : c ∈ hermOrth σ W := by
      have h1 : c = (c - κ • P c) + κ • P c := by abel
      rw [h1]
      exact (hermOrth σ W).add_mem (by simpa using hx)
        ((hermOrth σ W).smul_mem _ (hWP _ (hP1 c)))
    have hc0 : c = 0 := Submodule.disjoint_def.1 hC₀.disjoint c hcP hc
    simp [hc0]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ hermOrth σ W ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    refine Submodule.mem_sup.2 ⟨u + κ • P c, ?_, c - κ • P c, ⟨c, hc, rfl⟩, by abel⟩
    exact (hermOrth σ W).add_mem hu ((hermOrth σ W).smul_mem _ (hWP _ (hP1 c)))
  · rintro g hg _ ⟨c, hc, rfl⟩
    refine ⟨g • c, hC₀s g hg c hc, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, smul_sub,
      hPg g hg, smul_comm g κ (P c)]

end CFSG.LieType.SeitzGeneration
