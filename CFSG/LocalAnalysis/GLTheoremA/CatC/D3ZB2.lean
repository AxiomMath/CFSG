module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZB1
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL9

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Pointwise


section NF

variable {K : Type} [Field K] [Finite K]

theorem exists_sylow_nf {n : ℕ} (hK : Nat.card K = 3 ^ n) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) {S : Sylow 3 (D4Model K)}
    (hSt : (S : Subgroup (D4Model K)).map t.toMonoidHom = S) :
    ∃ (ψ : ↥(adjointGroup Tag.D4 K) ≃* D4Model K) (x : ↥(adjointGroup Tag.D4 K))
      (α' : MulAut ↥(adjointGroup Tag.D4 K)) (g : ↥(adjointGroup Tag.D4 K))
      (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ),
      (∀ y : ↥(adjointGroup Tag.D4 K), ψ y ∈ (S : Subgroup (D4Model K)) ↔ x⁻¹ * y * x ∈ unitU K) ∧
      (∀ w : ↥(adjointGroup Tag.D4 K), ψ (x * α' w * x⁻¹) = t (ψ (x * w * x⁻¹))) ∧
      α' ^ 3 = 1 ∧ (ε = 1 ∨ ε = 2) ∧
      α' = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∧
      (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
  classical
  haveI := charP_three_of_card hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (D4Model K) := inferInstance
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : adjointGroup Tag.D4 K ≃* D4Model K,
      ψ = coordinatePlusWitnessEquiv K (isoAdj K).symm := ⟨_, rfl⟩
  obtain ⟨S', hS'coe⟩ : ∃ S' : Sylow 3 ↥(adjointGroup Tag.D4 K),
      (S' : Subgroup ↥(adjointGroup Tag.D4 K)) =
        (S : Subgroup (D4Model K)).map ψ.symm.toMonoidHom :=
    ⟨Sylow.mapSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective S, Sylow.coe_mapSurjective _ _⟩
  have hS'mem : ∀ y, y ∈ (S' : Subgroup ↥(adjointGroup Tag.D4 K)) ↔
      ψ y ∈ (S : Subgroup (D4Model K)) := by
    intro y
    rw [hS'coe]
    constructor
    · rintro ⟨s, hs, rfl⟩
      show ψ (ψ.symm s) ∈ (S : Subgroup (D4Model K))
      rw [ψ.apply_symm_apply]; exact hs
    · intro h
      exact ⟨ψ y, h, by simp⟩
  obtain ⟨x, hmemS⟩ := exists_conj_to_U S'
  have hmem : ∀ y : ↥(adjointGroup Tag.D4 K), ψ y ∈ (S : Subgroup (D4Model K)) ↔
      x⁻¹ * y * x ∈ unitU K := fun y => (hS'mem y).symm.trans (hmemS y)
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(adjointGroup Tag.D4 K), α = MulAut.congr ψ.symm t := ⟨_, rfl⟩
  have hψα : ∀ w, ψ (α w) = t (ψ w) := by
    intro w; simp [hαdef, MulAut.congr_apply]
  have hSα : (S' : Subgroup ↥(adjointGroup Tag.D4 K)).map α.toMonoidHom = S' := by
    refine d3z_map_eq_of_forall_mem _ α fun y hy => ?_
    rw [hS'mem] at hy ⊢
    rw [hψα]
    have := Subgroup.mem_map_of_mem t.toMonoidHom hy
    rwa [hSt] at this
  have hUα' := stable_of_sylow_conj hmemS hSα
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut ↥(adjointGroup Tag.D4 K),
      α' = (MulAut.conj x)⁻¹ * α * MulAut.conj x := ⟨_, rfl⟩
  rw [← hα'def] at hUα'
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, ht3, map_one]
  have hα'3 : α' ^ 3 = 1 := by
    have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := α) (i := 3)
    rw [inv_inv] at h
    rw [hα'def, h, hα3]; group
  have hα'app : ∀ w, α' w = x⁻¹ * α (x * w * x⁻¹) * x := by
    intro w; simp [hα'def, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hαx : ∀ w, α (x * w * x⁻¹) = x * α' w * x⁻¹ := by
    intro w; rw [hα'app]; group
  obtain ⟨g, a, σ, ε, hε3, hα'eq, hgB⟩ := exists_normal_form_borel α' hα'3 hUα'
  have ht₂eq : MulAut.congr ψ α' = (MulAut.conj (ψ x))⁻¹ * t * MulAut.conj (ψ x) := by
    rw [hα'def, map_mul, map_mul, map_inv, d3f_congr_conj, hαdef, congr_congr_symm]
  have ht₂3 : (MulAut.congr ψ α') ^ 3 = 1 := by rw [← map_pow, hα'3, map_one]
  have ht₂E : MulAut.congr ψ α' ∉ D4Img K := by
    intro h
    apply htE
    have hc : MulAut.conj (ψ x) ∈ D4Img K := inner_le_D4Img ⟨ψ x, rfl⟩
    have e : t = MulAut.conj (ψ x) * MulAut.congr ψ α' * (MulAut.conj (ψ x))⁻¹ := by
      rw [ht₂eq]; group
    rw [e]
    exact mul_mem (mul_mem hc h) (inv_mem hc)
  have hε0 : ε ≠ 0 := by
    refine eps_ne_zero hK ht₂3 ht₂E g a σ ε ?_
    rw [← hψdef, hα'eq]
  refine ⟨ψ, x, α', g, a, σ, ε, hmem, fun w => ?_, hα'3, by omega, hα'eq, hgB⟩
  rw [← hαx w]
  exact hψα _

theorem four_group_borel {n : ℕ} (hK : Nat.card K = 3 ^ n) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) {S : Sylow 3 (D4Model K)}
    (hSt : (S : Subgroup (D4Model K)).map t.toMonoidHom = S) {y₀ y₁ : D4Model K}
    (hy₀S : y₀ ∈ Subgroup.normalizer ((S : Subgroup (D4Model K)) : Set (D4Model K)))
    (hy₁S : y₁ ∈ Subgroup.normalizer ((S : Subgroup (D4Model K)) : Set (D4Model K)))
    (hy₀2 : y₀ * y₀ = 1) (hy₁2 : y₁ * y₁ = 1) (hcomm : y₀ * y₁ = y₁ * y₀) (hy₀1 : y₀ ≠ 1)
    (hy₁1 : y₁ ≠ 1) (hne : y₀ ≠ y₁) (hty₀ : t y₀ = y₀) (hty₁ : t y₁ = y₁)
    {A : Subgroup (D4Model K)} (hAS : A ≤ (S : Subgroup (D4Model K)))
    (hA₀ : ∀ a ∈ A, y₀ * a * y₀⁻¹ = a) (hA₁ : ∀ a ∈ A, y₁ * a * y₁⁻¹ = a) : A = ⊥ := by
  classical
  haveI := charP_three_of_card hK
  haveI : Finite (D4Model K) := inferInstance
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  obtain ⟨ψ, x, α', g, a, σ, ε, hmem, hψα, hα'3, hε, hα'eq, hgB⟩ := exists_sylow_nf hK ht3 htE hSt
  obtain ⟨θ, hθdef⟩ : ∃ θ : D4Model K →* ↥(adjointGroup Tag.D4 K),
      θ = ((MulAut.conj x)⁻¹).toMonoidHom.comp ψ.symm.toMonoidHom := ⟨_, rfl⟩
  have hθapp : ∀ w, θ w = x⁻¹ * ψ.symm w * x := by
    intro w; rw [hθdef]; simp [MulAut.conj_inv_apply]
  have hθinj : Function.Injective θ := by
    rw [hθdef]
    exact ((MulAut.conj x)⁻¹).injective.comp ψ.symm.injective
  have hψθ : ∀ w, ψ (x * θ w * x⁻¹) = w := by
    intro w
    rw [hθapp, show x * (x⁻¹ * ψ.symm w * x) * x⁻¹ = ψ.symm w by group, ψ.apply_symm_apply]
  have hθψ : ∀ y : ↥(adjointGroup Tag.D4 K), θ (ψ (x * y * x⁻¹)) = y := by
    intro y
    rw [hθapp, ψ.symm_apply_apply]; group
  have hstab : ∀ {y : D4Model K},
      y ∈ Subgroup.normalizer ((S : Subgroup (D4Model K)) : Set (D4Model K)) →
        ((unitU K).map (MulAut.conj (θ y)).toMonoidHom = unitU K) := by
    intro y hy
    refine d3z_map_eq_of_forall_mem _ (MulAut.conj (θ y)) fun u hu => ?_
    have hu' : ψ (x * u * x⁻¹) ∈ (S : Subgroup (D4Model K)) := by
      rw [hmem]
      have e : x⁻¹ * (x * u * x⁻¹) * x = u := by group
      rw [e]; exact hu
    have h1 : y * ψ (x * u * x⁻¹) * y⁻¹ ∈ (S : Subgroup (D4Model K)) :=
      (Subgroup.mem_normalizer_iff.1 hy _).1 hu'
    have e2 : ψ (x * (MulAut.conj (θ y) u) * x⁻¹) = y * ψ (x * u * x⁻¹) * y⁻¹ := by
      have : x * (MulAut.conj (θ y) u) * x⁻¹ =
          (x * θ y * x⁻¹) * (x * u * x⁻¹) * (x * θ y * x⁻¹)⁻¹ := by
        simp only [MulAut.conj_apply]; group
      rw [this, map_mul, map_mul, map_inv, hψθ]
    have h3 : ψ (x * (MulAut.conj (θ y) u) * x⁻¹) ∈ (S : Subgroup (D4Model K)) := by
      rw [e2]; exact h1
    rw [hmem] at h3
    have e : x⁻¹ * (x * (MulAut.conj (θ y) u) * x⁻¹) * x = MulAut.conj (θ y) u := by group
    rw [e] at h3
    exact h3
  have hαfix : ∀ {y : D4Model K}, t y = y → α' (θ y) = θ y := by
    intro y hy
    have h1 := hψα (θ y)
    rw [hψθ, hy] at h1
    have h2 : x * α' (θ y) * x⁻¹ = x * θ y * x⁻¹ := by
      apply ψ.injective
      rw [h1, hψθ]
    have := congrArg (fun z => x⁻¹ * z * x) h2
    simpa [mul_assoc] using this
  have hgB' : (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := hgB
  have hβ : ∀ z : ↥(adjointGroup Tag.D4 K),
      ((α' z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        (g : ModGL Tag.D4 K) * d4F K a σ ε (z : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K)⁻¹ :=
    fun z => by rw [hα'eq]; rfl
  have hsg : BorelScalar (g : ModGL Tag.D4 K) := borelScalar_of_mem_borelGroup hgB'
  let la := d4LayerAct hsg a σ ε hβ
  have hr : ∀ k δ, (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1 := fun k δ => rfl
  have hA'U : A.map θ ≤ (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) := by
    rintro _ ⟨w, hw, rfl⟩
    have : ψ (x * θ w * x⁻¹) ∈ (S : Subgroup (D4Model K)) := by
      rw [hψθ]; exact hAS hw
    have := (hmem _).1 this
    have e : x⁻¹ * (x * θ w * x⁻¹) * x = θ w := by group
    rw [e] at this
    exact this
  have hmain := four_group_borel_c la hε hr (g₁ := θ y₀) (g₂ := θ y₁)
    (by rw [← map_mul, hy₀2, map_one]) (by rw [← map_mul, hy₁2, map_one])
    (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hy₀1 (hθinj (by rw [h, map_one])))
    (fun h => hy₁1 (hθinj (by rw [h, map_one])))
    (fun h => hne (hθinj h)) (hstab hy₀S) (hstab hy₁S) (hαfix hty₀) (hαfix hty₁)
    (A := A.map θ) hA'U
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul, hA₀ w hw])
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul, hA₁ w hw])
  rw [Subgroup.card_map_of_injective hθinj] at hmain
  exact Subgroup.card_eq_one.1 hmain

end NF

end CFSG.LocalAnalysis.GLTheoremA
