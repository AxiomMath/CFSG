module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeTriple
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6RankOne
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum d4 p k)

section OrbitVec

variable {D}

theorem orbitVec_succ_of_theta (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) (j : ℕ) :
    D.orbitVec O (j + 1) = rho (D.orbitVec O j) :=
  toReal_injective ((D.theta_orbitVec hO j).symm.trans (hθ _))

theorem orbitVec_eq_rho_of_theta (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitVec O 0 = orbitRoot O ∧ D.orbitVec O 1 = rho (orbitRoot O) ∧
      D.orbitVec O 2 = rho (rho (orbitRoot O)) := by
  have h0 : D.orbitVec O 0 = orbitRoot O := D.orbitVec_zero
  have h1 : D.orbitVec O 1 = rho (orbitRoot O) := by
    rw [orbitVec_succ_of_theta hθ hO 0, h0]
  exact ⟨h0, h1, by rw [orbitVec_succ_of_theta hθ hO 1, h1]⟩

theorem rho_orbitRoot_ne_of_orbitCard_eq_three (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) (h3 : orbitCard O = 3) :
    rho (orbitRoot O) ≠ orbitRoot O := by
  obtain ⟨h0, h1, -⟩ := orbitVec_eq_rho_of_theta hθ hO
  intro h
  have := D.orbitVec_injOn hO (i := 1) (j := 0) (by omega) (by omega) (h1.trans (h.trans h0.symm))
  omega

end OrbitVec

section OrbitXY

variable {D}

theorem orbitX_eq_of_orbitCard_eq_three (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) (h3 : orbitCard O = 3) (c : D.orbitField O) :
    D.orbitX O c =
      pinnedX d4 k (orbitRoot O) ((pinnedData d4 (orbitRoot O)).2.2 • ((c : k) ^ D.q ^ 0)) *
        pinnedX d4 k (rho (orbitRoot O))
          ((pinnedData d4 (rho (orbitRoot O))).2.2 • ((c : k) ^ D.q ^ 1)) *
        pinnedX d4 k (rho (rho (orbitRoot O)))
          ((pinnedData d4 (rho (rho (orbitRoot O)))).2.2 • ((c : k) ^ D.q ^ 2)) := by
  obtain ⟨h0, h1, h2⟩ := orbitVec_eq_rho_of_theta hθ hO
  rw [show D.orbitX O c = D.orbitMap O (uSL c) from rfl, orbitMap_eq_prod, h3,
    show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    D.orbitFactor_uSL, rootSL2_uSL_eq, h0, h1, h2, mul_assoc]

theorem orbitY_eq_of_orbitCard_eq_three (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ ε₀ ε₁ ε₂ : k, ε₀ * ε₀ = 1 ∧ ∀ c : D.orbitField O, orbitCard O = 3 →
      D.orbitY O c =
        pinnedX d4 k (-orbitRoot O) (ε₀ * ((c : k) ^ D.q ^ 0)) *
          pinnedX d4 k (rho (-orbitRoot O)) (ε₁ * ((c : k) ^ D.q ^ 1)) *
          pinnedX d4 k (rho (rho (-orbitRoot O))) (ε₂ * ((c : k) ^ D.q ^ 2)) := by
  obtain ⟨h0, h1, h2⟩ := orbitVec_eq_rho_of_theta hθ hO
  have hβ : IsRoot d4 (orbitRoot O) := (D.orbitRoot_mem_kernelRoots hO).1
  have hβ1 : IsRoot d4 (rho (orbitRoot O)) := isRoot_rho hβ
  have hβ2 : IsRoot d4 (rho (rho (orbitRoot O))) := isRoot_rho hβ1
  obtain ⟨ε₀, hε₀, hv₀⟩ := exists_rootSL2_vSL_eq (K := k) hβ
  obtain ⟨ε₁, -, hv₁⟩ := exists_rootSL2_vSL_eq (K := k) hβ1
  obtain ⟨ε₂, -, hv₂⟩ := exists_rootSL2_vSL_eq (K := k) hβ2
  refine ⟨ε₀, ε₁, ε₂, hε₀, fun c h3 => ?_⟩
  rw [show D.orbitY O c = D.orbitMap O (vSL c) from rfl, orbitMap_eq_prod, h3,
    show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    D.orbitFactor_vSL, h0, h1, h2, mul_assoc, hv₀, hv₁, hv₂]
  rfl

theorem exists_conj_orbitX (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) (h3 : orbitCard O = 3)
    (s : Fin d4.rank → kˣ) :
    ∃ α₀ : k, α₀ ≠ 0 ∧ ∀ c : D.orbitField O, ∃ b d : k,
      (rootDiagUnit d4 s)⁻¹ * D.orbitX O c * rootDiagUnit d4 s =
        pinnedX d4 k (orbitRoot O) (α₀ * c) * pinnedX d4 k (rho (orbitRoot O)) b *
          pinnedX d4 k (rho (rho (orbitRoot O))) d := by
  have hβ : IsRoot d4 (orbitRoot O) := (D.orbitRoot_mem_kernelRoots hO).1
  have hβ1 : IsRoot d4 (rho (orbitRoot O)) := isRoot_rho hβ
  have hβ2 : IsRoot d4 (rho (rho (orbitRoot O))) := isRoot_rho hβ1
  have hsgn : ∀ γ : Fin d4.rank → ℤ, (((pinnedData d4 γ).2.2 : ℤ) : k) ≠ 0 := fun γ => by
    rcases pinnedSign_eq d4 γ with h | h <;> rw [h] <;> simp
  refine ⟨(rootChar s⁻¹ (orbitRoot O) : k) * (((pinnedData d4 (orbitRoot O)).2.2 : ℤ) : k),
    mul_ne_zero (rootChar s⁻¹ (orbitRoot O)).ne_zero (hsgn _), fun c => ⟨
    (rootChar s⁻¹ (rho (orbitRoot O)) : k) *
      ((pinnedData d4 (rho (orbitRoot O))).2.2 • ((c : k) ^ D.q ^ 1)),
    (rootChar s⁻¹ (rho (rho (orbitRoot O))) : k) *
      ((pinnedData d4 (rho (rho (orbitRoot O)))).2.2 • ((c : k) ^ D.q ^ 2)), ?_⟩⟩
  have hconj : ∀ a b c : ModGL d4 k, (rootDiagUnit d4 s)⁻¹ * (a * b * c) * rootDiagUnit d4 s =
      ((rootDiagUnit d4 s)⁻¹ * a * rootDiagUnit d4 s) *
        ((rootDiagUnit d4 s)⁻¹ * b * rootDiagUnit d4 s) *
        ((rootDiagUnit d4 s)⁻¹ * c * rootDiagUnit d4 s) := fun a b c => by group
  have e0 : (rootChar s⁻¹ (orbitRoot O) : k) *
      ((pinnedData d4 (orbitRoot O)).2.2 • ((c : k) ^ D.q ^ 0)) =
      ((rootChar s⁻¹ (orbitRoot O) : k) * (((pinnedData d4 (orbitRoot O)).2.2 : ℤ) : k)) * c := by
    rw [zsmul_eq_mul, pow_zero, pow_one, mul_assoc]
  rw [orbitX_eq_of_orbitCard_eq_three hθ hO h3 c, hconj, rootDiagUnit_inv_mul_pinnedX_mul s hβ,
    rootDiagUnit_inv_mul_pinnedX_mul s hβ1, rootDiagUnit_inv_mul_pinnedX_mul s hβ2, e0]

theorem exists_conj_orbitY (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ))
    {O : Set (Fin d4.rank → ℤ)} (hO : O ∈ D.orbits) (h3 : orbitCard O = 3)
    (s : Fin d4.rank → kˣ) :
    ∃ δ₀ : k, δ₀ ≠ 0 ∧ ∀ c : D.orbitField O, ∃ b d : k,
      (rootDiagUnit d4 s)⁻¹ * D.orbitY O c * rootDiagUnit d4 s =
        pinnedX d4 k (-orbitRoot O) (δ₀ * c) * pinnedX d4 k (rho (-orbitRoot O)) b *
          pinnedX d4 k (rho (rho (-orbitRoot O))) d := by
  obtain ⟨ε₀, ε₁, ε₂, hε₀, hY⟩ := orbitY_eq_of_orbitCard_eq_three hθ hO
  have hβ : IsRoot d4 (orbitRoot O) := (D.orbitRoot_mem_kernelRoots hO).1
  have hβ' : IsRoot d4 (-orbitRoot O) := IsRoot.neg hβ
  have hβ1 : IsRoot d4 (rho (-orbitRoot O)) := isRoot_rho hβ'
  have hβ2 : IsRoot d4 (rho (rho (-orbitRoot O))) := isRoot_rho hβ1
  have hε0 : ε₀ ≠ 0 := fun h => by
    rw [h, zero_mul] at hε₀
    exact zero_ne_one hε₀
  refine ⟨(rootChar s⁻¹ (-orbitRoot O) : k) * ε₀,
    mul_ne_zero (rootChar s⁻¹ (-orbitRoot O)).ne_zero hε0, fun c => ⟨
    (rootChar s⁻¹ (rho (-orbitRoot O)) : k) * (ε₁ * ((c : k) ^ D.q ^ 1)),
    (rootChar s⁻¹ (rho (rho (-orbitRoot O))) : k) * (ε₂ * ((c : k) ^ D.q ^ 2)), ?_⟩⟩
  have hconj : ∀ a b c : ModGL d4 k, (rootDiagUnit d4 s)⁻¹ * (a * b * c) * rootDiagUnit d4 s =
      ((rootDiagUnit d4 s)⁻¹ * a * rootDiagUnit d4 s) *
        ((rootDiagUnit d4 s)⁻¹ * b * rootDiagUnit d4 s) *
        ((rootDiagUnit d4 s)⁻¹ * c * rootDiagUnit d4 s) := fun a b c => by group
  have e0 : (rootChar s⁻¹ (-orbitRoot O) : k) * (ε₀ * ((c : k) ^ D.q ^ 0)) =
      ((rootChar s⁻¹ (-orbitRoot O) : k) * ε₀) * c := by
    rw [pow_zero, pow_one, mul_assoc]
  rw [hY c h3, hconj, rootDiagUnit_inv_mul_pinnedX_mul s hβ',
    rootDiagUnit_inv_mul_pinnedX_mul s hβ1, rootDiagUnit_inv_mul_pinnedX_mul s hβ2, e0]

end OrbitXY

section Fixed

variable {D}

theorem eq_fixedPointsIn_tripleGroup_sup_of_orbit {e : ℕ} (he : 1 ≤ e) (hDe : D.e = e)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (rho γ)) {O₀ : Set (Fin d4.rank → ℤ)}
    (hO₀ : O₀ ∈ D.orbits) (h3 : orbitCard O₀ = 3) (s : Fin d4.rank → kˣ)
    {J : Subgroup (ModGL d4 k)}
    (hJF : ∀ y ∈ J, frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) y = y)
    (hJ : ∀ y, y ∈ J.map (MulAut.conj (rootDiagUnit d4 s)).toMonoidHom ↔
      ∃ A, y = D.orbitMapHom hO₀ A) :
    ∃ β : Fin d4.rank → ℤ, IsRoot d4 β ∧ rho β ≠ β ∧
      J = fixedPointsIn (tripleGroup k β)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) ⊔
        fixedPointsIn (tripleGroup k (-β))
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) := by
  classical
  have hβ : IsRoot d4 (orbitRoot O₀) := (D.orbitRoot_mem_kernelRoots hO₀).1
  have hne : rho (orbitRoot O₀) ≠ orbitRoot O₀ :=
    rho_orbitRoot_ne_of_orbitCard_eq_three hθ hO₀ h3
  refine ⟨orbitRoot O₀, hβ, hne, ?_⟩
  have hqD : D.q = p ^ e := by
    change p ^ D.e = p ^ e
    rw [hDe]
  have hKf : Nat.card (D.orbitField O₀) = (p ^ e) ^ 3 := by
    rw [D.card_orbitField hO₀, h3, hqD]
  have hRfin : Finite (fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))) :=
    finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.D4 k)
  have hTle : ∀ γ, tripleGroup k γ ≤ adjointGroup d4 k := fun γ =>
    sup_le (sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup _))
      (rootSubgroup_le_adjointGroup _)
  have hfin : ∀ γ, Finite (fixedPointsIn (tripleGroup k γ)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))) := fun γ =>
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_inf_right _ (hTle γ)))
  have := hfin (orbitRoot O₀)
  have := hfin (-orbitRoot O₀)
  exact eq_fixedPointsIn_tripleGroup_sup_of_conj
    (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) hβ hne (rootDiagUnit d4 s)
    hJF hKf (card_fixedPointsIn_tripleGroup_le p he hβ hne)
    (card_fixedPointsIn_tripleGroup_le p he (IsRoot.neg hβ) (rho_neg_ne hne))
    (D.orbitMapHom hO₀) hJ (exists_conj_orbitX hθ hO₀ h3 s) (exists_conj_orbitY hθ hO₀ h3 s)

end Fixed

end CFSG.ClassicalInvolution.ModelFacts
