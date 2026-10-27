module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagKill

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Torus


@[expose] def diagG {K : Type} [Field K] [Finite K] (g0 : ModGL Tag.E6 (AlgebraicClosure K))
    (c : ModGL Tag.E6 K) : ModGL Tag.E6 K →* ModGL Tag.E6 (AlgebraicClosure K) :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (MulAut.conj c).toMonoidHom)

theorem diagG_apply {K : Type} [Field K] [Finite K] (g0 : ModGL Tag.E6 (AlgebraicClosure K))
    (c x : ModGL Tag.E6 K) :
    diagG g0 c x = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * x * c⁻¹ : ModGL Tag.E6 K) * g0 := by
  simp [diagG, MulAut.conj_apply]

theorem diag_exponent_gen {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (c : ModGL Tag.E6 K)
    (S : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))
    (hS : S ≤ torusGroup Tag.E6 (AlgebraicClosure K))
    (hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K)) (c * x * c⁻¹ : ModGL Tag.E6 K) ∈
      S.map (MulAut.conj g0).toMonoidHom)
    (ω : (AlgebraicClosure K)ˣ) (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {x : ModGL Tag.E6 K} (hx : x ∈ A) (hx3 : x ^ 3 = 1) :
    ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E6 a = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c * x * c⁻¹ : ModGL Tag.E6 K) * g0 ∧
      ∃ k : Fin Tag.E6.rank → ℕ, ∀ i, a i = ω ^ k i := by
  obtain ⟨t, ht, hte⟩ := hc x hx
  have hdiag : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * x * c⁻¹ : ModGL Tag.E6 K) * g0 = t := by
    rw [← hte]
    simp [MulAut.conj_apply, mul_assoc]
  have htor : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := hS ht
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup htor
  have hx' : (c * x * c⁻¹ : ModGL Tag.E6 K) ^ 3 = 1 := by
    rw [conj_pow, hx3]
    group
  have hcube : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * x * c⁻¹ : ModGL Tag.E6 K) * g0) ^ 3 = 1 := by
    rw [show g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c * x * c⁻¹ : ModGL Tag.E6 K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c * x * c⁻¹ : ModGL Tag.E6 K) * (g0⁻¹)⁻¹ by rw [inv_inv], conj_pow, ← map_pow, hx',
      map_one]
    group
  have e1 : rootDiagUnit Tag.E6 (a ^ 3) = (rootDiagUnit Tag.E6 a) ^ 3 :=
    map_pow (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) a 3
  have e2 : rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) = 1 :=
    map_one (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))
  have h3 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
    rw [e1, ha, e2, ← hdiag]
    exact hcube
  have h4 : a ^ 3 = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h3
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun h4 i
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 3 = 1 → ∃ k : ℕ, b = ω ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 3 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hb'
    exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hk])⟩
  choose k hk using fun i => hpow (a i) (ha3 i)
  exact ⟨a, ha.trans hdiag.symm, k, hk⟩

theorem outer_kills_gen {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (hexp : ∀ x ∈ A, x ^ 3 = 1) (hcard : Nat.card A = 3 ^ 2)
    (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (c : ModGL Tag.E6 K)
    (S : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))
    (hS : S ≤ torusGroup Tag.E6 (AlgebraicClosure K))
    (hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K)) (c * x * c⁻¹ : ModGL Tag.E6 K) ∈
      S.map (MulAut.conj g0).toMonoidHom)
    (ω : (AlgebraicClosure K)ˣ) (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {x₁ : ModGL Tag.E6 K} (hx₁ : x₁ ∈ A) (hx₁1 : x₁ ≠ 1)
    (a₁ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (ha₁ : rootDiagUnit Tag.E6 a₁ = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * x₁ * c⁻¹ : ModGL Tag.E6 K) * g0)
    (k₁ : Fin Tag.E6.rank → ℕ) (hk₁ : ∀ i, a₁ i = ω ^ k₁ i)
    (hout : ¬ (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₁ i : ℤ)) :
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧
      ∀ y ∈ A, ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit Tag.E6 a = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (c * y * c⁻¹ : ModGL Tag.E6 K) * g0 ∧ rootChar a α = 1 := by
  obtain ⟨x₂, hx₂, hx₂n⟩ := exists_mem_not_mem_zpowers A hcard hx₁ (hexp x₁ hx₁) hx₁1
  have hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL Tag.E6 K)) = A :=
    closure_pair_eq_of_not_mem A hcard hx₁ hx₂ (hexp x₁ hx₁) hx₁1 hx₂n
  obtain ⟨a₂, ha₂, k₂, hk₂⟩ := diag_exponent_gen g0 c S hS hc ω hω hx₂ (hexp x₂ hx₂)
  obtain ⟨α, hα, h1, h2⟩ := e6_diagPair_killed k₁ k₂ (Or.inl hout)
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hr₁ : rootChar a₁ α = 1 := rootChar_eq_one_of_dvd hω3 hk₁ h1
  have hr₂ : rootChar a₂ α = 1 := rootChar_eq_one_of_dvd hω3 hk₂ h2
  have hker : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, rootChar a α = 1 →
      a ∈ (rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker :=
    fun a h => MonoidHom.mem_ker.2 (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from h)
  set Sg : Subgroup (ModGL Tag.E6 K) :=
    ((rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))).comap (diagG g0 c) with hSg
  have hmem : ∀ (x : ModGL Tag.E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit Tag.E6 a = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c * x * c⁻¹ : ModGL Tag.E6 K) * g0 → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hr
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, hker a hr, ?_⟩)
    rw [diagG_apply]
    exact hax
  have hx₁S : x₁ ∈ Sg := hmem x₁ a₁ ha₁ hr₁
  have hx₂S : x₂ ∈ Sg := hmem x₂ a₂ ha₂ hr₂
  have hAS : A ≤ Sg := by
    rw [← hgen]
    refine (Subgroup.closure_le Sg).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hx₁S
    · exact hx₂S
  refine ⟨α, hα, fun y hy => ?_⟩
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hy))
  refine ⟨a, ?_, ?_⟩
  · rw [diagG_apply] at hay
    exact hay
  · exact (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from MonoidHom.mem_ker.1 ha)

end Torus

end CFSG.LieType.SeitzGeneration.ExcWideThree
