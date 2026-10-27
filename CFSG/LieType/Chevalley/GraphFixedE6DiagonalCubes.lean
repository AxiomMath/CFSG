module

public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.TorusCoordinates

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem list_prod_map_torusElt_hVec
    (l : List (Fin τ.rank)) (s : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    (((l.map fun i => torusElt τ K i (s i)).prod : ModGL τ K) :
      Module.End K (RootModule τ K)) (hVec τ K j) = hVec τ K j := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, torusElt_hVec]

theorem list_prod_map_torusElt_rootVec
    (l : List (Fin τ.rank)) (s : Fin τ.rank → Kˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (((l.map fun i => torusElt τ K i (s i)).prod : ModGL τ K) :
      Module.End K (RootModule τ K)) (rootVec τ K α) =
        (((l.map fun i => s i ^ (∑ j, τ.cartan i j * α j)).prod : Kˣ) : K) • rootVec τ K α := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, map_smul,
      torusElt_rootVec _ _ hα, smul_smul]
    rw [mul_comm]

theorem rootDiagUnit_pow (b : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ b ^ n = rootDiagUnit τ (b ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]

theorem rootChar_pow (b : Fin τ.rank → Kˣ) (n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (b ^ n) v = rootChar b v ^ n := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end Torus

@[expose] def cubeEntriesE6 : Fin TwistTag.E6.tag.rank → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
    ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]

@[expose] def cubeMatrixE6 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
  Matrix.of cubeEntriesE6

theorem cubeMatrixE6_mul_cartan :
    cubeMatrixE6 * TwistTag.E6.tag.cartan =
      3 • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) := by
  decide +kernel

theorem cartan_mul_cubeMatrixE6 :
    TwistTag.E6.tag.cartan * cubeMatrixE6 =
      3 • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) := by
  decide +kernel

theorem cubeMatrixE6_perm (i j : Fin TwistTag.E6.tag.rank) :
    cubeMatrixE6 (TwistTag.E6.perm i) (TwistTag.E6.perm j) = cubeMatrixE6 i j := by
  have h : ∀ i j : Fin TwistTag.E6.tag.rank,
      cubeEntriesE6 (TwistTag.E6.perm i) (TwistTag.E6.perm j) = cubeEntriesE6 i j := by
    decide +kernel
  exact h i j

theorem sum_cubeMatrixE6_mul_cartan (α : Fin TwistTag.E6.tag.rank → ℤ)
    (l : Fin TwistTag.E6.tag.rank) :
    ∑ i, cubeMatrixE6 l i * ∑ j, TwistTag.E6.tag.cartan i j * α j = 3 * α l := by
  have h := congrFun (Matrix.mulVec_mulVec α cubeMatrixE6 TwistTag.E6.tag.cartan) l
  rw [cubeMatrixE6_mul_cartan] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply] using h

variable {K : Type} [Field K]

@[expose] def cubeParam (b : Fin TwistTag.E6.tag.rank → Kˣ) (i : Fin TwistTag.E6.tag.rank) : Kˣ :=
  ∏ j, b j ^ cubeMatrixE6 j i

theorem cubeParam_perm {σ : K →+* K} {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i))
    (i : Fin TwistTag.E6.tag.rank) :
    cubeParam b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (cubeParam b i) := by
  unfold cubeParam
  rw [map_prod]
  simp only [map_zpow, ← hb]
  exact (Fintype.prod_equiv TwistTag.E6.perm (fun j => b (TwistTag.E6.perm j) ^ cubeMatrixE6 j i)
    (fun j => b j ^ cubeMatrixE6 j (TwistTag.E6.perm i))
    fun j => by rw [cubeMatrixE6_perm]).symm

theorem rootChar_pow_three (b : Fin TwistTag.E6.tag.rank → Kˣ) (α : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (b ^ 3) α = ((List.finRange TwistTag.E6.tag.rank).map fun i =>
      cubeParam b i ^ (∑ j, TwistTag.E6.tag.cartan i j * α j)).prod := by
  rw [← List.ofFn_eq_map, List.prod_ofFn, rootChar_pow]
  unfold cubeParam rootChar
  simp only [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [prod_zpow_eq_zpow_sum, sum_cubeMatrixE6_mul_cartan, ← zpow_natCast, ← zpow_mul, mul_comm]
  rfl

theorem rootDiagUnit_pow_three
    (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    rootDiagUnit TwistTag.E6.tag b ^ 3 = ((List.finRange TwistTag.E6.tag.rank).map fun i =>
      torusElt TwistTag.E6.tag K i (cubeParam b i)).prod := by
  rw [rootDiagUnit_pow]
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)
  · rw [list_prod_map_torusElt_hVec]
    exact rootDiag_hVec _ j
  · rw [list_prod_map_torusElt_rootVec _ _ hα, ← rootChar_pow_three]
    exact rootDiag_rootVec _ hα


theorem compatDiag_E6 {σ : K →+* K}
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ) :
    compatDiag TwistTag.E6 σ u = ![orbitFieldUnit TwistTag.E6 σ (u ⟨0, by decide⟩),
      orbitFieldUnit TwistTag.E6 σ (u ⟨3, by decide⟩),
      orbitFieldUnit TwistTag.E6 σ (u ⟨1, by decide⟩),
      orbitFieldUnit TwistTag.E6 σ (u ⟨2, by decide⟩),
      Units.map σ.toMonoidHom (orbitFieldUnit TwistTag.E6 σ (u ⟨1, by decide⟩)),
      Units.map σ.toMonoidHom (orbitFieldUnit TwistTag.E6 σ (u ⟨0, by decide⟩))] := by
  have e0 : TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have e1 : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have e2 : TwistTag.E6.orbitMin ⟨2, by decide⟩ = ⟨3, by decide⟩ := by decide
  have e3 : TwistTag.E6.orbitMin ⟨3, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p0 : TwistTag.E6.perm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
  have p2 : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  have h0 := compatDiag_orbitMin u ⟨0, by decide⟩
  have h1 := compatDiag_orbitMin u ⟨1, by decide⟩
  have h2 := compatDiag_orbitMin u ⟨2, by decide⟩
  have h3 := compatDiag_orbitMin u ⟨3, by decide⟩
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h5 := compatDiag_perm u ⟨0, by decide⟩
  have h4 := compatDiag_perm u ⟨2, by decide⟩
  rw [p0, h0] at h5
  rw [p2, h1] at h4
  funext i
  obtain ⟨n, hn⟩ := i
  have hn' : n < 6 := hn
  interval_cases n
  · exact h0
  · exact h3
  · exact h1
  · exact h2
  · exact h4
  · exact h5

theorem orbitField_E6_eq_top {p f : ℕ} (hp : p.Prime) {σ : K ≃+* K}
    (hK : Nat.card K = (p ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : (TwistTag.E6.orbit a).card = 2) :
    orbitField TwistTag.E6 K σ.toRingHom a = ⊤ := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  refine eq_top_iff.2 fun c _ => (mem_orbitField).2 ?_
  rw [ha, pow_two, RingHom.coe_mul, Function.comp_apply]
  change σ (σ c) = c
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem mem_orbitField_iff_of_card_eq_one {t : TwistTag} {σ : K →+* K}
    {a : Fin t.foldedTag.rank} (ha : (t.orbit a).card = 1) {c : K} :
    c ∈ orbitField t K σ a ↔ σ c = c := by
  rw [mem_orbitField, ha, pow_one]

theorem compatDiagAutHom_pow_eq_conj
    {t : TwistTag} {σ : K →+* K}
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) (n : ℕ)
    (h : rootDiagUnit t.tag (compatDiag t σ u) ^ n ∈ graphFixedRootGroup t K σ) :
    compatDiagAutHom t K σ u ^ n = MulAut.conj (⟨_, h⟩ : graphFixedRootGroup t K σ) := by
  have hD : rootDiagUnit t.tag (compatDiag t σ (u ^ n)) =
      rootDiagUnit t.tag (compatDiag t σ u) ^ n :=
    congrArg Subtype.val (map_pow (compatDiagHom t K σ) u n)
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [← map_pow, coe_compatDiagAutHom, hD, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem twisted_E6_compatible_diagonal_data
    {p f : ℕ} (K : Type) [Field K]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (∀ u, twistHom TwistTag.E6 K σ.toRingHom
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∧
    Function.Injective (compatDiagAutHom TwistTag.E6 K σ.toRingHom) ∧
    (∀ u g, ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) ∧
    (∀ u, ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).toMonoidHom =
        (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).toMonoidHom =
        (graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ∧
    (∀ u a c, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        orbitX TwistTag.E6 K σ.toRingHom a c *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
        orbitX TwistTag.E6 K σ.toRingHom a ((u a : orbitField TwistTag.E6 K σ.toRingHom a) * c)) ∧
    (∀ u a c, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        orbitY TwistTag.E6 K σ.toRingHom a c *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
        orbitY TwistTag.E6 K σ.toRingHom a
          (((u a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) * c)) ∧
    ∀ δ : K ≃+* K, ∃ δ₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (∀ g, ((δ₀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g) ∧
      ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map δ₀.toMonoidHom =
        (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map δ₀.toMonoidHom =
        (graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ∀ u, ∃ u' : (a : Fin TwistTag.E6.foldedTag.rank) →
          (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
        (∀ a, ((u' a : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
          δ ((u a : orbitField TwistTag.E6 K σ.toRingHom a) : K)) ∧
        δ₀ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * δ₀⁻¹ =
          compatDiagAutHom TwistTag.E6 K σ.toRingHom u' := by
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  have hVC := graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  refine ⟨fun u => twistHom_rootDiagUnit (compatDiag_perm u), compatDiagAutHom_injective,
    coe_compatDiagAutHom, fun u => ⟨map_compatDiagAutHom_subgroupOf hUC u
      (map_conj_rootDiagUnit_graphFixedPosUnipotent (compatDiag_perm u)),
      map_compatDiagAutHom_subgroupOf hVC u
        (map_conj_rootDiagUnit_graphFixedNegUnipotent (compatDiag_perm u))⟩,
    compatDiag_conj_orbitX, compatDiag_conj_orbitY, fun δ => ?_⟩
  have hδ : ∀ c, δ (σ.toRingHom c) = σ.toRingHom (δ c) := fun c => by
    change δ (σ c) = σ (δ c)
    rw [hσ, hσ, map_pow]
  exact ⟨graphFixedEntrywiseAut σ.toRingHom hδ, coe_graphFixedEntrywiseAut hδ,
    map_graphFixedEntrywiseAut_subgroupOf hδ hUC
      (map_units_map_entrywiseHom_graphFixedPosUnipotent hδ),
    map_graphFixedEntrywiseAut_subgroupOf hδ hVC
      (map_units_map_entrywiseHom_graphFixedNegUnipotent hδ),
    fun u => ⟨orbitUnitsMap σ.toRingHom hδ u, coe_orbitUnitsMap hδ u,
      graphFixedEntrywiseAut_conj_compatDiagAutHom hδ u⟩⟩

theorem twisted_E6_all_characteristic_compatible_diagonal_cubes
    {p f : ℕ} (hp : p.Prime)
    (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    (∀ u, compatDiag TwistTag.E6 σ.toRingHom u =
      ![orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨3, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨2, by decide⟩),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩)),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩))]) ∧
    ((∀ u, twistHom TwistTag.E6 K σ.toRingHom
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∧
    Function.Injective (compatDiagAutHom TwistTag.E6 K σ.toRingHom) ∧
    (∀ u g, ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) ∧
    (∀ u, ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).toMonoidHom =
        (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).toMonoidHom =
        (graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ∧
    (∀ u a c, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        orbitX TwistTag.E6 K σ.toRingHom a c *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
        orbitX TwistTag.E6 K σ.toRingHom a ((u a : orbitField TwistTag.E6 K σ.toRingHom a) * c)) ∧
    (∀ u a c, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        orbitY TwistTag.E6 K σ.toRingHom a c *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
        orbitY TwistTag.E6 K σ.toRingHom a
          (((u a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) * c)) ∧
    ∀ δ : K ≃+* K, ∃ δ₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (∀ g, ((δ₀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g) ∧
      ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map δ₀.toMonoidHom =
        (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map δ₀.toMonoidHom =
        (graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ∀ u, ∃ u' : (a : Fin TwistTag.E6.foldedTag.rank) →
          (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
        (∀ a, ((u' a : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
          δ ((u a : orbitField TwistTag.E6 K σ.toRingHom a) : K)) ∧
        δ₀ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * δ₀⁻¹ =
          compatDiagAutHom TwistTag.E6 K σ.toRingHom u') ∧
    cubeMatrixE6 * TwistTag.E6.tag.cartan =
      3 • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) ∧
    TwistTag.E6.tag.cartan * cubeMatrixE6 =
      3 • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) ∧
    (∀ u i, cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.perm i) =
      Units.map σ.toRingHom.toMonoidHom (cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) i)) ∧
    (∀ u, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 =
      ((List.finRange TwistTag.E6.tag.rank).map fun i => torusElt TwistTag.E6.tag K i
        (cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) i)).prod) ∧
    (∀ u, ∃ s : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      (∀ a, orbitFieldUnit TwistTag.E6 σ.toRingHom (s a) =
        cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.orbitMin a)) ∧
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 =
        ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
          (orbitH TwistTag.E6 K σ.toRingHom a (s a) : ModGL TwistTag.E6.tag K)).prod) ∧
    (∀ u, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
    ∀ u, ∃ c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u ^ 3 = MulAut.conj c := by
  have hcube : ∀ u, ∃ s : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      (∀ a, orbitFieldUnit TwistTag.E6 σ.toRingHom (s a) =
        cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.orbitMin a)) ∧
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 =
        ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
          (orbitH TwistTag.E6 K σ.toRingHom a (s a) : ModGL TwistTag.E6.tag K)).prod := by
    intro u
    obtain ⟨s, hs⟩ := exists_compatDiag_eq (cubeParam_perm (compatDiag_perm u))
    refine ⟨s, fun a => ?_, ?_⟩
    · rw [← compatDiag_orbitMin, hs]
    · rw [list_prod_orbitH, hs, rootDiagUnit_pow_three]
  have hmem : ∀ u, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := fun u => by
    obtain ⟨s, -, hs⟩ := hcube u
    rw [hs]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom a (s a)
  refine ⟨orbitField_E6_eq_top hp hK hσ (by decide), orbitField_E6_eq_top hp hK hσ (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide), compatDiag_E6,
    twisted_E6_compatible_diagonal_data K σ hσ, cubeMatrixE6_mul_cartan,
    cartan_mul_cubeMatrixE6, fun u => cubeParam_perm (compatDiag_perm u),
    fun u => rootDiagUnit_pow_three _, hcube, hmem,
    fun u => ⟨_, compatDiagAutHom_pow_eq_conj u 3 (hmem u)⟩⟩

theorem twisted_E6_odd_compatible_diagonal_actors
    {p f : ℕ} (hp : p.Prime) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    (∀ u, compatDiag TwistTag.E6 σ.toRingHom u =
      ![orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨3, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨2, by decide⟩),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩)),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩))]) ∧
    (∀ u, twistHom TwistTag.E6 K σ.toRingHom
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∧
    (∀ u, (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (MulAut.conj
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))).toMonoidHom =
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
    Function.Injective (compatDiagAutHom TwistTag.E6 K σ.toRingHom) ∧
    (∀ u g, ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) ∧
    (∀ u, ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).toMonoidHom =
        (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).toMonoidHom =
        (graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ∧
    (∀ u a c, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        orbitX TwistTag.E6 K σ.toRingHom a c *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
        orbitX TwistTag.E6 K σ.toRingHom a ((u a : orbitField TwistTag.E6 K σ.toRingHom a) * c)) ∧
    (∀ u a c, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        orbitY TwistTag.E6 K σ.toRingHom a c *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
        orbitY TwistTag.E6 K σ.toRingHom a
          (((u a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) * c)) ∧
    ∀ δ : K ≃+* K, ∃ δ₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (∀ g, ((δ₀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g) ∧
      ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map δ₀.toMonoidHom =
        (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map δ₀.toMonoidHom =
        (graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      ∀ u, ∃ u' : (a : Fin TwistTag.E6.foldedTag.rank) →
          (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
        (∀ a, ((u' a : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
          δ ((u a : orbitField TwistTag.E6 K σ.toRingHom a) : K)) ∧
        δ₀ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * δ₀⁻¹ =
          compatDiagAutHom TwistTag.E6 K σ.toRingHom u' := by
  obtain ⟨hF, hinj, hcoe, hUV, hX, hY, hδ⟩ := twisted_E6_compatible_diagonal_data K σ hσ
  exact ⟨orbitField_E6_eq_top hp hK hσ (by decide), orbitField_E6_eq_top hp hK hσ (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide), compatDiag_E6, hF,
    fun u => map_conj_rootDiagUnit_graphFixedRootGroup (compatDiag_perm u), hinj, hcoe, hUV, hX,
    hY, hδ⟩

end CFSG.LieType.Chevalley
