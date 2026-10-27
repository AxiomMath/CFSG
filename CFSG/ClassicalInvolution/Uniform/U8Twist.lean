module

public import CFSG.ClassicalInvolution.Uniform.U8Adj
public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterE6
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Tw

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.RouteD.Exotic
open scoped MatrixGroups commutatorElement


section Datum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_mask2_datum3 (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
      (s : Fin TwistTag.E6.tag.rank → kˣ) (h : ModGL TwistTag.E6.tag k),
      h ∈ torusGroup TwistTag.E6.tag k ∧
      D.χ = signMaskChar TwistTag.E6.tag 2 ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)) ∧
      (∀ x : adjointGroup TwistTag.E6.tag k, (D.F x : ModGL TwistTag.E6.tag k) =
        frobTwistGL TwistTag.E6.tag k p e (h * diagramMap TwistTag.E6 k) x) ∧
      (fixedPointsIn (torusGroup TwistTag.E6.tag k ⊔
          rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)))
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))).map
          (MulAut.conj (rootDiagUnit TwistTag.E6.tag s)).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
  classical
  set t := TwistTag.E6 with ht
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  have hr : (⟨2, 36, 1, e6OmegaWords2⟩ : SignRep .E6) ∈ e6SignDiagramReps := by
    simp [e6SignDiagramReps]
  have hr0 : ([] : List (Fin Tag.E6.rank)) ∈
      (⟨2, 36, 1, e6OmegaWords2⟩ : SignRep .E6).omegaWords :=
    CFSG.ClassicalInvolution.ModelFacts.nil_mem_omegaWords_e6 hr
  set χ := signMaskChar t.tag 2 with hχ
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  set M := torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots χ) with hM_def
  have hD : (adjointGroup t.tag k).map (MulAut.conj (diagramMap t k)).toMonoidHom =
      adjointGroup t.tag k := map_conj_diagramMap t k (Or.inl rfl)
  have hMG : M ≤ adjointGroup t.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hne : (kernelRoots χ).Nonempty := ⟨e6Theta, layerShape_E6_mask2.mem_e⟩
  have hA := t.cartan_perm
  have hB := symmetrizedCartan_perm_E6
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_pinned_datum p hp hk he (τ := t.tag)
      (Or.inr (Or.inl rfl)) (ρ := t.perm) hA hB (h6.theta _ hr [] hr0) (Q₀ :=
        wordWeylMatrix t.tag k [] * diagramMap t k)
      (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX t [] hγ)
      (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer t))
      (map_conj_wordWeylMatrix_mul [] hD) (n6 _ hr [] hr0) hne
  have hQ₀ : wordWeylMatrix t.tag k [] * diagramMap t k = diagramMap t k := by
    rw [CFSG.ClassicalInvolution.ModelFacts.wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_rootDiagUnit_frob_eq p t he a₀⁻¹
  set u := rootDiagUnit t.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL t.tag k p e (h * diagramMap t k) y = h * F y * h⁻¹ :=
    fun y => CFSG.ClassicalInvolution.ModelFacts.frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) :=
    CFSG.ClassicalInvolution.ModelFacts.map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  have hθ1 : ∀ γ, thetaMap (ToralSign.wordElt Tag.E6 []) t.perm γ = permLattice t.perm γ :=
    fun γ => by
      rw [wordElt_nil]
      exact CFSG.ClassicalInvolution.ModelFacts.thetaMap_one _ γ
  exact ⟨D, s, h, hhT, hDχ, hDe, fun γ => (hDθ γ).trans (congrArg toReal (hθ1 γ)), hDF,
    hconj.trans hX.symm⟩

end Datum

section Card

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ J₂ : Set.range D.classOrbit} (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})
  (h2 : (J₂ : Set (KernelComponent D.χ)) = {cls₂ D hDχ})

include hDχ hDθ h1 h2 in
theorem card_orbitGroup_ne3 {e : ℕ} (hq : p ^ e = 3) (hDe : D.e = e) :
    Nat.card (D.withOrbit J₂).orbitGroup ≠ Nat.card (D.withOrbit J₁).orbitGroup := by
  classical
  set D₁ := D.withOrbit J₁ with hD₁
  set D₂ := D.withOrbit J₂ with hD₂
  have hO₁ : D₁.orbits = {{e6Theta}} := orbits_J₁ D hDχ hDθ h1
  have hOm₁ : ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∈ D₁.orbits := by
    rw [hO₁]
    exact Set.mem_singleton _
  have hcard₁ : OrthogonalSemilinearFixedRootDatum.orbitCard
      ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = 1 := Set.ncard_singleton _
  have hq1 : Nat.card (D₁.orbitField {e6Theta}) = p ^ e := by
    rw [D₁.card_orbitField hOm₁, hcard₁, pow_one]
    change p ^ D.e = p ^ e
    rw [hDe]
  have hfin1 : Finite (D₁.orbitField {e6Theta}) :=
    Nat.finite_of_card_ne_zero (by rw [hq1]; positivity)
  have hC₁ : D₁.orbitGroup = (D₁.orbitMapHom hOm₁).range := by
    apply SetLike.coe_injective
    rw [MonoidHom.coe_range]
    exact (D₁.range_orbitMap_eq_of_orbits_eq hO₁).symm
  have hdvd₁ : Nat.card D₁.orbitGroup ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [hC₁]
    have := Subgroup.card_range_dvd (D₁.orbitMapHom hOm₁)
    rwa [CFSG.GorensteinWalter.sl2_card_formula, hq1] at this
  have hO₃ := thetaOrbit_a3_mem_orbits D hDχ h2
  have hcard₃ := thetaOrbit_a3_ncard D hDθ
  set O₃ := thetaOrbit D.θ e6a3 with hO₃def
  have hq3 : Nat.card (D₂.orbitField O₃) = (p ^ e) ^ 2 := by
    rw [D₂.card_orbitField hO₃]
    change D₂.q ^ O₃.ncard = (p ^ e) ^ 2
    rw [hcard₃]
    change (p ^ D.e) ^ 2 = (p ^ e) ^ 2
    rw [hDe]
  let φ : Multiplicative (D₂.orbitField O₃) →* ModGL TwistTag.E6.tag k :=
    { toFun := fun c => D₂.orbitX O₃ (Multiplicative.toAdd c)
      map_one' := by
        change D₂.orbitX O₃ 0 = 1
        rw [OrthogonalSemilinearFixedRootDatum.orbitX, uSL_zero_eq_one, D₂.orbitMap_one]
      map_mul' := fun a b => by
        change D₂.orbitX O₃ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
        exact D₂.orbitX_add hO₃ _ _ }
  have hφinj : Function.Injective φ := fun a b h =>
    Multiplicative.toAdd.injective (D₂.orbitX_injective hO₃ h)
  have hφle : φ.range ≤ D₂.orbitGroup := by
    rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨O₃, hO₃, Multiplicative.toAdd c, Or.inl rfl⟩
  have hcardφ : Nat.card φ.range = (p ^ e) ^ 2 := by
    have h1 : Nat.card φ.range = Nat.card (Multiplicative (D₂.orbitField O₃)) :=
      (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
    rw [h1, Nat.card_congr Multiplicative.toAdd, hq3]
  have hdvd₂ : (p ^ e) ^ 2 ∣ Nat.card D₂.orbitGroup := by
    rw [← hcardφ]
    exact Subgroup.card_dvd_of_le hφle
  intro heq
  rw [heq] at hdvd₂
  have hcon := hdvd₂.trans hdvd₁
  rw [hq] at hcon
  exact absurd hcon (by norm_num)

end Card

section Center

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ : Set.range D.classOrbit} (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})

include hDχ hDθ h1 in
theorem orbitGroup_J₁_central_sq :
    ∀ a ∈ (D.withOrbit J₁).orbitGroup,
      (∀ y ∈ (D.withOrbit J₁).orbitGroup, a * y = y * a) → a * a = 1 := by
  classical
  intro a ha hcen
  set D₁ := D.withOrbit J₁ with hD₁
  have hO : D₁.orbits = {{e6Theta}} := orbits_J₁ D hDχ hDθ h1
  obtain ⟨hβK, -, -, hmem⟩ := CFSG.ClassicalInvolution.Q3.exc3_small_orbit_data D₁ hO
  obtain ⟨A, rfl⟩ := (hmem a).1 ha
  have hρ := D₁.rootSL2_injective e6Theta
  have hmapinj := D₁.map_subtype_injective {e6Theta}
  have hAB : ∀ B : SL2 (D₁.orbitField {e6Theta}), A * B = B * A := by
    intro B
    have hB : rootSL2 TwistTag.E6.tag k e6Theta
        (Matrix.SpecialLinearGroup.map (D₁.orbitField {e6Theta}).subtype B) ∈ D₁.orbitGroup :=
      (hmem _).2 ⟨B, rfl⟩
    have h := hcen _ hB
    apply hmapinj
    apply hρ
    rw [map_mul, map_mul, map_mul, map_mul]
    exact h
  have hcenter : A ∈ Subgroup.center (SL2 (D₁.orbitField {e6Theta})) :=
    Subgroup.mem_center_iff.2 fun B => (hAB B).symm
  have hsq := CFSG.ClassicalInvolution.Q3.exc3_mul_self_of_mem_center_sl2 hcenter
  rw [← map_mul, ← map_mul, hsq, map_one, map_one]

end Center

section Star

open CFSG.ClassicalInvolution.Q3 (Exc3Frob exc3_two_orbit_data exc3_two_orbit_exp e6_twoClass_two)

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ J₂ : Set.range D.classOrbit} (hne : J₁ ≠ J₂) (hJ : ∀ J, J = J₁ ∨ J = J₂)
  (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})

include hDχ hDθ hne hJ h1 in
theorem pow_three_mem_orbitGroup_J₂ {c : ModGL TwistTag.E6.tag k} (hc : Exc3Frob D c)
    (hq3 : p ^ D.e = 3) {y : adjointGroup TwistTag.E6.tag k} (hy : y ∈ D.totalFixedGroup)
    (hy3 : y ^ 3 = 1)
    (hyC : ∀ z ∈ (D.withOrbit J₁).orbitGroup,
      (y : ModGL TwistTag.E6.tag k) * z = z * (y : ModGL TwistTag.E6.tag k)) :
    (y : ModGL TwistTag.E6.tag k) ∈ (D.withOrbit J₂).orbitGroup := by
  classical
  obtain ⟨β₀, γ₁, hβ₀, hγ₁, hfix, hiso, hne1, hne2, hrest, hns⟩ := e6_twoClass_two
  have hθβ₀ : D.θ (toReal β₀) = toReal β₀ := (hDθ β₀).trans (congrArg toReal hfix)
  obtain ⟨J₀, J₁', hne', hall', hsq', -⟩ := exc3_two_orbit_data (D := D)
    (τ := TwistTag.E6.tag) (Or.inr (Or.inl rfl)) hc hq3 hDχ hβ₀ hγ₁ hiso hθβ₀ ⟨hne1, hne2⟩
    (fun γ hγ h1 h2 => ⟨0, γ₁, hγ₁, by simp, hrest γ hγ h1 h2⟩) (Or.inl hns)
  obtain ⟨m, hm⟩ := exc3_two_orbit_exp hc hq3 hne' hall' hsq' y hy
  set C₁ := (D.withOrbit J₁).orbitGroup with hC₁
  set C₂ := (D.withOrbit J₂).orbitGroup with hC₂
  set z : ModGL TwistTag.E6.tag k := (y : ModGL TwistTag.E6.tag k) with hz
  have hsup : (⨆ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup) ≤ C₁ ⊔ C₂ :=
    iSup_le fun J' => (hJ J').elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
  have hmem : z ^ (2 ^ m) ∈ C₁ ⊔ C₂ := hsup hm
  have hz3 : z ^ 3 = 1 := by
    have := congrArg (fun w : adjointGroup TwistTag.E6.tag k => (w : ModGL TwistTag.E6.tag k)) hy3
    simpa using this
  have hzmem : z ∈ C₁ ⊔ C₂ := by
    have hcop : (2 ^ m).gcd (orderOf z) = 1 :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hz3)
        (Nat.Coprime.pow_left m (by norm_num))
    exact Subgroup.zpowers_le.2 hmem (mem_zpowers_pow_iff.2 hcop)
  have hcent : C₁ ≤ Subgroup.centralizer (C₂ : Set (ModGL TwistTag.E6.tag k)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (D.commute_of_ne hne ((D.withOrbit J₁).orbitGroup_le_rootSpanJ ha)
      ((D.withOrbit J₂).orbitGroup_le_rootSpanJ hb)).symm.eq
  have hzC : z ∈ Subgroup.centralizer (C₁ : Set (ModGL TwistTag.E6.tag k)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (hyC g hg).symm
  exact le_of_pow_three_of_le_sup_of_commutes hcent
    (orbitGroup_J₁_central_sq D hDχ hDθ h1) hzmem hzC hz3

end Star

section Main

open CFSG.ClassicalInvolution.Q3 (Exc3Frob)

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_twisted_layer3 (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (hq : p ^ e = 3) :
    ∃ L : Subgroup (ModGL TwistTag.E6.tag k),
      L ≤ ⁅twistedR p k e, twistedR p k e⁆ ∧ CFSG.Open.IsQuasisimple ↥L ∧
      L ≤ Subgroup.centralizer (rankOneFix p k e : Set (ModGL TwistTag.E6.tag k)) ∧
      (∀ x ∈ twistedR p k e,
        x ∈ Subgroup.centralizer (rankOneFix p k e : Set (ModGL TwistTag.E6.tag k)) →
          x ^ 3 = 1 → x ∈ L) ∧
      Nat.card ↥L ≠ Nat.card ↥(rankOneFix p k e) := by
  classical
  obtain ⟨D, s, h, hhT, hDχ, hDe, hDθ, hDF, hconj⟩ := exists_mask2_datum3 p hp hk he
  obtain ⟨J₁, J₂, hne, hJ, h1, h2⟩ := exists_two_orbits D hDχ hDθ
  have hC₁ := orbitGroup_J₁_eq D hDχ hDθ h1 he hDe hconj
  have hx := involX_mem_rankOneFix D hDχ hDθ h1 he hDe hconj
  have hqs₂ := CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
    (isQuasisimple_orbitGroup_J₂ D hDχ hDθ h2)
  have hcard := card_orbitGroup_ne3 D hDχ hDθ h1 h2 hq hDe
  have hq3D : p ^ D.e = 3 := by rw [hDe]; exact hq
  set u := rootDiagUnit TwistTag.E6.tag s with hu
  set Mk := torusGroup TwistTag.E6.tag k ⊔
    rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)) with hMk
  set Fk := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hFk
  have hMG : Mk ≤ adjointGroup TwistTag.E6.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  set c := h * diagramMap TwistTag.E6 k with hc_def
  have hdn : diagramMap TwistTag.E6 k ∈
      Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) :=
    diagramMap_mem_normalizer TwistTag.E6
  have hd2 : diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k ∈
      torusGroup TwistTag.E6.tag k := by
    have h1 := diagramMap_pow_order TwistTag.E6 k
    rw [show TwistTag.E6.order = 2 from rfl, pow_two] at h1
    rw [h1]
    exact one_mem _
  have hcT : c ∈ Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL _ k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hdn
  have hc2 : c * c ∈ torusGroup TwistTag.E6.tag k := by
    have e : c * c = h * (diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) *
        (diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k) := by
      rw [hc_def]
      group
    rw [e]
    exact mul_mem (mul_mem hhT ((Subgroup.mem_normalizer_iff.1 hdn h).1 hhT)) hd2
  have hfrob : Exc3Frob D c := ⟨fun y => by rw [hDe]; exact hDF y, hcT, hc2⟩
  set C₂ := (D.withOrbit J₂).orbitGroup with hC₂
  set L := C₂.map (MulAut.conj u⁻¹).toMonoidHom with hL
  have hLM : L ≤ fixedPointsIn Mk Fk := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := orbitGroup_le_totalFixed D J₂ hc
    rw [← hconj] at hc'
    obtain ⟨m, hm, rfl⟩ := hc'
    have : (MulAut.conj u⁻¹).toMonoidHom ((MulAut.conj u).toMonoidHom m) = m := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hm
  have hLR : L ≤ twistedR p k e := hLM.trans (inf_le_inf_right _ hMG)
  have hqL : CFSG.Open.IsQuasisimple ↥L :=
    (open_isQuasisimple_congr (Subgroup.equivMapOfInjective C₂ (MulAut.conj u⁻¹).toMonoidHom
      (MulAut.conj u⁻¹).injective)).1 hqs₂
  have hLperf : L ≤ ⁅L, L⁆ := by
    have : Group.IsPerfect ↥L := ⟨hqL.1⟩
    exact (Subgroup.isPerfect_iff.1 this).ge
  refine ⟨L, hLperf.trans (Subgroup.commutator_mono hLR hLR), hqL, ?_, ?_, ?_⟩
  ·
    rintro y ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : u * r * u⁻¹ ∈ (D.withOrbit J₁).orbitGroup := by
      rw [hC₁]
      exact ⟨r, hr, rfl⟩
    have hcomm : Commute (u * r * u⁻¹) c :=
      D.commute_of_ne hne ((D.withOrbit J₁).orbitGroup_le_rootSpanJ hr')
        ((D.withOrbit J₂).orbitGroup_le_rootSpanJ hc)
    have h := hcomm.eq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc r * (u⁻¹ * c * u⁻¹⁻¹) = u⁻¹ * ((u * r * u⁻¹) * c) * u := by group
      _ = u⁻¹ * (c * (u * r * u⁻¹)) * u := by rw [h]
      _ = u⁻¹ * c * u⁻¹⁻¹ * r := by group
  ·
    intro x hxR hxC hx3
    obtain ⟨hxG, hxF⟩ := mem_fixedPointsIn.1 hxR
    have hxM : x ∈ fixedPointsIn Mk Fk :=
      mem_fixedPointsIn_of_commutes_involX hp hxG hxF (Subgroup.mem_centralizer_iff.1 hxC _ hx)
    have hxX : u * x * u⁻¹ ∈ D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
      rw [← hconj]
      exact ⟨x, hxM, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hxX
    have hyx' : (y : ModGL TwistTag.E6.tag k) = u * x * u⁻¹ := hyx
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      change (y : ModGL TwistTag.E6.tag k) ^ 3 = 1
      rw [hyx', conj_pow, hx3]
      group
    have hyC : ∀ z ∈ (D.withOrbit J₁).orbitGroup,
        (y : ModGL TwistTag.E6.tag k) * z = z * (y : ModGL TwistTag.E6.tag k) := by
      intro z hz
      rw [hC₁] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      have hrx := Subgroup.mem_centralizer_iff.1 hxC r hr
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hyx']
      calc u * x * u⁻¹ * (u * r * u⁻¹) = u * (x * r) * u⁻¹ := by group
        _ = u * (r * x) * u⁻¹ := by rw [← hrx]
        _ = u * r * u⁻¹ * (u * x * u⁻¹) := by group
    have hmem := pow_three_mem_orbitGroup_J₂ D hDχ hDθ hne hJ h1 hfrob hq3D hy hy3 hyC
    refine ⟨u * x * u⁻¹, ?_, ?_⟩
    · rw [← hyx']
      exact hmem
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  ·
    intro heq
    apply hcard
    have e1 : Nat.card ↥L = Nat.card ↥C₂ :=
      (Nat.card_congr (Subgroup.equivMapOfInjective C₂ (MulAut.conj u⁻¹).toMonoidHom
        (MulAut.conj u⁻¹).injective).toEquiv).symm
    have e2 : Nat.card ↥(rankOneFix p k e) =
        Nat.card ↥((D.withOrbit J₁).orbitGroup) := by
      rw [hC₁]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj u).toMonoidHom
        (MulAut.conj u).injective).toEquiv
    rw [← e1, ← e2]
    exact heq

end Main

section Lift

open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (conjSub_mem_fundamentalSubgroups)

variable {n : ℕ}

theorem hasLayer3_twistedE6 (hadm : StatedLieAdmissible .twistedE6 n 3 1) :
    HasLayer3 .twistedE6 n := by
  classical
  obtain rfl : n = 0 := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  set K0 := GaloisField 3 (2 * 1) with hK0
  set k := AlgebraicClosure K0 with hk
  have hChark : CharP k 3 := charP_of_injective_algebraMap (algebraMap K0 k).injective 3
  have halg := CFSG.LieType.AlgebraicGroups.isAlgebraic_zmod_of_isAlgClosure 3 K0 k
  obtain ⟨L, hLR, hLq, hLC, hL3, hLcard⟩ :=
    exists_twisted_layer3 (k := k) hp2 halg hf (by norm_num)
  set Φ := CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi 3 1 k with hΦ
  set Rθ : Subgroup (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 3 1) :=
    twistedRootGroup K0 (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) (proj e6Theta) ⊔
      twistedRootGroup K0 (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) (-proj e6Theta)
    with hRθ
  have hRθmem : Rθ ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 3 1 Fact.out).D :=
    ⟨1, proj e6Theta, Or.inl (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_twistedDatum_proj
      (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) isRoot_e6Theta perm_e6Theta),
      (conjSub_one _).symm⟩
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 3 1
    Fact.out trivial hadm (by decide) (by decide)
  have hmap : Rθ.map Φ = rankOneFix 3 k 1 := map_twistedRootGroup_theta hp2 hf
  have hrange := CFSG.ClassicalInvolution.ModelFacts.range_twistedE6Phi 3 1 hp2 hf
  have hker := CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center 3 1 k
  have hZ := CFSG.ClassicalInvolution.Q3.exc3_center_twistedE6
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hΦR : ∀ x, Φ x ∈ twistedR 3 k 1 :=
    fun x => CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi_mem_fixedPointsIn 3 1 hp2 hf x
  have hLΦ : L ≤ Φ.range := by
    rw [hΦ, hrange]
    exact hLR
  set M := L.comap Φ with hM
  have hMmap : M.map Φ = L := by
    rw [hM, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hLΦ
  have hlayer : LayerAt3 (K := CFSG.LieType.Steinberg.Exceptional.twistedE6Group 3 1)
      (fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 3 1 Fact.out).D) Rθ := by
    have eML : ↥M ≃* ↥L := (Subgroup.equivMapOfInjective M Φ hΦinj).trans
      (MulEquiv.subgroupCongr hMmap)
    refine ⟨M, (open_isQuasisimple_congr eML).2 hLq, ?_, ?_, ?_⟩
    · intro x hx
      refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
      apply hΦinj
      have hΦr : Φ r ∈ rankOneFix 3 k 1 := hmap ▸ Subgroup.mem_map_of_mem Φ hr
      have h := Subgroup.mem_centralizer_iff.1 (hLC hx) (Φ r) hΦr
      exact (map_mul Φ r x).trans (h.trans (map_mul Φ x r).symm)
    · intro x hx hx3
      have hΦx : Φ x ∈ Subgroup.centralizer (rankOneFix 3 k 1 : Set (ModGL TwistTag.E6.tag k)) := by
        refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
        rw [← hmap] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        have hrx : r * x = x * r := Subgroup.mem_centralizer_iff.1 hx r hr
        exact (map_mul Φ r x).symm.trans ((congrArg Φ hrx).trans (map_mul Φ x r))
      exact hL3 (Φ x) (hΦR x) hΦx
        ((map_pow Φ x 3).symm.trans ((congrArg Φ hx3).trans (map_one Φ)))
    · intro hmem
      obtain ⟨g, hg⟩ := hsingle Rθ hRθmem M hmem
      apply hLcard
      have e1 : Nat.card ↥L = Nat.card ↥M :=
        (Nat.card_congr eML.toEquiv).symm
      have e2 : Nat.card ↥M = Nat.card ↥Rθ := by
        rw [hg]
        exact (Nat.card_congr (Subgroup.equivMapOfInjective Rθ (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv).symm
      have e3 : Nat.card ↥(rankOneFix 3 k 1) = Nat.card ↥Rθ := by
        rw [← hmap]
        exact (Nat.card_congr (Subgroup.equivMapOfInjective Rθ Φ hΦinj).toEquiv).symm
      rw [e1, e2, e3]
  intro R₀ hR₀
  obtain ⟨g, hg⟩ := hsingle Rθ hRθmem R₀ hR₀
  rw [hg]
  exact LayerAt3.conj (fun S hS g => conjSub_mem_fundamentalSubgroups hS g) hlayer g

end Lift

end CFSG.ClassicalInvolution.Uniform
