module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Fam

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups
open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis
open CFSG.ComponentClassification.Burgoyne.X10

theorem iform_self_emod_four_of_bool_D4 :
    ∀ b : Fin TwistTag.D4.tag.rank → Bool,
      (∀ i, iform (fun j => if b j then (1 : ℤ) else 0) (Pi.single i 1) % 2 = 0) →
        iform (fun j => if b j then (1 : ℤ) else 0) (fun j => if b j then (1 : ℤ) else 0) %
          4 = 0 := by
  decide +kernel

theorem iform_self_emod_four_of_even_D4
    {x : Fin TwistTag.D4.tag.rank → ℤ} (hx : ∀ i, Even (iform x (Pi.single i 1))) :
    iform x x % 4 = 0 := by
  set b : Fin TwistTag.D4.tag.rank → Bool := fun j => decide (x j % 2 = 1) with hb
  set z : Fin TwistTag.D4.tag.rank → ℤ := fun j => if b j then (1 : ℤ) else 0 with hz
  set y : Fin TwistTag.D4.tag.rank → ℤ := fun j => x j / 2 with hy
  have hzx : ∀ j, z j = x j % 2 := by
    intro j
    rcases Int.emod_two_eq_zero_or_one (x j) with h | h <;> simp [hz, hb, h]
  have hxzy : x = z + (2 : ℤ) • y := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzx, hy]
    have := Int.mul_ediv_add_emod (x j) 2
    omega
  have hzev : ∀ i, iform z (Pi.single i 1) % 2 = 0 := by
    intro i
    obtain ⟨m, hm⟩ := hx i
    rw [hxzy, iform_add_left, iform_smul_left] at hm
    omega
  have hkey : iform z z % 4 = 0 := iform_self_emod_four_of_bool_D4 b hzev
  have hxx : iform x x = iform z z + 4 * iform z y + 4 * iform y y := by
    rw [hxzy]
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right]
    rw [iform_comm y z]
    ring
  rw [hxx]
  omega

theorem corootPair_eq_iform_D4
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ)
    (v : Fin TwistTag.D4.tag.rank → ℤ) : corootPair γ v = iform γ v := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have h1 : TwistTag.D4.tag.symmetrizer j j = 1 := by fin_cases j <;> rfl
  rw [corootPair, hj, h1, mul_one]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

section OrbitMap

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem orbitMap_neg_one_ne_one_D4
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.D4.tag p k)
    {O : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hO : O ∈ D.orbits)
    (hO13 : orbitCard O = 1 ∨ orbitCard O = 3) : D.orbitMap O (-1) ≠ 1 := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact D.odd
  have hf : ∀ j, D.orbitFactor O j (-1) = rootDiagUnit TwistTag.D4.tag
      (fun i => (-1 : kˣ) ^ corootPair (D.orbitVec O j) (Pi.single i 1)) := by
    intro j
    rw [D.orbitFactor_apply, map_neg_one_sl2, map_neg_one_sl2, ← HSL_neg_one_eq]
    exact rootSL2_neg_one_eq_rootDiagUnit (D.isRoot_orbitVec hO j) fun i => rfl
  have hcp : ∀ j (i : Fin TwistTag.D4.tag.rank), corootPair (D.orbitVec O j) (Pi.single i 1) =
      iform (D.orbitVec O j) (Pi.single i 1) := fun j i =>
    corootPair_eq_iform_D4 (D.isRoot_orbitVec hO j) _
  have hself : ∀ j, iform (D.orbitVec O j) (D.orbitVec O j) = 2 := by
    intro j
    obtain ⟨i, hi⟩ := iform_self_of_isRoot (D.isRoot_orbitVec hO j)
    have h1 : TwistTag.D4.tag.symmetrizer i i = 1 := by fin_cases i <;> rfl
    rw [hi, h1, mul_one]
  have horth : ∀ a b, a < orbitCard O → b < orbitCard O → a ≠ b →
      iform (D.orbitVec O a) (D.orbitVec O b) = 0 := by
    intro a b ha hb hab
    have hne : D.orbitVec O a ≠ D.orbitVec O b := fun h01 => hab (D.orbitVec_injOn hO ha hb h01)
    have hO' := D.eq_thetaOrbit_orbitRoot hO
    refine D.orbit_orthogonal _ (D.orbitRoot_mem_kernelRoots hO) _ ?_ _ ?_ hne
    · rw [← hO']
      exact D.orbitVec_mem hO a
    · rw [← hO']
      exact D.orbitVec_mem hO b
  intro h
  rw [D.orbitMap_eq_prod] at h
  rcases hO13 with hd | hd
  ·
    rw [hd] at h
    simp only [List.range_one, List.map_singleton, List.prod_singleton, hf] at h
    rw [← rootDiagUnit_one] at h
    have hb := rootDiagUnit_injective h
    have hev : ∀ i, Even (iform (D.orbitVec O 0) (Pi.single i 1)) := fun i => by
      rw [← hcp]
      exact SteinbergCA.even_of_neg_one_zpow_eq_one hk2 (congrFun hb i)
    have := iform_self_emod_four_of_even_D4 hev
    rw [hself] at this
    omega
  ·
    rw [hd] at h
    simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, hf] at h
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_one] at h
    have hb := rootDiagUnit_injective h
    have hev : ∀ i, Even (iform (D.orbitVec O 0 + D.orbitVec O 1 + D.orbitVec O 2)
        (Pi.single i 1)) := by
      intro i
      have h1 := congrFun hb i
      simp only [Pi.mul_apply, Pi.one_apply, ← zpow_add] at h1
      rw [iform_add_left, iform_add_left, ← hcp, ← hcp, ← hcp, add_assoc]
      exact SteinbergCA.even_of_neg_one_zpow_eq_one hk2 h1
    have := iform_self_emod_four_of_even_D4 hev
    have h01 := horth 0 1 (by omega) (by omega) (by omega)
    have h02 := horth 0 2 (by omega) (by omega) (by omega)
    have h12 := horth 1 2 (by omega) (by omega) (by omega)
    have hvv : iform (D.orbitVec O 0 + D.orbitVec O 1 + D.orbitVec O 2)
        (D.orbitVec O 0 + D.orbitVec O 1 + D.orbitVec O 2) = 6 := by
      simp only [iform_add_left, iform_add_right, hself]
      rw [iform_comm (D.orbitVec O 1) (D.orbitVec O 0), iform_comm (D.orbitVec O 2)
        (D.orbitVec O 0), iform_comm (D.orbitVec O 2) (D.orbitVec O 1), h01, h02, h12]
      norm_num
    rw [hvv] at this
    omega

end OrbitMap

theorem exists_SL2_equiv_of_d4_involution_component
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)))
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.D4.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {x}))) :
    ∃ (F₂ : Type) (_ : Field F₂) (_ : Finite F₂) (d : ℕ), (d = 1 ∨ d = 3) ∧
      Nat.card F₂ = (p ^ e) ^ d ∧ Nonempty (SL(2, F₂) ≃* L) := by
  classical
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, hcomp⟩ := exists_twisted_toral_reduction p
    TwistTag.D4 hp he d4SignDiagramReps h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp e) hx hx2
  have hrm : r.mask = 4 := by
    rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩]) with
      rfl | hr'
    · exfalso
      apply hx1
      have h0 : signMaskTuple TwistTag.D4.tag k 0 = 1 := by
        funext j
        simp [signMaskTuple]
      have e0 : g₁ * x * g₁⁻¹ = 1 := by
        rw [hg₁x]
        change rootDiagUnit TwistTag.D4.tag
          (signCharTuple (signMaskChar TwistTag.D4.tag 0)) = 1
        rw [signCharTuple_signMaskChar, h0, rootDiagUnit_one]
      exact mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one g₁).symm)
    · obtain rfl := List.mem_singleton.1 hr'
      rfl
  set χ := signMaskChar TwistTag.D4.tag r.mask with hχ
  set F := frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) with hF
  set M := torusGroup TwistTag.D4.tag k ⊔ rootSpan TwistTag.D4.tag k (kernelRoots χ) with hM_def
  obtain ⟨hJle, hJc⟩ := (hcomp L).1 ⟨hL, hLc⟩
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  have hD : (adjointGroup TwistTag.D4.tag k).map
      (MulAut.conj (diagramMap TwistTag.D4 k)).toMonoidHom = adjointGroup TwistTag.D4.tag k :=
    map_conj_diagramMap TwistTag.D4 k (Or.inl rfl)
  have hRfin : Finite (fixedPointsIn (adjointGroup TwistTag.D4.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.D4 k)
  have hMG : M ≤ adjointGroup TwistTag.D4.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hMFle : fixedPointsIn M F ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k) F :=
    inf_le_inf_right _ hMG
  have hMFfin : Finite (fixedPointsIn M F) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hMFle)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact not_isPComponent_of_kernelRoots_eq_empty hne (inf_le_left : fixedPointsIn M F ≤ M)
      _ hJc
  have hθ : ThetaProperties TwistTag.D4.perm 3 χ (wordElt TwistTag.D4.tag []) :=
    h4.theta r hr [] (nil_mem_omegaWords_d4 hr)
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ := exists_pinned_datum p hp hk he
    (τ := TwistTag.D4.tag) (Or.inl rfl) (ρ := TwistTag.D4.perm) (TwistTag.cartan_perm .D4)
    symmetrizedCartan_perm_D4 hθ
    (Q₀ := wordWeylMatrix TwistTag.D4.tag k [] * diagramMap TwistTag.D4 k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer TwistTag.D4))
    (map_conj_wordWeylMatrix_mul [] hD) (n4 r hr [] (nil_mem_omegaWords_d4 hr)) hne
  have hQ₀ : wordWeylMatrix TwistTag.D4.tag k [] * diagramMap TwistTag.D4 k =
      diagramMap TwistTag.D4 k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_frob_eq p TwistTag.D4 he a₀⁻¹
  set u := rootDiagUnit TwistTag.D4.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k) y =
      h * F y * h⁻¹ := fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k)) :=
    map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff u hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  have hMhfin : Finite (fixedPointsIn M
      (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k))) := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj u).subgroupMap (fixedPointsIn M F)).toEquiv
  set Mh := fixedPointsIn M (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k))
    with hMh_def
  set X := D.totalFixedGroup with hX_def
  set JD := J.map (MulAut.conj u).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup TwistTag.D4.tag k := hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup TwistTag.D4.tag k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro x hx
    have hx' : (x : ModGL TwistTag.D4.tag k) ∈ JD := hx
    have hmem : (x : ModGL TwistTag.D4.tag k) ∈ X.map (adjointGroup TwistTag.D4.tag k).subtype := by
      rw [hX]
      exact hJDle hx'
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup TwistTag.D4.tag k).subtype
      (adjointGroup TwistTag.D4.tag k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ x : X, ((eX x : Mh) : ModGL TwistTag.D4.tag k) =
      (((x : adjointGroup TwistTag.D4.tag k)) : ModGL TwistTag.D4.tag k) := fun x => rfl
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : (((eX.symm y : X) : adjointGroup TwistTag.D4.tag k) : ModGL TwistTag.D4.tag k) =
            (y : ModGL TwistTag.D4.tag k) := by
          have := heX (eX.symm y)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm y : X) : adjointGroup TwistTag.D4.tag k) :
          ModGL TwistTag.D4.tag k) ∈ JD
        rw [this]
        exact hy
      · intro hx
        refine ⟨eX x, ?_, MulEquiv.symm_apply_apply eX x⟩
        change ((eX x : Mh) : ModGL TwistTag.D4.tag k) ∈ JD
        rw [heX]
        exact hx
    rwa [h2] at h1
  have hqD : D.q = p ^ e := by
    change p ^ D.e = p ^ e
    rw [hDe]
  have hθD : ThetaProperties TwistTag.D4.perm 3 D.χ (wordElt TwistTag.D4.tag []) := by
    rw [hDχ]
    exact hθ
  obtain ⟨J', hJ', -⟩ := exists_eq_orbitGroupC_of_isPComponent D hXfin hJ₀X hJ₀comp
  obtain ⟨O₀, hA⟩ : ∃ O₀ : Set (Fin TwistTag.D4.tag.rank → ℤ),
      (D.withOrbit J').orbits = {O₀} := d4_orbits_eq_singleton D (by rw [hDχ, hχ, hrm]; rfl) J'
  have hO₀ : O₀ ∈ (D.withOrbit J').orbits := hA ▸ Set.mem_singleton O₀
  have hqD' : (D.withOrbit J').q = p ^ e := hqD
  have hsurj := (D.withOrbit J').orbitGroupHom_surjective hO₀ hA
  have hcardK := (D.withOrbit J').card_orbitField hO₀
  have hfinK := CFSG.ComponentClassification.ExcSelector.finite_orbitField' (D.withOrbit J') hO₀
  have hd := orbitCard_eq_of_thetaProperties (D.withOrbit J') hθD hDθ hO₀
  let eL : L ≃* J₀ := (L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
    ((J.equivMapOfInjective _ (MulAut.conj u).injective).trans
      (Subgroup.subgroupOfEquivOfLe hJDG).symm)
  let eC : (D.withOrbit J').orbitGroupC ≃* (D.withOrbit J').orbitGroup :=
    Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup
  let eJ : J₀ ≃* (D.withOrbit J').orbitGroup := (MulEquiv.subgroupCongr hJ').trans eC
  have hinj : Function.Injective ((D.withOrbit J').orbitGroupHom hO₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    rw [MonoidHom.mem_ker] at hA
    have h1 : (D.withOrbit J').orbitMap O₀ A = 1 := congrArg Subtype.val hA
    rcases (D.withOrbit J').eq_one_or_neg_one_of_orbitMap_eq_one hO₀ h1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ h1) (orbitMap_neg_one_ne_one_D4 (D.withOrbit J') hO₀ hd)
  exact ⟨_, inferInstance, hfinK, orbitCard O₀, hd, by rw [hcardK, hqD'],
    ⟨(MulEquiv.ofBijective _ ⟨hinj, hsurj⟩).trans (eL.trans eJ).symm⟩⟩

theorem trialityInnerNoPSL2_holds
    : ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .trialityD4 0 p f →
      LieModel J .trialityD4 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∈ (MulAut.conj : J →* MulAut J).range →
        ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L := by
  classical
  intro J _ p f hp hp2 hadm hm α hα hαi L hL
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβi : β ∈ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∈ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαi
  obtain ⟨c, hc⟩ := hβi
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  have hc2 : c ^ 2 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hc, hβ2, map_one])
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hα1 : α = 1 := (MulAut.congr e).injective (by rw [map_one, ← hβdef, ← hc, map_one])
    rw [hα1, orderOf_one] at hα
    exact absurd hα (by norm_num)
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK3' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3'
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd K hK3 σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) =
        twistedFixedGroup TwistTag.D4 k Fr := rfl
  set y := baseChangeGL ι (c : ModGL TwistTag.D4.tag K) with hydef
  have hyR : y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) := by
    rw [hRF]
    exact hHR ⟨c, c.2, rfl⟩
  have hy2 : y ^ 2 = 1 := by
    rw [hydef, ← map_pow, ← Subgroup.coe_pow, hc2, Subgroup.coe_one, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    refine hc1 (Subtype.ext (baseChangeGL_injective ι ?_))
    rw [Subgroup.coe_one, map_one]
    exact h1
  let φ : C →* ModGL TwistTag.D4.tag k := (baseChangeGL ι).comp C.subtype
  have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hmap : (fixedSubgroup (MulAut.conj c)).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {y} := by
    rw [hRF, hder]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a, a.2, rfl⟩, ?_⟩
      have ha' : c * a * c⁻¹ = a := ha
      have hac : a * c = c * a := by
        calc a * c = c * a * c⁻¹ * c := by rw [ha']
          _ = c * a := by group
      change baseChangeGL ι (a : ModGL TwistTag.D4.tag K) * y =
        y * baseChangeGL ι (a : ModGL TwistTag.D4.tag K)
      rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hac]
    · rintro ⟨⟨a, ha, rfl⟩, hay⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      change c * ⟨a, ha⟩ * c⁻¹ = ⟨a, ha⟩
      have hac : (⟨a, ha⟩ : C) * c = c * ⟨a, ha⟩ := by
        refine Subtype.ext (baseChangeGL_injective ι ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hay
      rw [← hac]
      group
  set X₀ := ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
      Subgroup.centralizer {y} with hX₀def
  let Φ : fixedSubgroup (MulAut.conj c) ≃* X₀ :=
    ((fixedSubgroup (MulAut.conj c)).equivMapOfInjective φ hφ).trans
      (MulEquiv.subgroupCongr hmap)
  let Θ : fixedSubgroup α ≃* X₀ := ((fixedSubgroupCongrEquiv e α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc.symm))).trans Φ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite X₀ := Finite.of_equiv _ Φ.toEquiv
  set L' := L.map Θ.toMonoidHom with hL'def
  have hL' : IsComponent L' := LocalCores.isComponent_map_mulEquiv Θ hL
  have hL'2 : IsPComponent 2 L' := CatLeafProof.isPComponent_two_of_isComponent hL'
  have hof : (L'.map X₀.subtype).subgroupOf X₀ = L' :=
    Subgroup.comap_map_eq_self_of_injective X₀.subtype_injective L'
  obtain ⟨F₂, _, _, d, hd, hF₂, ⟨eS⟩⟩ := exists_SL2_equiv_of_d4_involution_component p
    hp2 halg hf hyR hy1 hy2 (Subgroup.map_subtype_le L') (by rw [hof]; exact hL'2)
  let eL : L ≃* L'.map X₀.subtype := (L.equivMapOfInjective Θ.toMonoidHom Θ.injective).trans
    (L'.equivMapOfInjective X₀.subtype X₀.subtype_injective)
  have hd1 : 1 ≤ f * d := by rcases hd with rfl | rfl <;> omega
  have hF₂' : Nat.card F₂ = p ^ (f * d) := by rw [hF₂, ← pow_mul]
  have : CharP F₂ p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hd1 hF₂'
  have hF₂2 : ringChar F₂ ≠ 2 := by rw [ringChar.eq F₂ p]; exact hp2
  exact noPSL2Odd_of_mulEquiv_SL2 hF₂2 (eL.trans eS.symm)

theorem famInnerNoPSL2_trialityD4
    : FamInnerNoPSL2 .trialityD4 := by
  intro J _ n p f hp hp2 hadm hm g hg L hL
  obtain rfl : n = 0 := hadm.2.2
  exact trialityInnerNoPSL2_holds J p f hp hp2 hadm hm (MulAut.conj g) hg ⟨g, rfl⟩ L hL

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
