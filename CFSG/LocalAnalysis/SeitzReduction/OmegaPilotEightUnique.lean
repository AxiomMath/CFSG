module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueLinear
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.SeitzReduction.E7Pilot

section Cases

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem involution_cases_omegaPlus_of_mem_image (hn : 4 ≤ n) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))} (hβ : β * β = 1)
    (hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n F)) :
    (∃ s : matrixIsometries (coordinateQuadPlus n F), s * s = 1 ∧
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β) ∨
    (∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)),
      ψ * β * ψ⁻¹ = fieldAutT (coordinateQuadPlus n F) σ (coordinateQuadPlus_fieldMap n σ)) ∨
    (∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (b c : k)
      (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0), Nat.card k ^ 2 = Nat.card F ∧
      ∃ N : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F)),
        N ≤ fixedSubgroup β ∧ ⁅N, N⁆ = N ∧
        Nonempty (N ≃* matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c))) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have hE := commutator_coordinateQuadPlus n F (by omega)
  obtain ⟨-, -, -, huniq, Fm, hFm, hker, hinjκ, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega : 1 ≤ 2 * n) _ hQ hT hE
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  by_cases hβ1 : β = 1
  · left
    exact ⟨1, mul_one 1, by rw [map_one, map_one, hβ1]⟩
  have hβ2 : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ) hβ1
  obtain ⟨S, ⟨hS, hSβ⟩, -⟩ := huniq β hβim
  obtain ⟨hSS, hTT, hright⟩ := hinv β hβim hβ2 S hS hSβ
  rcases hright with hσ1 | ⟨hord, huniqσ, -⟩
  ·
    left
    have hmem : (⟨matrixProjectiveConjugationHom _ S, ⟨S, rfl⟩⟩ :
        matrixProjectiveImage (coordinateQuadPlus n F)) ∈ Fm.ker := by
      rw [MonoidHom.mem_ker, hFm, hσ1]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β := hs.trans hSβ
    refine ⟨s, hinjκ ?_, hs'⟩
    change matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ (s * s)) =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ 1)
    rw [map_mul, map_mul, hs', hβ, map_one, map_one]
  right
  have hσS : σ = S.val.right := huniqσ σ hσ
  have hσ1 : S.val.right ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus n F) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  rcases (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.1 n
      (by omega) hdim with ⟨b, hb⟩ | ⟨β', γ', -, hroot, b, hb⟩
  ·
    left
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_plus (by omega) hS hσσ hσ1 hTT b hb
    refine ⟨ψ, ?_⟩
    rw [← hSβ, hψ]
    subst hσS
    rfl
  ·
    right
    obtain ⟨hfeven, hkcard, -, -, ext, -, -, hinj, hinn, hNC, -, -⟩ :=
      evenOrthogonalFieldCentralizer_of_regular hf hK (by omega : 4 ≤ n) _ hQ hT hE β hβim hβ2 S
        hS hSβ hσ1
    obtain ⟨g', hg', hk'⟩ :=
      F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := descentField S.val.right)
    have hreg := regular_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega) hroot
    obtain ⟨eM⟩ := nonempty_derived_mulEquiv_of_isometry hg' hk' (by omega) _
      ((minusBasisIsometry b hb).trans
        (coordinateMinusIsometry n (descentField S.val.right) (by omega) β' γ'))
      hreg.1 hreg.2 (commutator_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega)
        hroot)
    refine ⟨descentField S.val.right, inferInstance, inferInstance, inferInstance, β', γ', hroot,
      ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hfeven
      rw [hkcard, hK, ← pow_mul]
      congr 1
      omega
    obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))),
        N = (extKappa (coordinateQuadPlus n F) ext).range := ⟨_, rfl⟩
    obtain ⟨N', hN'def⟩ : ∃ N' : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F)),
        N' = N.comap (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
          MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))) := ⟨_, rfl⟩
    have hinn' : N ≤ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range := hNdef ▸ hinn
    have hNC' : N ≤ matrixProjectiveImage (coordinateQuadPlus n F) ⊓ Subgroup.centralizer {β} :=
      hNdef ▸ hNC
    have hmapN : N'.map MulAut.conj = N := by
      rw [hN'def]
      exact Subgroup.map_comap_eq_self hinn'
    let e1 : N' ≃* N :=
      (N'.equivMapOfInjective _ hcj).trans (MulEquiv.subgroupCongr hmapN)
    let e2 : N ≃* pairDescentDerived hS :=
      (MulEquiv.subgroupCongr hNdef).trans (MonoidHom.ofInjective hinj).symm
    let eN : N' ≃* matrixProjectiveDerived (coordinateQuadMinus n (descentField S.val.right)
        (by omega) β' γ') := (e1.trans e2).trans eM
    refine ⟨N', ?_, ?_, ⟨eN⟩⟩
    ·
      intro x hx
      have hxN : MulAut.conj x ∈ N := by
        rw [hN'def] at hx
        exact hx
      have hc : MulAut.conj x ∈ Subgroup.centralizer {β} := (Subgroup.mem_inf.1 (hNC' hxN)).2
      have hcomm : β * MulAut.conj x = MulAut.conj x * β :=
        (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
      have h1 : MulAut.conj (β x) = MulAut.conj x := by
        rw [← mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
      exact hcj h1
    ·
      have hsimp := matrix_simple_nonabelian (by omega : 0 < 2 * n) hreg.1 hreg.2
      have : IsSimpleGroup (matrixProjectiveDerived
        (coordinateQuadMinus n (descentField S.val.right) (by omega) β' γ')) := hsimp.1
      have htop := commutator_top_of_isSimpleGroup hsimp.2
      set φ := N'.subtype.comp eN.symm.toMonoidHom with hφ
      have hφr : φ.range = N' := by
        rw [hφ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eN.symm.surjective,
          ← MonoidHom.range_eq_map, range_subtype]
      rw [← hφr]
      exact commutator_range_of_commutator_top φ htop

end Cases

section Renormalize

open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.Quasithin (perfectCore)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_comp_fieldEmbed_eq_twist (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} (hn : 4 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Ψ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G} (hinj : Function.Injective Ψ)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x))
    {ψ' : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hψ' : ψ' * β * ψ'⁻¹ =
      fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)) :
    ∃ (Φ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G)
      (e' : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)), Φ.range = Ψ.range ∧
      ∀ x, Φ (fieldEmbed ι n (by omega) x) = ((e'.symm x : L) : G) := by
  set σs := fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)
    with hσs
  set k := ι.fieldRange with hk
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => by
    rw [hfix, hk, RingHom.mem_fieldRange, Set.mem_range]
  have hext := E7Pilot.isExtension_coordinateQuadPlus n k
  set Ψ₁ := Ψ.comp ψ'.symm.toMonoidHom with hΨ₁
  have hinj₁ : Function.Injective Ψ₁ := hinj.comp ψ'.symm.injective
  have hrange₁ : Ψ₁.range = Ψ.range := by
    rw [hΨ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ'.symm.surjective,
      ← MonoidHom.range_eq_map]
  have hβ' : β = ψ'⁻¹ * σs * ψ' := by rw [← hψ']; group
  have hσΨ₁ : ∀ x, t * Ψ₁ x * t⁻¹ = Ψ₁ (σs x) := by
    intro x
    simp only [hΨ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hβ, hβ']
    congr 1
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hC : Ψ.range ⊓ centralizer ({t} : Set G) = (fixedSubgroup σs).map Ψ₁ := by
    rw [← hrange₁]
    exact SymplecticPilot.range_inf_centralizer_eq_map hinj₁ hσΨ₁
  obtain ⟨hQ, -⟩ := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    n F (by omega)
  have hQne : ∃ v, coordinateQuadPlus n F v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.exists_ne_zero_of_nondeg
      (by omega : 0 < 2 * n) hQ
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    E7Pilot.commutator_range_of_commutator_top _ (E7Pilot.commutator_top_coordinatePlus (by omega))
  have hcore := E7Pilot.perfectCore_fixedSubgroup_fieldAutT
    (E7Pilot.coordinateQuadPlus_fieldMap n σ) hσk hext hQne hJ
  have hιinj : Function.Injective (incl k hext) := incl_injective k hext (by omega)
  set ε : matrixProjectiveDerived (coordinateQuadPlus n k) →* G := Ψ₁.comp (incl k hext)
    with hε
  have hεinj : Function.Injective ε := hinj₁.comp hιinj
  have hperf : ⁅ε.range, ε.range⁆ = ε.range :=
    E7Pilot.commutator_range_of_commutator_top _ (E7Pilot.commutator_top_coordinatePlus (by omega))
  have hεC : ε.range ≤ centralizer ({t} : Set G) := by
    have h1 : ε.range ≤ (fixedSubgroup σs).map Ψ₁ := by
      rintro _ ⟨y, rfl⟩
      refine ⟨incl k hext y, ?_, rfl⟩
      have h2 : incl k hext y ∈ perfectCore (fixedSubgroup σs) := by
        rw [hcore]
        exact ⟨y, rfl⟩
      exact CFSG.Quasithin.perfectCore_le _ h2
    rw [← hC] at h1
    exact h1.trans inf_le_right
  have hle : ε.range ≤ L := std_perfect_le hset hOut htC ht hperf hεC
  have hcard : Nat.card L ≤ Nat.card ε.range := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv,
      Nat.card_congr (fieldRangeEquiv ι n (by omega)).toEquiv]
  have hεL : ε.range = L := Subgroup.eq_of_le_of_card_ge hle hcard
  set E : matrixProjectiveDerived (coordinateQuadPlus n k) ≃* L :=
    (MonoidHom.ofInjective hεinj).trans (MulEquiv.subgroupCongr hεL) with hE
  refine ⟨Ψ₁, E.symm.trans (fieldRangeEquiv ι n (by omega)).symm, hrange₁, fun x => ?_⟩
  rfl

end Renormalize

section TriRoot

open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore map_centralizerPerfectCore)

@[expose] def PlusFourTriRootInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (j : Fin 4),
      ∃ (j' : Fin 4) (x : matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        (plusSignedLevelTorus K (plusNodeSet 4 j) (plusNodeFlip 4 j)).map δ.toMonoidHom =
          (plusSignedLevelTorus K (plusNodeSet 4 j') (plusNodeFlip 4 j')).map
            (MulAut.conj x).toMonoidHom

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ}

theorem modelToG_map_conj_plus (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K))
    (A : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    modelToG e (A.map (MulAut.conj x).toMonoidHom) =
      (modelToG e A).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  rw [modelToG, modelToG, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

theorem modelToG_congr_plus (e e' : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K))
    (A : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    modelToG e' A = modelToG e (A.map (e'.symm.trans e).toMonoidHom) := by
  have h : e.symm.toMonoidHom.comp (e'.symm.trans e).toMonoidHom = e'.symm.toMonoidHom := by
    ext y
    simp
  have h2 : A.map e'.symm.toMonoidHom =
      (A.map (e'.symm.trans e).toMonoidHom).map e.symm.toMonoidHom := by
    rw [Subgroup.map_map, h]
  rw [modelToG, modelToG, h2]

theorem iSup_plusNode_le_of_triRoot (htri : PlusFourTriRootInput) {f : ℕ}
    (hKf : Nat.card K = 2 ^ f) (hK : 4 ≤ Nat.card K)
    (e e' : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    ⨆ j, plusNode e' j ≤ ⨆ j, plusNode e j := by
  have hLG := le_iSup_plusNode e (le_refl 4) hKf hK
  refine iSup_le fun j => ?_
  obtain ⟨j', x, hx⟩ := htri K hK (e'.symm.trans e) j
  have hg : ((e.symm x : L) : G) ∈ ⨆ j, plusNode e j := hLG (e.symm x).2
  have h1 : plusNode e' j =
      (plusNode e j').map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
    rw [plusNode, plusNode, plusSignedLevelCore, plusSignedLevelCore, modelToG_congr_plus e e',
      hx, modelToG_map_conj_plus, map_centralizerPerfectCore]
  rw [h1]
  calc (plusNode e j').map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom
      ≤ (⨆ j, plusNode e j).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom :=
        Subgroup.map_mono (le_iSup (fun j => plusNode e j) j')
    _ = ⨆ j, plusNode e j := Subgroup.conj_smul_eq_self_of_mem hg

end TriRoot

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conjugate_eq_of_omegaPlusFieldRow_four (hlin : OmegaPlusLinearInvolutionInput 4)
    (htri : PlusFourTriRootInput) (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j)
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F)) (h : G)
    (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G)) : CFSG.conjugate G₀ h = G₀ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hf1 : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hKc
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_plus le_rfl hf1 hKc e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFK]
    nlinarith
  set Ψ : matrixProjectiveDerived (coordinateQuadPlus 4 F) →* G :=
    (MulAut.conj h⁻¹).toMonoidHom.comp (G₀.subtype.comp ψ₀.symm.toMonoidHom) with hΨ
  have hinj : Function.Injective Ψ :=
    (MulAut.conj h⁻¹).injective.comp (G₀.subtype_injective.comp ψ₀.symm.injective)
  have hrange : Ψ.range = CFSG.conjugate G₀ h := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ψ₀.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htM)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  have hβ2 : IsPGroup 2 (zpowers β) := by
    have hdvd : orderOf β ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [_root_.sq]; exact hββ)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  obtain ⟨ψ, hψ⟩ := CFSG.ComponentClassification.RankTwoHypIIOrthogonal.exists_conj_le_image_plus_four
    (K := F) (f := 2 * f) (by omega) hF (zpowers β) hβ2
  have hβ'im : ψ⁻¹ * β * ψ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) := by
    have h1 := hψ ⟨β, mem_zpowers β, rfl⟩
    change ψ⁻¹ * β * ψ⁻¹⁻¹ ∈ _ at h1
    rwa [inv_inv] at h1
  set Ψ' : matrixProjectiveDerived (coordinateQuadPlus 4 F) →* G := Ψ.comp ψ.toMonoidHom with hΨ'
  have hinj' : Function.Injective Ψ' := hinj.comp ψ.injective
  have hrange' : Ψ'.range = Ψ.range := by
    rw [hΨ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ.surjective, ← MonoidHom.range_eq_map]
  have hβ' : ∀ x, t * Ψ' x * t⁻¹ = Ψ' ((ψ⁻¹ * β * ψ) x) := by
    intro x
    simp only [hΨ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply,
      MulAut.inv_apply, MulEquiv.apply_symm_apply]
    exact hβ (ψ x)
  have hββ' := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj' htt hβ'
  have hC := SymplecticPilot.range_inf_centralizer_eq_map hinj' hβ'
  have hCt : (fixedSubgroup (ψ⁻¹ * β * ψ)).map Ψ' ≤ centralizer ({t} : Set G) := by
    rw [← hC]
    exact inf_le_right
  rcases involution_cases_omegaPlus_of_mem_image le_rfl hσ hββ' hβ'im with ⟨s, hs1, hsβ⟩ |
      ⟨ψ'', hψ''⟩ | ⟨k, _, _, _, b, c, hirr, hk, N, hNβ, hNperf, ⟨eN⟩⟩
  ·
    exfalso
    apply hlin K F hFK s hs1
    rw [hsβ]
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt hCt
    rwa [Subgroup.card_map_of_injective hinj'] at hdvd
  ·
    obtain ⟨Φ, e', hΦr, hΦ⟩ := exists_comp_fieldEmbed_eq_twist hset.standardSetting hOut le_rfl e
      htC ht ι hfix hinj' hβ' hψ''
    have hle : CFSG.conjugate G₀ h ≤ G₀ := by
      rw [← hrange, ← hrange', ← hΦr, hG₀]
      exact (range_le_iSup_plusNode_of_comp_fieldEmbed le_rfl e' hF hF4 ι hΦ).trans
        (iSup_plusNode_le_of_triRoot htri hKc hq e e')
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge
  ·
    exfalso
    have hkK : Nat.card k = Nat.card K :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hk.trans hFK)
    have hNt : N.map Ψ' ≤ centralizer ({t} : Set G) := (Subgroup.map_mono hNβ).trans hCt
    have hNperf' : ⁅N.map Ψ', N.map Ψ'⁆ = N.map Ψ' := by
      rw [← Subgroup.map_commutator, hNperf]
    have hNL : N.map Ψ' ≤ L := std_perfect_le hset.standardSetting hOut htC ht hNperf' hNt
    have h1 : Nat.card (N.map Ψ') ≤ Nat.card L := Subgroup.card_le_of_le hNL
    rw [Subgroup.card_map_of_injective hinj', Nat.card_congr eN.toEquiv,
      Nat.card_congr e.toEquiv] at h1
    exact absurd h1 (not_le.2 (card_coordinatePlus_lt_card_coordinateMinus le_rfl hkK hirr))

theorem omegaPlusFourUniqueInput_of_inputs (hlin : OmegaPlusLinearInvolutionInput 4)
    (htri : PlusFourTriRootInput) : OmegaPlusFourUniqueInput := by
  intro G _ _ L hset f K _ _ _ hKc hf2 e t ht hKt F _ _ _ ι σ hσ hfix G₀ hG₀ hψ₀ g hg
  obtain ⟨ψ₀⟩ := hψ₀
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  exact F4Pilot.unique_of_forall_conjugate_eq (fun h htM =>
    conjugate_eq_of_omegaPlusFieldRow_four hlin htri hset hKc hq e ht hKt ι hσ hfix hG₀ ψ₀ h htM)
    g hg

end Unique

end CFSG.SeitzReduction.OmegaPilot
