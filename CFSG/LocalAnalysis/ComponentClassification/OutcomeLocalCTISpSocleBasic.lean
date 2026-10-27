module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleSteps
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}
  {r e : ℕ} {K : Type} [Field K]

theorem sp_socle_inner_false (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hr : 1 ≤ r) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* StatedProj (StatedSp r K))
    {ρ : A →* MulAut (StatedProj (StatedSp r K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) (hZ : center (StatedProj (StatedSp r K)) = ⊥)
    (hρa : ρ a ∈ OuterAutomorphisms.inner (StatedProj (StatedSp r K))) : False := by
  have hconj := conj_injective_of_center_eq_bot hZ
  obtain ⟨t, ht⟩ := hρa
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ hconj t, ht, orderOf_injective ρ hinj a, ha]
  have hW : W.map ρ = OuterAutomorphisms.inner (StatedProj (StatedSp r K)) :=
    map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      ((MulAut.conj : StatedProj (StatedSp r K) →* _).range ⊓ centralizer {MulAut.conj t}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rw [hCWimg, ← ht] at this
    exact this
  exact UnbalancingLocal.ComponentFree.no_component_of_mulEquiv
    (UnbalancingLocal.ComponentFree.centralizerRangeEquiv hconj t).symm
    (even_symplectic_involution_centralizers_component_free he hr hK t ht2) _
    ((isComponentOf_iff_isComponent_subgroupOf hL₁.1).mp hL₁)

theorem sp_socle_field_case [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hr : 2 ≤ r) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* StatedProj (StatedSp r K))
    {ρ : A →* MulAut (StatedProj (StatedSp r K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) {g : StatedSp r K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hρa : ρ a = spInner r K g * fieldAut r K σ) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) :
    r = 2 ∧ e = 2 ∧ p = 3 ∧ f = 2 ∧ (∀ t, σ t = t ^ 2) ∧
      StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 ∧ IsSimpleGroup L ∧
      (let ι₀ := (spInner r K).comp (subfieldSpHom r (descentField σ))
       let N₀ := ι₀.range
       let N₀' : Subgroup (MulAut (StatedProj (StatedSp r K))) := ⁅N₀, N₀⁆
       Function.Injective ι₀ ∧
       centralizer {fieldAut r K σ} ⊓ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) = N₀ ∧
       (∃ E : N₀ ≃* PresentationLocal.sympFour, ∀ x : N₀,
         (x : MulAut (StatedProj (StatedSp r K))) ∈ N₀' ↔
           PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
       Nonempty (N₀ ≃* Equiv.Perm (Fin 6)) ∧ Nonempty (N₀' ≃* alternatingGroup (Fin 6)) ∧
       ∃ h : StatedSp r K,
         ρ a = spInner r K h * fieldAut r K σ * (spInner r K h)⁻¹ ∧
         (centralizer {a}).map ρ = ρ.range ⊓
           (centralizer {fieldAut r K σ}).map (MulAut.conj (spInner r K h)).toMonoidHom ∧
         (W ⊓ centralizer {a}).map ρ = N₀.map (MulAut.conj (spInner r K h)).toMonoidHom ∧
         L.map ρ = N₀'.map (MulAut.conj (spInner r K h)).toMonoidHom ∧
         ∃ θ : L ≃* N₀', ∀ l : L,
           (θ l : MulAut (StatedProj (StatedSp r K))) =
             (spInner r K h)⁻¹ * ρ l * spInner r K h) := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hαα : ρ a * ρ a = 1 := by rw [← map_mul, ← sq, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, hk, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) he hK hαα g σ hρa hσ
  rw [← spInner_apply] at hh
  have he2 : 2 ≤ e := by
    obtain ⟨m, hm⟩ := heven
    omega
  obtain ⟨hNI, -, hι₀inj, ⟨act, -, Θ, hΘ⟩, -, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores hr he2 heven hK σ hσx
  set ι₀ := (spInner r K).comp (subfieldSpHom r (descentField σ)) with hι₀
  set N₀ := ι₀.range with hN₀
  have hNC : N₀ ≤ centralizer {fieldAut r K σ} := by
    rintro _ ⟨u, rfl⟩
    have hmem := (Θ ⟨u, 1⟩).2
    rw [hΘ, map_one, mul_one] at hmem
    exact (mem_inf.mp hmem).2
  have hIC : centralizer {fieldAut r K σ} ⊓ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) =
      N₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hNC hNI)
    obtain ⟨hxC, hxI⟩ := mem_inf.mp hx
    have hxE : x ∈ spSemilinearAutGroup r K ⊓ centralizer {fieldAut r K σ} :=
      mem_inf.mpr ⟨inner_le_spSemilinearAutGroup hxI, hxC⟩
    obtain ⟨⟨u, φ'⟩, hu⟩ := Θ.surjective ⟨x, hxE⟩
    have hx' : x = spInner r K (subfieldSpHom r (descentField σ) u) * fieldAut r K φ' := by
      rw [← hΘ]
      exact (congrArg Subtype.val hu).symm
    rw [← range_spInner] at hxI
    obtain ⟨s, hs⟩ := hxI
    have h1 : spInner r K s * fieldAut r K 1 =
        spInner r K (subfieldSpHom r (descentField σ) u) * fieldAut r K φ' := by
      rw [map_one, mul_one, hs, hx']
    obtain ⟨-, hφ'⟩ := spInner_mul_fieldAut_inj h1
    rw [hx', ← hφ', map_one, mul_one]
    exact ⟨u, rfl⟩
  set χ := spInner r K h with hχ
  have hW : W.map ρ = OuterAutomorphisms.inner (StatedProj (StatedSp r K)) :=
    map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hCA' : (centralizer {a}).map ρ = ρ.range ⊓
      (centralizer {fieldAut r K σ}).map (MulAut.conj χ).toMonoidHom := by
    rw [hCAimg, hh, map_conj_centralizer_singleton']
  have hCW' : (W ⊓ centralizer {a}).map ρ = N₀.map (MulAut.conj χ).toMonoidHom := by
    rw [hCWimg, hh, ← map_conj_inner_inf_centralizer, inf_comm, hIC]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (N₀.map (MulAut.conj χ).toMonoidHom) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCW'] at this
  have hid : (MulAut.conj χ⁻¹).toMonoidHom.comp (MulAut.conj χ).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hid' : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : Subgroup (MulAut (StatedProj (StatedSp r K))),
      L₀ = (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ ι₀.range := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [Subgroup.map_map _ (MulAut.conj χ⁻¹).toMonoidHom (MulAut.conj χ).toMonoidHom, hid,
      Subgroup.map_id, ← hL₀def] at this
  have hback : ∀ X : Subgroup (MulAut (StatedProj (StatedSp r K))), L₀ = X →
      L.map ρ = X.map (MulAut.conj χ).toMonoidHom := by
    intro X hX
    rw [← hX, hL₀def, Subgroup.map_map _ (MulAut.conj χ).toMonoidHom
      (MulAut.conj χ⁻¹).toMonoidHom, hid', Subgroup.map_id]
  let eL : L ≃* L₀ := (L.equivMapOfInjective ρ hinj).trans
    (((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective).trans
      (MulEquiv.subgroupCongr hL₀def.symm))
  have heL : ∀ l : L, (eL l : MulAut (StatedProj (StatedSp r K))) = χ⁻¹ * ρ l * χ := by
    intro l
    change MulAut.conj χ⁻¹ (ρ l) = _
    rw [MulAut.conj_apply, inv_inv]
  have hLnab := exists_ne_commute_of_isQuasisimple hLCW.2.2
  have hdim : Module.finrank (descentField σ) (Fin r ⊕ Fin r → descentField σ) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  rcases symplectic_component_dichotomy hι₀inj hL₀ hk (by omega : 1 ≤ r) (by omega)
      (pairedSympForm (descentField σ) r) pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate hdim
      CatalogueBSymplecticB.statedSpIsometryEquiv with
    ⟨-, -, hXs, -, ⟨eX⟩⟩ | ⟨he1, hr2, hXc, hE, hP6, ⟨eA⟩⟩
  ·
    exfalso
    have : IsSimpleGroup L₀ := hXs
    have : IsSimpleGroup L := eL.isSimpleGroup
    obtain ⟨eZ⟩ := nonempty_quotient_center_mulEquiv hLnab (eL.trans eX)
    obtain ⟨hr1, -⟩ := source_of_symplectic hk (by omega) eZ hp2 hsrc
    omega
  ·
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have eLA : L ≃* alternatingGroup (Fin 6) :=
      (eL.trans (MulEquiv.subgroupCongr hXc)).trans eA
    have : IsSimpleGroup L := eLA.isSimpleGroup
    obtain ⟨eZ⟩ := nonempty_quotient_center_mulEquiv hLnab eLA
    obtain ⟨hp3, hf2, hpsl, hA7, hP34⟩ := source_of_alternating_six eZ hp2 hsrc
    have he2' : e = 2 := by
      obtain ⟨m, hm⟩ := heven
      omega
    refine ⟨hr2, he2', hp3, hf2, fun t => by rw [hσx, he1, pow_one], hpsl, hA7, hP34, this,
      hι₀inj, hIC, hE, hP6, ⟨eA⟩, h, hh, hCA', hCW', hback _ hXc,
      eL.trans (MulEquiv.subgroupCongr hXc), fun l => ?_⟩
    exact heL l

end CFSG.ComponentClassification.OutcomeLocal
