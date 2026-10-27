module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalType
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap Matrix CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus)
open CFSG.Open (pRank StatedOmega StatedQuadMinus StatedProj StatedScalars)
open scoped commutatorElement

variable {K : Type} [Field K] {b c : K}

abbrev OmegaIdx : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

abbrev omegaMinus8 (K : Type) [Field K] (b c : K) : Subgroup (GL OmegaIdx K) :=
  StatedOmega (StatedQuadMinus 4 K b c)

@[expose] noncomputable def toModelIso [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (quadMinus 4 K b c).IsometryEquiv (modelForm b c) :=
  (nonempty_isometry_modelForm h3 hbc).some

theorem modelForm_regular [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin (modelForm b c)).Nondegenerate ∧
      ∃ T : Submodule K (ModelSpace K), finrank K T = 3 ∧ ∀ x ∈ T, modelForm b c x = 0 := by
  refine ⟨nondegenerate_polarBilin_modelForm h3 hbc, ?_⟩
  obtain ⟨-, T₀, hT₀, hT₀Q⟩ := regular_quadMinus (n := 4) (b := b) (c := c) le_rfl hbc
  refine ⟨T₀.map (toModelIso h3 hbc).toLinearEquiv.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hT₀
  · rintro _ ⟨y, hy, rfl⟩
    have key : ∀ x, modelForm b c ((toModelIso h3 hbc).toLinearEquiv x) = quadMinus 4 K b c x :=
      (toModelIso h3 hbc).map_app
    rw [LinearEquiv.coe_coe, key]
    exact hT₀Q y hy

theorem modelOmega_le_modelO (b c : K) : modelOmega b c ≤ modelO b c :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem modelOmega_eq_elementaryGroup [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    modelOmega b c = elementaryGroup (modelForm b c) := by
  obtain ⟨hQ, hT⟩ := modelForm_regular h3 hbc
  exact (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1

theorem modelO_le_closure_reflect [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    modelO b c ≤ Subgroup.closure (Set.range (reflect (modelForm b c)) ∪ modelOmega b c) := by
  obtain ⟨hQ, hT⟩ := modelForm_regular h3 hbc
  rw [modelOmega_eq_elementaryGroup h3 hbc]
  exact (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).2

theorem mem_modelOmega_of_odd [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : ModelSpace K ≃ₗ[K] ModelSpace K}
    (hg : g ∈ modelO b c) (hodd : Odd (orderOf g)) : g ∈ modelOmega b c := by
  obtain ⟨hQ, hT⟩ := modelForm_regular h3 hbc
  obtain ⟨-, -, -, -, -, -, hoddmem, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  exact hoddmem g hg hodd

theorem eichler_mem_modelOmega [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u w : ModelSpace K) :
    eichler (modelForm b c) u w ∈ modelOmega b c := by
  rw [modelOmega_eq_elementaryGroup h3 hbc]
  exact eichler_mem_elementaryGroup _ u w

theorem conj_mem_modelOmega {g x : ModelSpace K ≃ₗ[K] ModelSpace K} (hg : g ∈ modelO b c)
    (hx : x ∈ modelOmega b c) : g * x * g⁻¹ ∈ modelOmega b c := by
  have hle : modelOmega b c ≤ (modelOmega b c).comap (MulAut.conj g).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun a ha a' ha' => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h : g * ⁅a, a'⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * a' * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem hg ha) (inv_mem hg))
      (mul_mem (mul_mem hg ha') (inv_mem hg))
  exact hle hx

theorem exists_hypPair_orth_modelForm [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ P P' : HypPair (modelForm b c), P.Orth P' := by
  obtain ⟨hQ, T, hT, hTQ⟩ := modelForm_regular h3 hbc
  let t := Module.finBasisOfFinrankEq K T hT
  have ht : LinearIndependent K (fun i => (t i : ModelSpace K)) :=
    t.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  obtain ⟨P₁, P₂, P₃, h12, -, -⟩ := exists_three_hypPairs_of_family hQ ht
    (fun i => hTQ _ (t i).2)
    (fun i j => by
      have h := hTQ _ (T.add_mem (t i).2 (t j).2)
      simp only [QuadraticMap.polar]
      rw [h, hTQ _ (t i).2, hTQ _ (t j).2]
      ring)
  exact ⟨P₁, P₂, h12⟩

theorem reflect_mul_reflect_mem_modelOmega [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a d : ModelSpace K}
    (hQ : modelForm b c a = modelForm b c d) :
    reflect (modelForm b c) d * reflect (modelForm b c) a ∈ modelOmega b c := by
  by_cases ha : a = 0
  · subst ha
    have hd : modelForm b c d = 0 := by rw [← hQ]; exact QuadraticMap.map_zero _
    rw [reflect_of_map_eq_zero hd, reflect_of_map_eq_zero (QuadraticMap.map_zero _), one_mul]
    exact Subgroup.one_mem _
  by_cases hd : d = 0
  · subst hd
    have ha0 : modelForm b c a = 0 := by rw [hQ]; exact QuadraticMap.map_zero _
    rw [reflect_of_map_eq_zero (QuadraticMap.map_zero _), reflect_of_map_eq_zero ha0, one_mul]
    exact Subgroup.one_mem _
  obtain ⟨P, P', hPP'⟩ := exists_hypPair_orth_modelForm h3 hbc
  obtain ⟨hQnd, -⟩ := modelForm_regular h3 hbc
  obtain ⟨g, hg, hga⟩ := exists_mem_elementaryGroup_apply_eq hQnd hPP' ha hd hQ
  have hgO : g ∈ modelO b c := elementaryGroup_le_orthogonalGroup _ hg
  have h1 : g * reflect (modelForm b c) a * g⁻¹ = reflect (modelForm b c) d := by
    rw [reflect_conj hgO, hga]
  have h2 : reflect (modelForm b c) d * reflect (modelForm b c) a =
      ⁅g, reflect (modelForm b c) a⁆ := by
    rw [commutatorElement_def, ← h1, reflect_inv]
  rw [h2]
  exact Subgroup.commutator_mem_commutator hgO (reflect_mem_orthogonalGroup _ a)

@[expose] noncomputable def toModelGL (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c)) :
    GL OmegaIdx K ≃* (ModelSpace K ≃ₗ[K] ModelSpace K) :=
  (toLinEquiv OmegaIdx K).trans (LinearEquiv.autCongr Φ.toLinearEquiv)

theorem toModelGL_apply (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c)) (g : GL OmegaIdx K)
    (x : ModelSpace K) :
    toModelGL Φ g x = Φ.toLinearEquiv ((g : Matrix OmegaIdx OmegaIdx K) *ᵥ
      (Φ.toLinearEquiv.symm x)) := by
  simp [toModelGL, LinearEquiv.autCongr_apply_apply]

theorem map_orthogonalGroup_toModelGL (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c)) :
    (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)).map
        (LinearEquiv.autCongr Φ.toLinearEquiv).toMonoidHom = modelO b c := by
  have key : ∀ x, modelForm b c (Φ.toLinearEquiv x) = quadMinus 4 K b c x := Φ.map_app
  have key' : ∀ x, quadMinus 4 K b c (Φ.toLinearEquiv.symm x) = modelForm b c x := fun x => by
    rw [← key (Φ.toLinearEquiv.symm x), Φ.toLinearEquiv.apply_symm_apply]
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, modelO,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩ m
    rw [LinearEquiv.autCongr_apply_apply, key, hf, key']
  · refine fun hg => ⟨(LinearEquiv.autCongr Φ.toLinearEquiv).symm g, fun m => ?_,
      (LinearEquiv.autCongr Φ.toLinearEquiv).apply_symm_apply g⟩
    rw [LinearEquiv.autCongr_symm_apply_apply, key', hg, key]

theorem mem_omegaMinus8_iff (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c))
    (g : GL OmegaIdx K) : g ∈ omegaMinus8 K b c ↔ toModelGL Φ g ∈ modelOmega b c := by
  rw [omegaMinus8, statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c),
    Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  have h : modelOmega b c = ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)⁆.map
        (LinearEquiv.autCongr Φ.toLinearEquiv).toMonoidHom := by
    rw [Subgroup.map_commutator, map_orthogonalGroup_toModelGL Φ]
    rfl
  rw [h]
  have h2 : toModelGL Φ g =
      (LinearEquiv.autCongr Φ.toLinearEquiv) (toLinEquiv OmegaIdx K g) := rfl
  rw [h2, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem map_omegaMinus8_eq (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c)) :
    (omegaMinus8 K b c).map (toModelGL Φ).toMonoidHom = modelOmega b c := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_omegaMinus8_iff Φ, MulEquiv.apply_symm_apply]

@[expose] noncomputable def omegaEquiv (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c)) :
    omegaMinus8 K b c ≃* ↥(modelOmega b c) :=
  ((toModelGL Φ).subgroupMap (omegaMinus8 K b c)).trans
    (MulEquiv.subgroupCongr (map_omegaMinus8_eq Φ))

@[expose] noncomputable def omegaProj (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c)) :
    ↥(modelOmega b c) →* StatedProj (omegaMinus8 K b c) :=
  (QuotientGroup.mk' ((StatedScalars OmegaIdx K).subgroupOf (omegaMinus8 K b c))).comp
    (omegaEquiv Φ).symm.toMonoidHom

theorem cm_mem_modelOmega [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : Multiplicative (Fin 3 → ZMod 3)) : cm K v ∈ modelOmega b c := by
  refine mem_modelOmega_of_odd h3 hbc (cm_mem_modelO b c v) ?_
  have hv : v ^ 3 = 1 := by
    refine Multiplicative.toAdd.injective (funext fun i => ?_)
    simp [toAdd_pow]
    decide +revert
  have h : cm K v ^ 3 = 1 := by rw [← map_pow, hv, map_one]
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h)

@[expose] noncomputable def cmOmega [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Multiplicative (Fin 3 → ZMod 3) →* ↥(modelOmega b c) :=
  (cm K).codRestrict (modelOmega b c) (cm_mem_modelOmega h3 hbc)

@[expose] noncomputable def c₀ [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Multiplicative (Fin 3 → ZMod 3) →* ↥(omegaMinus8 K b c) :=
  (omegaEquiv (toModelIso h3 hbc)).symm.toMonoidHom.comp (cmOmega h3 hbc)

theorem omegaEquiv_c₀ [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    (omegaEquiv (toModelIso h3 hbc) (c₀ h3 hbc v) : ModelSpace K ≃ₗ[K] ModelSpace K) = cm K v := by
  simp [c₀, cmOmega]

theorem toModelGL_c₀ [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    toModelGL (toModelIso h3 hbc) ((c₀ h3 hbc v : omegaMinus8 K b c) : GL OmegaIdx K) = cm K v :=
  omegaEquiv_c₀ h3 hbc v

theorem c₀_injective [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (c₀ h3 hbc) := by
  intro v w h
  have h1 := (omegaEquiv (toModelIso h3 hbc)).symm.injective h
  exact cm_injective (congrArg Subtype.val h1)

theorem c₀_mulVec_eq_self_iff [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : Multiplicative (Fin 3 → ZMod 3))
    (w : OmegaIdx → K) :
    ((c₀ h3 hbc v : omegaMinus8 K b c) : GL OmegaIdx K) *ᵥ w = w ↔
      cm K v ((toModelIso h3 hbc).toLinearEquiv w) = (toModelIso h3 hbc).toLinearEquiv w := by
  have h1 := toModelGL_apply (toModelIso h3 hbc)
    ((c₀ h3 hbc v : omegaMinus8 K b c) : GL OmegaIdx K) ((toModelIso h3 hbc).toLinearEquiv w)
  rw [toModelGL_c₀, LinearEquiv.symm_apply_apply] at h1
  rw [h1]
  exact (toModelIso h3 hbc).toLinearEquiv.injective.eq_iff.symm

theorem fix_iff [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    {w : OmegaIdx → K |
        (((c₀ h3 hbc v : omegaMinus8 K b c) : GL OmegaIdx K) : Matrix OmegaIdx OmegaIdx K) *ᵥ
          w = w} =
      {w | ∀ v' : Multiplicative (Fin 3 → ZMod 3),
        (((c₀ h3 hbc v' : omegaMinus8 K b c) : GL OmegaIdx K) : Matrix OmegaIdx OmegaIdx K) *ᵥ
          w = w} ↔
      ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  have h1 : ∀ (u : Multiplicative (Fin 3 → ZMod 3)) (w : OmegaIdx → K),
      (((c₀ h3 hbc u : omegaMinus8 K b c) : GL OmegaIdx K) : Matrix OmegaIdx OmegaIdx K) *ᵥ w = w ↔
        ∀ i, Multiplicative.toAdd u i ≠ 0 → ((toModelIso h3 hbc).toLinearEquiv w).1 i = 0 := by
    intro u w
    rw [c₀_mulVec_eq_self_iff h3 hbc u w, cm_apply, cmEquiv_apply_eq_self_iff h3]
  have h2 : ∀ w : OmegaIdx → K, (∀ v' : Multiplicative (Fin 3 → ZMod 3),
      (((c₀ h3 hbc v' : omegaMinus8 K b c) : GL OmegaIdx K) : Matrix OmegaIdx OmegaIdx K) *ᵥ
        w = w) ↔ ∀ i, ((toModelIso h3 hbc).toLinearEquiv w).1 i = 0 := by
    intro w
    constructor
    · intro h i
      have := (h1 (Multiplicative.ofAdd (Pi.single i 1)) w).1 (h _) i (by simp)
      exact this
    · intro h u
      exact (h1 u w).2 fun i _ => h i
  constructor
  · intro hset
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := hcon
    set e := (toModelIso h3 hbc).toLinearEquiv
    have hw : e.symm (planeVec i (1, 0)) ∈ {w : OmegaIdx → K |
        (((c₀ h3 hbc v : omegaMinus8 K b c) : GL OmegaIdx K) : Matrix OmegaIdx OmegaIdx K) *ᵥ
          w = w} := by
      show _ = _
      rw [h1]
      intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp [planeVec, Pi.single_apply, hji]
    rw [hset] at hw
    have := (h2 _).1 hw i
    simp [planeVec] at this
  · intro hv
    ext w
    simp only [Set.mem_setOf_eq]
    rw [h1, h2]
    constructor
    · intro h i
      exact h i (hv i)
    · intro h i _
      exact h i

theorem orderOf_omegaEquiv_symm (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c))
    {x : ModelSpace K ≃ₗ[K] ModelSpace K} (hx : x ∈ modelOmega b c) :
    orderOf ((omegaEquiv Φ).symm ⟨x, hx⟩) = orderOf x := by
  rw [MulEquiv.orderOf_eq]
  exact Subgroup.orderOf_mk x hx

theorem commute_omegaEquiv_symm_iff (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c))
    {x y : ModelSpace K ≃ₗ[K] ModelSpace K} (hx : x ∈ modelOmega b c) (hy : y ∈ modelOmega b c) :
    Commute ((omegaEquiv Φ).symm ⟨x, hx⟩) ((omegaEquiv Φ).symm ⟨y, hy⟩) ↔ Commute x y := by
  constructor
  · intro h
    have := congrArg (omegaEquiv Φ) h.eq
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact congrArg Subtype.val this
  · intro h
    exact Commute.map (show Commute (⟨x, hx⟩ : ↥(modelOmega b c)) ⟨y, hy⟩ from Subtype.ext h.eq)
      (omegaEquiv Φ).symm

theorem omegaEquiv_symm_mem_zpowers_iff (Φ : (quadMinus 4 K b c).IsometryEquiv (modelForm b c))
    {x y : ModelSpace K ≃ₗ[K] ModelSpace K} (hx : x ∈ modelOmega b c) (hy : y ∈ modelOmega b c) :
    (omegaEquiv Φ).symm ⟨y, hy⟩ ∈ Subgroup.zpowers ((omegaEquiv Φ).symm ⟨x, hx⟩) ↔
      y ∈ Subgroup.zpowers x := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := congrArg (omegaEquiv Φ) hk
    rw [← map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact congrArg Subtype.val this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply (omegaEquiv Φ).injective
    rw [map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact Subtype.ext (by simpa using hk)

theorem omegaEquiv_symm_mem_centralizer_c₀ [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (S : Set (Multiplicative (Fin 3 → ZMod 3)))
    {x : ModelSpace K ≃ₗ[K] ModelSpace K} (hx : x ∈ modelOmega b c)
    (hS : ∀ s ∈ S, Commute x (cm K s)) :
    (omegaEquiv (toModelIso h3 hbc)).symm ⟨x, hx⟩ ∈
      Subgroup.centralizer (c₀ h3 hbc '' S : Set ↥(omegaMinus8 K b c)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  have hc : c₀ h3 hbc s =
      (omegaEquiv (toModelIso h3 hbc)).symm ⟨cm K s, cm_mem_modelOmega h3 hbc s⟩ := by
    apply (omegaEquiv (toModelIso h3 hbc)).injective
    apply Subtype.ext
    simpa using omegaEquiv_c₀ h3 hbc s
  rw [hc]
  exact ((commute_omegaEquiv_symm_iff (toModelIso h3 hbc) (cm_mem_modelOmega h3 hbc s) hx).2
    (hS s hs).symm).eq

theorem exists_conj_c₀_of_cmEquiv [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (f : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    {n : ModelSpace K ≃ₗ[K] ModelSpace K} (hn : n ∈ modelOmega b c)
    (h : ∀ v, n * cmEquiv K v * n⁻¹ = cmEquiv K (f v)) :
    ∃ m : ↥(omegaMinus8 K b c), ∀ v : Multiplicative (Fin 3 → ZMod 3),
      m * c₀ h3 hbc v * m⁻¹ = c₀ h3 hbc (Multiplicative.ofAdd (f (Multiplicative.toAdd v))) := by
  refine ⟨(omegaEquiv (toModelIso h3 hbc)).symm ⟨n, hn⟩, fun v => ?_⟩
  apply (omegaEquiv (toModelIso h3 hbc)).injective
  apply Subtype.ext
  have h1 := omegaEquiv_c₀ h3 hbc v
  have h2 := omegaEquiv_c₀ h3 hbc (Multiplicative.ofAdd (f (Multiplicative.toAdd v)))
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, h1, h2]
  exact h (Multiplicative.toAdd v)

theorem two_le_pRank_centralizer_c₀_of_model [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (S : Set (Multiplicative (Fin 3 → ZMod 3))) {x y : ModelSpace K ≃ₗ[K] ModelSpace K}
    (hx : x ∈ modelOmega b c) (hy : y ∈ modelOmega b c) (hxo : orderOf x = p)
    (hyo : orderOf y = p) (hxy : Commute x y) (hyx : y ∉ Subgroup.zpowers x)
    (hxS : ∀ s ∈ S, Commute x (cm K s)) (hyS : ∀ s ∈ S, Commute y (cm K s)) :
    2 ≤ pRank p (Subgroup.centralizer (c₀ h3 hbc '' S : Set ↥(omegaMinus8 K b c))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.GroupTheory.two_le_pRank_of_commute
    (omegaEquiv_symm_mem_centralizer_c₀ h3 hbc S hx hxS)
    (omegaEquiv_symm_mem_centralizer_c₀ h3 hbc S hy hyS)
    (by rw [orderOf_omegaEquiv_symm _ hx]; exact hxo)
    (by rw [orderOf_omegaEquiv_symm _ hy]; exact hyo)
    ((commute_omegaEquiv_symm_iff _ hx hy).2 hxy)
    (fun h => hyx ((omegaEquiv_symm_mem_zpowers_iff _ hx hy).1 h))

theorem one_le_pRank_centralizer_c₀_of_model [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (S : Set (Multiplicative (Fin 3 → ZMod 3))) {x : ModelSpace K ≃ₗ[K] ModelSpace K}
    (hx : x ∈ modelOmega b c) (hxo : orderOf x = p) (hxS : ∀ s ∈ S, Commute x (cm K s)) :
    1 ≤ pRank p (Subgroup.centralizer (c₀ h3 hbc '' S : Set ↥(omegaMinus8 K b c))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord := orderOf_omegaEquiv_symm (toModelIso h3 hbc) hx
  refine CFSG.SectionRank.le_pRank hp.one_lt
    (E := Subgroup.zpowers ((omegaEquiv (toModelIso h3 hbc)).symm ⟨x, hx⟩)) ?_ ?_ ?_
  · exact Subgroup.zpowers_le.2 (omegaEquiv_symm_mem_centralizer_c₀ h3 hbc S hx hxS)
  · refine CFSG.Open.isElemAbelian_zpowers ?_
    have := pow_orderOf_eq_one ((omegaEquiv (toModelIso h3 hbc)).symm ⟨x, hx⟩)
    rwa [hord, hxo] at this
  · rw [Nat.card_zpowers, hord, hxo, pow_one]

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
