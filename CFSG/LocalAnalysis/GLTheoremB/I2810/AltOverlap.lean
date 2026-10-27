module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement
open Matrix

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltOverlap

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem isSwap_conj {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap) (τ : Equiv.Perm (Fin n)) :
    (τ * σ * τ⁻¹).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  refine ⟨τ x, τ y, τ.injective.ne hxy, ?_⟩
  exact (Equiv.swap_apply_apply τ x y).symm

theorem exists_conj_of_equiv {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) {Ω : Type*} [Group Ω]
    (θ₀ θ' : Ω ≃* ↥(alternatingGroup (Fin n))) :
    ∃ τ : Equiv.Perm (Fin n), ∀ g : Ω,
      ((θ' g : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
        τ * ((θ₀ g : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) * τ⁻¹ := by
  obtain ⟨τ, hτ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
    hn6).2 (θ₀.symm.trans θ' : MulAut ↥(alternatingGroup (Fin n)))
  refine ⟨τ, fun g => ?_⟩
  have := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin n)) => (φ (θ₀ g) : Equiv.Perm (Fin n))) hτ
  simpa [MulAut.conjNormal_apply] using this.symm

section Four

open SmallOmegaFour

@[expose] def polar4 (x y : ι4 → ZMod 2) : ZMod 2 := Q4 (x + y) + Q4 x + Q4 y

@[expose] def lin4 (f x : ι4 → ZMod 2) : ZMod 2 := ∑ i, f i * x i

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem refl4_check : ∀ v f : ι4 → ZMod 2, v ≠ 0 → f ≠ 0 → lin4 f v = 0 →
    (∀ x, Q4 (x + lin4 f x • v) = Q4 x) → Q4 v = 1 ∧ ∀ x, lin4 f x = polar4 x v := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem swap4_check : ∀ v : ι4 → ZMod 2, Q4 v = 1 → ∃ i j : Fin 5, i ≠ j ∧
    ∀ k : Fin 5, sing k + polar4 (sing k) v • v = sing (Equiv.swap i j k) := by
  decide +kernel

theorem comm_le_O4 : ⁅O4, O4⁆ ≤ O4 :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact O4.mul_mem (O4.mul_mem (O4.mul_mem hx hy) (O4.inv_mem hx)) (O4.inv_mem hy)

theorem mem_O4_of_omega {g : GL ι4 (ZMod 2)} (hg : g ∈ StatedOmega Q4) : g ∈ O4 :=
  comm_le_O4 (statedOmega_eq ▸ hg)

@[expose] noncomputable def omegaPerm4 : ↥(StatedOmega Q4) →* Equiv.Perm (Fin 5) :=
  toPermHom.comp
    ((Subgroup.inclusion comm_le_O4).comp (MulEquiv.subgroupCongr statedOmega_eq).toMonoidHom)

theorem omegaPerm4_eq (g : ↥(StatedOmega Q4)) :
    omegaPerm4 g = toPermHom ⟨(g : GL ι4 (ZMod 2)), mem_O4_of_omega g.2⟩ := rfl

theorem omegaPerm4_spec (g : ↥(StatedOmega Q4)) (i : Fin 5) :
    (g : GL ι4 (ZMod 2)).1 *ᵥ sing i = sing (omegaPerm4 g i) :=
  toPerm_spec ⟨g, mem_O4_of_omega g.2⟩ i

theorem sign_omegaPerm4 (g : ↥(StatedOmega Q4)) : Equiv.Perm.sign (omegaPerm4 g) = 1 := by
  have hg : (g : GL ι4 (ZMod 2)) ∈ ⁅O4, O4⁆ := by rw [← statedOmega_eq]; exact g.2
  let ψ : ↥O4 →* ℤˣ := Equiv.Perm.sign.comp toPermHom
  have hle : ⁅O4, O4⁆ ≤ ψ.ker.map O4.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine Subgroup.mem_map.2 ⟨⁅(⟨x, hx⟩ : ↥O4), (⟨y, hy⟩ : ↥O4)⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨y, hy, hyg⟩ := hle hg
  have : y = ⟨(g : GL ι4 (ZMod 2)), mem_O4_of_omega g.2⟩ := Subtype.ext hyg
  rw [this] at hy
  exact hy

theorem omegaPerm4_injective : Function.Injective omegaPerm4 := fun g h hgh =>
  (MulEquiv.subgroupCongr statedOmega_eq).injective
    (Subgroup.inclusion_injective comm_le_O4 (toPermHom_injective hgh))

@[expose] noncomputable def thetaFour : ↥(StatedOmega Q4) ≃* ↥(alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective
    (omegaPerm4.codRestrict (alternatingGroup (Fin 5))
      fun g => Equiv.Perm.mem_alternatingGroup.2 (sign_omegaPerm4 g))
    (Function.Injective.bijective_of_nat_card_le
      (fun g h hgh => omegaPerm4_injective (congrArg Subtype.val hgh))
      (by rw [card_alternatingGroup_five, card_statedOmega_quadMinus_two]))

theorem thetaFour_apply (g : ↥(StatedOmega Q4)) :
    ((thetaFour g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = omegaPerm4 g := rfl

@[expose] def singSum : (Fin 5 → ZMod 2) →+ (ι4 → ZMod 2) where
  toFun x := ∑ i, x i • sing i
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem singSum_apply (x : Fin 5 → ZMod 2) : singSum x = ∑ i, x i • sing i := rfl

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem singSum_one : ∑ i, sing i = 0 := by decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem singSum_ker : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → ∑ i, x i • sing i = 0 → x = 0 := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem singSum_surj : ∀ v : ι4 → ZMod 2, ∃ x : Fin 5 → ZMod 2, ∑ i, x i = 0 ∧
    ∑ i, x i • sing i = v := by
  decide +kernel

@[expose] noncomputable def gammaFour : AltHeart 5 →+ (ι4 → ZMod 2) :=
  QuotientAddGroup.lift _ (singSum.comp (evenWt 5).subtype) (by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf] at hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx.1
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← hk,
      map_zsmul]
    have : singSum (fun _ : Fin 5 => (1 : ZMod 2)) = 0 := by
      rw [singSum_apply]
      simpa using singSum_one
    rw [this, smul_zero])

theorem gammaFour_bijective : Function.Bijective gammaFour := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
    have hx := x.2
    simp only [evenWt, AddMonoidHom.mem_ker, AddMonoidHom.finsetSum_apply,
      Pi.evalAddMonoidHom_apply] at hx
    have h0 : (x : Fin 5 → ZMod 2) = 0 := singSum_ker _ hx hw
    have : x = 0 := Subtype.ext h0
    rw [this]
    rfl
  · intro v
    obtain ⟨x, hx, hxv⟩ := singSum_surj v
    refine ⟨QuotientAddGroup.mk ⟨x, ?_⟩, hxv⟩
    simpa [evenWt] using hx

@[expose] noncomputable def betaFour : (ι4 → ZMod 2) ≃+ AltHeart 5 :=
  (AddEquiv.ofBijective gammaFour gammaFour_bijective).symm

theorem gammaFour_betaFour (v : ι4 → ZMod 2) : gammaFour (betaFour v) = v :=
  (AddEquiv.ofBijective gammaFour gammaFour_bijective).apply_symm_apply v

theorem gammaFour_altHeartAct (σ : Equiv.Perm (Fin 5)) (M : Matrix ι4 ι4 (ZMod 2))
    (hM : ∀ i, M *ᵥ sing i = sing (σ i)) (w : AltHeart 5) :
    gammaFour (altHeartAct 5 σ w) = M *ᵥ gammaFour w := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
  show ∑ i, ((permEven 5 σ x : ↥(evenWt 5)) : Fin 5 → ZMod 2) i • sing i =
    M *ᵥ ∑ i, (x : Fin 5 → ZMod 2) i • sing i
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hM]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (x : Fin 5 → ZMod 2) (σ⁻¹ (σ j)) • sing (σ j) = _
  simp

theorem equiv4 : ∃ (θ' : ↥(StatedOmega Q4) ≃* ↥(alternatingGroup (Fin 5)))
    (β : (ι4 → ZMod 2) ≃+ AltHeart 5), ∀ (g : ↥(StatedOmega Q4)) (v : ι4 → ZMod 2),
      β (Matrix.mulVec ((g : GL ι4 (ZMod 2)) : Matrix ι4 ι4 (ZMod 2)) v) =
        altHeartAct 5 (θ' g : Equiv.Perm (Fin 5)) (β v) := by
  refine ⟨thetaFour, betaFour, fun g v => ?_⟩
  apply gammaFour_bijective.1
  rw [gammaFour_betaFour, thetaFour_apply,
    gammaFour_altHeartAct (omegaPerm4 g) _ (omegaPerm4_spec g), gammaFour_betaFour]

theorem swap_of_transvection4 (θ' : ↥(StatedOmega Q4) ≃* ↥(alternatingGroup (Fin 5)))
    (t : GL ι4 (ZMod 2)) (ht : IsTransvection t)
    (hQ : ∀ x, Q4 (Matrix.mulVec (t : Matrix ι4 ι4 (ZMod 2)) x) = Q4 x) :
    ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧ ∀ g g' : ↥(StatedOmega Q4),
      (g' : GL ι4 (ZMod 2)) = t * g * t⁻¹ →
        ((θ' g' : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
          σ * ((θ' g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * σ⁻¹ := by
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := ht
  set fc : ι4 → ZMod 2 := fun i => f (fun j => if i = j then 1 else 0) with hfc
  have hfx : ∀ x, f x = lin4 fc x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, lin4]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hfc0 : fc ≠ 0 := by
    intro h0
    apply hf
    refine LinearMap.ext fun x => ?_
    rw [hfx, lin4]
    simp [h0]
  have hfv' : lin4 fc v = 0 := by rw [← hfx]; exact hfv
  have hQ' : ∀ x, Q4 (x + lin4 fc x • v) = Q4 x := fun x => by
    have := hQ x
    rw [htx x, hfx] at this
    exact this
  obtain ⟨hQv, hlin⟩ := refl4_check v fc hv hfc0 hfv' hQ'
  obtain ⟨i, j, hij, hsw⟩ := swap4_check v hQv
  have ht4 : t ∈ O4 := hQ
  have hperm : toPerm ⟨t, ht4⟩ = Equiv.swap i j := by
    apply toPerm_eq
    intro k
    show (t : Matrix ι4 ι4 (ZMod 2)) *ᵥ sing k = _
    rw [htx, hfx, hlin, hsw k]
  have hcompat : ∀ g g' : ↥(StatedOmega Q4), (g' : GL ι4 (ZMod 2)) = t * g * t⁻¹ →
      omegaPerm4 g' = Equiv.swap i j * omegaPerm4 g * (Equiv.swap i j)⁻¹ := by
    intro g g' hg'
    have h1 : (⟨(g' : GL ι4 (ZMod 2)), mem_O4_of_omega g'.2⟩ : ↥O4) =
        ⟨t, ht4⟩ * ⟨(g : GL ι4 (ZMod 2)), mem_O4_of_omega g.2⟩ * ⟨t, ht4⟩⁻¹ :=
      Subtype.ext hg'
    rw [omegaPerm4_eq, omegaPerm4_eq, h1, map_mul, map_mul, map_inv]
    change toPerm ⟨t, ht4⟩ * _ * (toPerm ⟨t, ht4⟩)⁻¹ = _
    rw [hperm]
  obtain ⟨τ, hτ⟩ := exists_conj_of_equiv (n := 5) (by norm_num) (by norm_num) thetaFour θ'
  refine ⟨τ * Equiv.swap i j * τ⁻¹, isSwap_conj ⟨i, j, hij, rfl⟩ τ, fun g g' hg' => ?_⟩
  rw [hτ g', hτ g, thetaFour_apply, thetaFour_apply, hcompat g g' hg']
  group

end Four

section Six

open SmallOmegaSix

@[expose] def lin6 (f x : ι6 → ZMod 2) : ZMod 2 := ∑ i, f i * x i

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem refl6_check : ∀ v f : ι6 → ZMod 2, v ≠ 0 → f ≠ 0 → lin6 f v = 0 →
    (∀ x, Q6 (x + lin6 f x • v) = Q6 x) → Q6 v = 1 ∧ ∀ x, lin6 f x = polar6 x v := by
  decide +kernel

theorem comm_le_O6 : ⁅O6, O6⁆ ≤ O6 :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact O6.mul_mem (O6.mul_mem (O6.mul_mem hx hy) (O6.inv_mem hx)) (O6.inv_mem hy)

theorem mem_O6_of_omega {g : GL ι6 (ZMod 2)} (hg : g ∈ StatedOmega Q6) : g ∈ O6 :=
  comm_le_O6 (statedOmega_eq ▸ hg)

@[expose] noncomputable def omegaPerm6 : ↥(StatedOmega Q6) →* Equiv.Perm (Fin 8) :=
  o6MulEquivPerm.symm.toMonoidHom.comp
    ((Subgroup.inclusion comm_le_O6).comp (MulEquiv.subgroupCongr statedOmega_eq).toMonoidHom)

theorem omegaPerm6_eq (g : ↥(StatedOmega Q6)) :
    omegaPerm6 g = o6MulEquivPerm.symm ⟨(g : GL ι6 (ZMod 2)), mem_O6_of_omega g.2⟩ := rfl

theorem psi_omegaPerm6 (g : ↥(StatedOmega Q6)) : psi (omegaPerm6 g) = (g : GL ι6 (ZMod 2)) := by
  have h := o6MulEquivPerm.apply_symm_apply ⟨(g : GL ι6 (ZMod 2)), mem_O6_of_omega g.2⟩
  rw [← omegaPerm6_eq] at h
  exact congrArg Subtype.val h

theorem sign_omegaPerm6 (g : ↥(StatedOmega Q6)) : Equiv.Perm.sign (omegaPerm6 g) = 1 := by
  have hg : (g : GL ι6 (ZMod 2)) ∈ ⁅O6, O6⁆ := by rw [← statedOmega_eq]; exact g.2
  let ψ : ↥O6 →* ℤˣ := Equiv.Perm.sign.comp o6MulEquivPerm.symm.toMonoidHom
  have hle : ⁅O6, O6⁆ ≤ ψ.ker.map O6.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine Subgroup.mem_map.2 ⟨⁅(⟨x, hx⟩ : ↥O6), (⟨y, hy⟩ : ↥O6)⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨y, hy, hyg⟩ := hle hg
  have : y = ⟨(g : GL ι6 (ZMod 2)), mem_O6_of_omega g.2⟩ := Subtype.ext hyg
  rw [this] at hy
  exact hy

theorem omegaPerm6_injective : Function.Injective omegaPerm6 := fun g h hgh =>
  Subtype.ext (by rw [← psi_omegaPerm6 g, ← psi_omegaPerm6 h, hgh])

@[expose] noncomputable def thetaSix : ↥(StatedOmega Q6) ≃* ↥(alternatingGroup (Fin 8)) :=
  MulEquiv.ofBijective
    (omegaPerm6.codRestrict (alternatingGroup (Fin 8))
      fun g => Equiv.Perm.mem_alternatingGroup.2 (sign_omegaPerm6 g))
    (Function.Injective.bijective_of_nat_card_le
      (fun g h hgh => omegaPerm6_injective (congrArg Subtype.val hgh))
      (by rw [card_alternatingGroup_eight, card_statedOmega_quadPlus_three]))

theorem thetaSix_apply (g : ↥(StatedOmega Q6)) :
    ((thetaSix g : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) = omegaPerm6 g := rfl

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem Tm_ker : ∀ x : Fin 8 → ZMod 2, ∑ k, x k = 0 → Tm *ᵥ x = 0 → x = 0 ∨ x = one8 := by
  decide +kernel

@[expose] noncomputable def gammaSix : AltHeart 8 →+ (ι6 → ZMod 2) :=
  QuotientAddGroup.lift _
    ((Matrix.mulVecLin Tm : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (ι6 → ZMod 2)).toAddMonoidHom.comp
      (evenWt 8).subtype) (by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf] at hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx.1
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← hk, map_zsmul]
    have h1 : (Matrix.mulVecLin Tm : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (ι6 → ZMod 2)).toAddMonoidHom
        (fun _ : Fin 8 => (1 : ZMod 2)) = 0 := T_one
    rw [h1, smul_zero])

theorem gammaSix_bijective : Function.Bijective gammaSix := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
    have hx := x.2
    simp only [evenWt, AddMonoidHom.mem_ker, AddMonoidHom.finsetSum_apply,
      Pi.evalAddMonoidHom_apply] at hx
    rcases Tm_ker _ hx hw with h0 | h1
    · have : x = 0 := Subtype.ext h0
      rw [this]
      rfl
    · rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
      refine ⟨AddSubgroup.mem_zmultiples_iff.2 ⟨1, by rw [one_zsmul]; exact h1.symm⟩, x.2⟩
  · intro v
    refine ⟨QuotientAddGroup.mk ⟨Fm *ᵥ v, ?_⟩, ?_⟩
    · simpa [evenWt] using F_even v
    · show Tm *ᵥ (Fm *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, TF, Matrix.one_mulVec]

@[expose] noncomputable def betaSix : (ι6 → ZMod 2) ≃+ AltHeart 8 :=
  (AddEquiv.ofBijective gammaSix gammaSix_bijective).symm

theorem gammaSix_betaSix (v : ι6 → ZMod 2) : gammaSix (betaSix v) = v :=
  (AddEquiv.ofBijective gammaSix gammaSix_bijective).apply_symm_apply v

theorem gammaSix_altHeartAct (σ : Equiv.Perm (Fin 8)) (w : AltHeart 8) :
    gammaSix (altHeartAct 8 σ w) = Mm σ *ᵥ gammaSix w := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
  show Tm *ᵥ ((permEven 8 σ x : ↥(evenWt 8)) : Fin 8 → ZMod 2) = Mm σ *ᵥ (Tm *ᵥ (x : Fin 8 → ZMod 2))
  have hx : ∑ k, (x : Fin 8 → ZMod 2) k = 0 := by
    have := x.2
    simpa [evenWt] using this
  have h1 : ((permEven 8 σ x : ↥(evenWt 8)) : Fin 8 → ZMod 2) = Pm σ *ᵥ (x : Fin 8 → ZMod 2) := by
    rw [Pm_mulVec]; rfl
  rw [h1, Mm_mulVec]
  rcases FT _ hx with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, Pm_one8, Matrix.mulVec_add, T_one, add_zero]

theorem equiv6 : ∃ (θ' : ↥(StatedOmega Q6) ≃* ↥(alternatingGroup (Fin 8)))
    (β : (ι6 → ZMod 2) ≃+ AltHeart 8), ∀ (g : ↥(StatedOmega Q6)) (v : ι6 → ZMod 2),
      β (Matrix.mulVec ((g : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) v) =
        altHeartAct 8 (θ' g : Equiv.Perm (Fin 8)) (β v) := by
  refine ⟨thetaSix, betaSix, fun g v => ?_⟩
  apply gammaSix_bijective.1
  rw [gammaSix_betaSix, thetaSix_apply, gammaSix_altHeartAct, gammaSix_betaSix,
    ← psi_val, psi_omegaPerm6]

theorem swap_of_transvection6 (θ' : ↥(StatedOmega Q6) ≃* ↥(alternatingGroup (Fin 8)))
    (t : GL ι6 (ZMod 2)) (ht : IsTransvection t)
    (hQ : ∀ x, Q6 (Matrix.mulVec (t : Matrix ι6 ι6 (ZMod 2)) x) = Q6 x) :
    ∃ σ : Equiv.Perm (Fin 8), σ.IsSwap ∧ ∀ g g' : ↥(StatedOmega Q6),
      (g' : GL ι6 (ZMod 2)) = t * g * t⁻¹ →
        ((θ' g' : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) =
          σ * ((θ' g : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) * σ⁻¹ := by
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := ht
  set fc : ι6 → ZMod 2 := fun i => f (fun j => if i = j then 1 else 0) with hfc
  have hfx : ∀ x, f x = lin6 fc x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, lin6]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hfc0 : fc ≠ 0 := by
    intro h0
    apply hf
    refine LinearMap.ext fun x => ?_
    rw [hfx, lin6]
    simp [h0]
  have hfv' : lin6 fc v = 0 := by rw [← hfx]; exact hfv
  have hQ' : ∀ x, Q6 (x + lin6 fc x • v) = Q6 x := fun x => by
    have := hQ x
    rw [htx x, hfx] at this
    exact this
  obtain ⟨hQv, hlin⟩ := refl6_check v fc hv hfc0 hfv' hQ'
  obtain ⟨i, j, hij, hvu⟩ := uvec_surj v hQv
  have htpsi : t = psi (Equiv.swap i j) := by
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [psi_val, swap_formula i j hij, htx, hfx, hlin, hvu]
  have hcompat : ∀ g g' : ↥(StatedOmega Q6), (g' : GL ι6 (ZMod 2)) = t * g * t⁻¹ →
      omegaPerm6 g' = Equiv.swap i j * omegaPerm6 g * (Equiv.swap i j)⁻¹ := by
    intro g g' hg'
    apply psi_injective
    rw [psi_omegaPerm6, hg', htpsi, map_mul, map_mul, map_inv, psi_omegaPerm6]
  obtain ⟨τ, hτ⟩ := exists_conj_of_equiv (n := 8) (by norm_num) (by norm_num) thetaSix θ'
  refine ⟨τ * Equiv.swap i j * τ⁻¹, isSwap_conj ⟨i, j, hij, rfl⟩ τ, fun g g' hg' => ?_⟩
  rw [hτ g', hτ g, thetaSix_apply, thetaSix_apply, hcompat g g' hg']
  group

end Six

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltOverlap
