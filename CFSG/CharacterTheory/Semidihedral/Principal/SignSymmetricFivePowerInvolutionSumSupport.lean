module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicFivePowerDefectColumnSupport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace SignSymmetric

open Equiv

@[expose] def s5Fix (π : Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun i : Fin 6 =>
    ∃ n : Fin 5, π * FiveKernel.fiveCycleList i * π⁻¹ = FiveKernel.fiveCycleList i ^ (n : ℕ)).card

theorem sum_s5Fix :
    ∑ π : Perm (Fin 5), ((s5Fix π : ℤ) - 1) * ((s5Fix π⁻¹ : ℤ) - 1) = 120 := by
  decide +kernel

theorem s5Fix_swap : ∀ x y : Fin 5, x ≠ y → s5Fix (swap x y) = 0 := by
  decide +kernel

theorem exists_swap_of_sq_eq_one_of_sign : ∀ π : Perm (Fin 5), π ^ 2 = 1 → Perm.sign π = -1 →
    ∃ x y : Fin 5, x ≠ y ∧ π = swap x y := by
  decide +kernel

theorem card_swap : (Finset.univ.filter fun π : Perm (Fin 5) =>
    ∃ x y : Fin 5, x ≠ y ∧ π = swap x y).card = 10 := by
  decide +kernel

theorem s5Fix_coe : ∀ π : alternatingGroup (Fin 5), s5Fix π = FiveKernel.sylowFixCount π := by
  decide +kernel

theorem card_alternating_involution : (Finset.univ.filter fun π : alternatingGroup (Fin 5) =>
    π ^ 2 = 1 ∧ π ≠ 1).card = 15 := by
  decide +kernel

theorem alternating_involution_conj : ∀ π π' : alternatingGroup (Fin 5), π ^ 2 = 1 → π ≠ 1 →
    π' ^ 2 = 1 → π' ≠ 1 → ∃ g : alternatingGroup (Fin 5), g * π * g⁻¹ = π' := by
  decide +kernel

section S5Action

open scoped Pointwise

@[expose, instance_reducible] noncomputable def s5Action :
    MulAction (Perm (Fin 5)) (Sylow 5 (alternatingGroup (Fin 5))) :=
  letI : MulAction (MulAut (alternatingGroup (Fin 5))) (Sylow 5 (alternatingGroup (Fin 5))) :=
    Sylow.pointwiseMulAction
  MulAction.compHom _ (MulAut.conjNormal (H := alternatingGroup (Fin 5)))

theorem s5_smul_sylowOf_eq_iff (π : Perm (Fin 5)) (i : Fin 6) :
    letI := s5Action
    π • FiveKernel.sylowOf (MulEquiv.refl _) i = FiveKernel.sylowOf (MulEquiv.refl _) i ↔
      ∃ n : Fin 5, π * FiveKernel.fiveCycleList i * π⁻¹ =
        FiveKernel.fiveCycleList i ^ (n : ℕ) := by
  let := s5Action
  set g : alternatingGroup (Fin 5) := FiveKernel.sylowGenerator (MulEquiv.refl _) i with hg
  have hgc : g = FiveKernel.fiveCycle i := rfl
  have hcoe : ((π • FiveKernel.sylowOf (MulEquiv.refl _) i : Sylow 5 _) :
      Subgroup (alternatingGroup (Fin 5))) = Subgroup.zpowers (MulAut.conjNormal π g) := by
    change MulAut.conjNormal π • ((FiveKernel.sylowOf (MulEquiv.refl _) i : Sylow 5 _) :
      Subgroup (alternatingGroup (Fin 5))) = _
    rw [Subgroup.pointwise_smul_def, FiveKernel.coe_sylowOf]
    exact MonoidHom.map_zpowers (MulAut.conjNormal π).toMonoidHom g
  have hord : orderOf (MulAut.conjNormal π g) = 5 := by
    rw [MulEquiv.orderOf_eq]
    exact FiveKernel.orderOf_sylowGenerator _ i
  have hval : ((MulAut.conjNormal π g : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      π * FiveKernel.fiveCycleList i * π⁻¹ := by
    rw [MulAut.conjNormal_apply, hgc]
    rfl
  rw [Sylow.ext_iff, hcoe, FiveKernel.coe_sylowOf]
  constructor
  · intro h
    have hmem : MulAut.conjNormal π g ∈ Subgroup.zpowers g := h ▸ Subgroup.mem_zpowers _
    obtain ⟨n, hn⟩ := (FiveKernel.mem_zpowers_sylowGenerator_iff (MulEquiv.refl _) i _).mp hmem
    refine ⟨n, ?_⟩
    have h' : ((MulAut.conjNormal π g : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        ((FiveKernel.fiveCycle i ^ (n : ℕ) : alternatingGroup (Fin 5)) : Perm (Fin 5)) :=
      congrArg Subtype.val hn
    rw [hval, SubgroupClass.coe_pow] at h'
    exact h'
  · rintro ⟨n, hn⟩
    apply FiveKernel.zpowers_eq_of_mem_of_orderOf_five hord
      (FiveKernel.orderOf_sylowGenerator _ i)
    rw [FiveKernel.mem_zpowers_sylowGenerator_iff]
    refine ⟨n, Subtype.ext ?_⟩
    rw [MulEquiv.refl_apply, hval, hn, SubgroupClass.coe_pow]
    rfl

theorem card_fixedBy_s5 (π : Perm (Fin 5)) :
    letI := s5Action
    Nat.card (MulAction.fixedBy (Sylow 5 (alternatingGroup (Fin 5))) π) = s5Fix π := by
  let := s5Action
  classical
  have h1 : Nat.card (MulAction.fixedBy (Sylow 5 (alternatingGroup (Fin 5))) π) =
      Nat.card {i : Fin 6 // π • FiveKernel.sylowOf (MulEquiv.refl _) i =
        FiveKernel.sylowOf (MulEquiv.refl _) i} :=
    Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ ⟨FiveKernel.sylowOf_injective _, FiveKernel.sylowOf_surjective _⟩)
      (fun _ => MulAction.mem_fixedBy.symm)).symm
  have h2 : Nat.card {i : Fin 6 // π • FiveKernel.sylowOf (MulEquiv.refl _) i =
        FiveKernel.sylowOf (MulEquiv.refl _) i} =
      Nat.card {i : Fin 6 // ∃ n : Fin 5, π * FiveKernel.fiveCycleList i * π⁻¹ =
        FiveKernel.fiveCycleList i ^ (n : ℕ)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun i => s5_smul_sylowOf_eq_iff π i)
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end S5Action

section Structure

open scoped Classical

variable {H : Type u} [Group H] {W E : Subgroup H} [W.Normal]
  (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥)

include hWE hdisj in
theorem mk_comp_bijective : Function.Bijective ((QuotientGroup.mk' W).comp E.subtype) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro e he
    have hW : (e : H) ∈ W := (QuotientGroup.eq_one_iff _).mp he
    have hmem : (e : H) ∈ W ⊓ E := ⟨hW, e.2⟩
    rw [hdisj] at hmem
    exact Subtype.ext hmem
  · intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective W q
    have hh : h ∈ ((W ⊔ E : Subgroup H) : Set H) := by
      rw [hWE]
      trivial
    rw [Subgroup.normal_mul] at hh
    obtain ⟨w, hw, e, he, rfl⟩ := hh
    refine ⟨⟨e, he⟩, ?_⟩
    change (QuotientGroup.mk e : H ⧸ W) = QuotientGroup.mk (w * e)
    rw [QuotientGroup.eq]
    have h := Subgroup.Normal.conj_mem inferInstance w hw e⁻¹
    rwa [inv_inv, mul_assoc] at h

@[expose] noncomputable def projE : H →* E :=
  (MulEquiv.ofBijective _ (mk_comp_bijective hWE hdisj)).symm.toMonoidHom.comp
    (QuotientGroup.mk' W)

theorem mk_projE (h : H) :
    (QuotientGroup.mk (projE hWE hdisj h : H) : H ⧸ W) = QuotientGroup.mk h :=
  (MulEquiv.ofBijective _ (mk_comp_bijective hWE hdisj)).apply_symm_apply
    (QuotientGroup.mk' W h)

theorem projE_eq_iff (h : H) (e : E) :
    projE hWE hdisj h = e ↔ (QuotientGroup.mk (e : H) : H ⧸ W) = QuotientGroup.mk h := by
  constructor
  · rintro rfl
    exact mk_projE hWE hdisj h
  · intro he
    apply (mk_comp_bijective hWE hdisj).1
    change (QuotientGroup.mk (projE hWE hdisj h : H) : H ⧸ W) = QuotientGroup.mk (e : H)
    rw [mk_projE, he]

theorem projE_coe (e : E) : projE hWE hdisj e = e := (projE_eq_iff hWE hdisj _ e).mpr rfl

theorem projE_mul_of_mem {w : H} (hw : w ∈ W) (e : E) : projE hWE hdisj (w * e) = e := by
  rw [projE_eq_iff, QuotientGroup.eq]
  have h := Subgroup.Normal.conj_mem inferInstance w hw (e : H)⁻¹
  rwa [inv_inv, mul_assoc] at h

theorem projE_of_mem {w : H} (hw : w ∈ W) : projE hWE hdisj w = 1 := by
  have h := projE_mul_of_mem hWE hdisj hw 1
  rwa [OneMemClass.coe_one, mul_one] at h

theorem mul_inv_projE_mem (h : H) : h * (projE hWE hdisj h : H)⁻¹ ∈ W := by
  have h1 := mk_projE hWE hdisj h
  rw [QuotientGroup.eq] at h1
  have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 (projE hWE hdisj h : H)
  rwa [mul_inv_cancel_left] at h2

theorem eq_mul_projE (h : H) : h = (h * (projE hWE hdisj h : H)⁻¹) * projE hWE hdisj h := by
  rw [inv_mul_cancel_right]

include hWE hdisj in
theorem mul_eq_mul_iff {w w' : H} (hw : w ∈ W) (hw' : w' ∈ W) {e e' : E}
    (h : w * (e : H) = w' * e') : w = w' ∧ e = e' := by
  have he : e = e' := by
    rw [← projE_mul_of_mem hWE hdisj hw e, h, projE_mul_of_mem hWE hdisj hw' e']
  subst he
  exact ⟨mul_right_cancel h, rfl⟩

include hWE hdisj in
theorem sum_eq_sum_mul [Fintype H] (f : H → ℂ) :
    ∑ h, f h = ∑ w : W, ∑ e : E, f ((w : H) * e) := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_bijective (fun x : W × E => (x.1 : H) * x.2) ⟨?_, ?_⟩ _ _
    fun _ => rfl).symm
  · intro x y hxy
    obtain ⟨h1, h2⟩ := mul_eq_mul_iff hWE hdisj x.1.2 y.1.2 hxy
    exact Prod.ext (Subtype.ext h1) h2
  · intro h
    exact ⟨(⟨_, mul_inv_projE_mem hWE hdisj h⟩, projE hWE hdisj h),
      (eq_mul_projE hWE hdisj h).symm⟩

include hWE hdisj in
theorem card_eq_mul [Finite H] : Nat.card H = Nat.card W * Nat.card E := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective (fun x : W × E => (x.1 : H) * x.2) ⟨?_, ?_⟩).symm
  · intro x y hxy
    obtain ⟨h1, h2⟩ := mul_eq_mul_iff hWE hdisj x.1.2 y.1.2 hxy
    exact Prod.ext (Subtype.ext h1) h2
  · intro h
    exact ⟨(⟨_, mul_inv_projE_mem hWE hdisj h⟩, projE hWE hdisj h),
      (eq_mul_projE hWE hdisj h).symm⟩

end Structure

section SupProduct

open scoped Classical

variable {H : Type u} [Group H] {W J : Subgroup H} [W.Normal]
  (hcomm : ∀ w ∈ W, ∀ j ∈ J, Commute w j) (hWJ : W ⊓ J = ⊥)

@[expose] noncomputable def supHom : W × J →* (W ⊔ J : Subgroup H) :=
  (MonoidHom.noncommCoprod W.subtype J.subtype fun w j => hcomm w w.2 j j.2).codRestrict _
    fun x => Subgroup.mul_mem_sup x.1.2 x.2.2

omit [W.Normal] in
theorem supHom_apply (x : W × J) : (supHom hcomm x : H) = x.1 * x.2 := rfl

include hWJ in
theorem supHom_bijective : Function.Bijective (supHom hcomm) := by
  constructor
  · intro x y h
    have h' : (x.1 : H) * x.2 = y.1 * y.2 := congrArg Subtype.val h
    have hmemW : (y.1 : H)⁻¹ * x.1 ∈ W := W.mul_mem (W.inv_mem y.1.2) x.1.2
    have hrel : (y.1 : H)⁻¹ * x.1 = y.2 * (x.2 : H)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
    have hmemJ : (y.1 : H)⁻¹ * x.1 ∈ J := by
      rw [hrel]
      exact J.mul_mem y.2.2 (J.inv_mem x.2.2)
    have hone : (y.1 : H)⁻¹ * x.1 = 1 := by
      have hmem : (y.1 : H)⁻¹ * x.1 ∈ W ⊓ J := ⟨hmemW, hmemJ⟩
      rw [hWJ] at hmem
      exact hmem
    have h1 : (x.1 : H) = y.1 := (inv_mul_eq_one.mp hone).symm
    have h2 : (x.2 : H) = y.2 := by
      rw [h1] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro k
    have hk : (k : H) ∈ ((W ⊔ J : Subgroup H) : Set H) := k.2
    rw [Subgroup.normal_mul] at hk
    obtain ⟨w, hw, j, hj, hwj⟩ := hk
    exact ⟨(⟨w, hw⟩, ⟨j, hj⟩), Subtype.ext hwj⟩

@[expose] noncomputable def supEquiv : W × J ≃* (W ⊔ J : Subgroup H) :=
  MulEquiv.ofBijective (supHom hcomm) (supHom_bijective hcomm hWJ)

theorem supEquiv_apply (x : W × J) : (supEquiv hcomm hWJ x : H) = x.1 * x.2 := rfl

theorem supEquiv_symm_apply {k : (W ⊔ J : Subgroup H)} {w : W} {j : J} (h : (k : H) = w * j) :
    (supEquiv hcomm hWJ).symm k = (w, j) := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext h

include hcomm hWJ in
theorem exists_sup_eq_mul (k : (W ⊔ J : Subgroup H)) : ∃ (w : W) (j : J), (k : H) = w * j :=
  ⟨((supEquiv hcomm hWJ).symm k).1, ((supEquiv hcomm hWJ).symm k).2,
    (congrArg Subtype.val ((supEquiv hcomm hWJ).apply_symm_apply k)).symm⟩

theorem coe_supEquiv_inv (w : W) (j : J) :
    (((supEquiv hcomm hWJ (w, j))⁻¹ : (W ⊔ J : Subgroup H)) : H) = (w : H)⁻¹ * (j : H)⁻¹ := by
  rw [← map_inv]
  rfl

include hcomm hWJ in
theorem card_sup : Nat.card (W ⊔ J : Subgroup H) = Nat.card W * Nat.card J := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (supEquiv hcomm hWJ).toEquiv).symm

theorem sum_sup [Fintype H] (f : (W ⊔ J : Subgroup H) → ℂ) :
    ∑ k, f k = ∑ w : W, ∑ j : J, f (supEquiv hcomm hWJ (w, j)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (supEquiv hcomm hWJ).toEquiv _ _ fun _ => rfl).symm

end SupProduct

section Sign

open scoped Classical

variable {H : Type u} [Group H] {W E : Subgroup H} [W.Normal]
  (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥) (σ : E ≃* Perm (Fin 5))

@[expose] noncomputable def rho : H →* Perm (Fin 5) := σ.toMonoidHom.comp (projE hWE hdisj)

theorem rho_apply (h : H) : rho hWE hdisj σ h = σ (projE hWE hdisj h) := rfl

theorem rho_coe (e : E) : rho hWE hdisj σ e = σ e := by rw [rho_apply, projE_coe]

theorem rho_mul_of_mem {w : H} (hw : w ∈ W) (e : E) : rho hWE hdisj σ (w * e) = σ e := by
  rw [rho_apply, projE_mul_of_mem hWE hdisj hw]

theorem rho_of_mem {w : H} (hw : w ∈ W) : rho hWE hdisj σ w = 1 := by
  rw [rho_apply, projE_of_mem hWE hdisj hw, map_one]

abbrev jSub : Subgroup H := ((alternatingGroup (Fin 5)).comap σ.toMonoidHom).map E.subtype

theorem jSub_le : jSub σ ≤ E := Subgroup.map_subtype_le _

theorem mem_jSub_iff (e : E) : (e : H) ∈ jSub σ ↔ σ e ∈ alternatingGroup (Fin 5) := by
  constructor
  · rintro ⟨e', he', hee'⟩
    obtain rfl : e' = e := Subtype.ext hee'
    exact he'
  · intro he
    exact ⟨e, he, rfl⟩

@[expose] noncomputable def eJ : jSub σ ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective ((σ.toMonoidHom.comp (Subgroup.inclusion (jSub_le σ))).codRestrict _
    fun j => (mem_jSub_iff σ (Subgroup.inclusion (jSub_le σ) j)).mp j.2) (by
      constructor
      · intro x y hxy
        have h := congrArg Subtype.val hxy
        exact Subgroup.inclusion_injective (jSub_le σ) (σ.injective h)
      · intro π
        refine ⟨⟨σ.symm π, (mem_jSub_iff σ (σ.symm π)).mpr (by
          rw [MulEquiv.apply_symm_apply]
          exact π.2)⟩, ?_⟩
        apply Subtype.ext
        change σ (Subgroup.inclusion (jSub_le σ) ⟨σ.symm π, _⟩) = π
        rw [show Subgroup.inclusion (jSub_le σ) ⟨((σ.symm π : E) : H), _⟩ = σ.symm π from rfl,
          MulEquiv.apply_symm_apply])

theorem coe_eJ (j : jSub σ) :
    ((eJ σ j : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ ⟨j, jSub_le σ j.2⟩ := rfl

theorem rho_jSub (j : jSub σ) :
    rho hWE hdisj σ j = ((eJ σ j : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  rw [coe_eJ, ← rho_coe hWE hdisj σ]

omit [W.Normal] in
include hdisj in
theorem disjoint_jSub : W ⊓ jSub σ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ W ⊓ E := ⟨hx.1, jSub_le σ hx.2⟩
  rwa [hdisj] at hmem

theorem sign_rho_of_mem_jSub {j : H} (hj : j ∈ jSub σ) : Perm.sign (rho hWE hdisj σ j) = 1 := by
  rw [show j = ((⟨j, hj⟩ : jSub σ) : H) from rfl, rho_jSub]
  exact Perm.mem_alternatingGroup.mp (eJ σ ⟨j, hj⟩).2

theorem mem_sup_iff (h : H) :
    h ∈ W ⊔ jSub σ ↔ Perm.sign (rho hWE hdisj σ h) = 1 := by
  constructor
  · intro hh
    have hh' : h ∈ ((W ⊔ jSub σ : Subgroup H) : Set H) := hh
    rw [Subgroup.normal_mul] at hh'
    obtain ⟨w, hw, j, hj, rfl⟩ := hh'
    rw [map_mul, rho_of_mem hWE hdisj σ hw, one_mul]
    exact sign_rho_of_mem_jSub hWE hdisj σ hj
  · intro hs
    rw [eq_mul_projE hWE hdisj h]
    refine Subgroup.mul_mem_sup (mul_inv_projE_mem hWE hdisj h) ?_
    rw [mem_jSub_iff, Perm.mem_alternatingGroup]
    rwa [rho_apply] at hs

theorem sup_eq_ker : W ⊔ jSub σ = (Perm.sign.comp (rho hWE hdisj σ)).ker := by
  ext h
  rw [mem_sup_iff, MonoidHom.mem_ker]
  rfl

include hWE hdisj in
theorem sup_normal : (W ⊔ jSub σ).Normal := by
  rw [sup_eq_ker hWE hdisj σ]
  infer_instance

variable (hact : ∀ (e : E), ∀ w ∈ W, (e : H) * w * (e : H)⁻¹ =
  w ^ ((Perm.sign (σ e) : ℤˣ) : ℤ))

omit [W.Normal] in
include hact in
theorem commute_jSub {w j : H} (hw : w ∈ W) (hj : j ∈ jSub σ) : Commute w j := by
  obtain ⟨e, he, rfl⟩ := hj
  have h := hact e w hw
  have he' : Perm.sign (σ e) = 1 := Perm.mem_alternatingGroup.mp he
  rw [he', Units.val_one, zpow_one] at h
  change w * e = e * w
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

omit [W.Normal] in
theorem comm_of_mem [IsCyclic W] {a b : H} (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (CyclicInversion.le_centralizer_of_isCyclic W hb) a ha

include hact in
theorem conj_mem_W [IsCyclic W] (c : H) {w : H} (hw : w ∈ W) :
    c * w * c⁻¹ = w ^ ((Perm.sign (rho hWE hdisj σ c) : ℤˣ) : ℤ) := by
  have hw' : c * (projE hWE hdisj c : H)⁻¹ ∈ W := mul_inv_projE_mem hWE hdisj c
  have hpow : w ^ ((Perm.sign (σ (projE hWE hdisj c)) : ℤˣ) : ℤ) ∈ W := W.zpow_mem hw _
  conv_lhs => rw [eq_mul_projE hWE hdisj c]
  rw [rho_apply]
  calc c * (projE hWE hdisj c : H)⁻¹ * (projE hWE hdisj c) * w *
        (c * (projE hWE hdisj c : H)⁻¹ * (projE hWE hdisj c))⁻¹ =
      c * (projE hWE hdisj c : H)⁻¹ * ((projE hWE hdisj c : H) * w *
        (projE hWE hdisj c : H)⁻¹) * (c * (projE hWE hdisj c : H)⁻¹)⁻¹ := by group
    _ = c * (projE hWE hdisj c : H)⁻¹ * w ^ ((Perm.sign (σ (projE hWE hdisj c)) : ℤˣ) : ℤ) *
        (c * (projE hWE hdisj c : H)⁻¹)⁻¹ := by rw [hact _ w hw]
    _ = w ^ ((Perm.sign (σ (projE hWE hdisj c)) : ℤˣ) : ℤ) := by
        rw [comm_of_mem hw' hpow, mul_assoc, mul_inv_cancel, mul_one]

include hWE hdisj hact in
theorem conj_mem_jSub (c : H) {j : H} (hj : j ∈ jSub σ) : c * j * c⁻¹ ∈ jSub σ := by
  have hw' : c * (projE hWE hdisj c : H)⁻¹ ∈ W := mul_inv_projE_mem hWE hdisj c
  obtain ⟨e, he, rfl⟩ := hj
  set p := projE hWE hdisj c
  have hpe : ((p * e * p⁻¹ : E) : H) ∈ jSub σ := by
    rw [mem_jSub_iff, map_mul, map_mul, map_inv]
    exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ he _
  have hcomm := commute_jSub σ hact hw' hpe
  have hc : c = (c * (p : H)⁻¹) * p := eq_mul_projE hWE hdisj c
  have hval : c * (E.subtype e) * c⁻¹ = ((p * e * p⁻¹ : E) : H) := by
    calc c * (E.subtype e) * c⁻¹ = (c * (p : H)⁻¹) * ((p * e * p⁻¹ : E) : H) *
          (c * (p : H)⁻¹)⁻¹ := by
          rw [Subgroup.coe_subtype]
          push_cast
          group
      _ = ((p * e * p⁻¹ : E) : H) := by
          rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hval]
  exact hpe

end Sign

section Involutions

open scoped Classical

variable {H : Type u} [Group H] {W E : Subgroup H} [W.Normal]
  (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥) (σ : E ≃* Perm (Fin 5))
  (hact : ∀ (e : E), ∀ w ∈ W, (e : H) * w * (e : H)⁻¹ =
    w ^ ((Perm.sign (σ e) : ℤˣ) : ℤ))
  (a : ℕ) (hWcard : Nat.card W = 5 ^ a)

omit [W.Normal] in
include hWcard in
theorem eq_one_of_mem_of_sq {w : H} (hw : w ∈ W) (h2 : w ^ 2 = 1) : w = 1 := by
  have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h5 : orderOf w ∣ 5 ^ a := by
    rw [← Subgroup.orderOf_mk w hw, ← hWcard]
    exact orderOf_dvd_natCard _
  have h := Nat.dvd_gcd h1 h5
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right a (by norm_num))] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

omit [W.Normal] in
include hWcard in
theorem exists_mul_self_eq {w : H} (hw : w ∈ W) : ∃ r ∈ W, r * r = w := by
  refine ⟨w ^ ((5 ^ a + 1) / 2), W.pow_mem hw _, ?_⟩
  obtain ⟨k, hk⟩ : Odd (5 ^ a) := Odd.pow (by decide)
  have hhalf : (5 ^ a + 1) / 2 + (5 ^ a + 1) / 2 = 5 ^ a + 1 := by omega
  have hpow : w ^ (5 ^ a) = 1 := by
    have h := pow_card_eq_one' (G := W) (x := ⟨w, hw⟩)
    rw [hWcard] at h
    exact congrArg Subtype.val h
  rw [← pow_add, hhalf, pow_succ, hpow, one_mul]

include hWE hdisj hact hWcard in
theorem orderOf_eq_two_iff [IsCyclic W] (u : H) :
    orderOf u = 2 ↔ (u ∈ jSub σ ∧ orderOf u = 2) ∨
      ∃ x y : Fin 5, x ≠ y ∧ rho hWE hdisj σ u = swap x y := by
  constructor
  · intro hu
    by_cases hs : Perm.sign (rho hWE hdisj σ u) = 1
    · left
      refine ⟨?_, hu⟩
      have hK := (mem_sup_iff hWE hdisj σ u).mpr hs
      obtain ⟨w, j, hwj⟩ := exists_sup_eq_mul (fun _ hw _ hj => commute_jSub σ hact hw hj)
        (disjoint_jSub hdisj σ) ⟨u, hK⟩
      have hsq : u ^ 2 = 1 := (orderOf_eq_prime_iff.mp hu).1
      have hu' : u = w * j := hwj
      rw [hu', (commute_jSub σ hact w.2 j.2).mul_pow] at hsq
      have hw2 : (w : H) ^ 2 ∈ jSub σ := by
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact (jSub σ).inv_mem ((jSub σ).pow_mem j.2 2)
      have hw2' : (w : H) ^ 2 = 1 := by
        have hmem : (w : H) ^ 2 ∈ W ⊓ jSub σ := ⟨W.pow_mem w.2 2, hw2⟩
        rwa [disjoint_jSub hdisj σ, Subgroup.mem_bot] at hmem
      rw [hu', eq_one_of_mem_of_sq a hWcard w.2 hw2', one_mul]
      exact j.2
    · right
      have hsq : rho hWE hdisj σ u ^ 2 = 1 := by
        rw [← map_pow, (orderOf_eq_prime_iff.mp hu).1, map_one]
      have hsign : Perm.sign (rho hWE hdisj σ u) = -1 := (Int.units_eq_one_or _).resolve_left hs
      exact exists_swap_of_sq_eq_one_of_sign _ hsq hsign
  · rintro (⟨-, hu⟩ | ⟨x, y, hxy, hu⟩)
    · exact hu
    · have hp : σ (projE hWE hdisj u) = swap x y := hu
      have hw : u * (projE hWE hdisj u : H)⁻¹ ∈ W := mul_inv_projE_mem hWE hdisj u
      have hp2 : projE hWE hdisj u * projE hWE hdisj u = 1 :=
        σ.injective (by rw [map_mul, hp, swap_mul_self, map_one])
      have hpw : (projE hWE hdisj u : H) * (u * (projE hWE hdisj u : H)⁻¹) *
          (projE hWE hdisj u : H)⁻¹ = (u * (projE hWE hdisj u : H)⁻¹)⁻¹ := by
        rw [hact _ _ hw, hp, Perm.sign_swap hxy, Units.val_neg, Units.val_one, zpow_neg_one]
      have hsq : u ^ 2 = 1 := by
        have hp2' : (projE hWE hdisj u : H) * projE hWE hdisj u = 1 := by
          rw [← Subgroup.coe_mul, hp2, Subgroup.coe_one]
        calc u ^ 2 = (u * (projE hWE hdisj u : H)⁻¹) * ((projE hWE hdisj u : H) *
              (u * (projE hWE hdisj u : H)⁻¹) * (projE hWE hdisj u : H)⁻¹) *
              ((projE hWE hdisj u : H) * projE hWE hdisj u) := by
                rw [sq]
                group
          _ = 1 := by rw [hpw, hp2', mul_inv_cancel, one_mul]
      have hne : u ≠ 1 := by
        intro h1
        rw [h1, map_one] at hu
        have h := congrArg (fun f : Perm (Fin 5) => f x) hu
        simp only [Perm.coe_one, id_eq, swap_apply_left] at h
        exact hxy h
      exact orderOf_eq_prime hsq hne

omit [W.Normal] in
theorem orderOf_conj (c x : H) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

include hWE hdisj hact in
theorem isConj_iff_of_mem_jSub {t : H} (ht : t ∈ jSub σ) (ht2 : orderOf t = 2) (u : H) :
    IsConj t u ↔ u ∈ jSub σ ∧ orderOf u = 2 := by
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := isConj_iff.mp h
    exact ⟨conj_mem_jSub hWE hdisj σ hact c ht, by rw [orderOf_conj, ht2]⟩
  · rintro ⟨hu, hu2⟩
    have hinv : ∀ (z : H) (hz : z ∈ jSub σ), orderOf z = 2 →
        eJ σ ⟨z, hz⟩ ^ 2 = 1 ∧ eJ σ ⟨z, hz⟩ ≠ 1 := by
      intro z hz hz2
      apply orderOf_eq_prime_iff.mp
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2]
    obtain ⟨g, hg⟩ := alternating_involution_conj _ _ (hinv t ht ht2).1 (hinv t ht ht2).2
      (hinv u hu hu2).1 (hinv u hu hu2).2
    refine isConj_iff.mpr ⟨((eJ σ).symm g : H), ?_⟩
    have h : (eJ σ).symm g * ⟨t, ht⟩ * ((eJ σ).symm g)⁻¹ = ⟨u, hu⟩ :=
      (eJ σ).injective (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg])
    exact congrArg Subtype.val h

include hWE hdisj hact hWcard in
theorem isConj_iff_of_swap [IsCyclic W] {x : E} (hx : ∃ c d : Fin 5, c ≠ d ∧ σ x = swap c d)
    (u : H) : IsConj (x : H) u ↔ ∃ c d : Fin 5, c ≠ d ∧ rho hWE hdisj σ u = swap c d := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    obtain ⟨c, d, hcd, hxcd⟩ := hx
    refine ⟨rho hWE hdisj σ g c, rho hWE hdisj σ g d,
      (rho hWE hdisj σ g).injective.ne hcd, ?_⟩
    rw [map_mul, map_mul, map_inv, rho_coe, hxcd, Equiv.swap_apply_apply]
  · rintro ⟨c', d', hcd', hu⟩
    obtain ⟨c, d, hcd, hxcd⟩ := hx
    have hp : σ (projE hWE hdisj u) = swap c' d' := hu
    obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_swap hcd hcd')
    have hxp : σ.symm g * x * (σ.symm g)⁻¹ = projE hWE hdisj u :=
      σ.injective (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hxcd, hg, hp])
    have hw : u * (projE hWE hdisj u : H)⁻¹ ∈ W := mul_inv_projE_mem hWE hdisj u
    obtain ⟨r, hr, hrr⟩ := exists_mul_self_eq a hWcard hw
    have hpr : (projE hWE hdisj u : H) * r⁻¹ * (projE hWE hdisj u : H)⁻¹ = r := by
      rw [hact _ _ (W.inv_mem hr), hp, Perm.sign_swap hcd', Units.val_neg, Units.val_one,
        zpow_neg_one, inv_inv]
    have hconj : r * (projE hWE hdisj u : H) * r⁻¹ = u := by
      calc r * (projE hWE hdisj u : H) * r⁻¹ = r * ((projE hWE hdisj u : H) * r⁻¹ *
            (projE hWE hdisj u : H)⁻¹) * projE hWE hdisj u := by group
        _ = u := by rw [hpr, hrr, inv_mul_cancel_right]
    refine (isConj_iff.mpr ⟨(σ.symm g : H), ?_⟩).trans (isConj_iff.mpr ⟨r, hconj⟩)
    exact congrArg Subtype.val hxp

include hWE hdisj hact in
theorem not_isConj_of_swap {t : H} (ht : t ∈ jSub σ) (ht2 : orderOf t = 2) {x : E}
    (hx : ∃ c d : Fin 5, c ≠ d ∧ σ x = swap c d) : ¬ IsConj t (x : H) := by
  intro h
  have hxJ := ((isConj_iff_of_mem_jSub hWE hdisj σ hact ht ht2 x).mp h).1
  obtain ⟨c, d, hcd, hxcd⟩ := hx
  have hs := sign_rho_of_mem_jSub hWE hdisj σ hxJ
  rw [rho_coe, hxcd, Perm.sign_swap hcd] at hs
  exact absurd hs (by decide)

end Involutions

section Counting

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] {W E : Subgroup H} [W.Normal]
  (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥) (σ : E ≃* Perm (Fin 5))
  (hact : ∀ (e : E), ∀ w ∈ W, (e : H) * w * (e : H)⁻¹ =
    w ^ ((Perm.sign (σ e) : ℤˣ) : ℤ))
  (a : ℕ) (hWcard : Nat.card W = 5 ^ a)

include hWE hdisj σ hWcard in
theorem card_H : Nat.card H = 5 ^ a * 120 := by
  rw [card_eq_mul hWE hdisj, hWcard, Nat.card_congr σ.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

omit [Fintype H] [W.Normal] in
theorem card_jSub : Nat.card (jSub σ) = 60 := by
  rw [Nat.card_congr (eJ σ).toEquiv, Nat.card_eq_fintype_card, FiveKernel.card_alternating]

omit [Fintype H] in
include hWE hdisj hact in
theorem card_class_of_mem_jSub {t : H} (ht : t ∈ jSub σ) (ht2 : orderOf t = 2) :
    Nat.card {u : H // IsConj t u} = 15 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (isConj_iff_of_mem_jSub hWE hdisj σ hact ht ht2))]
  let e1 : {u : H // u ∈ jSub σ ∧ orderOf u = 2} ≃
      {j : jSub σ // eJ σ j ^ 2 = 1 ∧ eJ σ j ≠ 1} :=
    { toFun := fun u => ⟨⟨u.1, u.2.1⟩, orderOf_eq_prime_iff.mp (by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
        exact u.2.2)⟩
      invFun := fun j => ⟨j.1, j.1.2, by
        rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq (eJ σ)]
        exact orderOf_eq_prime j.2.1 j.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e1.trans (Equiv.subtypeEquiv
      (q := fun π : alternatingGroup (Fin 5) => π ^ 2 = 1 ∧ π ≠ 1) (eJ σ).toEquiv
      fun _ => Iff.rfl)),
    Nat.card_eq_fintype_card, Fintype.card_subtype, card_alternating_involution]

omit [Fintype H] in
include hWE hdisj hact hWcard in
theorem card_class_of_swap [IsCyclic W] {x : E} (hx : ∃ c d : Fin 5, c ≠ d ∧ σ x = swap c d) :
    Nat.card {u : H // IsConj (x : H) u} = 10 * 5 ^ a := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (isConj_iff_of_swap hWE hdisj σ hact a hWcard hx))]
  have hbij : Function.Bijective (fun z : W × {p : E // ∃ c d : Fin 5, c ≠ d ∧ σ p = swap c d} =>
      (⟨(z.1 : H) * z.2.1, by rw [rho_mul_of_mem hWE hdisj σ z.1.2]; exact z.2.2⟩ :
        {u : H // ∃ c d : Fin 5, c ≠ d ∧ rho hWE hdisj σ u = swap c d})) := by
    constructor
    · intro z z' h
      obtain ⟨h1, h2⟩ := mul_eq_mul_iff hWE hdisj z.1.2 z'.1.2 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro u
      exact ⟨(⟨_, mul_inv_projE_mem hWE hdisj u.1⟩, ⟨projE hWE hdisj u.1, u.2⟩),
        Subtype.ext (eq_mul_projE hWE hdisj u.1).symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hWcard,
    Nat.card_congr (Equiv.subtypeEquiv
      (p := fun p : E => ∃ c d : Fin 5, c ≠ d ∧ σ p = swap c d)
      (q := fun π : Perm (Fin 5) => ∃ c d : Fin 5, c ≠ d ∧ π = swap c d) σ.toEquiv
      fun _ => Iff.rfl), Nat.card_eq_fintype_card,
    Fintype.card_subtype, card_swap]
  ring

omit [W.Normal] in
theorem card_centralizer_mul_card_class (g : H) :
    Nat.card (Subgroup.centralizer {g}) * Nat.card {u : H // IsConj g u} = Nat.card H := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have h2 : (MulAction.orbit (ConjAct H) g).ncard = Nat.card {u : H // IsConj g u} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u =>
      ConjAct.mem_orbit_conjAct.trans isConj_comm)
  rw [← h2, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

include hWE hdisj hact hWcard in
theorem card_centralizer_of_mem_jSub {t : H} (ht : t ∈ jSub σ) (ht2 : orderOf t = 2) :
    Nat.card (Subgroup.centralizer {t}) = 8 * 5 ^ a := by
  have h := card_centralizer_mul_card_class t
  rw [card_class_of_mem_jSub hWE hdisj σ hact ht ht2, card_H hWE hdisj σ a hWcard] at h
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 15)
  rw [h]
  ring

include hWE hdisj hact hWcard in
theorem card_centralizer_of_swap [IsCyclic W] {x : E}
    (hx : ∃ c d : Fin 5, c ≠ d ∧ σ x = swap c d) :
    Nat.card (Subgroup.centralizer {(x : H)}) = 12 := by
  have h := card_centralizer_mul_card_class (x : H)
  rw [card_class_of_swap hWE hdisj σ hact a hWcard hx, card_H hWE hdisj σ a hWcard] at h
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 10 * 5 ^ a)
  rw [h]
  ring

include hWE hdisj hact hWcard in
theorem sum_involutions [IsCyclic W] (f : H → ℂ) (hf : ∀ x c : H, f (c * x * c⁻¹) = f x)
    {t : H} (ht : t ∈ jSub σ) (ht2 : orderOf t = 2) {x : E}
    (hx : ∃ c d : Fin 5, c ≠ d ∧ σ x = swap c d) :
    ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2), f u =
      15 * f t + 10 * 5 ^ a * f x := by
  have hsplit : Finset.univ.filter (fun u : H => orderOf u = 2) =
      Finset.univ.filter (fun u => IsConj t u) ∪
        Finset.univ.filter (fun u => IsConj (x : H) u) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [orderOf_eq_two_iff hWE hdisj σ hact a hWcard,
      isConj_iff_of_mem_jSub hWE hdisj σ hact ht ht2,
      isConj_iff_of_swap hWE hdisj σ hact a hWcard hx]
  have hdisj' : Disjoint (Finset.univ.filter (fun u => IsConj t u))
      (Finset.univ.filter (fun u => IsConj (x : H) u)) := by
    rw [Finset.disjoint_filter]
    intro u _ h1 h2
    exact not_isConj_of_swap hWE hdisj σ hact ht ht2 hx (h1.trans (isConj_comm.mp h2))
  have hconst : ∀ g : H, ∑ u ∈ Finset.univ.filter (fun u => IsConj g u), f u =
      (Nat.card {u : H // IsConj g u} : ℂ) * f g := by
    intro g
    have h1 : ∑ u ∈ Finset.univ.filter (fun u => IsConj g u), f u =
        ∑ u ∈ Finset.univ.filter (fun u => IsConj g u), f g := by
      refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨c, rfl⟩ := isConj_iff.mp (Finset.mem_filter.mp hu).2
      exact hf g c
    rw [h1, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsplit, Finset.sum_union hdisj', hconst, hconst,
    card_class_of_mem_jSub hWE hdisj σ hact ht ht2, card_class_of_swap hWE hdisj σ hact a hWcard hx]
  push_cast
  ring

end Counting

theorem exists_twist_label {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ν : G →* ℂˣ) (χ : basis.index) :
    ∃ χ' : basis.index, ∀ g, (basis.representation χ').character g =
      (ν g : ℂ) * (basis.representation χ).character g := by
  let data : FiniteComplexRepresentation G :=
    { vector := (basis.representation χ).vector
      representation := CFSG.Section1.representationTwistByCharacter ν
        (basis.representation χ).representation }
  have hirr : data.IsIrreducible :=
    CFSG.Section1.irreducible_twistByCharacter ν _ (basis.irreducible χ)
  obtain ⟨χ', hχ'⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr
  refine ⟨χ', fun g => ?_⟩
  rw [hχ']
  change (CFSG.Section1.representationTwistByCharacter ν
    (basis.representation χ).representation).character g = _
  rw [CFSG.Section1.representationTwistByCharacter_character, Pi.mul_apply]

theorem s5Fix_one : s5Fix 1 = 6 := by decide +kernel

section Characters

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] {W E : Subgroup H} [W.Normal]
  (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥) (σ : E ≃* Perm (Fin 5))

@[expose, instance_reducible] noncomputable def liftAction :
    MulAction H (ULift.{u} (Sylow 5 (alternatingGroup (Fin 5)))) :=
  letI := s5Action
  { smul := fun h P => ⟨rho hWE hdisj σ h • P.down⟩
    one_smul := fun P => by
      change (⟨rho hWE hdisj σ 1 • P.down⟩ : ULift _) = P
      rw [map_one, one_smul]
    mul_smul := fun g h P => by
      change (⟨rho hWE hdisj σ (g * h) • P.down⟩ : ULift _) =
        ⟨rho hWE hdisj σ g • rho hWE hdisj σ h • P.down⟩
      rw [map_mul, mul_smul] }

@[expose] noncomputable def sylowPermH : FiniteComplexRepresentation.{u, u} H :=
  letI := liftAction hWE hdisj σ
  { vector := MonoidAlgebra ℂ (ULift.{u} (Sylow 5 (alternatingGroup (Fin 5))))
    representation := Representation.ofMulAction ℂ H _ }

omit [Fintype H] in
theorem sylowPermH_character (h : H) :
    (sylowPermH hWE hdisj σ).character h = s5Fix (rho hWE hdisj σ h) := by
  let := liftAction hWE hdisj σ
  let := s5Action
  let : Fintype (Sylow 5 (alternatingGroup (Fin 5))) := Fintype.ofFinite _
  have h1 : (sylowPermH hWE hdisj σ).character h =
      Nat.card (MulAction.fixedBy (ULift.{u} (Sylow 5 (alternatingGroup (Fin 5)))) h) :=
    DoublyTransitive.ofMulAction_character_eq_card_fixedBy h
  have h2 : Nat.card (MulAction.fixedBy (ULift.{u} (Sylow 5 (alternatingGroup (Fin 5)))) h) =
      Nat.card (MulAction.fixedBy (Sylow 5 (alternatingGroup (Fin 5))) (rho hWE hdisj σ h)) :=
    Nat.card_congr (Equiv.subtypeEquiv Equiv.ulift fun P => by
      rw [MulAction.mem_fixedBy, MulAction.mem_fixedBy]
      constructor
      · intro hP
        exact congrArg ULift.down hP
      · intro hP
        exact congrArg ULift.up hP)
  rw [h1, h2, card_fixedBy_s5]

@[expose] noncomputable def thetaP (h : H) : ℂ := (s5Fix (rho hWE hdisj σ h) : ℂ) - 1

theorem thetaP_mem_virtualCharacters (basis : FiniteIrreducibleCharacterBasis H) :
    thetaP hWE hdisj σ ∈ virtualCharacters H := by
  obtain ⟨one, hone⟩ := FiveKernel.exists_principal_label basis
  have heq : thetaP hWE hdisj σ =
      (sylowPermH hWE hdisj σ).character - (basis.representation one).character := by
    funext h
    rw [Pi.sub_apply, sylowPermH_character, hone, Pi.one_apply]
    rfl
  rw [heq]
  exact Submodule.sub_mem _ (character_mem_virtualCharacters _)
    (character_mem_virtualCharacters _)

omit [Fintype H] in
theorem thetaP_one : thetaP hWE hdisj σ 1 = 5 := by
  rw [thetaP, map_one, s5Fix_one]
  norm_num

omit [Fintype H] in
theorem thetaP_mul_of_mem {w : H} (hw : w ∈ W) (h : H) :
    thetaP hWE hdisj σ (w * h) = thetaP hWE hdisj σ h := by
  rw [thetaP, thetaP, map_mul, rho_of_mem hWE hdisj σ hw, one_mul]

omit [Fintype H] in
theorem thetaP_of_swap {x : E} (hx : ∃ c d : Fin 5, c ≠ d ∧ σ x = swap c d) :
    thetaP hWE hdisj σ x = -1 := by
  obtain ⟨c, d, hcd, hxcd⟩ := hx
  rw [thetaP, rho_coe, hxcd, s5Fix_swap c d hcd]
  norm_num

theorem thetaP_jSub (j : jSub σ) :
    thetaP hWE hdisj σ j = FiveKernel.sylowAugmentation (jSub σ) j := by
  rw [FiveKernel.sylowAugmentation_apply (eJ σ), thetaP, rho_jSub, s5Fix_coe]
  push_cast
  rfl

include hWE hdisj in
theorem characterPairing_thetaP (a : ℕ) (hWcard : Nat.card W = 5 ^ a) :
    characterPairing (thetaP hWE hdisj σ) (thetaP hWE hdisj σ) = 1 := by
  unfold characterPairing
  rw [card_H hWE hdisj σ a hWcard, sum_eq_sum_mul hWE hdisj]
  have hterm : ∀ (w : W) (e : E), thetaP hWE hdisj σ ((w : H) * e) *
      thetaP hWE hdisj σ ((w : H) * e)⁻¹ =
      ((((s5Fix (σ e) : ℤ) - 1) * ((s5Fix (σ e)⁻¹ : ℤ) - 1) : ℤ) : ℂ) := by
    intro w e
    simp only [thetaP]
    rw [map_inv, rho_mul_of_mem hWE hdisj σ w.2]
    push_cast
    ring
  simp_rw [hterm]
  have hσ : ∑ e : E, ((((s5Fix (σ e) : ℤ) - 1) * ((s5Fix (σ e)⁻¹ : ℤ) - 1) : ℤ) : ℂ) =
      ∑ π : Perm (Fin 5), ((((s5Fix π : ℤ) - 1) * ((s5Fix π⁻¹ : ℤ) - 1) : ℤ) : ℂ) :=
    Fintype.sum_equiv σ.toEquiv _ _ fun _ => rfl
  rw [Finset.sum_congr rfl fun _ _ => hσ, ← Int.cast_sum, sum_s5Fix, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, hWcard, nsmul_eq_mul]
  push_cast
  field_simp

@[expose] noncomputable def sgnH : H →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (Perm.sign.comp (rho hWE hdisj σ))

omit [Fintype H] in
theorem sgnH_apply (h : H) :
    (sgnH hWE hdisj σ h : ℂ) = (((Perm.sign (rho hWE hdisj σ h) : ℤˣ) : ℤ) : ℂ) := rfl

omit [Fintype H] in
theorem sgnH_of_mem_sup {h : H} (hh : h ∈ W ⊔ jSub σ) : (sgnH hWE hdisj σ h : ℂ) = 1 := by
  rw [sgnH_apply, (mem_sup_iff hWE hdisj σ h).mp hh, Units.val_one, Int.cast_one]

omit [Fintype H] in
theorem sgnH_of_not_mem_sup {h : H} (hh : h ∉ W ⊔ jSub σ) : (sgnH hWE hdisj σ h : ℂ) = -1 := by
  rw [sgnH_apply, ((Int.units_eq_one_or _).resolve_left (fun h1 =>
    hh ((mem_sup_iff hWE hdisj σ h).mpr h1))), Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one]

variable (hact : ∀ (e : E), ∀ w ∈ W, (e : H) * w * (e : H)⁻¹ =
  w ^ ((Perm.sign (σ e) : ℤˣ) : ℤ))

include hWE hdisj hact in
theorem induced_apply_mul [IsCyclic W] (a : ℕ) (hWcard : Nat.card W = 5 ^ a) (ν : W → ℂ)
    (f : (W ⊔ jSub σ : Subgroup H) → ℂ)
    (hf : ∀ (k : (W ⊔ jSub σ : Subgroup H)) (w : W) (j : jSub σ), (k : H) = w * j →
      f k = FiveKernel.sylowAugmentation (jSub σ) j * ν w)
    (w : W) (j : jSub σ) :
    inducedFunction (W ⊔ jSub σ) f ((w : H) * j) =
      FiveKernel.sylowAugmentation (jSub σ) j * (ν w + ν w⁻¹) := by
  have hθconj : ∀ (c : H) (hc : c⁻¹ * (j : H) * c ∈ jSub σ),
      FiveKernel.sylowAugmentation (jSub σ) ⟨c⁻¹ * j * c, hc⟩ =
        FiveKernel.sylowAugmentation (jSub σ) j := by
    intro c hc
    apply FivePowerColumn.sylowAugmentation_eq_of_orderOf_eq (eJ σ) (eJ σ)
    have h := orderOf_conj c⁻¹ (j : H)
    rw [inv_inv] at h
    rw [Subgroup.orderOf_mk, h, Subgroup.orderOf_coe]
  have hvalue : ∀ c : H,
      (if hmem : c⁻¹ * ((w : H) * j) * c ∈ (W ⊔ jSub σ : Subgroup H) then
        f ⟨c⁻¹ * ((w : H) * j) * c, hmem⟩ else 0) =
      if c ∈ (W ⊔ jSub σ : Subgroup H) then
        FiveKernel.sylowAugmentation (jSub σ) j * ν w else
        FiveKernel.sylowAugmentation (jSub σ) j * ν w⁻¹ := by
    intro c
    have hcj : c⁻¹ * (j : H) * c ∈ jSub σ := by
      have h := conj_mem_jSub hWE hdisj σ hact c⁻¹ j.2
      rwa [inv_inv] at h
    have hcw := conj_mem_W hWE hdisj σ hact c⁻¹ w.2
    simp only [inv_inv, map_inv, Int.units_inv_eq_self] at hcw
    have hsplit : c⁻¹ * ((w : H) * j) * c = (c⁻¹ * w * c) * (c⁻¹ * j * c) := by group
    by_cases hcK : c ∈ (W ⊔ jSub σ : Subgroup H)
    · rw [(mem_sup_iff hWE hdisj σ c).mp hcK, Units.val_one, zpow_one] at hcw
      have hmem : c⁻¹ * ((w : H) * j) * c ∈ (W ⊔ jSub σ : Subgroup H) := by
        rw [hsplit, hcw]
        exact Subgroup.mul_mem_sup w.2 hcj
      rw [dite_eq_left hmem, ite_eq_left hcK, hf ⟨_, hmem⟩ w ⟨_, hcj⟩ (by
        show c⁻¹ * ((w : H) * j) * c = (w : H) * (c⁻¹ * j * c)
        rw [hsplit, hcw]), hθconj c hcj]
    · rw [(Int.units_eq_one_or _).resolve_left (fun h1 =>
        hcK ((mem_sup_iff hWE hdisj σ c).mpr h1)), Units.val_neg, Units.val_one,
        zpow_neg_one] at hcw
      have hmem : c⁻¹ * ((w : H) * j) * c ∈ (W ⊔ jSub σ : Subgroup H) := by
        rw [hsplit, hcw]
        exact Subgroup.mul_mem_sup (W.inv_mem w.2) hcj
      rw [dite_eq_left hmem, ite_eq_right hcK, hf ⟨_, hmem⟩ w⁻¹ ⟨_, hcj⟩ (by
        show c⁻¹ * ((w : H) * j) * c = ((w⁻¹ : W) : H) * (c⁻¹ * j * c)
        rw [hsplit, hcw]
        rfl), hθconj c hcj]
  unfold inducedFunction
  rw [Finset.sum_congr rfl fun c _ => hvalue c, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hK : (Finset.univ.filter fun c : H => c ∈ (W ⊔ jSub σ : Subgroup H)).card =
      Nat.card (W ⊔ jSub σ : Subgroup H) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hcompl : (Finset.univ.filter fun c : H => c ∉ (W ⊔ jSub σ : Subgroup H)).card =
      Nat.card (W ⊔ jSub σ : Subgroup H) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset H)) (fun c => c ∈ (W ⊔ jSub σ : Subgroup H))
    rw [hK, Finset.card_univ, ← Nat.card_eq_fintype_card, card_H hWE hdisj σ a hWcard,
      card_sup (fun _ hw _ hj => commute_jSub σ hact hw hj) (disjoint_jSub hdisj σ), hWcard,
      card_jSub] at h
    rw [card_sup (fun _ hw _ hj => commute_jSub σ hact hw hj) (disjoint_jSub hdisj σ), hWcard,
      card_jSub]
    omega
  rw [hK, hcompl]
  have hne : (Nat.card (W ⊔ jSub σ : Subgroup H) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

include hWE hdisj in
theorem induced_eq_zero (f : (W ⊔ jSub σ : Subgroup H) → ℂ) {h : H}
    (hh : h ∉ (W ⊔ jSub σ : Subgroup H)) : inducedFunction (W ⊔ jSub σ) f h = 0 := by
  have hK := sup_normal hWE hdisj σ
  unfold inducedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro c _
  rw [dite_eq_right]
  intro hmem
  apply hh
  have h' := hK.conj_mem _ hmem c
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel,
    mul_one] at h'

end Characters

section Column

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] {W E : Subgroup H} [W.Normal] [IsCyclic W]
  (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥) (σ : E ≃* Perm (Fin 5))
  (hact : ∀ (e : E), ∀ w ∈ W, (e : H) * w * (e : H)⁻¹ =
    w ^ ((Perm.sign (σ e) : ℤˣ) : ℤ))

noncomputable abbrev kEquiv : W × jSub σ ≃* (W ⊔ jSub σ : Subgroup H) :=
  supEquiv (fun _ hw _ hj => commute_jSub σ hact hw hj) (disjoint_jSub hdisj σ)

omit [IsCyclic W] in
include hdisj hact in
theorem exists_rep_mul (ν : W →* ℂˣ) :
    ∃ data : FiniteComplexRepresentation.{u, u} (W ⊔ jSub σ : Subgroup H),
      ∀ (k : (W ⊔ jSub σ : Subgroup H)) (w : W) (j : jSub σ), (k : H) = w * j →
        data.character k = FiveKernel.sylowAugmentation (jSub σ) j * ν w := by
  obtain ⟨basisJ⟩ := finiteIrreducibleCharacterBasis_exists (G := jSub σ)
  obtain ⟨l, hl⟩ := FiveKernel.exists_label_sylowAugmentation (eJ σ) basisJ
  let pW : (W ⊔ jSub σ : Subgroup H) →* W :=
    (MonoidHom.fst W (jSub σ)).comp (kEquiv hdisj σ hact).symm.toMonoidHom
  let pJ : (W ⊔ jSub σ : Subgroup H) →* jSub σ :=
    (MonoidHom.snd W (jSub σ)).comp (kEquiv hdisj σ hact).symm.toMonoidHom
  refine ⟨{ vector := (basisJ.representation l).vector
            representation := CFSG.Section1.representationTwistByCharacter (ν.comp pW)
              ((basisJ.representation l).representation.comp pJ) }, fun k w j hk => ?_⟩
  change (CFSG.Section1.representationTwistByCharacter (ν.comp pW)
    ((basisJ.representation l).representation.comp pJ)).character k = _
  rw [CFSG.Section1.representationTwistByCharacter_character, Pi.mul_apply]
  have hsymm := supEquiv_symm_apply (fun _ hw _ hj => commute_jSub σ hact hw hj)
    (disjoint_jSub hdisj σ) hk
  change (ν (pW k) : ℂ) * (basisJ.representation l).character (pJ k) = _
  have hpW : pW k = w := by
    change ((kEquiv hdisj σ hact).symm k).1 = w
    rw [hsymm]
  have hpJ : pJ k = j := by
    change ((kEquiv hdisj σ hact).symm k).2 = j
    rw [hsymm]
  rw [hpW, hpJ, hl, mul_comm]

include hWE hdisj hact in
theorem characterPairing_induced_mul (a : ℕ) (hWcard : Nat.card W = 5 ^ a) (lam : W →* ℂˣ)
    (hlam : orderOf lam = 5) (f : (W ⊔ jSub σ : Subgroup H) → ℂ)
    (hf : ∀ (k : (W ⊔ jSub σ : Subgroup H)) (w : W) (j : jSub σ), (k : H) = w * j →
      f k = FiveKernel.sylowAugmentation (jSub σ) j * lam w) :
    characterPairing (inducedFunction (W ⊔ jSub σ) f) (inducedFunction (W ⊔ jSub σ) f) = 1 := by
  have hcomm : ∀ w ∈ W, ∀ j ∈ jSub σ, Commute w j := fun _ hw _ hj => commute_jSub σ hact hw hj
  have hWJ := disjoint_jSub hdisj σ
  have hind := induced_apply_mul hWE hdisj σ hact a hWcard (fun w => (lam w : ℂ)) f hf
  unfold characterPairing
  have hsub : ∑ h : H, inducedFunction (W ⊔ jSub σ) f h * inducedFunction (W ⊔ jSub σ) f h⁻¹ =
      ∑ k : (W ⊔ jSub σ : Subgroup H), inducedFunction (W ⊔ jSub σ) f (k : H) *
        inducedFunction (W ⊔ jSub σ) f ((k⁻¹ : (W ⊔ jSub σ : Subgroup H)) : H) := by
    rw [← Finset.sum_filter_of_ne (p := fun h : H => h ∈ (W ⊔ jSub σ : Subgroup H))
      (fun h _ hne => by
        by_contra hh
        exact hne (by rw [induced_eq_zero hWE hdisj σ f hh, zero_mul]))]
    exact Finset.sum_subtype _ (fun h => by simp) _
  rw [hsub, sum_sup hcomm hWJ]
  have hterm : ∀ (w : W) (j : jSub σ),
      inducedFunction (W ⊔ jSub σ) f (supEquiv hcomm hWJ (w, j) : H) *
        inducedFunction (W ⊔ jSub σ) f
          (((supEquiv hcomm hWJ (w, j))⁻¹ : (W ⊔ jSub σ : Subgroup H)) : H) =
      FiveKernel.sylowAugmentation (jSub σ) j * FiveKernel.sylowAugmentation (jSub σ) j⁻¹ *
        (((lam ^ 2) w : ℂ) + 2 + (((lam ^ 2)⁻¹) w : ℂ)) := by
    intro w j
    rw [supEquiv_apply, coe_supEquiv_inv, hind w j,
      show (w : H)⁻¹ * (j : H)⁻¹ = ((w⁻¹ : W) : H) * ((j⁻¹ : jSub σ) : H) from rfl,
      hind w⁻¹ j⁻¹, inv_inv]
    have hne : (lam w : ℂ) ≠ 0 := Units.ne_zero _
    simp only [map_inv, Units.val_inv_eq_inv_val, MonoidHom.pow_apply, MonoidHom.inv_apply,
      Units.val_pow_eq_pow_val]
    field_simp
    ring
  simp_rw [hterm]
  have hinner : ∀ w : W, ∑ j : jSub σ, FiveKernel.sylowAugmentation (jSub σ) j *
      FiveKernel.sylowAugmentation (jSub σ) j⁻¹ *
        (((lam ^ 2) w : ℂ) + 2 + (((lam ^ 2)⁻¹) w : ℂ)) =
      60 * (((lam ^ 2) w : ℂ) + 2 + (((lam ^ 2)⁻¹) w : ℂ)) := by
    intro w
    rw [← Finset.sum_mul, FivePowerColumn.sum_sylowAugmentation_mul_inv (eJ σ)]
  have hlam2 : lam ^ 2 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hlam] at h'
    norm_num at h'
  have hlam2inv : (lam ^ 2)⁻¹ ≠ 1 := by
    intro h
    apply hlam2
    refine MonoidHom.ext fun w => ?_
    have h' := DFunLike.congr_fun h w
    simp only [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at h'
    rw [h', MonoidHom.one_apply]
  rw [Finset.sum_congr rfl fun w _ => hinner w, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, FivePowerColumn.sum_linear W (lam ^ 2),
    FivePowerColumn.sum_linear W (lam ^ 2)⁻¹, ite_eq_right hlam2, ite_eq_right hlam2inv,
    card_H hWE hdisj σ a hWcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    hWcard]
  push_cast
  field_simp
  ring

include hWE hact in
theorem induced_theta_eq (a : ℕ) (hWcard : Nat.card W = 5 ^ a)
    (f : (W ⊔ jSub σ : Subgroup H) → ℂ)
    (hf : ∀ (k : (W ⊔ jSub σ : Subgroup H)) (w : W) (j : jSub σ), (k : H) = w * j →
      f k = FiveKernel.sylowAugmentation (jSub σ) j) (h : H) :
    inducedFunction (W ⊔ jSub σ) f h =
      thetaP hWE hdisj σ h + (sgnH hWE hdisj σ h : ℂ) * thetaP hWE hdisj σ h := by
  by_cases hh : h ∈ (W ⊔ jSub σ : Subgroup H)
  · obtain ⟨w, j, hk⟩ := exists_sup_eq_mul (fun _ hw _ hj => commute_jSub σ hact hw hj)
      (disjoint_jSub hdisj σ) ⟨h, hh⟩
    have hk' : h = w * j := hk
    rw [sgnH_of_mem_sup hWE hdisj σ hh, hk', induced_apply_mul hWE hdisj σ hact a hWcard
      (fun _ => 1) f (fun k w j hkwj => by rw [hf k w j hkwj, mul_one]) w j,
      thetaP_mul_of_mem hWE hdisj σ w.2, thetaP_jSub]
    ring
  · rw [induced_eq_zero hWE hdisj σ f hh, sgnH_of_not_mem_sup hWE hdisj σ hh]
    ring

end Column

end SignSymmetric

end CFSG.Semidihedral.Principal
