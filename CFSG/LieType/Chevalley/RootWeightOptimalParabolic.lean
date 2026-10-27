module

public import CFSG.LieType.Chevalley.RootWeightStabilizers
public import CFSG.LieType.Chevalley.RootWeightOptimalFiltration
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley RootWeightSpace RootWeight
open scoped RealInnerProductSpace Pointwise

theorem conj_sub_one_of_mul_eq_one {R : Type*} [Ring R] {x y : R} (h : y * x = 1) (q : R) :
    y * (q - 1) * x = y * q * x - 1 := by
  rw [mul_sub, sub_mul, mul_one, h]

section Conj

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem units_inv_mul_sub_one_mul (g q : (Module.End K V)ˣ) :
    (↑g⁻¹ : Module.End K V) * ((q : Module.End K V) - 1) * ↑g =
      ((g⁻¹ * q * g : (Module.End K V)ˣ) : Module.End K V) - 1 := by
  rw [Units.val_mul, Units.val_mul]
  exact conj_sub_one_of_mul_eq_one (Units.inv_mul g) _

theorem units_mul_sub_one_mul_inv (g q : (Module.End K V)ˣ) :
    (g : Module.End K V) * ((q : Module.End K V) - 1) * ↑g⁻¹ =
      ((g * q * g⁻¹ : (Module.End K V)ˣ) : Module.End K V) - 1 := by
  rw [Units.val_mul, Units.val_mul]
  exact conj_sub_one_of_mul_eq_one (Units.mul_inv g) _

theorem conjFamily_image_conj [DecidableEq (Module.End K V)] (A : Finset (Module.End K V))
    (d g : (Module.End K V)ˣ) :
    conjFamily (A.image fun a => (d : Module.End K V) * a * ((d⁻¹ : (Module.End K V)ˣ) :
      Module.End K V)) g = conjFamily A (d⁻¹ * g) := by
  ext a
  simp only [conjFamily, Finset.mem_image, exists_exists_and_eq_and]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  rw [mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  simp only [mul_assoc]

variable {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

theorem semilinearConjUnit_one (s : V ≃ₛₗ[σ] V) :
    semilinearConjUnit s (1 : (Module.End K V)ˣ) = 1 :=
  Units.ext (LinearMap.ext fun v => by
    rw [coe_semilinearConjUnit, semilinearConj_apply, Units.val_one, Module.End.one_apply,
      Module.End.one_apply, LinearEquiv.apply_symm_apply])

theorem semilinearConjUnit_eq_one_iff (s : V ≃ₛₗ[σ] V) {q : (Module.End K V)ˣ} :
    semilinearConjUnit s q = 1 ↔ q = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ semilinearConjUnit_one s⟩
  have := semilinearConjUnit_symm_semilinearConjUnit s.symm q
  rw [LinearEquiv.symm_symm, h, semilinearConjUnit_one] at this
  exact this.symm

theorem semilinearConj_sub_one (s : V ≃ₛₗ[σ] V) (q : (Module.End K V)ˣ) :
    semilinearConj s ((q : Module.End K V) - 1) =
      (semilinearConjUnit s q : Module.End K V) - 1 :=
  LinearMap.ext fun v => by
    rw [coe_semilinearConjUnit, semilinearConj_apply, LinearMap.sub_apply, LinearMap.sub_apply,
      Module.End.one_apply, Module.End.one_apply, map_sub, LinearEquiv.apply_symm_apply,
      semilinearConj_apply]

end Conj

section Shifts

variable {τ : Tag} {K : Type*} [Field K] [Finite K]

@[expose] def subgroupShifts (Q : Subgroup (ModGL τ K)) :
    Finset (Module.End K (RootModule τ K)) :=
  haveI : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  (Set.toFinite {a | ∃ q ∈ Q, q ≠ 1 ∧ (q : Module.End K (RootModule τ K)) - 1 = a}).toFinset

theorem mem_subgroupShifts
    {Q : Subgroup (ModGL τ K)} {a : Module.End K (RootModule τ K)} :
    a ∈ subgroupShifts Q ↔ ∃ q ∈ Q, q ≠ 1 ∧ (q : Module.End K (RootModule τ K)) - 1 = a := by
  rw [subgroupShifts, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem subgroupShifts_nonempty
    {Q : Subgroup (ModGL τ K)} (hQ : Q ≠ ⊥) :
    (subgroupShifts Q).Nonempty := by
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
  exact ⟨_, mem_subgroupShifts.2 ⟨q, hq, fun h => hq1 (Subtype.ext h), rfl⟩⟩

theorem zero_notMem_subgroupShifts (Q : Subgroup (ModGL τ K)) :
    (0 : Module.End K (RootModule τ K)) ∉ subgroupShifts Q := fun h => by
  obtain ⟨q, -, hq1, h0⟩ := mem_subgroupShifts.1 h
  exact hq1 (Units.ext (sub_eq_zero.1 h0))

theorem image_conj_subgroupShifts
    [DecidableEq (Module.End K (RootModule τ K))]
    {Q : Subgroup (ModGL τ K)} {x : ModGL τ K}
    (hx : x ∈ Subgroup.normalizer (Q : Set (ModGL τ K))) :
    ((subgroupShifts Q).image fun a => (x : Module.End K (RootModule τ K)) * a *
      ((x⁻¹ : ModGL τ K) : Module.End K (RootModule τ K))) = subgroupShifts Q := by
  ext a
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨q, hq, hq1, rfl⟩ := mem_subgroupShifts.1 hb
    refine mem_subgroupShifts.2 ⟨x * q * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx q).1 hq,
      fun h => hq1 (conj_eq_one_iff.1 h), (units_mul_sub_one_mul_inv x q).symm⟩
  · intro ha
    obtain ⟨q, hq, hq1, rfl⟩ := mem_subgroupShifts.1 ha
    have e : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
    refine ⟨((x⁻¹ * q * x : ModGL τ K) : Module.End K (RootModule τ K)) - 1,
      mem_subgroupShifts.2 ⟨_, (Subgroup.mem_normalizer_iff.1 hx _).2 (e.symm ▸ hq), fun h => ?_,
        rfl⟩, ?_⟩
    · apply hq1
      rw [← e, h, mul_one, mul_inv_cancel]
    · rw [units_mul_sub_one_mul_inv, e]

theorem subgroupShifts_eq_image_image
    [DecidableEq (Module.End K (RootModule τ K))]
    {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (s : RootModule τ K ≃ₛₗ[σ] RootModule τ K) (d : ModGL τ K) {Q Q' : Subgroup (ModGL τ K)}
    (hQ' : ∀ x, x ∈ Q' ↔ ∃ q ∈ Q, d * semilinearConjUnit s q * d⁻¹ = x) :
    subgroupShifts Q' = ((subgroupShifts Q).image (semilinearConj s)).image
      fun a => (d : Module.End K (RootModule τ K)) * a *
        ((d⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) := by
  have key : ∀ q : ModGL τ K, (d : Module.End K (RootModule τ K)) *
      semilinearConj s ((q : Module.End K (RootModule τ K)) - 1) * ↑d⁻¹ =
        ((d * semilinearConjUnit s q * d⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) - 1 :=
    fun q => by rw [semilinearConj_sub_one, units_mul_sub_one_mul_inv]
  ext a
  rw [Finset.mem_image, mem_subgroupShifts]
  constructor
  · rintro ⟨x, hx, hx1, rfl⟩
    obtain ⟨q, hq, rfl⟩ := (hQ' x).1 hx
    refine ⟨semilinearConj s ((q : Module.End K (RootModule τ K)) - 1),
      Finset.mem_image.2 ⟨_, mem_subgroupShifts.2 ⟨q, hq, fun h => ?_, rfl⟩, rfl⟩, key q⟩
    apply hx1
    rw [h, semilinearConjUnit_one, mul_one, mul_inv_cancel]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨q, hq, hq1, rfl⟩ := mem_subgroupShifts.1 hb'
    exact ⟨_, (hQ' _).2 ⟨q, hq, rfl⟩,
      fun h => hq1 ((semilinearConjUnit_eq_one_iff s).1 (conj_eq_one_iff.1 h)), (key q).symm⟩

end Shifts

namespace RootWeightDatum

variable {K : Type} [Field K] (D : RootWeightDatum K)

theorem borel_le_group :
    D.borel ≤ D.group :=
  (D.borel_le_parabolic ∅).trans (D.parabolic_le_group ∅)

theorem unipotent_le_group
    : D.unipotent ≤ D.group := by
  cases D with
  | ordinary τ => exact le_sup_right.trans (RootWeightDatum.borel_le_group (ordinary τ))
  | fixed t σ hσ => exact graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom

theorem exists_sylow_eq_unipotent
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ P : Sylow p D.group, (P : Subgroup D.group) = D.unipotent.subgroupOf D.group := by
  cases D with
  | ordinary τ =>
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w : WeylGroup τ => (coxeterSystem τ).length w
    exact (exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀).1
  | fixed t σ hσ =>
    obtain ⟨w₀, hw₀⟩ :=
      Finite.exists_max fun w : WeylGroup t.tag => (coxeterSystem t.tag).length w
    exact (exceptional_fixed_Sylow_opposition t K p σ w₀ hw₀).1

theorem exists_conj_mem_unipotent
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {Q : Subgroup (ModGL D.tag K)} (hQG : Q ≤ D.group) (hQp : IsPGroup p Q) :
    ∃ g ∈ D.group, ∀ q ∈ Q, g⁻¹ * q * g ∈ D.unipotent := by
  have := finite_modGL (τ := D.tag) (K := K)
  obtain ⟨P, hP⟩ := D.exists_sylow_eq_unipotent p
  have hQ'p : IsPGroup p (Q.subgroupOf D.group) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQG).symm
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq D.group P S
  refine ⟨c, c.2, fun q hq => ?_⟩
  have hq' : (⟨q, hQG hq⟩ : D.group) ∈ (S : Subgroup D.group) :=
    hS (Subgroup.mem_subgroupOf.2 hq)
  rw [← hc, coe_smul_sylow_eq_map, hP, map_conj_subgroupOf D.unipotent_le_group,
    Subgroup.mem_subgroupOf] at hq'
  obtain ⟨u, hu, hqu⟩ := Subgroup.mem_map.1 hq'
  have hqu' : (MulAut.conj (c : ModGL D.tag K)).toMonoidHom u = q := hqu
  have e : (c : ModGL D.tag K)⁻¹ * q * c = u := by
    rw [← hqu', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hu

theorem exists_mem_openDominant
    : ∃ l ∈ D.openDominant, l ≠ 0 := by
  refine ⟨⟨heightVec D.tag, D.heightVec_mem_space⟩, fun i => D.inner_simpleVec_heightVec_pos i,
    fun h => ?_⟩
  have := D.inner_simpleVec_heightVec_pos ⟨0, D.rank_pos⟩
  have h' : heightVec D.tag = 0 := congrArg Subtype.val h
  rw [h', inner_zero_right] at this
  exact lt_irrefl 0 this

@[expose] def isometryRep
    (x : D.space ≃ₗᵢ[ℝ] D.space) : ModGL D.tag K := by
  classical
  exact if h : ∃ w : D.weyl, D.weylAction w = x then D.rep h.choose else 1

theorem isometryRep_weylAction
    (w : D.weyl) : D.isometryRep (D.weylAction w) = D.rep w := by
  classical
  have h : ∃ w' : D.weyl, D.weylAction w' = D.weylAction w := ⟨w, rfl⟩
  rw [isometryRep, dite_eq_left h, D.weylAction_injective h.choose_spec]

theorem setOf_stab_eq_map_conj_parabolic
    {l : D.space} (hl : l ∈ D.dominant)
    {g : ModGL D.tag K} (hg : g ∈ D.group) {F : ℝ → Submodule K (RootModule D.tag K)}
    (hF : ∀ c, (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) = F c) :
    {x : ModGL D.tag K | x ∈ D.group ∧
        ∀ c, (F c).map (x : Module.End K (RootModule D.tag K)) = F c} =
      ((D.parabolic (D.face l)).map (MulAut.conj g).toMonoidHom : Set (ModGL D.tag K)) := by
  have hmap : ∀ (a b : ModGL D.tag K) (X : Submodule K (RootModule D.tag K)),
      (X.map (a : Module.End K (RootModule D.tag K))).map (b : Module.End K (RootModule D.tag K)) =
        X.map ((b * a : ModGL D.tag K) : Module.End K (RootModule D.tag K)) := fun a b X => by
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  have hone : ∀ X : Submodule K (RootModule D.tag K),
      X.map ((1 : ModGL D.tag K) : Module.End K (RootModule D.tag K)) = X := fun X => by
    rw [Units.val_one, Module.End.one_eq_id, Submodule.map_id]
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [← D.mem_group_and_filtrationStab_iff hl, mem_filtrationStab]
  have hxG : x ∈ D.group ↔ g⁻¹ * x * g ∈ D.group := by
    refine ⟨fun h => mul_mem (mul_mem (inv_mem hg) h) hg, fun h => ?_⟩
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hg h) (inv_mem hg)
  rw [hxG]
  refine and_congr_right fun _ => forall_congr' fun c => ?_
  rw [← hF c, hmap]
  constructor
  · intro h
    rw [show g⁻¹ * x * g = g⁻¹ * (x * g) by group, ← hmap, h, hmap, inv_mul_cancel, hone]
  · intro h
    rw [show x * g = g * (g⁻¹ * x * g) by group, ← hmap, h]

theorem map_conj_parabolic_lt_group
    {l : D.space} (hl0 : l ≠ 0) {g : ModGL D.tag K}
    (hg : g ∈ D.group) :
    (D.parabolic (D.face l)).map (MulAut.conj g).toMonoidHom < D.group := by
  have hlt := D.parabolic_face_lt_group hl0
  refine lt_of_le_of_ne (fun x hx => ?_) fun h => hlt.ne (le_antisymm (D.parabolic_le_group _)
    fun y hy => ?_)
  · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hx
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hg (D.parabolic_le_group _ hx)) (inv_mem hg)
  · have hy' : g * y * g⁻¹ ∈ (D.parabolic (D.face l)).map (MulAut.conj g).toMonoidHom := by
      rw [h]
      exact mul_mem (mul_mem hg hy) (inv_mem hg)
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hy'
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at hy'

open _root_.Classical in
theorem root_p_subgroup_optimal_parabolic_containment
    [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (Q : Subgroup (ModGL D.tag K)) (hQG : Q ≤ D.group) (hQp : IsPGroup p Q)
    (hQ : Q ≠ ⊥) :
    ∃ M : ℝ, 0 < M ∧
      (∃ g ∈ D.group, ∃ l : D.space, ‖l‖ = 1 ∧
        frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M) ∧
      (∀ g ∈ D.group, ∀ l : D.space, ‖l‖ = 1 →
        frameShift D.isInternal_weightSpace (subgroupShifts Q) g l ≤ M) ∧
      ∃ F : ℝ → Submodule K (RootModule D.tag K),
        (∀ g ∈ D.group, ∀ l : D.space, ‖l‖ = 1 →
          frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M → ∀ c : ℝ,
            (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) = F c) ∧
        (∀ F' : ℝ → Submodule K (RootModule D.tag K),
          (∀ g ∈ D.group, ∀ l : D.space, ‖l‖ = 1 →
            frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M → ∀ c : ℝ,
              (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) = F' c) →
          F' = F) ∧
        (∃ g ∈ D.group, ∃ l ∈ D.dominant, ‖l‖ = 1 ∧
          frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M) ∧
        (∀ g ∈ D.group, ∀ l ∈ D.dominant, ‖l‖ = 1 →
          frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M →
          D.face l ≠ Set.univ ∧
          D.group ⊓ Subgroup.centralizer (Q : Set (ModGL D.tag K)) ≤
            D.group ⊓ Subgroup.normalizer (Q : Set (ModGL D.tag K)) ∧
          (∀ x ∈ D.group ⊓ Subgroup.normalizer (Q : Set (ModGL D.tag K)), ∀ c : ℝ,
            (F c).map (x : Module.End K (RootModule D.tag K)) = F c) ∧
          {x : ModGL D.tag K | x ∈ D.group ∧
              ∀ c : ℝ, (F c).map (x : Module.End K (RootModule D.tag K)) = F c} =
            ((D.parabolic (D.face l)).map (MulAut.conj g).toMonoidHom :
              Set (ModGL D.tag K)) ∧
          (D.parabolic (D.face l)).map (MulAut.conj g).toMonoidHom < D.group) ∧
        ∀ (σ σ' : K →+* K) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
          (s : RootModule D.tag K ≃ₛₗ[σ] RootModule D.tag K),
          (∀ g : ModGL D.tag K, semilinearConjUnit s g ∈ D.group ↔ g ∈ D.group) →
          ∀ u : D.space ≃ₗᵢ[ℝ] D.space, D.weights.image u = D.weights →
          (∀ χ ∈ D.weights, (D.weightSpace χ).map s.toLinearMap = D.weightSpace (u χ)) →
          ∀ d ∈ D.group, ∀ Q' : Subgroup (ModGL D.tag K),
            (∀ x, x ∈ Q' ↔ ∃ q ∈ Q, d * semilinearConjUnit s q * d⁻¹ = x) →
            (∃ g ∈ D.group, ∃ l : D.space, ‖l‖ = 1 ∧
              frameShift D.isInternal_weightSpace (subgroupShifts Q') g l = M) ∧
            (∀ g ∈ D.group, ∀ l : D.space, ‖l‖ = 1 →
              frameShift D.isInternal_weightSpace (subgroupShifts Q') g l ≤ M) ∧
            ∀ g ∈ D.group, ∀ l : D.space, ‖l‖ = 1 →
              frameShift D.isInternal_weightSpace (subgroupShifts Q') g l = M → ∀ c : ℝ,
                (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) =
                  ((F c).map s.toLinearMap).map (d : Module.End K (RootModule D.tag K)) := by
  have := finite_modGL (τ := D.tag) (K := K)
  have hA := subgroupShifts_nonempty hQ
  have hA0 := zero_notMem_subgroupShifts Q
  have hWΩ : ∀ w ∈ D.weylAction.range, D.weights.image w = D.weights := fun w hw => by
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hw
    exact D.image_weylAction_weights w
  have hnG : ∀ w ∈ D.weylAction.range, D.isometryRep w ∈ D.group := fun w hw => by
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hw
    rw [isometryRep_weylAction]
    exact D.rep_mem_group w
  have hn : ∀ w ∈ D.weylAction.range, ∀ χ ∈ D.weights,
      (D.weightSpace χ).map (D.isometryRep w : Module.End K (RootModule D.tag K)) =
        D.weightSpace (w χ) := fun w hw χ _ => by
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hw
    rw [isometryRep_weylAction]
    exact D.map_weightSpace_rep w χ
  have hDom : ∀ x : D.space, ∃ w ∈ D.weylAction.range, ∃ μ ∈ D.dominant, w μ = x := fun x => by
    obtain ⟨w, l, hl, hx⟩ := D.exists_weylAction_mem_dominant x
    exact ⟨_, MonoidHom.mem_range.2 ⟨w, rfl⟩, l, hl, hx⟩
  have hB : ∀ b ∈ D.borel, ∀ l ∈ D.dominant, ∀ c : ℝ,
      (weightFiltration D.weights D.weightSpace l c).map
          (b : Module.End K (RootModule D.tag K)) =
        weightFiltration D.weights D.weightSpace l c :=
    fun b hb l hl c => D.borel_le_filtrationStab hl hb c
  have hG : (D.group : Set (ModGL D.tag K)) = ⋃ w ∈ D.weylAction.range,
      (D.borel : Set (ModGL D.tag K)) * {D.isometryRep w} * (D.borel : Set (ModGL D.tag K)) := by
    rw [D.group_eq_iUnion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨D.weylAction w, MonoidHom.mem_range.2 ⟨w, rfl⟩, by rwa [isometryRep_weylAction]⟩
    · rintro ⟨x, hx, hgx⟩
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hx
      exact ⟨w, by rwa [isometryRep_weylAction] at hgx⟩
  obtain ⟨g₀, hg₀, hg₀U⟩ := D.exists_conj_mem_unipotent p hQG hQp
  obtain ⟨l₀, hl₀, hl₀0⟩ := D.exists_mem_openDominant
  have hpos : 0 < frameShift D.isInternal_weightSpace (subgroupShifts Q) g₀ l₀ := by
    obtain ⟨ε, hε, hm⟩ := D.exists_pos_le_inner_ofLattice hl₀
    have hle : ε ≤ frameShift D.isInternal_weightSpace (subgroupShifts Q) g₀ l₀ :=
      (le_minWeightShift_iff D.isInternal_weightSpace (conjFamily_nonempty hA g₀)
        (zero_notMem_conjFamily hA0 g₀) l₀ ε).2 fun a ha c => by
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨q, hq, -, rfl⟩ := mem_subgroupShifts.1 hb
        have hR := (posUnipotent_le_labelRaisingSubgroup hε.le hm
          (D.unipotent_le_posUnipotent (hg₀U q hq))).1
        rw [units_inv_mul_sub_one_mul]
        exact D.map_filtration_le_of_labelRaises l₀ hR c
    linarith
  obtain ⟨M, hM0, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, hMmax, F, hF, hFnorm, hFsemi⟩ :=
    finite_Bruhat_optimal_weight_filtration D.isInternal_weightSpace (subgroupShifts Q) hA hA0
      D.group D.borel D.borel_le_group D.weylAction.range hWΩ D.isometryRep hnG hn D.dominant hDom
      hB hG ⟨g₀, hg₀, l₀, hl₀0, hpos⟩
  have huniq : ∀ F' : ℝ → Submodule K (RootModule D.tag K),
      (∀ g ∈ D.group, ∀ l : D.space, ‖l‖ = 1 →
        frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M → ∀ c : ℝ,
          (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) = F' c) → F' = F :=
    fun F' hF' => funext fun c => (hF' g₁ hg₁ l₁ hl₁ hgl₁ c).symm.trans (hF g₁ hg₁ l₁ hl₁ hgl₁ c)
  have hdom : ∃ g ∈ D.group, ∃ l ∈ D.dominant, ‖l‖ = 1 ∧
      frameShift D.isInternal_weightSpace (subgroupShifts Q) g l = M := by
    obtain ⟨w, μ, hμ, hμl⟩ := D.exists_weylAction_mem_dominant l₁
    refine ⟨g₁ * D.rep w, mul_mem hg₁ (D.rep_mem_group w), μ, hμ, ?_, ?_⟩
    · rw [← (D.weylAction w).norm_map μ, hμl, hl₁]
    · rw [frameShift_mul_rep D.isInternal_weightSpace hA hA0 g₁ (D.rep w)
        (D.image_weylAction_weights w) (fun χ _ => D.map_weightSpace_rep w χ) μ, hμl, hgl₁]
  refine ⟨M, hM0, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, hMmax, F, hF, huniq, hdom,
    fun g hg l hl hl1 hgl => ?_, fun σ σ' _ _ s hsG u hu hs d hd Q' hQ' => ?_⟩
  ·
    have hl0 : l ≠ 0 := fun h => by
      rw [h, norm_zero] at hl1
      exact zero_ne_one hl1
    refine ⟨D.face_ne_univ hl0, inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _),
      fun x hx c => hFnorm x (Subgroup.mem_inf.1 hx).1
        (image_conj_subgroupShifts (Subgroup.mem_inf.1 hx).2) c,
      D.setOf_stab_eq_map_conj_parabolic hl hg (hF g hg l hl1 hgl),
      D.map_conj_parabolic_lt_group hl0 hg⟩
  ·
    obtain ⟨-, -, ⟨g', hg', l', hl', hgl'⟩, hMmax', hF'⟩ := hFsemi σ σ' s hsG u hu hs
    have hshift : ∀ (g : ModGL D.tag K) (l : D.space),
        frameShift D.isInternal_weightSpace (subgroupShifts Q') g l =
          frameShift D.isInternal_weightSpace ((subgroupShifts Q).image (semilinearConj s))
            (d⁻¹ * g) l := fun g l => by
      rw [subgroupShifts_eq_image_image s d hQ', frameShift, frameShift, conjFamily_image_conj]
    refine ⟨⟨d * g', mul_mem hd hg', l', hl', ?_⟩, fun g hg l hl => ?_, fun g hg l hl hgl c => ?_⟩
    · rw [hshift, inv_mul_cancel_left, hgl']
    · rw [hshift]
      exact hMmax' _ (mul_mem (inv_mem hd) hg) l hl
    · rw [hshift] at hgl
      have h := hF' _ (mul_mem (inv_mem hd) hg) l hl hgl c
      calc (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) =
            ((D.filtration l c).map ((d⁻¹ * g : ModGL D.tag K) :
              Module.End K (RootModule D.tag K))).map (d : Module.End K (RootModule D.tag K)) := by
            rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul,
              mul_inv_cancel_left]
        _ = ((F c).map s.toLinearMap).map (d : Module.End K (RootModule D.tag K)) := by
            rw [← h]
            rfl

end RootWeightDatum

end CFSG.LieType.Chevalley
