module

public import CFSG.CharacterTheory.Wreathed.ActualCentralizerLayer
public import CFSG.CharacterTheory.Wreathed.NoncentralScalarSylowCoverage
public import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

open CFSG.Wreathed
open CFSG.Wreathed.NoncentralScalarSylowCoverage
open scoped Classical

namespace CFSG.Wreathed.OriginalSylowCentralizerCoverage

universe u

theorem quasisimple_nontrivial {H : Type u} [Group H] (hH : CFSG.IsQuasisimple H) :
    Nontrivial H := by
  obtain ⟨a, b, hab⟩ := hH.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) b
  have hneq : a * b ≠ b * a := by
    intro h
    apply hab
    simp only [← map_mul, h]
  exact ⟨⟨a * b, b * a, hneq⟩⟩

theorem quasisimple_not_le_center {H : Type u} [Group H]
    (M : Subgroup H) (hM : CFSG.IsQuasisimple M) : ¬ M ≤ Subgroup.center H := by
  let : Group.IsPerfect M := hM.1
  let : Nontrivial M := quasisimple_nontrivial hM
  intro hle
  have hcomm : IsMulCommutative M := isMulCommutative_iff.mpr (by
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hle a.property) (b : H)).symm)
  exact Group.IsPerfect.not_isMulCommutative M hcomm

theorem coverage_iff_noncentral_centralizer
    {N : Type u} [Group N] [Finite N] (R : Subgroup N) [R.Normal]
    (M : Subgroup (N ⧸ R)) [M.Normal] (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set (N ⧸ R)) = Subgroup.center (N ⧸ R))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card R) (P : Sylow ell R) :
    let pi := QuotientGroup.mk' R
    let C := Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set N)
    (C ⊓ M.comap pi).map pi = M ↔ ¬ C ≤ (Subgroup.center (N ⧸ R)).comap pi := by
  dsimp only
  constructor
  · intro hcoverage hle
    apply quasisimple_not_le_center M hM
    intro m hm
    rw [← hcoverage] at hm
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm
    exact hle ha.1
  · intro hnoncentral
    obtain ⟨v, hv, hvnoncentral⟩ := IsConcreteLE.not_le_iff_exists.mp hnoncentral
    exact noncentral_scalar_Sylow_action_gives_quasisimple_centralizer_coverage
      R M hM hcentralizer hell hdiv P v
      (Subgroup.centralizer_le_normalizer _ hv) hvnoncentral
      (Or.inl (by
        intro a ha
        have h := (Subgroup.mem_centralizer_iff.mp hv a ha).symm
        calc v * a * v⁻¹ = a * v * v⁻¹ := by rw [h]
             _ = a := by simp [mul_assoc]))

theorem solvable_center_preimage
    {N : Type u} [Group N] [Finite N] (R : Subgroup N) [R.Normal]
    (hodd : Odd (Nat.card R)) [IsCyclic (Subgroup.center (N ⧸ R))] :
    Group.IsSolvable ((Subgroup.center (N ⧸ R)).comap (QuotientGroup.mk' R)) := by
  let K := (Subgroup.center (N ⧸ R)).comap (QuotientGroup.mk' R)
  let i : R →* K := R.subtype.codRestrict K (by
    intro r
    change QuotientGroup.mk' R r ∈ Subgroup.center (N ⧸ R)
    change ((r : N) : N ⧸ R) ∈ Subgroup.center (N ⧸ R)
    rw [(QuotientGroup.eq_one_iff (N := R) (r : N)).mpr r.property]
    exact (Subgroup.center (N ⧸ R)).one_mem)
  let f : K →* Subgroup.center (N ⧸ R) :=
    (QuotientGroup.mk' R).subgroupComap (Subgroup.center (N ⧸ R))
  let : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let : CommGroup (Subgroup.center (N ⧸ R)) := IsCyclic.commGroup
  let : Group.IsSolvable (Subgroup.center (N ⧸ R)) := Group.isSolvable_of_comm
    (fun a b => mul_comm a b)
  apply Group.isSolvable_of_ker_le_range i f
  intro a ha
  have hr : (a : N) ∈ R := by
    apply (QuotientGroup.eq_one_iff (N := R) (a : N)).mp
    exact congrArg Subtype.val ha
  exact ⟨⟨a, hr⟩, rfl⟩

theorem coverage_gives_not_solvable
    {N : Type u} [Group N] (R : Subgroup N) [R.Normal]
    (M : Subgroup (N ⧸ R)) (hM : CFSG.IsQuasisimple M) (C : Subgroup N)
    (hcoverage : (C ⊓ M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M) :
    ¬ Group.IsSolvable C := by
  let pi := QuotientGroup.mk' R
  let D := C ⊓ M.comap pi
  let f : D →* M := (pi.domRestrict D).codRestrict M (fun a => a.property.2)
  have hf : Function.Surjective f := by
    intro m
    have hm : (m : N ⧸ R) ∈ D.map pi := hcoverage.symm ▸ m.property
    obtain ⟨a, ha, hea⟩ := Subgroup.mem_map.mp hm
    exact ⟨⟨a, ha⟩, Subtype.ext hea⟩
  let : Group.IsPerfect M := hM.1
  let : Nontrivial M := quasisimple_nontrivial hM
  intro hsolv
  let : Group.IsSolvable C := hsolv
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (show D ≤ C from inf_le_left))
  exact Group.IsPerfect.not_isSolvable M (Group.isSolvable_of_surjective hf)

theorem coverage_iff_not_solvable
    {N : Type u} [Group N] [Finite N] (R : Subgroup N) [R.Normal]
    (hodd : Odd (Nat.card R)) [IsCyclic (Subgroup.center (N ⧸ R))]
    (M : Subgroup (N ⧸ R)) [M.Normal] (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set (N ⧸ R)) = Subgroup.center (N ⧸ R))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card R) (P : Sylow ell R) :
    let pi := QuotientGroup.mk' R
    let C := Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set N)
    (C ⊓ M.comap pi).map pi = M ↔ ¬ Group.IsSolvable C := by
  dsimp only
  constructor
  · exact coverage_gives_not_solvable R M hM _
  · intro hnonsolv
    apply (coverage_iff_noncentral_centralizer R M hM hcentralizer hell hdiv P).mpr
    intro hle
    let := solvable_center_preimage R hodd
    exact hnonsolv (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hle))

theorem coverage_two_subgroup_centralizes
    {N : Type u} [Group N] (R : Subgroup N) [R.Normal]
    (hodd : Odd (Nat.card R)) (M : Subgroup (N ⧸ R))
    (P Q : Subgroup N) (hQtwo : IsPGroup 2 Q) (hQP : Q ≤ Subgroup.normalizer (P : Set N))
    (hQM : Q.map (QuotientGroup.mk' R) ≤ M)
    (hcoverage : (Subgroup.centralizer (P : Set N) ⊓
      M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M) :
    Q ≤ Subgroup.centralizer (P : Set N) := by
  let pi := QuotientGroup.mk' R
  let action := P.normalizerMonoidHom
  intro q hq
  have hqm : pi q ∈ M := hQM (Subgroup.mem_map_of_mem pi hq)
  obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp (hcoverage.symm ▸ hqm)
  let cB : Subgroup.normalizer (P : Set N) := ⟨c, Subgroup.centralizer_le_normalizer _ hc.1⟩
  let qB : Subgroup.normalizer (P : Set N) := ⟨q, hQP hq⟩
  let rB : Subgroup.normalizer (P : Set N) := cB⁻¹ * qB
  have hcaction : action cB = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [Subgroup.normalizerMonoidHom_ker]
    exact hc.1
  have hr : (rB : N) ∈ R := by
    apply (QuotientGroup.eq_one_iff (N := R) (rB : N)).mp
    change pi (c⁻¹ * q) = 1
    rw [map_mul, map_inv, hceq, inv_mul_cancel]
  have haqr : action qB = action rB := by
    dsimp only [rB]
    rw [map_mul, map_inv, hcaction, inv_one, one_mul]
  obtain ⟨k, hk⟩ := hQtwo ⟨q, hq⟩
  have hqpow : qB ^ (2 ^ k) = 1 := Subtype.ext (congrArg (fun a : Q => (a : N)) hk)
  have hrpow : rB ^ Nat.card R = 1 := by
    apply Subtype.ext
    exact congrArg (fun a : R => (a : N))
      (pow_card_eq_one' (x := (⟨(rB : N), hr⟩ : R)))
  have haqpow : (action qB) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hqpow, map_one]
  have haqodd : (action qB) ^ Nat.card R = 1 := by
    rw [haqr, ← map_pow, hrpow, map_one]
  have haone : action qB = 1 :=
    (pow_eq_one_iff_of_coprime ((Nat.coprime_two_left.mpr hodd).pow_left k)).mp
      ⟨haqpow, haqodd⟩
  have hker : qB ∈ action.ker := MonoidHom.mem_ker.mpr haone
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact hker

variable {G : Type u} [Group G] [Finite G]

theorem original_center_preimage
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.center (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e) =
        centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e := by
  have hk : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
    QuotientGroup.ker_mk' _
  rw [centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e,
    centralizerFullCenterImage, Subgroup.comap_map_eq, hk, sup_comm]

theorem original_quotient_center_isCyclic
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (Subgroup.center (centralizerOddCoreQuotient n S e)) := by
  rw [centralizerOddCoreQuotient_center_eq_fullCenterImage, centralizerFullCenterImage]
  exact isCyclic_of_surjective
    ((centralizerOddCoreMap n S e).subgroupMap (centralizerFullCenter n hn S e))
    ((centralizerOddCoreMap n S e).subgroupMap_surjective _)

theorem original_center_product_inf_sylow
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) ⊓
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) =
        centralizerFullCenter n hn S e := by
  apply le_antisymm
  · rintro s ⟨hs, hsS⟩
    rw [← original_center_preimage n hn S e] at hs
    change centralizerOddCoreMap n S e s ∈
      Subgroup.center (centralizerOddCoreQuotient n S e) at hs
    rw [centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e] at hs
    change centralizerOddCoreMap n S e s ∈
      (centralizerFullCenter n hn S e).map (centralizerOddCoreMap n S e) at hs
    obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hs
    have has : a ∈ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) :=
      centralizerFullCenter_le_sylow n hn S e ha
    have haeq : a = s := congrArg Subtype.val
      (centralizerOddCoreMap_sylow_injective n hn S e
        (a₁ := ⟨a, has⟩) (a₂ := ⟨s, hsS⟩) heq)
    exact haeq ▸ ha
  · exact le_inf le_sup_right (centralizerFullCenter_le_sylow n hn S e)

theorem original_quaternion_image_le_layer
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) ≤
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  have hdata := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  rw [hdata.layer, ← centralizerLiftedLayerSylow_image hnonab n hn S e hfour]
  exact Subgroup.map_subtype_le _

theorem original_layer_data
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.IsQuasisimple (CFSG.layer (centralizerOddCoreQuotient n S e)) ∧
      Subgroup.centralizer (CFSG.layer (centralizerOddCoreQuotient n S e) :
        Set (centralizerOddCoreQuotient n S e)) =
          Subgroup.center (centralizerOddCoreQuotient n S e) := by
  have hdata := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  rw [hdata.layer]
  exact ⟨hdata.quasisimple, hdata.centralizer.trans hdata.ambient_center.symm⟩

omit [Finite G] in
theorem original_quaternion_nonabelian
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ a b : centralizerQuaternion n hn S e, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := originalY_is_nonabelian n hn
  let E := modelYEquiv (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
  refine ⟨E a, E b, ?_⟩
  intro h
  apply hab
  apply E.injective
  change E a * E b = E b * E a at h
  simpa only [map_mul] using h

omit [Finite G] in
theorem original_quaternion_not_isCyclic
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ¬ IsCyclic (centralizerQuaternion n hn S e) := by
  intro hcyc
  let : IsCyclic (centralizerQuaternion n hn S e) := hcyc
  let : CommGroup (centralizerQuaternion n hn S e) := IsCyclic.commGroup
  obtain ⟨a, b, hab⟩ := original_quaternion_nonabelian n hn S e
  exact hab (mul_comm a b)

omit [Finite G] in
theorem original_involution_centralizes
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (P : Subgroup (involutionCentralizer n S e)) :
    Subgroup.zpowers (centralInvolution n S e) ≤ Subgroup.centralizer (P :
      Set (involutionCentralizer n S e)) := by
  apply Subgroup.zpowers_le.mpr
  rw [Subgroup.mem_centralizer_iff]
  intro p _
  exact Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e) p

theorem original_coverage_quaternion_centralizes
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e))
    (hinvariant : (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) ≤
      Subgroup.normalizer (((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)))
    (hcoverage : (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
        (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
          (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)) :
    centralizerQuaternion n hn S e ≤
      Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) := by
  exact coverage_two_subgroup_centralizes (centralizerOddCore n S e)
    (centralizerOddCore_card_odd n S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
    _ (centralizerQuaternion n hn S e)
    ((centralizerSylow n hn S e).isPGroup'.to_le (centralizerQuaternion_le_sylow n hn S e))
    ((centralizerQuaternion_le_sylow n hn S e).trans hinvariant)
    (original_quaternion_image_le_layer hnonab n hn S e hfour) hcoverage

omit [Finite G] in
theorem original_fullCenter_map
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullCenter n hn S e).map (involutionCentralizer n S e).subtype =
      (Subgroup.center S).map (S : Subgroup G).subtype := by
  rw [centralizerFullCenter, modelCenter, Subgroup.map_map, centralizerModelHom_comp]
  rw [← modelSylowCenter_eq_center n hn S e, modelSylowCenter_eq_map,
    Subgroup.map_map]
  rfl

omit [Finite G] in
theorem original_centralizer_inf_sylow_le_center_iff
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    {C : Subgroup (involutionCentralizer n S e)} :
    C ⊓ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) ≤
      centralizerFullCenter n hn S e ↔
    (C.map (involutionCentralizer n S e).subtype).subgroupOf (S : Subgroup G) ≤
      Subgroup.center S := by
  have hmapSylow : (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)).map (involutionCentralizer n S e).subtype =
        (S : Subgroup G) := by
    rw [centralizerSylow_coe, Subgroup.map_subgroupOf_eq_of_le
      (sylow_le_involutionCentralizer n hn S e)]
  constructor
  · intro hle s hs
    have hsN : (s : G) ∈ involutionCentralizer n S e :=
      sylow_le_involutionCentralizer n hn S e s.property
    have hsc : (⟨(s : G), hsN⟩ : involutionCentralizer n S e) ∈ C := by
      obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hs
      exact (Subtype.ext heq : a = ⟨(s : G), hsN⟩) ▸ ha
    have hsS : (⟨(s : G), hsN⟩ : involutionCentralizer n S e) ∈
        (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) := by
      rw [centralizerSylow_coe]
      exact s.property
    have hsZ : (s : G) ∈ (Subgroup.center S).map (S : Subgroup G).subtype := by
      rw [← original_fullCenter_map n hn S e]
      exact Subgroup.mem_map_of_mem _ (hle ⟨hsc, hsS⟩)
    obtain ⟨z, hz, heq⟩ := Subgroup.mem_map.mp hsZ
    exact (Subtype.ext heq : z = s) ▸ hz
  · intro hle q hq
    have hqS : (q : G) ∈ (S : Subgroup G) := by
      rw [← hmapSylow]
      exact Subgroup.mem_map_of_mem _ hq.2
    have hqC : (⟨(q : G), hqS⟩ : S) ∈
        (C.map (involutionCentralizer n S e).subtype).subgroupOf (S : Subgroup G) :=
      Subgroup.mem_map_of_mem _ hq.1
    have hqZ : (q : G) ∈ (centralizerFullCenter n hn S e).map
        (involutionCentralizer n S e).subtype := by
      rw [original_fullCenter_map n hn S e]
      exact Subgroup.mem_map_of_mem _ (hle hqC)
    obtain ⟨z, hz, heq⟩ := Subgroup.mem_map.mp hqZ
    exact (Subtype.ext heq : z = q) ▸ hz

omit [Finite G] in
@[expose] def originalPrimeSubgroup (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    Subgroup (involutionCentralizer n S e) :=
  (P : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype

omit [Finite G] in
@[expose] def originalPrimeCentralizer (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    Subgroup (involutionCentralizer n S e) :=
  Subgroup.centralizer (originalPrimeSubgroup n S e P : Set (involutionCentralizer n S e))

omit [Finite G] in
@[expose] def originalSylowIntersection (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    Subgroup (involutionCentralizer n S e) :=
  originalPrimeCentralizer n S e P ⊓
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))

theorem original_coverage_iff_noncentral
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    {P : Sylow ell (centralizerOddCore n S e)} :
    (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) ↔
    ¬ originalPrimeCentralizer n S e P ≤
      centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e := by
  have hdata := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    rw [hdata.layer]
    exact hdata.normal
  let : (show Subgroup (involutionCentralizer n S e ⧸ centralizerOddCore n S e) from
      CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    change (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal
    infer_instance
  have hM := original_layer_data hnonab n hn S e hfour
  have h := coverage_iff_noncentral_centralizer (centralizerOddCore n S e)
    (CFSG.layer (centralizerOddCoreQuotient n S e)) hM.1 hM.2 hell hdiv P
  change _ ↔ ¬ originalPrimeCentralizer n S e P ≤
    (Subgroup.center (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e) at h
  rwa [original_center_preimage n hn S e] at h

theorem original_coverage_iff_not_solvable
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    {P : Sylow ell (centralizerOddCore n S e)} :
    (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) ↔
      ¬ Group.IsSolvable (originalPrimeCentralizer n S e P) := by
  have hdata := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    rw [hdata.layer]
    exact hdata.normal
  let : IsCyclic (Subgroup.center
      (involutionCentralizer n S e ⧸ centralizerOddCore n S e)) := by
    change IsCyclic (Subgroup.center (centralizerOddCoreQuotient n S e))
    exact original_quotient_center_isCyclic n hn S e
  let : (show Subgroup (involutionCentralizer n S e ⧸ centralizerOddCore n S e) from
      CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    change (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal
    infer_instance
  have hM := original_layer_data hnonab n hn S e hfour
  exact coverage_iff_not_solvable (centralizerOddCore n S e)
    (centralizerOddCore_card_odd n S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
    hM.1 hM.2 hell hdiv P

theorem original_noncentral_intersection_gives_coverage
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hnoncentral : ¬ originalSylowIntersection n hn S e P ≤ centralizerFullCenter n hn S e) :
    (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) := by
  apply (original_coverage_iff_noncentral hnonab (n := n) hn (S := S) (e := e)
      hfour hell hdiv (P := P)).mpr
  intro hle
  apply hnoncentral
  rw [← original_center_product_inf_sylow n hn S e]
  exact inf_le_inf_right _ hle


omit [Finite G] in
theorem original_quaternion_containment_gives_noncyclic
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e))
    (hQ : centralizerQuaternion n hn S e ≤ originalSylowIntersection n hn S e P) :
    ¬ IsCyclic (originalSylowIntersection n hn S e P) := by
  intro hcyclic
  let : IsCyclic (originalSylowIntersection n hn S e P) := hcyclic
  exact original_quaternion_not_isCyclic n hn S e (Subgroup.isCyclic_of_le hQ)

omit [Finite G] in
theorem original_noncyclic_intersection_not_le_center
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e))
    (hnoncyclic : ¬ IsCyclic (originalSylowIntersection n hn S e P)) :
    ¬ originalSylowIntersection n hn S e P ≤ centralizerFullCenter n hn S e := by
  exact fun hle => hnoncyclic (Subgroup.isCyclic_of_le hle)

theorem original_invariant_coverage_equivalences
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hinvariant : (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) ≤
      Subgroup.normalizer (originalPrimeSubgroup n S e P : Set (involutionCentralizer n S e))) :
    let coverage := (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)
    (coverage ↔ centralizerQuaternion n hn S e ≤ originalSylowIntersection n hn S e P) ∧
    (coverage ↔ ¬ IsCyclic (originalSylowIntersection n hn S e P)) ∧
    (coverage ↔ ¬ originalSylowIntersection n hn S e P ≤ centralizerFullCenter n hn S e) := by
  dsimp only
  have hCQ : (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) →
      centralizerQuaternion n hn S e ≤ originalSylowIntersection n hn S e P := by
    intro hcoverage
    exact le_inf
      (original_coverage_quaternion_centralizes hnonab n hn S e hfour P hinvariant hcoverage)
      (centralizerQuaternion_le_sylow n hn S e)
  have hQN := original_quaternion_containment_gives_noncyclic n hn S e P
  have hNZ := original_noncyclic_intersection_not_le_center n hn S e P
  have hZC := original_noncentral_intersection_gives_coverage hnonab n hn S e hfour hell hdiv P
  exact ⟨⟨hCQ, fun h => hZC (hNZ (hQN h))⟩,
    ⟨fun h => hQN (hCQ h), fun h => hZC (hNZ h)⟩,
    ⟨fun h => hNZ (hQN (hCQ h)), hZC⟩⟩


omit [Finite G] in
@[expose] def originalSylowCentralizer
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) : Subgroup S :=
  ((originalPrimeCentralizer n S e P).map (involutionCentralizer n S e).subtype).subgroupOf
    (S : Subgroup G)

omit [Finite G] in
theorem originalSylowCentralizer_eq_ambient
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    originalSylowCentralizer n S e P =
      (Subgroup.centralizer (((originalPrimeSubgroup n S e P).map
        (involutionCentralizer n S e).subtype) : Set G)).subgroupOf (S : Subgroup G) := by
  ext s
  constructor
  · intro hs
    obtain ⟨c, hc, hcs⟩ := Subgroup.mem_map.mp hs
    change (s : G) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro p ⟨q, hq, rfl⟩
    have h := congrArg (fun a : involutionCentralizer n S e => (a : G))
      (Subgroup.mem_centralizer_iff.mp hc q hq)
    change (q : G) * (c : G) = (c : G) * (q : G) at h
    change (c : G) = (s : G) at hcs
    change (q : G) * (s : G) = (s : G) * (q : G)
    rwa [hcs] at h
  · intro hs
    have hsN : (s : G) ∈ involutionCentralizer n S e :=
      sylow_le_involutionCentralizer n hn S e s.property
    refine Subgroup.mem_map.mpr ⟨⟨s, hsN⟩, ?_, rfl⟩
    change (⟨(s : G), hsN⟩ : involutionCentralizer n S e) ∈
      Subgroup.centralizer (originalPrimeSubgroup n S e P : Set (involutionCentralizer n S e))
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hs (p : G)
      (Subgroup.mem_map_of_mem _ hp)

omit [Finite G] in
theorem originalSylowCentralizer_map
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    (originalSylowCentralizer n S e P).map (S : Subgroup G).subtype =
      (originalSylowIntersection n hn S e P).map (involutionCentralizer n S e).subtype := by
  change (((originalPrimeCentralizer n S e P).map
    (involutionCentralizer n S e).subtype).comap (S : Subgroup G).subtype).map
      (S : Subgroup G).subtype = _
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm,
    originalSylowIntersection, Subgroup.map_inf _ _ _
      (involutionCentralizer n S e).subtype_injective]
  have hS : (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)).map
      (involutionCentralizer n S e).subtype = (S : Subgroup G) := by
    rw [centralizerSylow_coe, Subgroup.map_subgroupOf_eq_of_le
      (sylow_le_involutionCentralizer n hn S e)]
  rw [hS]

omit [Finite G] in
@[expose] def originalSylowCentralizerEquiv
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    originalSylowCentralizer n S e P ≃* originalSylowIntersection n hn S e P :=
  ((originalSylowCentralizer n S e P).equivMapOfInjective (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective).trans
    ((MulEquiv.subgroupCongr (originalSylowCentralizer_map n hn S e P)).trans
      ((originalSylowIntersection n hn S e P).equivMapOfInjective
        (involutionCentralizer n S e).subtype
        (involutionCentralizer n S e).subtype_injective).symm)

omit [Finite G] in
theorem originalSylowCentralizer_isCyclic_iff
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    {ell : ℕ} {P : Sylow ell (centralizerOddCore n S e)} :
    IsCyclic (originalSylowCentralizer n S e P) ↔
      IsCyclic (originalSylowIntersection n hn S e P) := by
  let E := originalSylowCentralizerEquiv n hn S e P
  constructor
  · intro h
    let : IsCyclic (originalSylowCentralizer n S e P) := h
    exact isCyclic_of_surjective E E.surjective
  · intro h
    let : IsCyclic (originalSylowIntersection n hn S e P) := h
    exact isCyclic_of_surjective E.symm E.symm.surjective

omit [Finite G] in
theorem originalSylowCentralizer_quaternion_iff
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    {ell : ℕ} {P : Sylow ell (centralizerOddCore n S e)} :
    (modelY S e).subgroupOf (S : Subgroup G) ≤ originalSylowCentralizer n S e P ↔
      centralizerQuaternion n hn S e ≤ originalSylowIntersection n hn S e P := by
  have hambient : (modelY S e).subgroupOf (S : Subgroup G) ≤
      originalSylowCentralizer n S e P ↔ modelY S e ≤
        (originalSylowIntersection n hn S e P).map (involutionCentralizer n S e).subtype := by
    constructor
    · intro h
      have hm := Subgroup.map_mono (f := (S : Subgroup G).subtype) h
      rw [Subgroup.map_subgroupOf_eq_of_le (modelY_le_sylow S e),
        originalSylowCentralizer_map n hn S e P] at hm
      exact hm
    · intro h q hq
      change (q : G) ∈ (originalPrimeCentralizer n S e P).map
        (involutionCentralizer n S e).subtype
      have hm : (q : G) ∈ (originalSylowIntersection n hn S e P).map
          (involutionCentralizer n S e).subtype := h hq
      exact Subgroup.map_mono (f := (involutionCentralizer n S e).subtype) inf_le_left hm
  rw [hambient, ← centralizerQuaternion_map n hn S e]
  exact Subgroup.map_le_map_iff_of_injective (involutionCentralizer n S e).subtype_injective


omit [Finite G] in
theorem original_Sylow_center_isCyclic
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (Subgroup.center S) := by
  let : IsCyclic (Original.Z (2 ^ n)) := by
    unfold Original.Z
    infer_instance
  rw [← modelSylowCenter_eq_center n hn S e, modelSylowCenter_eq_map]
  exact isCyclic_of_surjective (e.symm.toMonoidHom.subgroupMap (Original.Z (2 ^ n)))
    (e.symm.toMonoidHom.subgroupMap_surjective _)

omit [Finite G] in
@[expose] def originalSylowInvolution
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : S :=
  e.symm (Original.x (2 ^ n))

omit [Finite G] in
theorem originalSylowInvolution_centralizes
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    Subgroup.zpowers (originalSylowInvolution n S e) ≤ originalSylowCentralizer n S e P := by
  apply Subgroup.zpowers_le.mpr
  change (originalSylowInvolution n S e : G) ∈
    (originalPrimeCentralizer n S e P).map (involutionCentralizer n S e).subtype
  exact Subgroup.mem_map_of_mem _
    (original_involution_centralizes n S e (originalPrimeSubgroup n S e P)
      (Subgroup.mem_zpowers (centralInvolution n S e)))

theorem original_failed_coverage_consequences
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hfailure : ¬ (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)) :
    originalPrimeCentralizer n S e P ≤ centralizerOddCore n S e ⊔
        centralizerFullCenter n hn S e ∧
    Group.IsSolvable (originalPrimeCentralizer n S e P) ∧
    Subgroup.zpowers (originalSylowInvolution n S e) ≤ originalSylowCentralizer n S e P ∧
    originalSylowCentralizer n S e P ≤ Subgroup.center S ∧
    IsCyclic (originalSylowCentralizer n S e P) := by
  have hle : originalPrimeCentralizer n S e P ≤ centralizerOddCore n S e ⊔
      centralizerFullCenter n hn S e := by
    by_contra hnot
    exact hfailure ((original_coverage_iff_noncentral hnonab (n := n) hn (S := S) (e := e)
      hfour hell hdiv (P := P)).mpr hnot)
  have hsolv : Group.IsSolvable (originalPrimeCentralizer n S e P) := by
    by_contra hnot
    exact hfailure ((original_coverage_iff_not_solvable hnonab (n := n) hn (S := S) (e := e)
      hfour hell hdiv (P := P)).mpr
      hnot)
  have hZ : originalSylowCentralizer n S e P ≤ Subgroup.center S := by
    apply (original_centralizer_inf_sylow_le_center_iff (n := n) hn (S := S) (e := e) (C := _)).mp
    rw [← original_center_product_inf_sylow n hn S e]
    exact inf_le_inf_right _ hle
  let : IsCyclic (Subgroup.center S) := original_Sylow_center_isCyclic n hn S e
  exact ⟨hle, hsolv, originalSylowInvolution_centralizes n S e P, hZ,
    Subgroup.isCyclic_of_le hZ⟩

theorem original_coverage_criterion_fullCenterQuotient
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e)) :
    let coverage := (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)
    (coverage ↔ ¬ originalPrimeCentralizer n S e P ≤
      centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) ∧
    (coverage ↔ ¬ Group.IsSolvable (originalPrimeCentralizer n S e P)) ∧
    ((centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) ≤
      Subgroup.normalizer (originalPrimeSubgroup n S e P : Set (involutionCentralizer n S e)) →
      (coverage ↔ ¬ originalSylowCentralizer n S e P ≤ Subgroup.center S) ∧
      (coverage ↔ (modelY S e).subgroupOf (S : Subgroup G) ≤ originalSylowCentralizer n S e P) ∧
      (coverage ↔ ¬ IsCyclic (originalSylowCentralizer n S e P))) ∧
    (¬ coverage →
      originalPrimeCentralizer n S e P ≤ centralizerOddCore n S e ⊔
        centralizerFullCenter n hn S e ∧
      Group.IsSolvable (originalPrimeCentralizer n S e P) ∧
      Subgroup.zpowers (originalSylowInvolution n S e) ≤ originalSylowCentralizer n S e P ∧
      originalSylowCentralizer n S e P ≤ Subgroup.center S ∧
      IsCyclic (originalSylowCentralizer n S e P)) := by
  dsimp only
  refine ⟨original_coverage_iff_noncentral hnonab (n := n) hn (S := S) (e := e)
      hfour hell hdiv (P := P),
    original_coverage_iff_not_solvable hnonab (n := n) hn (S := S) (e := e)
      hfour hell hdiv (P := P), ?_,
    original_failed_coverage_consequences hnonab n hn S e hfour hell hdiv P⟩
  intro hinvariant
  have h := original_invariant_coverage_equivalences hnonab n hn S e hfour hell hdiv P hinvariant
  have hcenter := original_centralizer_inf_sylow_le_center_iff (n := n) hn (S := S) (e := e)
    (C := originalPrimeCentralizer n S e P)
  exact ⟨h.2.2.trans (not_congr hcenter),
    h.1.trans (originalSylowCentralizer_quaternion_iff (n := n) hn (S := S) (e := e) (P := P)).symm,
    h.2.1.trans (not_congr
      (originalSylowCentralizer_isCyclic_iff
        (n := n) hn (S := S) (e := e) (P := P)).symm)⟩


omit [Finite G] in
theorem original_Sylow_invariance_iff
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    {ell : ℕ} {P : Sylow ell (centralizerOddCore n S e)} :
    (S : Subgroup G) ≤ Subgroup.normalizer (((originalPrimeSubgroup n S e P).map
      (involutionCentralizer n S e).subtype) : Set G) ↔
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) ≤
      Subgroup.normalizer (originalPrimeSubgroup n S e P : Set (involutionCentralizer n S e)) := by
  have hS : (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)).map
      (involutionCentralizer n S e).subtype = (S : Subgroup G) := by
    rw [centralizerSylow_coe, Subgroup.map_subgroupOf_eq_of_le
      (sylow_le_involutionCentralizer n hn S e)]
  rw [← hS, Subgroup.map_le_iff_le_comap,
    Subgroup.comap_normalizer_eq_of_le_range
      (Subgroup.map_le_range (involutionCentralizer n S e).subtype
        (originalPrimeSubgroup n S e P)),
    Subgroup.comap_map_eq_self_of_injective (involutionCentralizer n S e).subtype_injective]

theorem original_Sylow_centralizer_coverage_equivalent_to_noncentral_wreath_action_kernel
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e)) :
    let coverage := (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)
    (coverage ↔ ¬ originalPrimeCentralizer n S e P ≤
      centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) ∧
    (coverage ↔ ¬ Group.IsSolvable (originalPrimeCentralizer n S e P)) ∧
    ((S : Subgroup G) ≤ Subgroup.normalizer (((originalPrimeSubgroup n S e P).map
      (involutionCentralizer n S e).subtype) : Set G) →
      (coverage ↔ ¬ originalSylowCentralizer n S e P ≤ Subgroup.center S) ∧
      (coverage ↔ (modelY S e).subgroupOf (S : Subgroup G) ≤ originalSylowCentralizer n S e P) ∧
      (coverage ↔ ¬ IsCyclic (originalSylowCentralizer n S e P))) ∧
    (¬ coverage →
      originalPrimeCentralizer n S e P ≤ centralizerOddCore n S e ⊔
        centralizerFullCenter n hn S e ∧
      Group.IsSolvable (originalPrimeCentralizer n S e P) ∧
      Subgroup.zpowers (originalSylowInvolution n S e) ≤ originalSylowCentralizer n S e P ∧
      originalSylowCentralizer n S e P ≤ Subgroup.center S ∧
      IsCyclic (originalSylowCentralizer n S e P)) := by
  have hfull : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) := by
    intro h
    obtain ⟨E⟩ := h
    apply hfour
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e)).trans E⟩
  have h := original_coverage_criterion_fullCenterQuotient hnonab n hn S e hfull hell hdiv P
  exact ⟨h.1, h.2.1, fun hS => h.2.2.1
    ((original_Sylow_invariance_iff (n := n) hn (S := S) (e := e) (P := P)).mp hS), h.2.2.2⟩

theorem original_noncentral_Sylow_element_gives_coverage
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (v : S) (hv : v ∈ originalSylowCentralizer n S e P) (hvZ : v ∉ Subgroup.center S) :
    (originalPrimeCentralizer n S e P ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) := by
  by_contra hfailure
  have h := original_Sylow_centralizer_coverage_equivalent_to_noncentral_wreath_action_kernel
    hnonab n hn S e hfour hell hdiv P
  exact hvZ ((h.2.2.2 hfailure).2.2.2.1 hv)

end CFSG.Wreathed.OriginalSylowCentralizerCoverage
