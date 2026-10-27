module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalDescent
public import CFSG.LieType.Chevalley.OddDiagramDerivedFieldFixedComponents
public import CFSG.LieType.Chevalley.E6SignedGraphQuasisimple

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

abbrev frobFixedCentralizer (τ : Tag) {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (e : ℕ) (A Q : ModGL τ k) : Subgroup (ModGL τ k) :=
  graphCentralizer τ k A ⊓ (frobTwistGL τ k p e Q).eqLocus (MonoidHom.id _)

theorem frobFixedCentralizer_zero_eq
    {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] {p : ℕ}
    [Fact p.Prime] [CharP k p] {e : ℕ} (Q : ModGL τ k) {A : ModGL τ k}
    {AK : ModGL τ (fixSubfield (iterateFrobeniusEquiv k p e))}
    (hAK : CFSG.LieType.Chevalley.baseChangeGL
      (fixSubfield (iterateFrobeniusEquiv k p e)).subtype AK = A) :
    frobFixedCentralizer τ p e A (Q ^ 0) = rationalFixedGroup (iterateFrobeniusEquiv k p e) AK := by
  subst hAK
  ext g
  refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
  change frobTwistGL τ k p e (Q ^ 0) g = g ↔
    Units.map (entrywiseHom (iterateFrobeniusEquiv k p e).toRingHom) g = g
  rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one, iterateFrobeniusEquiv_toRingHom]

theorem finite_rationalFixedGroup
    {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K)
    [Finite (fixSubfield σ)] (A : ModGL τ (fixSubfield σ)) : Finite (rationalFixedGroup σ A) := by
  classical
  have hentry : ∀ (g : rationalFixedGroup σ A) (a b : Label τ),
      σ (((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a) =
        ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a := by
    intro g a b
    have hF : Units.map (entrywiseHom σ.toRingHom) (g : ModGL τ K) = g :=
      (Subgroup.mem_inf.1 g.2).2
    have hcoord := congrArg (fun B : ModGL τ K =>
      (B : Module.End K (RootModule τ K)) (Finsupp.single b 1) a) hF
    simp only [Units.coe_map] at hcoord
    change entrywise σ.toRingHom _ (Finsupp.single b 1) a = _ at hcoord
    rw [entrywise_single, Finsupp.mapRange_apply] at hcoord
    exact hcoord
  refine Finite.of_injective (fun (g : rationalFixedGroup σ A) (a b : Label τ) =>
    (⟨_, hentry g a b⟩ : fixSubfield σ)) fun g g' hgg' => Subtype.ext (Units.ext ?_)
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  exact congrArg Subtype.val (congrFun (congrFun hgg' a) b)

section Components

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem isQuasisimple_rationalRootGroup_diagram
    [Finite (fixSubfield σ)]
    (hK : ringChar (fixSubfield σ) ≠ 2) :
    CFSG.IsQuasisimple (rationalRootGroup σ (diagramMap TwistTag.E6 (fixSubfield σ))) := by
  have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 (fixSubfield σ))) ⊔
        (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓ graphCentralizer TwistTag.E6.tag
          (fixSubfield σ) (diagramMap TwistTag.E6 (fixSubfield σ))) =
      graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
    rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
      twistedFixedGroup_id_eq]
  obtain ⟨hsimple, hnc, -⟩ :=
    odd_diagram_field_fixed_p_components TwistTag.E6 (fixSubfield σ) hK (RingEquiv.refl _)
  rw [RingEquiv.toRingHom_refl'] at hsimple hnc
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  rw [rationalRootGroup, hinner]
  exact (isQuasisimple_congr (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _))).1 hq

open E6SignedGraph in
theorem isQuasisimple_rationalRootGroup_signed
    (hK : ringChar (fixSubfield σ) ≠ 2) :
    CFSG.IsQuasisimple (rationalRootGroup σ (rootDiagUnit TwistTag.E6.tag
      (signTuple (fixSubfield σ)) * diagramMap TwistTag.E6 (fixSubfield σ))) := by
  have hinner : rootGenerated (fixSubfield σ) =
      (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓ graphCentralizer TwistTag.E6.tag
        (fixSubfield σ) (rootDiagUnit TwistTag.E6.tag (signTuple (fixSubfield σ)) *
          diagramMap TwistTag.E6 (fixSubfield σ))) ⊔
        (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓ graphCentralizer TwistTag.E6.tag
          (fixSubfield σ) (rootDiagUnit TwistTag.E6.tag (signTuple (fixSubfield σ)) *
            diagramMap TwistTag.E6 (fixSubfield σ))) :=
    rfl
  have hq := (E6_signed_graph_fixed_root_group_quasisimple (fixSubfield σ) hK).2.2.1
  rw [hinner] at hq
  exact (isQuasisimple_congr (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _))).1 hq

variable (c : Fin TwistTag.E6.tag.rank → (fixSubfield σ)ˣ)

theorem rationalFixedGroup_components
    [Finite (fixSubfield σ)]
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))
    (hJ : (rationalFixedGroup σ AK : Set (ModGL TwistTag.E6.tag K)) ⊆
      (rationalFixedTorus σ AK : Set (ModGL TwistTag.E6.tag K)) *
        (rationalRootGroup σ AK : Set (ModGL TwistTag.E6.tag K)))
    (hS : CFSG.IsQuasisimple (rationalRootGroup σ AK)) :
    Finite (rationalFixedGroup σ AK) ∧
    ((rationalRootGroup σ AK).subgroupOf (rationalFixedGroup σ AK)).Normal ∧
    (∀ x ∈ rationalFixedGroup σ AK, ∀ y ∈ rationalFixedGroup σ AK,
      x * y * x⁻¹ * y⁻¹ ∈ rationalRootGroup σ AK) ∧
    ∀ r : ℕ, r.Prime → ∀ L : Subgroup (rationalFixedGroup σ AK), CFSG.IsPComponent r L →
      CFSG.IsQuasisimple L := by
  subst hAK
  have hfin := finite_rationalFixedGroup σ
    (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))
  have hnormal := rationalRootGroup_normal σ c hJ
  have hcomm : ∀ x ∈ rationalFixedGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)),
      ∀ y ∈ rationalFixedGroup σ
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)),
      x * y * x⁻¹ * y⁻¹ ∈ rationalRootGroup σ
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :=
    fun x hx y hy => commutator_mem_rationalRootGroup σ c hJ hx hy
  refine ⟨hfin, hnormal, hcomm, fun r hr L hL => ?_⟩
  have hNq := (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe
    (rationalRootGroup_le σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))))).2 hS
  have : Group.IsSolvable (rationalFixedGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) ⧸
        (rationalRootGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))).subgroupOf
          (rationalFixedGroup σ
            (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)))) :=
    Group.isSolvable_of_comm fun a b => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h : (((x * y)⁻¹ * (y * x) : rationalFixedGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))) :
            ModGL TwistTag.E6.tag K) =
          (y : ModGL TwistTag.E6.tag K)⁻¹ * (x : ModGL TwistTag.E6.tag K)⁻¹ *
            (y : ModGL TwistTag.E6.tag K)⁻¹⁻¹ * (x : ModGL TwistTag.E6.tag K)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
      rw [h]
      exact hcomm _ (inv_mem y.2) _ (inv_mem x.2)
  exact (pComponent_eq_of_quasisimple_normal r hr _ hNq L hL).2

end Components

section Twisted

variable {k : Type} [Field k]

theorem diagramMap_conj_eq_of_mem {c : Fin TwistTag.E6.tag.rank → kˣ} {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ graphCentralizer TwistTag.E6.tag k
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k)) :
    diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹ =
      (rootDiagUnit TwistTag.E6.tag c)⁻¹ * x * rootDiagUnit TwistTag.E6.tag c := by
  have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
  calc diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹ =
      (rootDiagUnit TwistTag.E6.tag c)⁻¹ *
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k * x) *
          (diagramMap TwistTag.E6 k)⁻¹ := by group
    _ = (rootDiagUnit TwistTag.E6.tag c)⁻¹ *
        (x * (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k)) *
          (diagramMap TwistTag.E6 k)⁻¹ := by rw [← h]
    _ = _ := by group

variable {p : ℕ} [Fact p.Prime] [CharP k p]

theorem frobFixedCentralizer_diagram_one_eq (e : ℕ) :
    frobFixedCentralizer TwistTag.E6.tag p e (diagramMap TwistTag.E6 k)
        (diagramMap TwistTag.E6 k ^ 1) =
      frobFixedCentralizer TwistTag.E6.tag p e (diagramMap TwistTag.E6 k)
        (diagramMap TwistTag.E6 k ^ 0) := by
  ext x
  refine Subgroup.mem_inf.trans ((and_congr_right fun hxZ => ?_).trans Subgroup.mem_inf.symm)
  change frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 1) x = x ↔
    frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 0) x = x
  have hxc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hxZ).2
  have hFrP : entrywiseFrobGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) =
      diagramMap TwistTag.E6 k :=
    units_map_entrywiseHom_diagramMap _
  have hFx : diagramMap TwistTag.E6 k * entrywiseFrobGL TwistTag.E6.tag k p e x *
      (diagramMap TwistTag.E6 k)⁻¹ = entrywiseFrobGL TwistTag.E6.tag k p e x := by
    rw [mul_inv_eq_iff_eq_mul]
    calc diagramMap TwistTag.E6 k * entrywiseFrobGL TwistTag.E6.tag k p e x =
        entrywiseFrobGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k * x) := by
          rw [map_mul, hFrP]
      _ = entrywiseFrobGL TwistTag.E6.tag k p e (x * diagramMap TwistTag.E6 k) := by rw [hxc]
      _ = _ := by rw [map_mul, hFrP]
  rw [frobTwistGL_apply, frobTwistGL_apply, pow_one, pow_zero, one_mul, inv_one, mul_one, hFx]

variable [IsAlgClosed k]

open E6SignedGraph in
theorem exists_map_conj_frobFixedCentralizer_signed
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) :
    ∃ v ∈ graphCentralizer TwistTag.E6.tag k
        (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k),
      (frobFixedCentralizer TwistTag.E6.tag p e
          (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k)
          (diagramMap TwistTag.E6 k ^ 1)).map (MulAut.conj v).toMonoidHom =
        frobFixedCentralizer TwistTag.E6.tag p e
          (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k)
          (diagramMap TwistTag.E6 k ^ 0) := by
  have hTle : torusGroup TwistTag.E6.tag k ≤ adjointGroup TwistTag.E6.tag k :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  have hDZ : rootDiagUnit TwistTag.E6.tag (signTuple k) ∈ graphCentralizer TwistTag.E6.tag k
      (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) := by
    refine Subgroup.mem_inf.2 ⟨hTle rootDiagUnit_signTuple_mem_torusGroup, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (rootDiagUnit_commute_iff (signTuple k) (signTuple k)).2 (signTuple_perm_symm k)
  obtain ⟨-, hLang⟩ := E6_geometric_graph_centralizers_connected_Lang p hp k
    (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) (Or.inr rfl)
  obtain ⟨-, -, -, hL⟩ := hLang e he 0
  obtain ⟨v, hvZ, hv⟩ := hL _ (inv_mem hDZ)
  rw [pow_zero, one_mul, inv_one, mul_one, inv_mul_eq_iff_eq_mul] at hv
  have hFZ : ∀ {x}, x ∈ graphCentralizer TwistTag.E6.tag k
      (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) →
        entrywiseFrobGL TwistTag.E6.tag k p e x ∈ graphCentralizer TwistTag.E6.tag k
          (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) :=
    fun {x} hx => by
      have h1 := frobTwistGL_diagramMap_pow_mem p (signTuple_eq_one_or k)
        (signTuple_perm_symm k) e 0 hx
      rwa [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one] at h1
  have hkey : ∀ x ∈ graphCentralizer TwistTag.E6.tag k
      (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k),
      entrywiseFrobGL TwistTag.E6.tag k p e (v * x * v⁻¹) =
        v * frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 1) x * v⁻¹ := by
    intro x hx
    rw [map_mul, map_mul, map_inv, hv, frobTwistGL_apply, pow_one,
      diagramMap_conj_eq_of_mem (hFZ hx)]
    group
  have hF0 : ∀ y, frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 0) y =
      entrywiseFrobGL TwistTag.E6.tag k p e y := fun y => by
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one]
  refine ⟨v, hvZ, le_antisymm ?_ fun y hy => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxZ, hxF⟩ := Subgroup.mem_inf.1 hx
    have hxF' : frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 1) x = x := hxF
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hvZ hxZ) (inv_mem hvZ), ?_⟩
    change frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 0) (v * x * v⁻¹) =
      v * x * v⁻¹
    rw [hF0, hkey x hxZ, hxF']
  · obtain ⟨hyZ, hyF⟩ := Subgroup.mem_inf.1 hy
    have hyF' : frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 0) y = y := hyF
    rw [hF0] at hyF'
    have hxZ : v⁻¹ * y * v ∈ graphCentralizer TwistTag.E6.tag k
        (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) :=
      mul_mem (mul_mem (inv_mem hvZ) hyZ) hvZ
    refine ⟨v⁻¹ * y * v, Subgroup.mem_inf.2 ⟨hxZ, ?_⟩, ?_⟩
    · change frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 1) (v⁻¹ * y * v) =
        v⁻¹ * y * v
      have h1 := hkey _ hxZ
      rw [show v * (v⁻¹ * y * v) * v⁻¹ = y by group, hyF'] at h1
      calc frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 1) (v⁻¹ * y * v) =
          v⁻¹ * (v * frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ 1)
            (v⁻¹ * y * v) * v⁻¹) * v := by group
        _ = v⁻¹ * y * v := by rw [← h1]
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end Twisted

open E6SignedGraph in
theorem E6_canonical_graph_centralizer_rational_fixed_components
    (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (A : ModGL TwistTag.E6.tag k)
    (AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e)))
    (hA : (A = diagramMap TwistTag.E6 k ∧ AK = diagramMap TwistTag.E6 _) ∨
      (A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k ∧
        AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _)) :
    (∀ c : k, c ∈ fixSubfield (iterateFrobeniusEquiv k p e) ↔ c ^ p ^ e = c) ∧
    (∀ ε ∈ ({0, 1} : Set ℕ),
      Finite (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ ε)) ∧
      ∀ r : ℕ, r.Prime → ∀ L : Subgroup
        (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ ε)),
          CFSG.IsPComponent r L → CFSG.IsQuasisimple L) ∧
    rationalRootGroup (iterateFrobeniusEquiv k p e) AK ≤
      frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0) ∧
    ((rationalRootGroup (iterateFrobeniusEquiv k p e) AK).subgroupOf
      (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0))).Normal ∧
    (∀ [((rationalRootGroup (iterateFrobeniusEquiv k p e) AK).subgroupOf
        (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0))).Normal],
      ∀ a b : ↥(frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)) ⧸
        (rationalRootGroup (iterateFrobeniusEquiv k p e) AK).subgroupOf
          (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)),
        a * b = b * a) ∧
    CFSG.IsQuasisimple (rationalRootGroup (iterateFrobeniusEquiv k p e) AK) ∧
    (A = diagramMap TwistTag.E6 k →
      frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 1) =
        frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)) ∧
    (A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k →
      ∃ v ∈ graphCentralizer TwistTag.E6.tag k A,
        (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 1)).map
            (MulAut.conj v).toMonoidHom =
          frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)) := by
  classical
  have hmem : ∀ c : k, c ∈ fixSubfield (iterateFrobeniusEquiv k p e) ↔ c ^ p ^ e = c :=
    fun _ => Iff.rfl
  have hKfin : Finite (fixSubfield (iterateFrobeniusEquiv k p e)) := by
    have hq1 : 1 < p ^ e := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
    have hP0 : (Polynomial.X ^ (p ^ e) - Polynomial.X : Polynomial k) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k hq1
    refine Set.Finite.to_subtype ((Polynomial.finite_setOfPred_isRoot hP0).subset fun c hc => ?_)
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
    exact (hmem c).1 hc
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have hK2 := ringChar_fixSubfield_ne_two hk (iterateFrobeniusEquiv k p e)
  have hAK : CFSG.LieType.Chevalley.baseChangeGL
      (fixSubfield (iterateFrobeniusEquiv k p e)).subtype AK = A := by
    rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact baseChangeGL_diagramMap _ TwistTag.E6
    · rw [baseChangeGL_rootDiagUnit_mul_diagramMap, units_map_signTuple]
  have hJ0 := frobFixedCentralizer_zero_eq (diagramMap TwistTag.E6 k) hAK
  obtain ⟨c, hc, hsub, hSq⟩ : ∃ c : Fin TwistTag.E6.tag.rank →
      (fixSubfield (iterateFrobeniusEquiv k p e))ˣ,
      AK = rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 _ ∧
      (rationalFixedGroup (iterateFrobeniusEquiv k p e) AK : Set (ModGL TwistTag.E6.tag k)) ⊆
        (rationalFixedTorus (iterateFrobeniusEquiv k p e) AK : Set (ModGL TwistTag.E6.tag k)) *
          (rationalRootGroup (iterateFrobeniusEquiv k p e) AK : Set (ModGL TwistTag.E6.tag k)) ∧
      CFSG.IsQuasisimple (rationalRootGroup (iterateFrobeniusEquiv k p e) AK) := by
    rcases hA with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · refine ⟨1, by rw [rootDiagUnit_one, one_mul], ?_,
        isQuasisimple_rationalRootGroup_diagram _ hK2⟩
      have h := rationalFixedGroup_subset_diagram (k := k) (p := p) e
      rwa [rootDiagUnit_one, one_mul] at h
    · exact ⟨_, rfl, rationalFixedGroup_subset_signed e hp,
        isQuasisimple_rationalRootGroup_signed _ hK2⟩
  obtain ⟨hfin0, hnormal0, hcomm0, hcomp0⟩ :=
    rationalFixedGroup_components (iterateFrobeniusEquiv k p e) c hc hsub hSq
  have hP : A = diagramMap TwistTag.E6 k →
      frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 1) =
        frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0) := by
    rintro rfl
    exact frobFixedCentralizer_diagram_one_eq e
  have hD : A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k →
      ∃ v ∈ graphCentralizer TwistTag.E6.tag k A,
        (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 1)).map
            (MulAut.conj v).toMonoidHom =
          frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0) := by
    rintro rfl
    exact exists_map_conj_frobFixedCentralizer_signed hp he
  have hiso : Nonempty
      (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 1) ≃*
        frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)) := by
    rcases hA with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact ⟨MulEquiv.subgroupCongr (hP hA)⟩
    · obtain ⟨v, -, hv⟩ := hD hA
      exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj v).injective).trans
        (MulEquiv.subgroupCongr hv)⟩
  obtain ⟨φ⟩ := hiso
  have hfinJ : Finite
      (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)) := by
    rw [hJ0]
    exact hfin0
  have hcompJ : ∀ r : ℕ, r.Prime → ∀ L : Subgroup
      (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 0)),
        CFSG.IsPComponent r L → CFSG.IsQuasisimple L := by
    rw [hJ0]
    exact hcomp0
  refine ⟨hmem, fun ε hε => ?_, ?_, ?_, ?_, hSq, hP, hD⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hε
    rcases hε with rfl | rfl
    · exact ⟨hfinJ, hcompJ⟩
    · have : Finite
          (frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ 1)) :=
        Finite.of_equiv _ φ.symm.toEquiv
      exact ⟨this, fun r hr L hL => pComponents_quasisimple_of_mulEquiv hr φ (hcompJ r hr) L hL⟩
  · rw [hJ0]
    exact rationalRootGroup_le _ _
  · rw [hJ0]
    exact hnormal0
  · rw [hJ0]
    intro _ a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h : (((x * y)⁻¹ * (y * x) : rationalFixedGroup (iterateFrobeniusEquiv k p e) AK) :
        ModGL TwistTag.E6.tag k) =
        (y : ModGL TwistTag.E6.tag k)⁻¹ * (x : ModGL TwistTag.E6.tag k)⁻¹ *
          (y : ModGL TwistTag.E6.tag k)⁻¹⁻¹ * (x : ModGL TwistTag.E6.tag k)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
    rw [h]
    exact hcomm0 _ (inv_mem y.2) _ (inv_mem x.2)

end CFSG.LieType.AlgebraicGroups
