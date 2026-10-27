module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

open MulAction

@[expose] def equivariantSubgroup (P Ω : Type*) [Group P] [MulAction P Ω] :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.centralizer (Set.range (MulAction.toPermHom P Ω))

theorem mem_equivariantSubgroup {P Ω : Type*} [Group P] [MulAction P Ω]
    (c : Equiv.Perm Ω) : c ∈ equivariantSubgroup P Ω ↔
      ∀ (g : P) (x : Ω), c (g • x) = g • c x := by
  constructor
  · intro hc g x
    have h := Subgroup.mem_centralizer_iff.mp hc _ ⟨g, rfl⟩
    exact (Equiv.congr_fun h x).symm
  · intro hc
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨g, rfl⟩
    exact Equiv.ext (fun x => (hc g x).symm)

theorem equivariant_evaluation_injective {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω) :
    Function.Injective (fun c : equivariantSubgroup P Ω => c.val x) := by
  intro c d h
  change c.val x = d.val x at h
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P x y
  rw [(mem_equivariantSubgroup c.val).mp c.property,
    (mem_equivariantSubgroup d.val).mp d.property, h]

theorem equivariant_nonidentity_fixedPointFree {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (c : equivariantSubgroup P Ω) (hc : c ≠ 1) :
    ∀ x : Ω, c.val x ≠ x := by
  intro x h
  exact hc (equivariant_evaluation_injective x h)

@[expose] noncomputable def transitiveCosetEquiv (P Ω : Type*) [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω) :
    (P ⧸ MulAction.stabilizer P x) ≃ Ω :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer P x)
    ⟨MulAction.injective_ofQuotientStabilizer P x, fun y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x y
      exact ⟨g, hg⟩⟩

theorem transitiveCosetEquiv_mk {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω) (g : P) :
    transitiveCosetEquiv P Ω x (g : P ⧸ MulAction.stabilizer P x) = g • x := rfl

@[expose] noncomputable def equivariantRightHom (P Ω : Type*) [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω) :
    (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op →* Equiv.Perm Ω :=
  (transitiveCosetEquiv P Ω x).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom
      (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op
      (P ⧸ MulAction.stabilizer P x))

theorem equivariantRightHom_apply {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω)
    (a : (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op) (g : P) :
    equivariantRightHom P Ω x a (g • x) = (g * a.val.unop) • x := by
  rw [← transitiveCosetEquiv_mk x g]
  change (transitiveCosetEquiv P Ω x).permCongr
    (MulAction.toPermHom _ _ a) (transitiveCosetEquiv P Ω x g) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change transitiveCosetEquiv P Ω x ((g * a.val.unop : P) : P ⧸ _) = _
  exact transitiveCosetEquiv_mk x _

theorem equivariantRightHom_mem {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω)
    (a : (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op) :
    equivariantRightHom P Ω x a ∈ equivariantSubgroup P Ω := by
  apply (mem_equivariantSubgroup _).mpr
  intro g y
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq P x y
  rw [← mul_smul, equivariantRightHom_apply, equivariantRightHom_apply,
    ← mul_smul, mul_assoc]

@[expose] noncomputable def equivariantNormalizerHom (P Ω : Type*)
    [Group P] [MulAction P Ω] [MulAction.IsPretransitive P Ω] (x : Ω) :
    (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op →*
      equivariantSubgroup P Ω :=
  (equivariantRightHom P Ω x).codRestrict _ (equivariantRightHom_mem x)

theorem equivariantNormalizerHom_surjective {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω) :
    Function.Surjective (equivariantNormalizerHom P Ω x) := by
  intro c
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq P x (c.val x)
  have hstab : MulAction.stabilizer P (c.val x) = MulAction.stabilizer P x := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      ← (mem_equivariantSubgroup c.val).mp c.property g x]
    exact c.val.injective.eq_iff
  have hnormal : a ∈ Subgroup.normalizer (MulAction.stabilizer P x : Set P) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      (MulAction.stabilizer_smul_eq_stabilizer_map_conj a x).symm.trans
        (ha ▸ hstab)
  refine ⟨⟨MulOpposite.op a, hnormal⟩, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P x y
  change equivariantRightHom P Ω x _ (g • x) = c.val (g • x)
  rw [equivariantRightHom_apply]
  change (g * a) • x = c.val (g • x)
  rw [mul_smul, ha,
    (mem_equivariantSubgroup c.val).mp c.property]

theorem equivariantNormalizerHom_ker {P Ω : Type*} [Group P] [MulAction P Ω]
    [MulAction.IsPretransitive P Ω] (x : Ω) :
    (equivariantNormalizerHom P Ω x).ker =
      (MulAction.stabilizer P x).op.subgroupOf
        (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op := by
  ext a
  change equivariantNormalizerHom P Ω x a = 1 ↔
    a.val.unop ∈ MulAction.stabilizer P x
  rw [← (equivariant_evaluation_injective x).eq_iff]
  change equivariantRightHom P Ω x a x = x ↔ a.val.unop • x = x
  have happly := equivariantRightHom_apply x a 1
  simp only [one_smul, one_mul] at happly
  rw [happly]

theorem transitive_equivariant_card {P Ω : Type*} [Group P] [Finite P]
    [MulAction P Ω] [MulAction.IsPretransitive P Ω] (x : Ω) :
    Nat.card (equivariantSubgroup P Ω) =
      (MulAction.stabilizer P x).relIndex
        (Subgroup.normalizer (MulAction.stabilizer P x : Set P)) := by
  let H := MulAction.stabilizer P x
  let N := Subgroup.normalizer (H : Set P)
  let f := equivariantNormalizerHom P Ω x
  let : Finite N.op := Finite.of_equiv N N.equivOp
  let : Finite f.ker := inferInstance
  have hkerCard : Nat.card f.ker = Nat.card H := by
    rw [equivariantNormalizerHom_ker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.op_le_op_iff.mpr H.le_normalizer)).toEquiv).trans
        (Nat.card_congr H.equivOp).symm
  have hnormalizerCard : Nat.card N.op = Nat.card N :=
    (Nat.card_congr N.equivOp).symm
  have hsubgroupCard : Nat.card (H.subgroupOf N) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.le_normalizer).toEquiv
  calc
    Nat.card (equivariantSubgroup P Ω) = Nat.card (N.op ⧸ f.ker) :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
        (equivariantNormalizerHom_surjective x)).toEquiv).symm
    _ = Nat.card N.op / Nat.card f.ker := f.ker.index_eq_card_div
    _ = Nat.card N / Nat.card H := by rw [hnormalizerCard, hkerCard]
    _ = H.relIndex N := by
      change _ = (H.subgroupOf N).index
      rw [Subgroup.index_eq_card_div, hsubgroupCard]

theorem transitive_equivariant_isPGroup {P Ω : Type*} [Group P] [Finite P]
    [MulAction P Ω] [MulAction.IsPretransitive P Ω] (p : ℕ) [Fact p.Prime]
    (hP : IsPGroup p P) (x : Ω) : IsPGroup p (equivariantSubgroup P Ω) := by
  have hop := hP.of_equiv (MulEquiv.inv' P)
  exact (hop.to_subgroup _).of_surjective (equivariantNormalizerHom P Ω x)
    (equivariantNormalizerHom_surjective x)

theorem transitive_equivariant_nontrivial {P Ω : Type*} [Group P] [Finite P]
    [MulAction P Ω] [MulAction.IsPretransitive P Ω] [Nontrivial Ω]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P) (x : Ω) :
    Nontrivial (equivariantSubgroup P Ω) := by
  let : Group.IsNilpotent P := hP.isNilpotent
  have hproper : MulAction.stabilizer P x < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x y
    have hx : g • x = x := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [htop]
      trivial
    exact hy (hg.symm.trans hx)
  have hlt := Group.normalizerCondition_of_isNilpotent
    (MulAction.stabilizer P x) hproper
  obtain ⟨a, ha, hnot⟩ := IsConcreteLE.exists_of_lt hlt
  let b : (Subgroup.normalizer (MulAction.stabilizer P x : Set P)).op :=
    ⟨MulOpposite.op a, ha⟩
  apply nontrivial_of_ne (equivariantNormalizerHom P Ω x b) 1
  intro heq
  have h := congrArg (fun c : equivariantSubgroup P Ω => c.val x) heq
  change equivariantRightHom P Ω x b x = x at h
  have hmove : a • x = x := by
    have happly := equivariantRightHom_apply x b 1
    simp only [one_smul, one_mul] at happly
    exact happly.symm.trans h
  exact hnot (MulAction.mem_stabilizer_iff.mpr hmove)

end CFSG.ComponentClassification.CatalogueBAlternating
