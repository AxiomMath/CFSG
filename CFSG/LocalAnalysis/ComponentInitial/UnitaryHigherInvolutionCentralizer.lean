module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionPaired

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {p f : ℕ} {E : Type} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

abbrev unitaryOp (A : sesqUnitaryGroup B) : Module.End E V :=
  ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)

theorem mem_sesqNormOneScalars_commute {z : sesqUnitaryGroup B} (hz : z ∈ sesqNormOneScalars h B)
    (x : sesqUnitaryGroup B) : z * x = x * z := by
  obtain ⟨c, -, hc⟩ := hz
  refine Subtype.ext (Units.ext ?_)
  change unitaryOp z * unitaryOp x = unitaryOp x * unitaryOp z
  rw [unitaryOp, hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem sesqNormOneScalars_le_centralizer (A : sesqUnitaryGroup B) :
    sesqNormOneScalars h B ≤ Subgroup.centralizer {A} := fun _ hz =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_sesqNormOneScalars_commute hz A)

section Commutator

variable (A : sesqUnitaryGroup B)

noncomputable abbrev projCentralizerPreimage : Subgroup (sesqUnitaryGroup B) :=
  (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A}).comap
    (QuotientGroup.mk' (sesqNormOneScalars h B))

variable {A}

theorem commutator_mem_of_mem_preimage {g : sesqUnitaryGroup B}
    (hg : g ∈ projCentralizerPreimage A) : g * A * g⁻¹ * A⁻¹ ∈ sesqNormOneScalars h B := by
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hg)
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  change (QuotientGroup.mk' (sesqNormOneScalars h B) g) *
    (QuotientGroup.mk' (sesqNormOneScalars h B) A) *
      (QuotientGroup.mk' (sesqNormOneScalars h B) g)⁻¹ *
        (QuotientGroup.mk' (sesqNormOneScalars h B) A)⁻¹ = 1
  rw [h1]
  group

variable (A) in
@[expose] noncomputable def commutatorHom :
    projCentralizerPreimage A →* sesqUnitaryGroup B where
  toFun g := g * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹
  map_one' := by
    change (1 : sesqUnitaryGroup B) * A * 1⁻¹ * A⁻¹ = 1
    group
  map_mul' g g' := by
    obtain ⟨k', hk'⟩ : ∃ k' : sesqUnitaryGroup B,
        k' = (g' : sesqUnitaryGroup B) * A * (g' : sesqUnitaryGroup B)⁻¹ * A⁻¹ := ⟨_, rfl⟩
    have hk'mem : k' ∈ sesqNormOneScalars h B := by
      rw [hk']
      exact commutator_mem_of_mem_preimage g'.2
    have e1 : (g' : sesqUnitaryGroup B) * A * (g' : sesqUnitaryGroup B)⁻¹ = k' * A := by
      rw [hk']
      group
    change ((g : sesqUnitaryGroup B) * g') * A * ((g : sesqUnitaryGroup B) * g')⁻¹ * A⁻¹ =
      ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹) *
        ((g' : sesqUnitaryGroup B) * A * (g' : sesqUnitaryGroup B)⁻¹ * A⁻¹)
    rw [← hk', mul_inv_rev]
    calc (g : sesqUnitaryGroup B) * g' * A * ((g' : sesqUnitaryGroup B)⁻¹ *
          (g : sesqUnitaryGroup B)⁻¹) * A⁻¹ =
          (g : sesqUnitaryGroup B) * ((g' : sesqUnitaryGroup B) * A *
            (g' : sesqUnitaryGroup B)⁻¹) * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹ := by group
      _ = (g : sesqUnitaryGroup B) * k' * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹ := by
          rw [e1, ← mul_assoc]
      _ = k' * ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹) := by
          rw [← mem_sesqNormOneScalars_commute hk'mem]
          group
      _ = ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹) * k' :=
          mem_sesqNormOneScalars_commute hk'mem _

theorem commutatorHom_apply (g : projCentralizerPreimage A) :
    commutatorHom A g = g * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹ :=
  rfl

theorem centralizer_le_preimage :
    Subgroup.centralizer {A} ≤ projCentralizerPreimage A := fun g hg => by
  refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]

theorem ker_commutatorHom :
    (commutatorHom A).ker = (Subgroup.centralizer {A}).subgroupOf (projCentralizerPreimage A) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    commutatorHom_apply, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem card_range_commutatorHom_le [Nontrivial V] {l : E}
    (hl0 : l ≠ 0) (hAA : unitaryOp A * unitaryOp A = (l ^ 2) • 1) :
    Nat.card (commutatorHom A).range ≤ 2 := by
  classical
  have hval : ∀ g : projCentralizerPreimage A,
      unitaryOp (commutatorHom A g) = 1 ∨ unitaryOp (commutatorHom A g) = -1 := by
    intro g
    obtain ⟨c, -, hc⟩ := commutator_mem_of_mem_preimage g.2
    have hkA : unitaryOp ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹) =
        c • unitaryOp A := by
      have e : (g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹ =
          ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹) * A := by group
      rw [e]
      change unitaryOp ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹ * A⁻¹) *
        unitaryOp A = _
      rw [unitaryOp, hc, smul_mul_assoc, one_mul]
    have hsq : unitaryOp ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹) *
        unitaryOp ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹) =
          (l ^ 2) • 1 := by
      have e2 : ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹) *
          ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹) =
            (g : sesqUnitaryGroup B) * (A * A) * (g : sesqUnitaryGroup B)⁻¹ := by group
      change unitaryOp (((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹) *
        ((g : sesqUnitaryGroup B) * A * (g : sesqUnitaryGroup B)⁻¹)) = _
      rw [e2]
      change unitaryOp (g : sesqUnitaryGroup B) * (unitaryOp A * unitaryOp A) *
        unitaryOp (g : sesqUnitaryGroup B)⁻¹ = _
      rw [hAA, mul_smul_comm, mul_one, smul_mul_assoc]
      change (l ^ 2) • unitaryOp ((g : sesqUnitaryGroup B) * (g : sesqUnitaryGroup B)⁻¹) = _
      rw [mul_inv_cancel]
      rfl
    rw [hkA, smul_mul_smul_comm, hAA, smul_smul] at hsq
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl0
    have hc2 : c * c = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have h1 := congrArg (fun φ : Module.End E V => φ v) hsq
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h1
      have h3 : (c * c * l ^ 2 - l ^ 2) • v = 0 := by rw [sub_smul, h1, sub_self]
      have h4 := (smul_eq_zero.mp h3).resolve_right hv
      have h5 : (c * c - 1) * l ^ 2 = 0 := by linear_combination h4
      exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hl2)
    rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
    · left
      rw [commutatorHom_apply, unitaryOp, hc, one_smul]
    · right
      rw [commutatorHom_apply, unitaryOp, hc, neg_one_smul]
  have hinj : Function.Injective fun z : (commutatorHom A).range =>
      decide (unitaryOp (z : sesqUnitaryGroup B) = 1) := by
    rintro ⟨z, g, rfl⟩ ⟨z', g', rfl⟩ hzz
    have hz := hval g
    have hz' := hval g'
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change unitaryOp (commutatorHom A g) = unitaryOp (commutatorHom A g')
    simp only at hzz
    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
    · rw [hz, hz']
    · rw [hz, hz'] at hzz
      simp at hzz
      rw [hz, hz']
      exact hzz.symm
    · rw [hz, hz'] at hzz
      simp at hzz
      rw [hz, hz']
      exact hzz
    · rw [hz, hz']
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this

variable (A) in
@[expose] noncomputable def projCentralizerHom :
    projCentralizerPreimage A →*
      Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :=
  ((QuotientGroup.mk' (sesqNormOneScalars h B)).comp
    (projCentralizerPreimage A).subtype).codRestrict _ fun g => g.2

theorem projCentralizerHom_surjective : Function.Surjective (projCentralizerHom A) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars h B) x
  exact ⟨⟨y, hx⟩, rfl⟩

theorem map_centralizer_subgroupOf :
    ((Subgroup.centralizer {A}).map (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
        (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A}) =
      (commutatorHom A).ker.map (projCentralizerHom A) := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf, ker_commutatorHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, centralizer_le_preimage hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨g, Subgroup.mem_subgroupOf.mp hg, ?_⟩
    exact congrArg Subtype.val hgx

theorem image_centralizer_normal_index_le [Nontrivial V] {l : E} (hl0 : l ≠ 0)
    (hAA : unitaryOp A * unitaryOp A = (l ^ 2) • 1) :
    (((Subgroup.centralizer {A}).map (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
        (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A})).Normal ∧
    (((Subgroup.centralizer {A}).map (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
        (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A})).index ≤ 2 := by
  rw [map_centralizer_subgroupOf]
  refine ⟨Subgroup.Normal.map inferInstance _ projCentralizerHom_surjective, ?_⟩
  have hker : (projCentralizerHom A).ker ≤ (commutatorHom A).ker := by
    intro g hg
    rw [ker_commutatorHom, Subgroup.mem_subgroupOf]
    have h1 : (QuotientGroup.mk' (sesqNormOneScalars h B)) (g : sesqUnitaryGroup B) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    exact sesqNormOneScalars_le_centralizer A ((QuotientGroup.eq_one_iff _).mp h1)
  rw [← Subgroup.index_comap_of_surjective _ projCentralizerHom_surjective,
    Subgroup.comap_map_eq_self hker, Subgroup.index_ker]
  exact card_range_commutatorHom_le hl0 hAA

end Commutator

theorem projective_unitary_involution_centralizer_matrix_structure
    (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V] (hn : 2 ≤ finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2) :
    ∃ l : E, l ≠ 0 ∧ unitaryOp A * unitaryOp A = (l ^ 2) • 1 ∧
      (h.norm l = 1 ∨ h.norm l = -1) ∧
      eigenPlus l (unitaryOp A) ≠ ⊥ ∧ eigenMinus l (unitaryOp A) ≠ ⊥ ∧
      IsCompl (eigenPlus l (unitaryOp A)) (eigenMinus l (unitaryOp A)) ∧
      (h.norm l = 1 →
        (∀ v ∈ eigenPlus l (unitaryOp A), ∀ w ∈ eigenMinus l (unitaryOp A), B v w = 0) ∧
        (B.domRestrict₁₂ (eigenPlus l (unitaryOp A))
          (eigenPlus l (unitaryOp A))).SeparatingLeft ∧
        (B.domRestrict₁₂ (eigenMinus l (unitaryOp A))
          (eigenMinus l (unitaryOp A))).SeparatingLeft ∧
        ∃ e : Subgroup.centralizer {A} ≃*
            sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l (unitaryOp A))
              (eigenPlus l (unitaryOp A))) ×
            sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l (unitaryOp A))
              (eigenMinus l (unitaryOp A))),
          ∀ g : Subgroup.centralizer {A},
            (eigenPlus l (unitaryOp A)).subtype ∘ₗ
                (((e g).1 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) :
                  Module.End E (eigenPlus l (unitaryOp A))) =
              unitaryOp (g : sesqUnitaryGroup B) ∘ₗ (eigenPlus l (unitaryOp A)).subtype ∧
            (eigenMinus l (unitaryOp A)).subtype ∘ₗ
                (((e g).2 : LinearMap.GeneralLinearGroup E (eigenMinus l (unitaryOp A))) :
                  Module.End E (eigenMinus l (unitaryOp A))) =
              unitaryOp (g : sesqUnitaryGroup B) ∘ₗ (eigenMinus l (unitaryOp A)).subtype) ∧
      (h.norm l = -1 →
        (∀ v ∈ eigenPlus l (unitaryOp A), ∀ w ∈ eigenPlus l (unitaryOp A), B v w = 0) ∧
        (∀ v ∈ eigenMinus l (unitaryOp A), ∀ w ∈ eigenMinus l (unitaryOp A), B v w = 0) ∧
        finrank E (eigenPlus l (unitaryOp A)) = finrank E (eigenMinus l (unitaryOp A)) ∧
        2 * finrank E (eigenPlus l (unitaryOp A)) = finrank E V ∧
        (∀ v ∈ eigenPlus l (unitaryOp A),
          (∀ w ∈ eigenMinus l (unitaryOp A), B v w = 0) → v = 0) ∧
        (∀ w ∈ eigenMinus l (unitaryOp A),
          (∀ v ∈ eigenPlus l (unitaryOp A), B v w = 0) → w = 0) ∧
        ∃ e : Subgroup.centralizer {A} ≃*
            LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A)),
          (∀ g : Subgroup.centralizer {A},
            (eigenPlus l (unitaryOp A)).subtype ∘ₗ
                ((e g : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) :
                  Module.End E (eigenPlus l (unitaryOp A))) =
              unitaryOp (g : sesqUnitaryGroup B) ∘ₗ (eigenPlus l (unitaryOp A)).subtype) ∧
          (∀ (g : Subgroup.centralizer {A}) (w : V), w ∈ eigenMinus l (unitaryOp A) →
            ∀ w' ∈ eigenMinus l (unitaryOp A),
              ((∀ v ∈ eigenPlus l (unitaryOp A),
                B (unitaryOp (g : sesqUnitaryGroup B) v) w' = B v w) ↔
                w' = unitaryOp (g : sesqUnitaryGroup B) w)) ∧
          (∀ g : Subgroup.centralizer {A},
            (g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B ↔
              ∃ c : E, h.norm c = 1 ∧
                ((e g : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) :
                  Module.End E (eigenPlus l (unitaryOp A))) = c • 1)) ∧
      (Subgroup.centralizer {A}).map (QuotientGroup.mk' (sesqNormOneScalars h B)) ≤
        Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A} ∧
      (((Subgroup.centralizer {A}).map (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
        (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A})).Normal ∧
      (((Subgroup.centralizer {A}).map (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
        (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A})).index ≤ 2 ∧
      sesqNormOneScalars h B ≤ Subgroup.center (sesqUnitaryGroup B) ∧
      sesqNormOneScalars h B ≤ Subgroup.centralizer {A} ∧
      ∀ g ∈ Subgroup.centralizer {A},
        (QuotientGroup.mk' (sesqNormOneScalars h B)) g = 1 ↔ g ∈ sesqNormOneScalars h B := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨⟨l, hl0, hAA, hN⟩, hns⟩ := involution_lift_sq hp hBl hA
  have h2 := two_ne_zero_of_odd h hp
  obtain ⟨hP, hM⟩ := eigen_ne_bot h2 hl0 hAA hns
  obtain ⟨hnorm, hidx⟩ := image_centralizer_normal_index_le hl0 hAA
  refine ⟨l, hl0, hAA, hN, hP, hM, isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA),
    fun hN1 => exists_split_centralizer_equiv hp hB hBl hl0 hAA hN1,
    fun hN1 => exists_paired_centralizer_equiv hp hB hBl hl0 hAA hN1, ?_, hnorm, hidx,
    fun z hz => Subgroup.mem_center_iff.mpr fun x => (mem_sesqNormOneScalars_commute hz x).symm,
    sesqNormOneScalars_le_centralizer A, fun g _ => QuotientGroup.eq_one_iff g⟩
  rintro _ ⟨g, hg, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
