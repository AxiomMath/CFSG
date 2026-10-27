module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ConjU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TypeL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Center

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut UnitaryConj
open scoped commutatorElement

theorem eq_one_or_eq_neg_one_of_end {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) (hV : Module.finrank E V = 2) {T : Module.End E V}
    (hdet : LinearMap.det T = 1) (hT : T * T = 1) : T = 1 ∨ T = -1 := by
  classical
  have : FiniteDimensional E V := Module.finite_of_finrank_eq_succ hV
  let b := Module.finBasisOfFinrankEq E V hV
  set φ := LinearMap.toMatrixAlgEquiv b with hφ
  have hd : (φ T).det = 1 := by
    have : φ T = LinearMap.toMatrix b b T := rfl
    rw [this, LinearMap.det_toMatrix, hdet]
  have hsq : φ T * φ T = 1 := by rw [← map_mul, hT, map_one]
  rcases eq_one_or_eq_neg_one_of_mul_self h2 _ hd hsq with h1 | h1
  · left
    apply φ.injective
    rw [h1, map_one]
  · right
    apply φ.injective
    rw [h1, map_neg, map_one]

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem sq_eq_neg_one_of_comm_orderOf_U4 (hp2 : p ≠ 2)
    {u v : StatedProj (StatedSU 4 (p ^ f) K)} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1) (hv : orderOf v = s)
    (huv : u * v = v * u) (X : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hX : (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) = u) :
    ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = -1 := by
  have := Fact.mk hs
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective v
  have hinj := projSUToProjU_injective h 4 (by norm_num)
  have hXo : orderOf (toProjU h 4 X) = 2 := by
    rw [show toProjU h 4 X = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk X) from rfl,
      orderOf_injective _ hinj, hX]
    exact orderOf_eq_prime hu2 hu1
  have hgo : orderOf (toProjU h 4 g) = s := by
    rw [show toProjU h 4 g = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk g) from rfl,
      orderOf_injective _ hinj, hg, hv]
  have hcomm : toProjU h 4 g * toProjU h 4 X = toProjU h 4 X * toProjU h 4 g := by
    rw [show toProjU h 4 g = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk g) from rfl,
      show toProjU h 4 X = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk X) from rfl,
      ← map_mul, ← map_mul, hg, hX, huv]
  obtain ⟨l, -, hAA, -, hl2, -⟩ := unitary_four_core h hp2 X g hXo hs hs2 hsq hgo hcomm
  rw [hl2] at hAA
  refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
  have h1 := congrArg (fun T : Module.End K (Fin 4 → K) => T w) hAA
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
  rw [toSesq_apply, toSesq_apply, Matrix.mulVec_mulVec] at h1
  rw [Matrix.toLin'_apply, h1, Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec,
    neg_one_smul]

include h in
theorem exists_conj_of_sq_eq_neg_one_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (X Y : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = -1)
    (hY : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Y : GL (Fin 4) K) = -1) :
    ∃ w : StatedProj (StatedSU 4 (p ^ f) K),
      w * QuotientGroup.mk X * w⁻¹ = QuotientGroup.mk Y := by
  obtain ⟨g, hg⟩ := exists_conj_unitary h hp2 hq X Y hX hY
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg,
    mul_inv_cancel_right]

include h in
theorem sq_neg_one_structure (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (A : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hA : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : GL (Fin 4) K) = -1) :
    ∃ V : Submodule K (Fin 4 → K), Module.finrank K V = 2 ∧
      ∃ eC : Subgroup.centralizer {toSesq h 4 A} ≃* LinearMap.GeneralLinearGroup K V,
        ∀ x : Subgroup.centralizer {toSesq h 4 A},
          V.subtype ∘ₗ ((eC x : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
            unitaryOp (x : sesqUnitaryGroup (stdHermForm h 4)) ∘ₗ V.subtype := by
  classical
  set B := stdHermForm h 4 with hB
  set Asq := toSesq h 4 A with hAdef
  set M := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  have hAv : ∀ v, unitaryOp Asq v = M *ᵥ v := fun v => toSesq_apply h 4 A v
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hAA : unitaryOp Asq * unitaryOp Asq = -1 := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hAv, hAv, Matrix.mulVec_mulVec, hA, LinearMap.neg_apply,
      Module.End.one_apply, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hA2 : orderOf (QuotientGroup.mk Asq : sesqProjUnitary h B) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine ⟨-1, ?_, ?_⟩
      · rw [UnitaryFieldData.norm, map_neg, map_one]
        ring
      · change (((Asq ^ 2 : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :
          Module.End K (Fin 4 → K)) = _
        rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, pow_two]
        change unitaryOp Asq * unitaryOp Asq = _
        rw [hAA]
        ext v
        simp
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨c, hc, hAc⟩ := h1
      have hAc' : unitaryOp Asq = c • 1 := hAc
      have hc2 : c ^ 2 = -1 := by
        have h3 := hAA
        rw [hAc', smul_mul_smul_comm, one_mul, ← sq] at h3
        have h4 := congrArg (fun T : Module.End K (Fin 4 → K) => T (Pi.single 0 1) 0) h3
        simpa using h4
      rw [norm_eq_neg_one_of_sq h hq hc2] at hc
      apply h2K
      linear_combination -hc
  obtain ⟨l', hl'0, hAA', hN, -, -, hcompl, -, hpair, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2
      (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
      (stdHermForm_separatingLeft h 4) hA2
  have hl'2 : l' ^ 2 = -1 := by
    rw [hAA] at hAA'
    have h4 := congrArg (fun T : Module.End K (Fin 4 → K) => T (Pi.single 0 1) 0) hAA'
    simp at h4
    linear_combination -h4
  obtain ⟨-, -, hdeq, h2d, -, -, eC, heC, -, -⟩ := hpair (norm_eq_neg_one_of_sq h hq hl'2)
  rw [Module.finrank_fin_fun] at h2d
  exact ⟨_, by omega, eC, heC⟩

include h in
theorem scalar_eq_one_or_neg_one_U4 (hq : p ^ f % 4 = 1) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) K) : c = 1 ∨ c = -1 := by
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨h4, hq1⟩ := (scalar_mem_statedSU_iff h.prime hK (by norm_num) c).1 hc
  have h2 : c ^ 2 = 1 := by
    obtain ⟨t, ht⟩ : ∃ t, p ^ f + 1 = 4 * t + 2 := ⟨(p ^ f + 1) / 4, by omega⟩
    rw [ht, pow_add, pow_mul, h4, one_pow, one_mul] at hq1
    exact hq1
  have h3 : (c : K) * c = 1 := by rw [← Units.val_mul, ← sq, h2, Units.val_one]
  rcases mul_self_eq_one_iff.1 h3 with h5 | h5
  · left
    exact Units.ext h5
  · right
    exact Units.ext (by rw [h5, Units.val_neg, Units.val_one])

include h in
theorem exists_lift_sq_eq_neg_one_of_perfect_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (k : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hk : ((k : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (k : GL (Fin 4) K) = -1)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJ' : J' ≤ Subgroup.centralizer {(QuotientGroup.mk k : StatedProj (StatedSU 4 (p ^ f) K))})
    (hJp : ⁅J', J'⁆ = J') {z : StatedProj (StatedSU 4 (p ^ f) K)} (hz : z ∈ J')
    (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ X : ClassicalGroups.UnitaryFlag.unitarySU p f K 4, QuotientGroup.mk X = z ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = -1 := by
  classical
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set Z := (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) with hZ
  set π : ClassicalGroups.UnitaryFlag.unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' Z with hπ
  set kG : GL (Fin 4) K := (k : GL (Fin 4) K) with hkG
  obtain ⟨V, hdP, eC, heC⟩ := sq_neg_one_structure h hp2 hq k hk
  set C' : Subgroup (ClassicalGroups.UnitaryFlag.unitarySU p f K 4) :=
    Subgroup.centralizer {k} with hC'
  have hscal : StatedScalars (Fin 4) K ≤ Subgroup.center (GL (Fin 4) K) := by
    rw [StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar]
  have hcen : ∀ X : ClassicalGroups.UnitaryFlag.unitarySU p f K 4,
      π X ∈ Subgroup.centralizer {π k} →
      (X : GL (Fin 4) K) * kG * (X : GL (Fin 4) K)⁻¹ * kG⁻¹ ∈ StatedScalars (Fin 4) K := by
    intro X hX
    rw [Subgroup.mem_centralizer_singleton_iff] at hX
    have h1 : π (X * k * X⁻¹ * k⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hX]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  set φ : C' →* StatedProj (StatedSU 4 (p ^ f) K) := π.comp C'.subtype with hφ
  have hcomm_le : ⁅Subgroup.centralizer {π k}, Subgroup.centralizer {π k}⁆ ≤
      (⊤ : Subgroup C').map φ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨X, rfl⟩ := QuotientGroup.mk'_surjective Z u
    obtain ⟨Y, rfl⟩ := QuotientGroup.mk'_surjective Z v
    have hXY : ⁅X, Y⁆ ∈ C' := by
      rw [hC', Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hcoe : ((⁅X, Y⁆ : ClassicalGroups.UnitaryFlag.unitarySU p f K 4) : GL (Fin 4) K) =
          ⁅(X : GL (Fin 4) K), (Y : GL (Fin 4) K)⁆ :=
        map_commutatorElement (ClassicalGroups.UnitaryFlag.unitarySU p f K 4).subtype X Y
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
      exact commutator_comm_of_comm_mod hscal (hcen X hu) (hcen Y hv)
    refine ⟨⟨⁅X, Y⁆, hXY⟩, Subgroup.mem_top _, ?_⟩
    rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    change π ⁅X, Y⁆ = _
    rw [map_commutatorElement]
  have hJ'C : J' ≤ (⁅(⊤ : Subgroup C'), (⊤ : Subgroup C')⁆).map φ := by
    have h1 : J' ≤ (⊤ : Subgroup C').map φ := by
      rw [← hJp]
      exact (Subgroup.commutator_mono hJ' hJ').trans hcomm_le
    rw [Subgroup.map_commutator, ← hJp]
    exact Subgroup.commutator_mono h1 h1
  obtain ⟨x', hx', rfl⟩ := hJ'C hz
  let ι : C' →* Subgroup.centralizer {toSesq h 4 k} :=
    ((toSesq h 4).comp C'.subtype).codRestrict _ fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul,
        Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff.mp x.2]
  have hι : ∀ x : C', ((ι x : Subgroup.centralizer {toSesq h 4 k}) :
      sesqUnitaryGroup (stdHermForm h 4)) = toSesq h 4 (x : _) := fun x => rfl
  let ρ' := eC.toMonoidHom.comp ι
  have hρ' : ∀ x : C', ρ' x = eC (ι x) := fun x => rfl
  have hρ'inj : Function.Injective ρ' := eC.injective.comp fun a b hab => by
    apply Subtype.ext
    apply toSesq_injective h 4
    have := congrArg Subtype.val hab
    rw [hι, hι] at this
    exact this
  set T : Module.End K V := ((ρ' x' : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hT
  have hdet : LinearMap.det T = 1 := by
    have hle : ⁅(⊤ : Subgroup C'), (⊤ : Subgroup C')⁆ ≤
        ((Units.map (LinearMap.det : Module.End K V →* K)).comp ρ').ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have := congrArg Units.val (hle hx')
    simpa [hT] using this
  set X : ClassicalGroups.UnitaryFlag.unitarySU p f K 4 :=
    (x' : ClassicalGroups.UnitaryFlag.unitarySU p f K 4) with hXdef
  have hX2 : X ^ 2 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    change (φ x') ^ 2 = 1
    rw [sq, hz2]
  rw [hZ, Subgroup.mem_subgroupOf] at hX2
  obtain ⟨c, hc⟩ := hX2
  have hcSU : GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) K := by
    rw [hc]
    exact (X ^ 2).2
  have hneg1 : (-1 : GL (Fin 4) K) ∈ ClassicalGroups.UnitaryFlag.unitarySU p f K 4 :=
    neg_one_mem_statedSU_four h
  have hnegC : (⟨-1, hneg1⟩ : ClassicalGroups.UnitaryFlag.unitarySU p f K 4) ∈ C' := by
    rw [hC', Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (-1 : GL (Fin 4) K) * kG = kG * -1
    rw [neg_one_mul, mul_neg_one]
  have hρ'neg : ((ρ' ⟨⟨-1, hneg1⟩, hnegC⟩ : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) = -1 := by
    rw [hρ']
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := congrArg (fun F => F v) (heC (ι ⟨⟨-1, hneg1⟩, hnegC⟩))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    change (((eC (ι ⟨⟨-1, hneg1⟩, hnegC⟩) : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) v : Fin 4 → K) = _
    rw [h1, LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg]
    show (((toSesq h 4 ⟨-1, hneg1⟩ : sesqUnitaryGroup (stdHermForm h 4)) :
      LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] Fin 4 → K)
        (v : Fin 4 → K) = _
    rw [toSesq_apply, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  rcases scalar_eq_one_or_neg_one_U4 h hq hcSU with hc1 | hc1
  · exfalso
    have hx'2 : x' ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change ((X : GL (Fin 4) K)) ^ 2 = 1
      rw [← Subgroup.coe_pow, ← hc, hc1, map_one]
    have hTT : T * T = 1 := by
      rw [hT, ← Units.val_mul, ← sq, ← map_pow, hx'2, map_one, Units.val_one]
    rcases eq_one_or_eq_neg_one_of_end h2K hdP hdet hTT with h3 | h3
    · have : x' = 1 := hρ'inj (by rw [map_one]; exact Units.ext (by rw [← hT, h3, Units.val_one]))
      apply hz1
      rw [this, map_one]
    · have : x' = ⟨⟨-1, hneg1⟩, hnegC⟩ := hρ'inj (Units.ext (by rw [← hT, h3, hρ'neg]))
      apply hz1
      rw [this, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ⟨-1, scalar_neg_one_eq 4⟩
  · refine ⟨X, rfl, ?_⟩
    have h3 : ((X : GL (Fin 4) K)) ^ 2 = -1 := by
      rw [← Subgroup.coe_pow, ← hc, hc1, scalar_neg_one_eq]
    have := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K)) h3
    simpa [sq] using this

end CFSG.ComponentClassification.CatFactsL4U4
