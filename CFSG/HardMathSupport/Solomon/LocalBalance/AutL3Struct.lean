module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513
public import CFSG.Quasithin.Background.A318PL3Unit
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

section Diag

variable {Y : Type*} [Group Y] {F : Type} [Field F]

theorem congr_eq_conjAut_of_diagProp
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))
    (A : GL (Fin 3) F) (α : MulAut Y)
    (h : ∀ (y : Y) (M M' : ↥(CFSG.Open.StatedSL 3 F)), θ (QuotientGroup.mk y) = QuotientGroup.mk M →
      (M' : GL (Fin 3) F) = A * M * A⁻¹ → θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M') :
    MulAut.congr (θ.trans (psiO F)) (centerDescend Y α) = conjAut 3 F A := by
  ext x
  obtain ⟨z, rfl⟩ := (θ.trans (psiO F)).surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [descend_apply_mk (θ.trans (psiO F)) α y]
  obtain ⟨M₀, hM₀⟩ := QuotientGroup.mk_surjective (θ (QuotientGroup.mk y))
  have hM' : A * (M₀ : GL (Fin 3) F) * A⁻¹ ∈ CFSG.Open.StatedSL 3 F :=
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_statedSL A) M₀).1 M₀.2
  have h1 := h y M₀ ⟨_, hM'⟩ hM₀.symm rfl
  simp only [MulEquiv.trans_apply]
  rw [h1, ← hM₀]
  exact psiO_mk_conj A M₀ ⟨_, hM'⟩ rfl

theorem diagProp_of_congr_eq_conjAut
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))
    (A : GL (Fin 3) F) (α : MulAut Y)
    (h : MulAut.congr (θ.trans (psiO F)) (centerDescend Y α) = conjAut 3 F A) :
    ∀ (y : Y) (M M' : ↥(CFSG.Open.StatedSL 3 F)), θ (QuotientGroup.mk y) = QuotientGroup.mk M →
      (M' : GL (Fin 3) F) = A * M * A⁻¹ → θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M' := by
  intro y M M' hM hM'
  apply (psiO F).injective
  have h1 := descend_apply_mk (θ.trans (psiO F)) α y
  rw [h] at h1
  simp only [MulEquiv.trans_apply] at h1
  rw [← h1, hM, psiO_mk_conj A M M' hM']

end Diag

section DiagU

variable {Y : Type*} [Group Y] {K : Type} [Field K] {p f : ℕ}

theorem mem_normalizer_of_forall (h : UnitaryFieldData p f K) {A : GL (Fin 3) K}
    (hA : ∀ M : ↥(unitarySU p f K 3), ∃ M' : ↥(unitarySU p f K 3),
      (M' : GL (Fin 3) K) = A * M * A⁻¹) :
    A ∈ Subgroup.normalizer (unitarySU p f K 3 : Set (GL (Fin 3) K)) := by
  have hfin : Finite K := h.finite
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hle : ∀ x ∈ unitarySU p f K 3, A * x * A⁻¹ ∈ unitarySU p f K 3 := fun x hx => by
    obtain ⟨M', hM'⟩ := hA ⟨x, hx⟩
    rw [← hM']
    exact M'.2
  refine ⟨hle x, fun hx => ?_⟩
  have hmap : (unitarySU p f K 3).map (MulAut.conj A).toMonoidHom ≤ unitarySU p f K 3 := by
    rintro _ ⟨z, hz, rfl⟩
    simpa using hle z hz
  have heq : (unitarySU p f K 3).map (MulAut.conj A).toMonoidHom = unitarySU p f K 3 := by
    apply Subgroup.eq_of_le_of_card_ge hmap
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj A).toMonoidHom
      (MulAut.conj A).injective).toEquiv]
  have : A * x * A⁻¹ ∈ (unitarySU p f K 3).map (MulAut.conj A).toMonoidHom := by
    rw [heq]; exact hx
  obtain ⟨z, hz, hzx⟩ := this
  have : z = x := by
    have := (MulAut.conj A).injective (show (MulAut.conj A) z = (MulAut.conj A) x by
      simpa [MulAut.conj_apply] using hzx)
    exact this
  rw [← this]; exact hz


theorem symm_psuO_mk (h : UnitaryFieldData p f K) (M : ↥(CFSG.Open.StatedSU 3 (p ^ f) K)) :
    (psuO h).symm (QuotientGroup.mk M) =
      unitaryProj h 3 (⟨M.1, M.2⟩ : ↥(unitarySU p f K 3)) := by
  rw [MulEquiv.symm_apply_eq]
  exact (psuO_proj h ⟨M.1, M.2⟩).symm

theorem diagPropU_of_congr_eq_psuConj (h : UnitaryFieldData p f K)
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) K))
    (α : MulAut Y) (A : unitaryIsom3 h)
    (hc : MulAut.congr (θ.trans (psuO h).symm) (centerDescend Y α) = psuConj h A) :
    ∀ (y : Y) (M M' : ↥(CFSG.Open.StatedSU 3 (p ^ f) K)), θ (QuotientGroup.mk y) = QuotientGroup.mk M →
      (M' : GL (Fin 3) K) = (A : GL (Fin 3) K) * (M : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ →
        θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M' := by
  intro y M M' hM hM'
  apply (psuO h).symm.injective
  have h1 := descend_apply_mk (θ.trans (psuO h).symm) α y
  rw [hc] at h1
  simp only [MulEquiv.trans_apply] at h1
  rw [← h1, hM, symm_psuO_mk, symm_psuO_mk]
  change psuConj h A (QuotientGroup.mk (⟨M.1, M.2⟩ : ↥(unitarySU p f K 3))) =
    QuotientGroup.mk (⟨M'.1, M'.2⟩ : ↥(unitarySU p f K 3))
  rw [psuConj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suConj]
  exact hM'.symm

theorem congr_mem_psuConj_range_of_diagProp (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) K))
    (α : MulAut Y) (A : GL (Fin 3) K)
    (hA : ∀ M : ↥(CFSG.Open.StatedSU 3 (p ^ f) K), ∃ M' : ↥(CFSG.Open.StatedSU 3 (p ^ f) K),
      (M' : GL (Fin 3) K) = A * (M : GL (Fin 3) K) * A⁻¹)
    (hα : ∀ (y : Y) (M M' : ↥(CFSG.Open.StatedSU 3 (p ^ f) K)),
      θ (QuotientGroup.mk y) = QuotientGroup.mk M →
        (M' : GL (Fin 3) K) = A * (M : GL (Fin 3) K) * A⁻¹ →
        θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M') :
    MulAut.congr (θ.trans (psuO h).symm) (centerDescend Y α) ∈ (psuConj h).range := by
  rw [congr_trans]
  refine congr_psuO_mem_psuConj_range h hq ⟨A, mem_normalizer_of_forall h hA, fun M M' hM' => ?_⟩
  obtain ⟨z, hz⟩ := θ.surjective (QuotientGroup.mk M)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  change θ (centerDescend Y α (θ.symm (QuotientGroup.mk M))) = QuotientGroup.mk M'
  rw [← hz, MulEquiv.symm_apply_apply, centerDescend_mk]
  exact hα y M M' hz hM'

end DiagU

section Field

variable {Y : Type*} [Group Y]

theorem isFieldAutPSL3_of_model {α : MulAut Y} {F : Type} [Field F] [Finite F]
    (e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F) (σ : F ≃+* F)
    (γ : MulAut (projectiveSL 3 F))
    (h : MulAut.congr e (centerDescend Y α) = γ * fieldAut 3 F σ * γ⁻¹) : IsFieldAutPSL3 α := by
  refine ⟨F, inferInstance, inferInstance, e.trans (psiO F).symm, σ,
    MulAut.congr (psiO F).symm (fieldAut 3 F σ), MulAut.congr (psiO F).symm γ, ?_, ?_⟩
  · intro A A' hA
    obtain ⟨s, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective A
    have h1 : (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s) :
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) = mkO F s := rfl
    have h3 : A' = specialLinearGroupEquivStatedSL 3 F
        (Matrix.SpecialLinearGroup.map σ.toRingHom s) := by
      apply Subtype.ext
      apply Units.ext
      simpa [specialLinearGroupEquivStatedSL_coe] using hA
    simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply]
    rw [h1, psiO_mkO, fieldAut_proj, h3]
    apply (psiO F).injective
    rw [MulEquiv.apply_symm_apply]
    exact (psiO_mkO F _).symm
  · intro y
    have h1 := descend_apply_mk e α y
    rw [h] at h1
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.congr_apply,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    rw [← h1]
    simp [MulAut.mul_apply]


theorem isFieldAutPSU3_of_model {α : MulAut Y} {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU h 3)
    (σ : K ≃+* K) (hσ : Odd (orderOf σ)) (γ : MulAut (unitaryPSU h 3))
    (hc : MulAut.congr e (centerDescend Y α) = γ * psuField h σ * γ⁻¹) : IsFieldAutPSU3 α := by
  have hfin := h.finite
  refine ⟨K, inferInstance, hfin, p ^ f, e.trans (psuO h), σ,
    MulAut.congr (psuO h) (psuField h σ), MulAut.congr (psuO h) γ, ?_, hσ, ?_, ?_⟩
  · rw [h.card, pow_mul']
  · intro A A' hA
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [symm_psuO_mk]
    change psuO h (psuField h σ (QuotientGroup.mk (⟨A.1, A.2⟩ : ↥(unitarySU p f K 3)))) = _
    rw [psuField_mk]
    have : (suField h σ ⟨A.1, A.2⟩ : ↥(unitarySU p f K 3)) = ⟨A'.1, A'.2⟩ := by
      apply Subtype.ext
      rw [coe_suField]
      apply Units.ext
      rw [UnitaryHigher.coe_glAut]
      exact hA.symm
    rw [this]
    exact psuO_proj h _
  · intro y
    have h1 := descend_apply_mk e α y
    rw [hc] at h1
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.congr_apply,
      MulEquiv.symm_apply_apply]
    rw [← h1]
    simp [MulAut.mul_apply]

end Field

section Std

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513Ns CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def StdModelL (Y : Type*) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), 3 ∣ Nat.card K - 1 ∧
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K)

@[expose] def StdModelU (Y : Type*) [Group Y] : Prop :=
  ∃ (p f : ℕ) (K : Type) (_ : Field K) (hF : UnitaryFieldData p f K), 2 < p ^ f ∧ 3 ∣ p ^ f + 1 ∧
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3)

theorem stdModel_of_etaEquiv {Y : Type} [Group Y] {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hmod : ModThree π (p ^ f)) (h2 : 2 < p ^ f)
    (ε : (Y ⧸ Subgroup.center Y) ≃*
      (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))) :
    StdModelL Y ∨ StdModelU Y := by
  have hfin := hK.finite
  cases π
  · right
    refine ⟨p, f, K, inferInstance, hK.unitary, h2, ?_, ⟨ε.trans (etaFalse hK h2)⟩⟩
    have : p ^ f % 3 = 2 := hmod
    omega
  · left
    refine ⟨K, inferInstance, hfin, ?_, ⟨ε.trans (etaTrue (p ^ f) K)⟩⟩
    have h1 : Nat.card K = p ^ f := hK.card
    have : p ^ f % 3 = 1 := hmod
    omega

theorem exists_stdModel {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hT : IsExtremalType Y ∨ IsSLThreeEps Y) : StdModelL Y ∨ StdModelU Y := by
  rcases model_of_type hY hT with ⟨π, p, f, K, _, hK, hq, h8, h2, ⟨e⟩⟩ |
      ⟨π, p, f, K, _, hK, hq, h8, h2, ⟨e⟩⟩
  · exact stdModel_of_etaEquiv hK hq h2 (barEquiv e)
  · have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
      isQuasisimple_slPi hK (fun _ h => by omega)
    have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) K) := (Group.isPerfect_def).2 hGq.1
    have hcQ : Subgroup.center (↥(slPi π 3 (p ^ f) K) ⧸
        Subgroup.center ↥(slPi π 3 (p ^ f) K)) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot _
    have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
    exact stdModel_of_etaEquiv hK hq h2 ((barEquivBot hZ).trans e)


end Std

section Dich

variable {Y : Type*} [Group Y]

theorem diag_or_field_L {K : Type} [Field K] [Finite K]
    (ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K) {α : MulAut Y} (h3 : α ^ 3 = 1) :
    α ∈ Lemma513Ns.diagAut Y ∨ IsFieldAutThree α := by
  have hψ3 : MulAut.congr ε (centerDescend Y α) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  by_cases hD : MulAut.congr ε (centerDescend Y α) ∈ linearAutGroup 3 K
  · left
    rw [linearAutGroup_eq_range] at hD
    obtain ⟨A, hA⟩ := hD
    apply Subgroup.subset_closure
    left
    refine ⟨K, inferInstance, inferInstance, ε.trans (psiO K).symm, A, ?_, ?_⟩
    · intro M
      exact ⟨⟨A * (M : GL (Fin 3) K) * A⁻¹,
        (Subgroup.mem_normalizer_iff.1 (mem_normalizer_statedSL A) M).1 M.2⟩, rfl⟩
    · apply diagProp_of_congr_eq_conjAut
      have : (ε.trans (psiO K).symm).trans (psiO K) = ε := by
        ext x; simp
      rw [this]
      exact hA.symm
  · right
    obtain ⟨σ, hσ, H, hH⟩ := linear_order_three_field_descent le_rfl _ hψ3 hD
    exact Or.inr (Or.inl (isFieldAutPSL3_of_model ε σ (conjAut 3 K H) hH))

theorem diag_or_field_U {p f : ℕ} {K : Type} [Field K] (hF : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (ε : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3) {α : MulAut Y}
    (h3 : α ^ 3 = 1) : α ∈ Lemma513Ns.diagAut Y ∨ IsFieldAutThree α := by
  have hfin := hF.finite
  have hψ3 : MulAut.congr ε (centerDescend Y α) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  by_cases hD : MulAut.congr ε (centerDescend Y α) ∈ (psuConj hF).range
  · left
    obtain ⟨A, hA⟩ := hD
    apply Subgroup.subset_closure
    right
    refine ⟨K, inferInstance, hfin, p ^ f, ε.trans (psuO hF), (A : GL (Fin 3) K),
      by rw [hF.card, pow_mul'], ?_, ?_⟩
    · intro M
      exact ⟨⟨(A : GL (Fin 3) K) * (M : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹,
        conj_mem_unitarySU A.2 M.2⟩, rfl⟩
    · apply diagPropU_of_congr_eq_psuConj hF _ α A
      have : (ε.trans (psuO hF)).trans (psuO hF).symm = ε := by
        ext x; simp
      rw [this]
      exact hA.symm
  · right
    obtain ⟨σ, hσ, H, hH⟩ := unitary_order_three_field_descent hq _ hψ3 hD
    exact Or.inr (Or.inr (isFieldAutPSU3_of_model hF ε σ (by rw [hσ]; decide) (psuConj hF H) hH))

end Dich

section Index

theorem mem_commutator_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : G} :
    e x ∈ commutator H ↔ x ∈ commutator G := by
  have h1 : (commutator G).map e.toMonoidHom = commutator H := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      ← commutator_def]
  rw [← h1]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := e.injective hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {Y M : Type*} [Group Y] [Group M]

theorem index_le_of_model [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (ε : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M) (hP : GoodPinned P)
    [Finite M] (hidx : (innerAut M).relIndex P.inndiag ≤ 3)
    (hdiag : ∀ α : MulAut Y, α ∈ Lemma513Ns.diagAut Y →
      MulAut.congr ε (centerDescend Y α) ∈ commutator (MulAut M)) :
    ((innerAut Y).subgroupOf (Lemma513Ns.innerDiag Y)).index ≤ 3 := by
  set Φ : MulAut Y →* MulAut M := (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    apply eq_one_of_centerDescend_eq_one hY
    have : MulAut.congr ε (centerDescend Y α) = 1 := hα
    have h2 := (MulAut.congr ε).injective (show MulAut.congr ε (centerDescend Y α) =
      MulAut.congr ε 1 by rw [this, map_one])
    exact h2
  have hΦconj : ∀ y : Y, Φ (MulAut.conj y) = MulAut.conj (ε (QuotientGroup.mk y)) := fun y => by
    simp only [hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [Coordinator.centerDescend_conj, congr_mulAutConj]
  have hΦN : (innerAut Y).map Φ = innerAut M := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨ε (QuotientGroup.mk y), (hΦconj y).symm⟩
    · rintro ⟨m, rfl⟩
      obtain ⟨z, rfl⟩ := ε.surjective m
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
      exact ⟨MulAut.conj y, ⟨y, rfl⟩, hΦconj y⟩
  have hΦH : (Lemma513Ns.innerDiag Y).map Φ ≤ P.inndiag := by
    unfold Lemma513Ns.innerDiag
    rw [Subgroup.map_sup, hΦN]
    refine sup_le P.inn_le ?_
    unfold Lemma513Ns.diagAut
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨α, hα, rfl⟩
    exact hP.down (hdiag α (Subgroup.subset_closure hα))
  have hNH : innerAut M ≤ (Lemma513Ns.innerDiag Y).map Φ := by
    rw [← hΦN]
    exact Subgroup.map_mono le_sup_left
  show (innerAut Y).relIndex (Lemma513Ns.innerDiag Y) ≤ 3
  rw [← Subgroup.relIndex_map_map_of_injective (innerAut Y) (Lemma513Ns.innerDiag Y) hΦinj, hΦN]
  have h1 := Subgroup.relIndex_mul_relIndex (innerAut M) ((Lemma513Ns.innerDiag Y).map Φ) P.inndiag
    hNH hΦH
  have h2 : ((Lemma513Ns.innerDiag Y).map Φ).relIndex P.inndiag ≠ 0 := by
    have : Finite ↥P.inndiag := Finite.of_injective _ Subtype.val_injective
    have : Finite (↥P.inndiag ⧸ ((Lemma513Ns.innerDiag Y).map Φ).subgroupOf P.inndiag) :=
      inferInstance
    exact Subgroup.index_ne_zero_of_finite
  have h3 : 0 < ((Lemma513Ns.innerDiag Y).map Φ).relIndex P.inndiag := Nat.pos_of_ne_zero h2
  calc (innerAut M).relIndex ((Lemma513Ns.innerDiag Y).map Φ)
      ≤ (innerAut M).relIndex ((Lemma513Ns.innerDiag Y).map Φ) *
        ((Lemma513Ns.innerDiag Y).map Φ).relIndex P.inndiag := Nat.le_mul_of_pos_right _ h3
    _ = (innerAut M).relIndex P.inndiag := h1
    _ ≤ 3 := hidx

end Index

section Final

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem diag_descend_mem_commutator {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {α : MulAut Y} (h : Lemma513Ns.IsDiagAutPSL3 α ∨ Lemma513Ns.IsDiagAutPSU3 α) :
    centerDescend Y α ∈ commutator (MulAut (Y ⧸ Subgroup.center Y)) := by
  rcases h with ⟨F, _, _, θ, A, -, hα⟩ | ⟨F, _, hfin, q, θ, A, hcard, hnorm, hα⟩
  · have h1 := congr_eq_conjAut_of_diagProp θ A α hα
    refine (mem_commutator_congr (MulAut.congr (θ.trans (psiO F)))).1 ?_
    rw [h1]
    exact conjAut_mem_commutator F A
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hq := two_lt_pow_of_quasisimple hY hF (θ.trans (psuO hF).symm)
    obtain ⟨B, hB⟩ := congr_mem_psuConj_range_of_diagProp hF hq θ α A hnorm hα
    refine (mem_commutator_congr (MulAut.congr (θ.trans (psuO hF).symm))).1 ?_
    rw [← hB]
    exact psuConj_mem_commutator hF hq B

theorem diagAut_descend_mem_commutator {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {α : MulAut Y} (h : α ∈ Lemma513Ns.diagAut Y) :
    centerDescend Y α ∈ commutator (MulAut (Y ⧸ Subgroup.center Y)) := by
  have : Lemma513Ns.diagAut Y ≤ (commutator (MulAut (Y ⧸ Subgroup.center Y))).comap
      (centerDescend Y) := by
    unfold Lemma513Ns.diagAut
    rw [Subgroup.closure_le]
    intro β hβ
    exact diag_descend_mem_commutator hY hβ
  exact this h

theorem inputInnDiagStructure_holds : Lemma513Ns.InputInnDiagStructure := by
  intro Y _ _ hY hT
  have hdiag : ∀ {M : Type} [Group M] (ε : (Y ⧸ Subgroup.center Y) ≃* M) (α : MulAut Y),
      α ∈ Lemma513Ns.diagAut Y → MulAut.congr ε (centerDescend Y α) ∈ commutator (MulAut M) :=
    fun ε α h => (mem_commutator_congr (MulAut.congr ε)).2 (diagAut_descend_mem_commutator hY h)
  rcases exists_stdModel hY hT with ⟨K, _, _, h3, ⟨ε⟩⟩ | ⟨p, f, K, _, hF, hq, h3, ⟨ε⟩⟩
  · refine ⟨?_, fun α hα hnd => ?_⟩
    · refine index_le_of_model hY ε (stdPinnedPSL 3 K) (goodPinned_psl K) ?_ (hdiag ε)
      rw [stdPinnedPSL_inndiag]
      exact (CFSG.Quasithin.A318P.relIndex_inner_linearAutGroup_eq_three h3).le
    · rcases diag_or_field_L ε hα with h | h
      · exact absurd (Subgroup.mem_sup_right h) hnd
      · exact h
  · have := hF.finite
    refine ⟨?_, fun α hα hnd => ?_⟩
    · refine index_le_of_model hY ε (stdPinnedPSU3 hF) (goodPinned_psu hF hq) ?_ (hdiag ε)
      exact (CFSG.Quasithin.A318P.relIndex_inner_psuConj_eq_three hF hq h3).le
    · rcases diag_or_field_U hF hq ε hα with h | h
      · exact absurd (Subgroup.mem_sup_right h) hnd
      · exact h

end Final

section Elem

theorem card_le_three_of_pow {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (h : ∀ c : C, c ^ 3 = 1) : Nat.card C ≤ 3 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd (by norm_num) (Monoid.exponent_dvd_of_forall_pow_eq_one h)

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _


open CFSG.Quasithin.A318P in
theorem elem_struct_of_frame {M : Type} [Group M] [Finite M] {C : Type} [Group C] [Finite C]
    [IsCyclic C] (F : L3Frame M C)
    (hD9 : ∀ E : Subgroup (MulAut M), E ≤ F.D → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (Ee : Subgroup (MulAut M)) (hE : CFSG.Open.IsElemAbelian 3 Ee) :
    ∃ G : Subgroup (MulAut M), G ≤ Ee ∧ (G.subgroupOf Ee).index ≤ 9 ∧
      ∀ x ∈ G, x = 1 ∨ ∃ (h : MulAut M) (c : C), orderOf c = 3 ∧ x = h * F.fld c * h⁻¹ := by
  have hle : Ee ≤ F.E := by
    intro x hx
    have h3 : x ^ 3 = 1 := hE.2 x hx
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · have : x = 1 := orderOf_eq_one_iff.1 h1
      rw [this]; exact F.E.one_mem
    · exact F.mem_E.2 (F.three_mem x 1 (by rw [h1]; norm_num))
  set ρ : ↥Ee →* C := F.rho.comp (Subgroup.inclusion hle) with hρ
  have hker : ∀ x : ↥Ee, ρ x = 1 ↔ (x : MulAut M) ∈ F.D := fun x =>
    F.rho_eq_one_iff ⟨x, hle x.2⟩
  have hcube : ∀ c ∈ ρ.range, c ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : (x : ↥Ee) ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
    rw [this, map_one]
  have hrcard : Nat.card ρ.range ≤ 3 := card_le_three_of_pow (fun c => Subtype.ext (by simpa using hcube c c.2))
  by_cases hr : ρ.range = ⊥
  · have hED : Ee ≤ F.D := fun x hx => (hker ⟨x, hx⟩).1 (by
      have : ρ ⟨x, hx⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hr] at this
      exact Subgroup.mem_bot.1 this)
    refine ⟨⊥, bot_le, ?_, fun x hx => Or.inl (Subgroup.mem_bot.1 hx)⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact hD9 Ee hED hE
  · obtain ⟨⟨c, x, rfl⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hr
    have hρx : ρ x ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hx3 : x ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
    have hxne : x ≠ 1 := fun h => hρx (by rw [h, map_one])
    have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hxne
    have hρord : orderOf (ρ x) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hρx
    have hdvd : 3 ∣ Nat.card ρ.range := by
      have := Subgroup.orderOf_dvd_natCard ρ.range (⟨x, rfl⟩ : ρ x ∈ ρ.range)
      rwa [hρord] at this
    have hrc : Nat.card ρ.range = 3 :=
      Nat.le_antisymm hrcard (Nat.le_of_dvd Nat.card_pos hdvd)
    set G : Subgroup (MulAut M) := Subgroup.zpowers (x : MulAut M) with hG
    have hGE : G ≤ Ee := (Subgroup.zpowers_le).2 x.2
    refine ⟨G, hGE, ?_, ?_⟩
    ·
      have h1 := Subgroup.card_mul_index (G.subgroupOf Ee)
      have h2 : Nat.card (G.subgroupOf Ee) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGE).toEquiv, hG, Nat.card_zpowers,
          Subgroup.orderOf_coe, hxord]
      have h3 := Subgroup.card_ker_mul_card_range ρ
      rw [hrc] at h3
      have h4 : Nat.card ρ.ker ≤ 9 := by
        have hK0 : (ρ.ker.map Ee.subtype) ≤ F.D := by
          rintro _ ⟨z, hz, rfl⟩
          exact (hker z).1 hz
        have hK0e : CFSG.Open.IsElemAbelian 3 (ρ.ker.map Ee.subtype) := by
          refine CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_mono hE ?_
          rintro _ ⟨z, -, rfl⟩
          exact z.2
        have := hD9 _ hK0 hK0e
        rwa [Subgroup.card_map_of_injective Ee.subtype_injective] at this
      rw [h2] at h1
      omega
    · intro y hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · right
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hyE : ((x : MulAut M) ^ k) ∈ Ee := Ee.zpow_mem x.2 k
        have hyx : (⟨(x : MulAut M) ^ k, hyE⟩ : ↥Ee) = x ^ k := by
          apply Subtype.ext; simp
        have hnotD : (x : MulAut M) ^ k ∉ F.D := by
          intro hD
          have h1 : ρ ⟨_, hyE⟩ = 1 := (hker _).2 hD
          rw [hyx, map_zpow] at h1
          have h2 : (3 : ℤ) ∣ k := by
            have := orderOf_dvd_iff_zpow_eq_one.2 h1
            rwa [hρord] at this
          apply hy1
          obtain ⟨m, rfl⟩ := h2
          have h3 : (x : MulAut M) ^ 3 = 1 := by
            have := congrArg Subtype.val hx3
            simpa using this
          rw [_root_.zpow_mul]
          have h4 : (x : MulAut M) ^ (3 : ℤ) = 1 := by exact_mod_cast h3
          rw [h4, _root_.one_zpow]
        have hy3 : ((x : MulAut M) ^ k) ^ 3 = 1 := hE.2 _ hyE
        obtain ⟨h, -, c, hc, hh⟩ := F.lang _ hy3 (F.mem_E.1 (hle hyE)) hnotD
        exact ⟨h, c, hc, hh⟩


theorem phi_injective {Y M : Type*} [Group Y] [Group M] (hY : CFSG.Open.IsQuasisimple Y)
    (ε : (Y ⧸ Subgroup.center Y) ≃* M) :
    Function.Injective ((MulAut.congr ε).toMonoidHom.comp (centerDescend Y)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  apply eq_one_of_centerDescend_eq_one hY
  have : MulAut.congr ε (centerDescend Y α) = 1 := hα
  exact (MulAut.congr ε).injective (by rw [this, map_one])

open CFSG.Quasithin.A318P in
theorem l3Aut_of_frame {Y M : Type} [Group Y] [Finite Y] [Group M] [Finite M] {C : Type}
    [Group C] [Finite C] [IsCyclic C] (hY : CFSG.Open.IsQuasisimple Y)
    (ε : (Y ⧸ Subgroup.center Y) ≃* M) (F : L3Frame M C)
    (hD9 : ∀ E : Subgroup (MulAut M), E ≤ F.D → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hfield : ∀ (α : MulAut Y) (h : MulAut M) (c : C), orderOf c = 3 →
      MulAut.congr ε (centerDescend Y α) = h * F.fld c * h⁻¹ → IsFieldAutThree α)
    (E : Subgroup (MulAut Y)) (hE : CFSG.Open.IsElemAbelian 3 E) :
    ∃ G : Subgroup (MulAut Y), G ≤ E ∧ (G.subgroupOf E).index ≤ 9 ∧
      ∀ α ∈ G, IsFieldAutThree α := by
  set Φ : MulAut Y →* MulAut M := (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
  have hinj : Function.Injective Φ := phi_injective hY ε
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map Φ) := isElemAbelian_map Φ hE
  obtain ⟨G', hG'E, hidx, hG'⟩ := elem_struct_of_frame F hD9 (E.map Φ) hE'
  refine ⟨G'.comap Φ, ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨β, hβ, hβα⟩ := hG'E hα
    have : β = α := hinj hβα
    rwa [← this]
  · have h1 : (G'.comap Φ).map Φ = G' := by
      rw [Subgroup.map_comap_eq]
      exact inf_of_le_right (hG'E.trans (Subgroup.map_le_range Φ E))
    have h2 := Subgroup.relIndex_map_map_of_injective (f := Φ) (G'.comap Φ) E hinj
    rw [h1] at h2
    show (G'.comap Φ).relIndex E ≤ 9
    rw [← h2]
    exact hidx
  · intro α hα
    rcases hG' (Φ α) hα with h1 | ⟨h, c, hc, hh⟩
    · have : α = 1 := hinj (by rw [h1, map_one])
      rw [this]
      exact Or.inl rfl
    · exact hfield α h c hc hh

end Elem

section Final2

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem hD9_L {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (E : Subgroup (MulAut (projectiveSL 3 K))) (hED : E ≤ linearAutGroup 3 K)
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  let ρ : (⊤ : Subgroup (GL (Fin 3) K)) →* MulAut (projectiveSL 3 K) :=
    (conjAut 3 K).comp (⊤ : Subgroup (GL (Fin 3) K)).subtype
  have h2 : Nat.card E ≤ 3 ^ (3 - 1) :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel Nat.prime_three
      (by norm_num) (by rwa [Nat.card_units]) (by omega) ⊤ ρ
      (fun A => by
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype,
          CFSG.HardMathSupport.Timmesfeld.Tables.T1b.conjAut_eq_one_iff_scalar le_rfl]
        exact (CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff).symm)
      E (fun y hy => by
        obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp (hED hy)
        exact ⟨⟨A, trivial⟩, hA⟩) hE
  simpa using h2

theorem hD9_U {p f : ℕ} {K : Type} [Field K] (hF : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (E : Subgroup (MulAut (unitaryPSU hF 3))) (hED : E ≤ (psuConj hF).range)
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have hfin := hF.finite
  have h2 : Nat.card E ≤ 3 ^ (3 - 1) :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel Nat.prime_three
      (by norm_num) (CFSG.HardMathSupport.Timmesfeld.LinearRank.dvd_card_units_of_dvd_add_one hF h3)
      (by omega) (unitaryIsom3 hF) (psuConj hF)
      (fun A => by
        rw [psuConj_eq_one_iff A, StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar])
      E hED hE
  simpa using h2

theorem input7_L3Aut_holds : Lemma510Ns.Input7_L3Aut := by
  intro Y _ _ hY hT E hE
  rcases exists_stdModel hY hT with ⟨K, _, _, h3, ⟨ε⟩⟩ | ⟨p, f, K, _, hF, hq, h3, ⟨ε⟩⟩
  · have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    exact l3Aut_of_frame hY ε (CFSG.Quasithin.A318P.l3FrameLinear h3)
      (fun E hED hE => hD9_L h3 E hED hE)
      (fun α h c _ hform => Or.inr (Or.inl (isFieldAutPSL3_of_model ε c h hform))) E hE
  · have hfin := hF.finite
    have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    exact l3Aut_of_frame hY ε (CFSG.Quasithin.A318P.l3FramePSU hF hq h3)
      (fun E hED hE => hD9_U hF h3 E hED hE)
      (fun α h c hc hform => Or.inr (Or.inr (isFieldAutPSU3_of_model hF ε c
        (by rw [hc]; decide) h hform))) E hE

end Final2

end CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
