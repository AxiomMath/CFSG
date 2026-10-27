module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F.Cls

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU heldGU)
open CFSG.Assembly (LargeEvenProjMk LargeEvenProj)

theorem compType_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag} {r e : ℕ}
    (ht : t ∈ CFSG.Blueprint.classicalTags)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) t r 2 e) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
      Nat.card (X ⧸ Subgroup.center X) = 360 :=
  Or.inl ⟨t, r, e, (CFSG.Blueprint.LieModel.classical_iff ht).2 h⟩

theorem compType_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) t r 2 e) ∨
      Nat.card (Y ⧸ Subgroup.center Y) = 360) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
      Nat.card (X ⧸ Subgroup.center X) = 360 := by
  rcases h with ⟨t, r, k, hm⟩ | hcard
  · exact Or.inl ⟨t, r, k, CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv φ.symm hm⟩
  · exact Or.inr (by
      rw [Nat.card_congr (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) φ
        (Subgroup.map_center_eq φ)).toEquiv, hcard])

theorem compType_of_quot_statedSL {X : Type} [Group X] [Finite X] {a k : ℕ} {E : Type}
    [Field E] [Finite E] (hJ : CFSG.Open.IsQuasisimple X) (ha : 2 ≤ a)
    (hE : Nat.card E = 2 ^ k)
    (hφ : Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSL a E))) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
      Nat.card (X ⧸ Subgroup.center X) = 360 := by
  by_cases h22 : a = 2 ∧ k = 1
  ·
    obtain ⟨rfl, rfl⟩ := h22
    have hE2 : Nat.card E = 2 := by simpa using hE
    obtain ⟨φ⟩ := hφ
    have hcard : Nat.card (X ⧸ Subgroup.center X) < 60 := by
      rw [Nat.card_congr φ.toEquiv]
      have hdvd : Nat.card (StatedProj (StatedSL 2 E)) ∣ Nat.card ↥(StatedSL 2 E) :=
        Subgroup.index_dvd_card _
      rw [CFSG.Open.StatedAPI.card_statedSL_two E, hE2] at hdvd
      norm_num at hdvd
      exact lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hJ.2
    haveI : Group.IsSolvable (X ⧸ Subgroup.center X) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable hcard
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
      (J := X) inferInstance).elim
  ·
    have hk : 1 ≤ k := by
      have h2 : 1 < Nat.card E := Finite.one_lt_card
      rw [hE] at h2
      by_contra hk0
      rw [show k = 0 by omega, pow_zero] at h2
      omega
    have hadm : StatedLieAdmissible .PSL a 2 k := by
      refine ⟨Nat.prime_two, hk, ha, ?_, ?_⟩
      · intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h22 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      · intro h
        obtain ⟨-, h3⟩ := Prod.mk.inj h
        have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        rw [h3] at hdvd
        norm_num at hdvd
    have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL a 2 k :=
      ⟨hadm, E, inferInstance, inferInstance, hE, hφ⟩
    exact compType_of_statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]) hmodel

theorem compType_of_quot_heldSU {X : Type} [Group X] [Finite X] {a k : ℕ} {E : Type}
    [Field E] [Finite E] (hJ : CFSG.Open.IsQuasisimple X) (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a)
    (hτ'k : ∀ x, τ' x = x ^ (2 ^ k)) (hE : Nat.card E = (2 ^ k) ^ 2)
    (hφ : Nonempty (X ⧸ Subgroup.center X ≃*
      ↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ'))) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
      Nat.card (X ⧸ Subgroup.center X) = 360 := by
  obtain ⟨φ⟩ := hφ
  have hk : 1 ≤ k := by
    by_contra hk0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show k = 0 by omega] at h2
    norm_num at h2
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    obtain ⟨K, hKf, hKfin, hk', ⟨ψ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl
        τ' hτ' hτ'k hE
    exact compType_of_quot_statedSL hJ le_rfl hk' ⟨φ.trans ψ⟩
  · by_cases h31 : a = 3 ∧ k = 1
    ·
      obtain ⟨rfl, rfl⟩ := h31
      haveI := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two
        τ' hτ' (fun x => by simpa using hτ'k x) (by simpa using hE)
      haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hJ.2
      exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
        (J := X) (solvable_of_surjective (f := φ.symm.toMonoidHom)
          φ.symm.surjective)).elim
    · have hak : (a, 2 ^ k) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ' hτ' hτ'k hE ha3 hak
      have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU a 2 k :=
        ⟨⟨Nat.prime_two, hk, ha3, hak⟩, E, inferInstance, inferInstance, hE, ⟨φ.trans ψ⟩⟩
      exact compType_of_statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]) hmodel

theorem compType_of_quot_statedSp {X : Type} [Group X] {s k : ℕ} {E : Type}
    [Field E] [Finite E] (hs : 2 ≤ s) (hE : Nat.card E = 2 ^ k)
    (hne : ¬(s = 2 ∧ Nat.card E = 2))
    (φ : X ⧸ Subgroup.center X ≃* StatedProj (StatedSp s E)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
      Nat.card (X ⧸ Subgroup.center X) = 360 := by
  have hk : 1 ≤ k := by
    by_contra hk0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show k = 0 by omega] at h2
    norm_num at h2
  have hne' : (s, 2 ^ k) ≠ (2, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact hne ⟨h1, by rw [hE, h2]⟩
  have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp s 2 k :=
    ⟨⟨Nat.prime_two, hk, hs, hne'⟩, E, inferInstance, inferInstance, hE, ⟨φ⟩⟩
  exact compType_of_statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]) hmodel

theorem compType_of_orthModel {X : Type} [Group X] {s f : ℕ}
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .POmegaPlus s 2 f ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .POmegaMinus s 2 f) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
      Nat.card (X ⧸ Subgroup.center X) = 360 := by
  have hplus : .POmegaPlus ∈ CFSG.Blueprint.classicalTags := by
    simp [CFSG.Blueprint.classicalTags]
  have hminus : .POmegaMinus ∈ CFSG.Blueprint.classicalTags := by
    simp [CFSG.Blueprint.classicalTags]
  rcases hM with h | h
  · exact compType_of_statedClassicalModel hplus h
  · exact compType_of_statedClassicalModel hminus h

theorem card_quot_center_eq_360_of_sp42 {R F : Type} [Group R] [Field F] [Finite F]
    (hK2 : Nat.card F = 2) (e : ↥(commutator ↥(StatedSp 2 F)) ≃* R) :
    Nat.card (R ⧸ Subgroup.center R) = 360 := by
  let eR : R ≃* alternatingGroup (Fin 6) :=
    e.symm.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
  have hZ : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eR z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro a
      obtain ⟨y, rfl⟩ := eR.surjective a
      rw [← map_mul, ← map_mul, hz]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact eR.injective (by simpa using hz')
  calc Nat.card (R ⧸ Subgroup.center R) = Nat.card (R ⧸ (⊥ : Subgroup R)) := by rw [hZ]
    _ = Nat.card R := Nat.card_congr (QuotientGroup.quotientBot (G := R)).toEquiv
    _ = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr eR.toEquiv
    _ = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num

theorem compType_uni_scalar {F : Type} [Field F] [Finite F] {Q d p : ℕ}
    (h2 : (2 : F) = 0) {τ : F ≃+* F} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (A : GL (Fin d) F) (hA : A ∈ heldGU d F τ hτ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcardF : Nat.card F = Q ^ 2) (hd : 3 ≤ d) (hdQ : (d, Q) ≠ (3, 2))
    (u : MulAut (LargeEvenProj (StatedSU d Q F)))
    (hu : ∀ h h' : ↥(StatedSU d Q F),
      (h' : GL (Fin d) F) = A * (h : GL (Fin d) F) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d Q F) h) = LargeEvenProjMk (StatedSU d Q F) h')
    (hpow : u ^ p = 1) : ((orderOf A : ℕ) : F) ≠ 0 := by
  have hH : heldSU d F τ hτ = StatedSU d Q F :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) F, g ∈ heldGU d F τ hτ → ∀ x ∈ StatedSU d Q F,
      g * x * g⁻¹ ∈ StatedSU d Q F := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d Q F) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniConjSub (StatedSU d Q F) A (hnorm A hA)
      (hnorm A⁻¹ (inv_mem hA))
  have hpowk : ∀ (k : ℕ) (h h' : ↥(StatedSU d Q F)),
      (h' : GL (Fin d) F) = A ^ k * (h : GL (Fin d) F) * (A ^ k)⁻¹ →
      (u ^ k) (LargeEvenProjMk (StatedSU d Q F) h) = LargeEvenProjMk (StatedSU d Q F) h' := by
    intro k
    induction k with
    | zero =>
      intro h h' hk
      have : h' = h := by
        apply Subtype.ext
        simpa using hk
      subst this
      simp
    | succ k ih =>
      intro h h' hk
      have step1 : u (LargeEvenProjMk (StatedSU d Q F) h) =
          LargeEvenProjMk (StatedSU d Q F) (cA h) := hu h (cA h) rfl
      have step2 := ih (cA h) h' (by
        rw [hk, CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniConjSub_apply_val, pow_succ]
        group)
      rw [pow_succ, MulAut.mul_apply, step1, step2]
  have hAp : A ^ p ∈ heldGU d F τ hτ := pow_mem hA p
  have hconjB : ∀ g : GL (Fin d) F, g ∈ StatedSU d Q F → ∃ c : F,
      ((A ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          (g : Matrix (Fin d) (Fin d) F) *
        (((A ^ p)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          c • (g : Matrix (Fin d) (Fin d) F) := by
    intro g hg
    let h : ↥(StatedSU d Q F) := ⟨g, hg⟩
    let h' : ↥(StatedSU d Q F) := ⟨A ^ p * g * (A ^ p)⁻¹, hnorm (A ^ p) hAp g hg⟩
    have hk : (h' : GL (Fin d) F) = A ^ p * (h : GL (Fin d) F) * (A ^ p)⁻¹ := rfl
    have hmk : LargeEvenProjMk (StatedSU d Q F) h' = LargeEvenProjMk (StatedSU d Q F) h := by
      have h1 := hpowk p h h' hk
      rw [hpow] at h1
      simpa using h1.symm
    obtain ⟨c, hc⟩ :=
      (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.projMk_eq_iff_uni (StatedSU d Q F) h' h).mp hmk
    have hh' : (h' : GL (Fin d) F) =
        (h : GL (Fin d) F) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
      rw [hc]
      group
    have hGL : A ^ p * g * (A ^ p)⁻¹ =
        g * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := hh'
    refine ⟨(c : F)⁻¹, ?_⟩
    have hM := congrArg (fun X : GL (Fin d) F => (X : Matrix (Fin d) (Fin d) F)) hGL
    simp only [Units.val_mul] at hM
    rw [hM, ← map_inv, CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl,
      Units.val_inv_eq_inv_val, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨c0, hc0⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds F Q d τ hτ hτQ
    hcardF hd hdQ (A ^ p) hconjB
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 (by omega) A
      (hp.odd_of_ne_two hp2) hc0
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd

theorem compType_uni_decomp {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]
    {Q d : ℕ} {τ : F ≃+* F} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hcardF : Nat.card F = Q ^ 2)
    {A : GL (Fin d) F} (hA : A ∈ heldGU d F τ hτ)
    (hord : ((orderOf A : ℕ) : F) ≠ 0)
    {β : MulAut S} {e : S ≃* LargeEvenProj (StatedSU d Q F)}
    {u : MulAut (LargeEvenProj (StatedSU d Q F))}
    (hu : ∀ h h' : ↥(StatedSU d Q F),
      (h' : GL (Fin d) F) = A * (h : GL (Fin d) F) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d Q F) h) = LargeEvenProjMk (StatedSU d Q F) h')
    (hue : MulAut.congr e β = u) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
        (hτ' : ∀ x, τ' (τ' x) = x),
        2 ≤ a ∧ (∀ x, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
          ↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ'))) ∨
      (∃ (b e' : ℕ) (E : Type) (_ : Field E) (_ : Finite E),
        2 ≤ b ∧ Nat.card E = Q ^ (2 * e') ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL b E))) := by
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e β hJ
  rw [hue] at hJ'
  have hH : heldSU d F τ hτ = StatedSU d Q F :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) F, g ∈ heldGU d F τ hτ → ∀ x ∈ StatedSU d Q F,
      g * x * g⁻¹ ∈ StatedSU d Q F := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d Q F) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniConjSub (StatedSU d Q F) A (hnorm A hA)
      (hnorm A⁻¹ (inv_mem hA))
  obtain ⟨M, hM, hMJ⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_isComponentOf_lift
    (LargeEvenProjMk (StatedSU d Q F)) (QuotientGroup.mk'_surjective _)
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center (StatedSU d Q F))
    cA u (fun k => (hu k (cA k) rfl).symm) hJ'
  have hMinj : Function.Injective (StatedSU d Q F).subtype := Subtype.val_injective
  have hM' : IsComponentOf (M.map (StatedSU d Q F).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSU d Q F) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.map_fixSubgroup_uniConjSub
      (StatedSU d Q F) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map _ (fun g hg => ?_) hM
    rw [show g = 1 from hMinj (by simpa using hg)]
    exact one_mem _
  have hcompH : IsComponentOf (M.map (StatedSU d Q F).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ heldSU d F τ hτ) := by
    rw [hH]
    exact hM'
  have hcompGU := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isComponentOf_centralizer_gu_of_su
    hτ A hcompH
  have hsized := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.held_unitary_components_gu_sized
    CFSG.LieType.SemisimpleCentralizers.Held.SUComponentsTrivial_holds
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds hτ hτQ hcardF A hA hord
    (M.map (StatedSU d Q F).subtype) hcompGU
  obtain ⟨eJM⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.nonempty_centerQuot_of_map_eq
    (LargeEvenProjMk (StatedSU d Q F))
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center (StatedSU d Q F))
    hM.2.2.1 hMJ
  obtain ⟨eMZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
    (Subgroup.equivMapOfInjective M _ hMinj)
  let eqJ : ↥J ≃* ↥(J.map e.toMonoidHom) :=
    J.equivMapOfInjective e.toMonoidHom e.injective
  let eQ : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) :=
    QuotientGroup.congr _ _ eqJ (Subgroup.map_center_eq eqJ)
  rcases hsized with ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨eM⟩⟩ |
    ⟨b, e', E, hE, hEfin, hb2, hcardE, ⟨eM⟩⟩
  · exact Or.inl ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE,
      ⟨eQ.trans ((eJM.trans eMZ).trans eM)⟩⟩
  · exact Or.inr ⟨b, e', E, hE, hEfin, hb2, hcardE,
      ⟨eQ.trans ((eJM.trans eMZ).trans eM)⟩⟩

theorem compType_of_quot_sp42 {X Y : Type} [Group X] [Group Y] {F : Type} [Field F] [Finite F]
    (hK2 : Nat.card F = 2) (eX : X ≃* ↥(commutator (StatedSp 2 F)))
    (eY : Y ⧸ Subgroup.center Y ≃* X ⧸ Subgroup.center X) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) t r 2 e) ∨
      Nat.card (Y ⧸ Subgroup.center Y) = 360 := by
  refine Or.inr ?_
  rw [Nat.card_congr eY.toEquiv, card_quot_center_eq_360_of_sp42 hK2 eX.symm]

section Families

theorem compType_lin {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hF : FamLin labL)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  obtain ⟨F, hF', hFf, d, hd, hcard, A, u, e, hαu, hu⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiag_linear_data hcen hF hin
  have h2 : (2 : F) = 0 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.two_eq_zero_of_card hcard
  have hue : MulAut.congr e β = u := by
    ext z
    obtain ⟨l, rfl⟩ := e.surjective z
    show e (β (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply]
    exact hαu l
  have hupow : u ^ p = 1 := by rw [← hue, ← map_pow, hβp, map_one]
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.isScalar_of_pow_trivial
    h2 A p u hu hupow
  have hodd := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd A
    (hp.odd_of_ne_two hp2) hc
  have hord := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e β hJ
  rw [hue] at hJ'
  obtain ⟨M, hM, hMJ⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_isComponentOf_lift
    (LargeEvenProjMk (StatedSL d F)) (QuotientGroup.mk'_surjective _)
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL A) u
    (fun k => (hu k (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL A k) rfl).symm) hJ'
  have hMinj : Function.Injective (StatedSL d F).subtype := Subtype.val_injective
  have hM' : IsComponentOf (M.map (StatedSL d F).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.map_fixSubgroup_conjSL A]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map _ (fun g hg => ?_) hM
    rw [show g = 1 from hMinj (by simpa using hg)]
    exact one_mem _
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.held_linear_components_gl
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds A hord _ hM'
  obtain ⟨eJM⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.nonempty_centerQuot_of_map_eq
    (LargeEvenProjMk (StatedSL d F))
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center hM.2.2.1 hMJ
  obtain ⟨eMZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
    (Subgroup.equivMapOfInjective M _ hMinj)
  letI := hEf
  letI := hEalg
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_card_eq_two_pow
    (F := F) (E := E) h2
  exact compType_of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
    (compType_of_quot_statedSL hJ'.2.2 ha hk ⟨(eJM.trans eMZ).trans eM⟩)

theorem compType_uni {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hFam : FamUni labL)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  obtain ⟨F, hF', hFf, d, τ, hτ, hτQ, hcardF, hd, hd3, A, u, e, hA, hαu, hu⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.innDiag_unitary_data hcen hFam hin
  have h2 : (2 : F) = 0 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.two_eq_zero_of_card
    (n := 2 * labL.n) (by rw [hcardF, ← pow_mul, Nat.mul_comm])
  generalize hQdef : 2 ^ labL.n = Q at *
  have hdQ : (d, Q) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2'⟩ := Prod.mk.inj h
    have hn2 := hd3 h1
    have : 4 ≤ Q := by
      rw [← hQdef]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ labL.n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hue : MulAut.congr e β = u := by
    ext z
    obtain ⟨l, rfl⟩ := e.surjective z
    show e (β (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply]
    exact hαu l
  have hpow : u ^ p = 1 := by rw [← hue, ← map_pow, hβp, map_one]
  have hord := compType_uni_scalar h2 hτ hτQ A hA hp hp2 hcardF hd hdQ u hu hpow
  rcases compType_uni_decomp hτ hτQ hcardF hA hord hu hue hJ with
    ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨eM⟩⟩ |
    ⟨b, e', E, hE, hEfin, hb2, hcardE, ⟨eM⟩⟩
  · letI := hE
    have hpw : Q ^ dd = 2 ^ (labL.n * dd) := by rw [← hQdef, ← pow_mul]
    rw [hpw] at hτ'Q hcardE
    exact compType_of_quot_heldSU hJ.2.2 τ' hτ' ha2 hτ'Q hcardE ⟨eM⟩
  · letI := hE
    have hpw : Q ^ (2 * e') = 2 ^ (labL.n * (2 * e')) := by rw [← hQdef, ← pow_mul]
    rw [hpw] at hcardE
    exact compType_of_quot_statedSL hJ.2.2 hb2 hcardE ⟨eM⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem compType_symp_data {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    (hcen : Subgroup.center S = ⊥) (ht : labL.tag = .B ∨ labL.tag = .C)
    (hin : InnDiagKind S labL β) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (r : ℕ) (_ : 2 ≤ r),
      1 ≤ labL.n ∧ Nat.card F = 2 ^ labL.n ∧ (2 : F) = 0 ∧
      ∃ (e : S ≃* StatedProj (StatedSp r F)) (A : gsp r F),
        ∀ l : S, e (β l) = conjAut r F A (e l) := by
  obtain ⟨F, hF, hFf, r, hr, hcard, e, A, hαA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CanonTriL.innDiagKind_symp_data_BC hcen ht hin
  have hn : 1 ≤ labL.n := by
    rcases Nat.eq_zero_or_pos labL.n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : F) = 0 := by
    haveI := Fintype.ofFinite F
    obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' F
    have hc := hcard
    rw [Nat.card_eq_fintype_card, hqcard] at hc
    have hdvd : q ∣ 2 ^ labL.n := by
      rw [← hc]
      exact dvd_pow_self q (PNat.ne_zero k)
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero F 2
  exact ⟨F, hF, hFf, r, hr, hn, hcard, h2, e, A, hαA⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem compType_symp {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (ht : labL.tag = .B ∨ labL.tag = .C) (hin : InnDiagKind S labL β) (hβp : β ^ p = 1)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  obtain ⟨F, hF, hFf, r, hr, hn, hcard, h2, e, A, hαA⟩ := compType_symp_data hcen ht hin
  letI := hF
  letI := hFf
  obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e β = MulAut.conj (proj r F x) := by
    rw [← hx]
    ext z
    have h1 := hαA (e.symm z)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp r F)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj r F x) ^ p = 1 := by
    rw [← hMEq, ← map_pow, hβp, map_one]
  have hxp : x ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e β hJ
  rw [hMEq] at hJ'
  obtain ⟨-, hcomp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hcard (by omega) hp2 (fun h => h.elim) x hxp
  obtain ⟨X, inst, hXfin, ⟨hXLie, -⟩, hfac, f, hf, hker⟩ := hcomp _ hJ'
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect f hf hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hSp42
  · rw [hcard] at hSL
    obtain ⟨b, k, E, _, _, hb, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.linCase_of_factor eJ hSL
    exact compType_of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (compType_of_quot_statedSL hJ'.2.2 hb hE hφ)
  · rw [hcard] at hSU
    obtain ⟨b, k, E, _, _, τ, hτ, hb, hτk, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJ hSU
    exact compType_of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (compType_of_quot_heldSU hJ'.2.2 τ hτ hb hτk hE hφ)
  · obtain ⟨-, -, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hne' : ¬(s = 2 ∧ Nat.card F = 2) := fun h => hne (by rw [h.1, h.2])
    have hchar : CharP F 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hcard
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
      (s := s) hs2 hne' hchar eX
    exact compType_of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (compType_of_quot_statedSp hs2 hcard hne' (eJ.trans eXZ))
  · obtain ⟨-, -, hK2, ⟨eX⟩⟩ := hSp42
    exact compType_of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (compType_of_quot_sp42 hK2 eX eJ)

open CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel in
theorem compType_orth {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hF : FamOrth labL)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  obtain ⟨hmodel, a, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
  have hap : a ^ p = 1 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.pow_eq_one_of_conj_pow_eq_one
    hcen hβp
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t labL.rank 2 (canonLabel labL).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  obtain ⟨X, inst, -, hXLie, hfac, -, g, hg, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_conj_omega_card
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorField_holds
      hp hp2 (Or.inr ht) hG hp2 a hap J hJ
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect g hg hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hOm
  · obtain ⟨b, k, E, _, _, hb, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.linCase_of_factor eJ hSL
    exact compType_of_quot_statedSL hJ.2.2 hb hE hφ
  · obtain ⟨b, k, E, _, _, τ, hτ, hb, hτk, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJ hSU
    exact compType_of_quot_heldSU hJ.2.2 τ hτ hb hτk hE hφ
  · obtain ⟨K', _, _, hK'card, hK'ring, s, hs2, hne, ⟨eX⟩⟩ := hSp
    haveI : Finite K' := Finite.of_fintype K'
    have hchar : CharP K' 2 := ringChar.of_eq hK'ring
    have hne' : ¬(s = 2 ∧ Nat.card K' = 2) := fun h => hne (by rw [h.1, h.2])
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
      (s := s) hs2 hne' hchar eX
    exact compType_of_quot_statedSp hs2 hK'card hne' (eJ.trans eXZ)
  · obtain ⟨K', _, _, V, _, _, _, Q, hK'card, _, hQ, hd, hT, ⟨eX⟩⟩ := hOm
    obtain ⟨s, hs⟩ :=
      exists_statedClassicalModel_quotCenter_orthDerived hK'card hQ hd hT eX
    rcases hs with hplus | hminus
    · exact compType_of_orthModel
        (Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hplus))
    · exact compType_of_orthModel
        (Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hminus))

end Families

end CFSG.LocalAnalysis.GLTheoremA.I141F.Cls
