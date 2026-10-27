module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.RankThree.PartTwo.KFacts.K72OutL3
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns

@[expose] def IsConjByGL' {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F))
    (φ : MulAut (StatedProj H)) : Prop :=
  ∃ g ∈ Subgroup.normalizer (H : Set (GL (Fin 3) F)), ∀ A A' : ↥H,
    (A' : GL (Fin 3) F) = g * (A : GL (Fin 3) F) * g⁻¹ →
      φ (QuotientGroup.mk A) = QuotientGroup.mk A'

theorem isConjByGL_iff {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F))
    (φ : MulAut (StatedProj H)) : IsConjByGL H φ ↔ IsConjByGL' H φ :=
  Iff.rfl

theorem mem_statedSL_iff {n : ℕ} {F : Type} [Field F] {x : GL (Fin n) F} :
    x ∈ StatedSL n F ↔ (x : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem mem_normalizer_statedSL {n : ℕ} {F : Type} [Field F] (A : GL (Fin n) F) :
    A ∈ Subgroup.normalizer (StatedSL n F : Set (GL (Fin n) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_statedSL_iff, mem_statedSL_iff, Units.val_mul, Units.val_mul, Matrix.det_units_conj]

@[expose] noncomputable def psiPSL (F : Type) [Field F] :
    StatedProj (StatedSL 3 F) ≃* projectiveSL 3 F :=
  (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)

theorem psiPSL_mk (F : Type) [Field F] (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    psiPSL F (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s)) = proj 3 F s := by
  unfold psiPSL
  rw [MulEquiv.trans_apply]
  have h : (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s)) = QuotientGroup.mk s := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h]
  rfl

theorem isConjByGL_of_congr_eq_conjAut (F : Type) [Field F]
    (γ : MulAut (StatedProj (StatedSL 3 F))) (A : GL (Fin 3) F)
    (h : MulAut.congr (psiPSL F) γ = conjAut 3 F A) : IsConjByGL' (StatedSL 3 F) γ := by
  refine ⟨A, mem_normalizer_statedSL A, fun x x' hx => ?_⟩
  obtain ⟨s, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective x
  obtain ⟨s', rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective x'
  apply (psiPSL F).injective
  have h1 : psiPSL F (γ (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s))) =
      conjAut 3 F A (psiPSL F (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s))) := by
    have := congrArg (fun τ => τ (psiPSL F
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s)))) h
    simpa [MulAut.congr_apply] using this
  rw [h1, psiPSL_mk, psiPSL_mk, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hx
  simpa [Units.val_mul, specialLinearGroupEquivStatedSL_coe] using this.symm

theorem isConjByGL_commutator_psl (F : Type) [Field F] [Finite F]
    (a b : MulAut (StatedProj (StatedSL 3 F))) :
    IsConjByGL' (StatedSL 3 F) (a * b * a⁻¹ * b⁻¹) := by
  have h := OuterDerived.commutator_mem_linearAutGroup (K := F) (n := 3) le_rfl
    (MulAut.congr (psiPSL F) a) (MulAut.congr (psiPSL F) b)
  rw [linearAutGroup_eq_range] at h
  obtain ⟨A, hA⟩ := h
  refine isConjByGL_of_congr_eq_conjAut F _ A ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hA.symm

section Unitary

variable {p f : ℕ} {F : Type} [Field F]

theorem isConjByGL_of_congr_eq_psuConj {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (γ : MulAut (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) F))) (A : unitaryIsom3 h)
    (hγ : MulAut.congr (unitaryPSUEquiv h (n := 3) (by norm_num)).symm γ = psuConj h A) :
    IsConjByGL' (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) F) γ := by
  set ψ := unitaryPSUEquiv h (n := 3) (by norm_num) with hψ
  refine ⟨(A : GL (Fin 3) F), ?_, fun x x' hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact conj_mem_unitarySU A.2 hy
    · intro hy
      have := conj_mem_unitarySU (inv_mem A.2) hy
      simpa [mul_assoc] using this
  · have key : ∀ z : CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) F),
        γ z = ψ (psuConj h A (ψ.symm z)) := by
      intro z
      have := congrArg (fun τ => τ (ψ.symm z)) hγ
      simp only [MulAut.congr_apply, MulEquiv.symm_symm] at this
      rw [← this]
      simp
    have hx1 : ψ.symm (QuotientGroup.mk x) = unitaryProj h 3 x := by
      rw [MulEquiv.symm_apply_eq, hψ, unitaryPSUEquiv_unitaryProj]
    rw [key, hx1]
    have : psuConj h A (unitaryProj h 3 x) =
        unitaryProj h 3 ⟨(A : GL (Fin 3) F) * x * (A : GL (Fin 3) F)⁻¹,
          conj_mem_unitarySU A.2 x.2⟩ := rfl
    rw [this, hψ, unitaryPSUEquiv_unitaryProj]
    congr 1
    exact Subtype.ext hx.symm

theorem isConjByGL_commutator_psu (h : UnitaryFieldData p f F) (hq : 2 < p ^ f)
    (a b : MulAut (StatedProj (StatedSU 3 (p ^ f) F))) :
    IsConjByGL' (StatedSU 3 (p ^ f) F) (a * b * a⁻¹ * b⁻¹) := by
  obtain ⟨A, hA⟩ := commutator_mem_psuConj_range h hq
    (MulAut.congr (unitaryPSUEquiv h (n := 3) (by norm_num)).symm a)
    (MulAut.congr (unitaryPSUEquiv h (n := 3) (by norm_num)).symm b)
  refine isConjByGL_of_congr_eq_psuConj h _ A ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hA.symm

end Unitary

theorem descend_compat {Y P : Type*} [Group Y] [Group P] (e : (Y ⧸ Subgroup.center Y) ≃* P)
    (α : MulAut Y) (y : Y) :
    e (QuotientGroup.mk (α y)) =
      MulAut.congr e (centerDescend Y α) (e (QuotientGroup.mk y)) := by
  simp [MulAut.congr_apply, centerDescend_mk]

theorem exists_unitaryFieldData {F : Type} [Field F] [Finite F] {q : ℕ}
    (hq : Nat.card F = q ^ 2) :
    ∃ p f : ℕ, q = p ^ f ∧ Nonempty (UnitaryFieldData p f F) := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ : ∃ p, CharP F p := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  rw [← Nat.card_eq_fintype_card] at hn
  have hdvd : q ∣ p ^ (n : ℕ) := by
    rw [← hn, hq]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨j, hj, hqj⟩ := (Nat.dvd_prime_pow hpp).1 hdvd
  have h2 : (n : ℕ) = 2 * j := by
    have : p ^ (n : ℕ) = p ^ (2 * j) := by
      rw [← hn, hq, hqj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hpp.two_le this
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      subst h0
      have : Nat.card F = 1 := by rw [hq, hqj]; simp
      have := Finite.one_lt_card (α := F)
      omega
    · exact h0
  exact ⟨p, j, hqj, ⟨⟨hpp, hj1, by rw [hn, h2]⟩⟩⟩

theorem input7_autQuotAbelian_holds : LocalBalance.Lemma53Ns.Input7_AutQuotAbelian := by
  intro Y _ _ hY hT α β
  rcases hT with ⟨F, _, _, ⟨e⟩⟩ | ⟨F, _, _, q, hcard, ⟨e⟩⟩
  · left
    refine ⟨F, inferInstance, inferInstance, e,
      MulAut.congr e (centerDescend Y (α * β * α⁻¹ * β⁻¹)), ?_, fun y => descend_compat e _ y⟩
    have h := isConjByGL_commutator_psl F (MulAut.congr e (centerDescend Y α))
      (MulAut.congr e (centerDescend Y β))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    exact h
  · right
    obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hq2 : 2 < p ^ f := by
      have hp := hF.prime
      have hf := hF.one_le
      by_contra hle
      push Not at hle
      have h2 : p ^ f = 2 := by
        have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        omega
      have h2' : p ^ f = 2 ^ 1 := by rw [h2]; rfl
      rw [h2'] at e
      have hsol : Group.IsSolvable (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 1) F)) :=
        CFSG.Quasithin.isSolvable_statedProj_one (by rw [hcard, h2'])
      have hsolQ : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have hsolY : Group.IsSolvable Y :=
        CFSG.Quasithin.isSolvable_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Y))
          (by rw [QuotientGroup.ker_mk'])
      have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hY.1
      have : Nontrivial Y := by
        have := hY.2.toNontrivial
        exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
      exact Group.IsPerfect.not_isSolvable Y hsolY
    refine ⟨F, inferInstance, inferInstance, p ^ f, e,
      MulAut.congr e (centerDescend Y (α * β * α⁻¹ * β⁻¹)), hcard, ?_, fun y => descend_compat e _ y⟩
    have h := isConjByGL_commutator_psu hF hq2 (MulAut.congr e (centerDescend Y α))
      (MulAut.congr e (centerDescend Y β))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    exact h

end CFSG.HardMathSupport.Solomon.Coordinator
