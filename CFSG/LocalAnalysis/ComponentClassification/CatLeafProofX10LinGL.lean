module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSL

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel centralModel_SL)

@[expose] def linInnerTuples (n f : ℕ) : Set (StatedLieTag × ℕ × ℕ) :=
  {x | (∃ k, Odd k ∧ 3 ≤ k ∧ k < n ∧ x = (.PSL, k, f)) ∨ (Even n ∧ x = (.PSL, n / 2, 2 * f))}

theorem centralModel_GL_component_two_le {k : Type} [Field k] [Finite k] {ℓ j n : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j) (hn : 2 ≤ n)
    (h3 : n ≠ 2 ∨ Nat.card k ≠ 3) {L : Subgroup (GL (Fin n) k)} (hL : IsComponent L) :
    CentralModel ℓ .PSL n j L := by
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  have hq3 := OddInner.three_le_pow hℓ hℓ2 hj
  have h2 : n ≠ 2 ∨ Nat.card k ≠ 2 := Or.inr (by omega)
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k hn h2 h3 L
    hL.2
  have hadm : StatedLieAdmissible .PSL n ℓ j :=
    OddInner.admissible_PSL hℓ hj hn (by rw [← hk]; exact h2) (by rw [← hk]; exact h3)
  exact (centralModel_SL hadm hk).of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem neg_one_mem_specialLinearRange {K : Type} [Field K] {r : ℕ} (hr : Even r) :
    (-1 : GL (Fin r) K) ∈ CatalogueBGeneralLinear.specialLinearRange r K := by
  have hdet : (-1 : Matrix (Fin r) (Fin r) K).det = 1 := by
    rw [Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin, hr.neg_one_pow]
  exact ⟨⟨-1, hdet⟩, Units.ext rfl⟩

theorem glFactor_component_cases {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {t : ℕ} (ht : 1 ≤ t) {M : Type}
    [Group M] (ρ : M →* GL (Fin t) K) (hρi : Function.Injective ρ)
    (hρc : IsComponent ρ.range) :
    (Even t ∧ ∃ x : M, ρ x = -1) ∨ (Odd t ∧ 3 ≤ t ∧ CentralModel p .PSL t f M) := by
  by_cases hsmall : t = 1 ∨ t = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable t K hsmall
    exact absurd hρc (OddInner.not_isComponent_of_isSolvable _)
  obtain ⟨ht2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters t K ht hsmall
  rcases Nat.even_or_odd t with he | ho
  · left
    have : Group.IsPerfect ρ.range := hρc.1.1
    have : Nontrivial ρ.range := LocalCores.isQuasisimple_nontrivial hρc.1
    have hrange := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange t K ht2 h22
      h23 ρ.range hρc.2
    obtain ⟨x, hx⟩ : (-1 : GL (Fin t) K) ∈ ρ.range :=
      hrange ▸ neg_one_mem_specialLinearRange he
    exact ⟨he, x, hx⟩
  · right
    have ht3 : 3 ≤ t := by
      obtain ⟨u, rfl⟩ := ho
      omega
    exact ⟨ho, ht3, (centralModel_GL_component_two_le hp hp2 hf hK ht2 h23 hρc).of_mulEquiv
      (MonoidHom.ofInjective hρi)⟩

theorem glProd_component_cases {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {M : Subgroup (GL (Fin r) K × GL (Fin s) K)} (hM : IsComponent M) :
    ((-1, 1) ∈ M ∨ (1, -1) ∈ M) ∨
      ∃ k, Odd k ∧ 3 ≤ k ∧ (k = r ∨ k = s) ∧ CentralModel p .PSL k f M := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hM with h2 | h1
  · obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hM h2
    rcases glFactor_component_cases hp hp2 hf hK hr ρ hρi hρc with ⟨-, x, hx⟩ | ⟨ho, h3, hm⟩
    · left
      left
      have hx' : (x : GL (Fin r) K × GL (Fin s) K) = (-1, 1) :=
        Prod.ext ((hρ x).symm.trans hx) (h2 x x.2)
      exact hx' ▸ x.2
    · exact Or.inr ⟨r, ho, h3, Or.inl rfl, hm⟩
  · have h1' : ∀ x ∈ M, (MulEquiv.prodComm x).2 = 1 := h1
    obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hM h1'
    rcases glFactor_component_cases hp hp2 hf hK hs ρ hρi hρc with ⟨-, x, hx⟩ | ⟨ho, h3, hm⟩
    · left
      right
      have hx' : (x : GL (Fin r) K × GL (Fin s) K) = (1, -1) :=
        Prod.ext (h1 x x.2) ((hρ x).symm.trans hx)
      exact hx' ▸ x.2
    · exact Or.inr ⟨s, ho, h3, Or.inr rfl, hm⟩

theorem neg_one_comm {K : Type} [Field K] {t : ℕ} (g : GL (Fin t) K) : -1 * g = g * -1 := by
  rw [neg_one_mul, mul_neg_one]

theorem coe_eq_of_one_eq_scalar {K : Type} [Field K] {t : ℕ} (ht : 1 ≤ t) {c : Kˣ}
    (h : (1 : GL (Fin t) K) = GeneralLinearGroup.scalar (Fin t) c) : (c : K) = 1 := by
  have h0 := congrArg (fun g : GL (Fin t) K => (g : Matrix (Fin t) (Fin t) K) ⟨0, ht⟩ ⟨0, ht⟩) h
  simp at h0
  exact h0.symm

theorem coe_eq_of_neg_one_eq_scalar {K : Type} [Field K] {t : ℕ} (ht : 1 ≤ t) {c : Kˣ}
    (h : (-1 : GL (Fin t) K) = GeneralLinearGroup.scalar (Fin t) c) : (c : K) = -1 := by
  have h0 := congrArg (fun g : GL (Fin t) K => (g : Matrix (Fin t) (Fin t) K) ⟨0, ht⟩ ⟨0, ht⟩) h
  simp at h0
  exact h0.symm

theorem glCentralizer_component_cases {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (A : GL (Fin n) K) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) (lambda : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) lambda)
    {M : Subgroup (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))} (hM : IsComponent M) :
    (∃ z ∈ M, (∀ y ∈ M, z * y = y * z) ∧ z * z = 1 ∧
      ∀ c : Kˣ, (z : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c) ∨
    ModelIn p (linInnerTuples n f) M := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, hrs, e, -, he, -, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A lambda h2
        hne hsq hsquare
    have hcent : ∀ x : Subgroup.centralizer ({A} : Set (GL (Fin n) K)),
        (e x = (-1, 1) ∨ e x = (1, -1)) → x ∈ M →
          (∀ y ∈ M, x * y = y * x) ∧ x * x = 1 ∧
            ∀ c : Kˣ, (x : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c := by
      intro x hx _
      refine ⟨fun y _ => e.injective ?_, e.injective ?_, fun c hc => ?_⟩
      · rw [map_mul, map_mul]
        rcases hx with hx | hx <;> rw [hx] <;>
          exact Prod.ext (by simp) (by simp)
      · rw [map_mul, map_one]
        rcases hx with hx | hx <;> rw [hx] <;> exact Prod.ext (by simp) (by simp)
      · have hxs : x = CatalogueBProjectiveInvolution.ordinaryCentralizerScalar A c :=
          Subtype.ext hc
        have hes := he c
        rw [← hxs] at hes
        rcases hx with hx | hx <;> rw [hx] at hes <;> obtain ⟨h₁, h₂⟩ := Prod.mk.inj hes
        · exact h2 (by linear_combination (coe_eq_of_neg_one_eq_scalar hr h₁) -
            (coe_eq_of_one_eq_scalar hs h₂))
        · exact h2 (by linear_combination (coe_eq_of_neg_one_eq_scalar hs h₂) -
            (coe_eq_of_one_eq_scalar hr h₁))
    have hMe := LocalCores.isComponent_map_mulEquiv e hM
    rcases glProd_component_cases hp hp2 hf hK hr hs hMe with h | ⟨k, ho, h3, hk, hm⟩
    · left
      have hmem : ∃ x ∈ M, e x = (-1, 1) ∨ e x = (1, -1) := by
        rcases h with h | h
        · obtain ⟨x, hxM, hx⟩ := Subgroup.mem_map.1 h
          exact ⟨x, hxM, Or.inl hx⟩
        · obtain ⟨x, hxM, hx⟩ := Subgroup.mem_map.1 h
          exact ⟨x, hxM, Or.inr hx⟩
      obtain ⟨x, hxM, hx⟩ := hmem
      exact ⟨x, hxM, hcent x hx hxM⟩
    · right
      refine ⟨.PSL, k, f, Or.inl ⟨k, ho, h3, ?_, rfl⟩,
        hm.of_mulEquiv (M.equivMapOfInjective e.toMonoidHom e.injective)⟩
      omega
  · right
    let : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite lambda.val
    have hmd := CatalogueBProjectiveQuadratic.matrixDimension_twice A lambda hsq
    rw [Fintype.card_fin] at hmd
    set m := CatalogueBProjectiveQuadratic.matrixDimension A lambda hsq
    have hE : Nat.card (CatalogueBProjectiveQuadratic.extension lambda.val) = p ^ (2 * f) := by
      rw [OddInner.card_extension, hK, ← pow_mul, mul_comm]
    have hE9 : 9 ≤ p ^ (2 * f) := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left (OddInner.three_le_pow hp hp2 hf) 2
    refine modelIn_of_component_equiv
      (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq)
      (fun N hN => ?_) hM
    rcases Nat.lt_or_ge m 2 with h1 | h2'
    · exfalso
      have := CatalogueBGeneralLinear.generalLinear_small_solvable m
        (CatalogueBProjectiveQuadratic.extension lambda.val) (Or.inl (by omega))
      exact OddInner.not_isComponent_of_isSolvable N hN
    · exact ⟨.PSL, m, 2 * f, Or.inr ⟨⟨m, by omega⟩, by rw [show n / 2 = m by omega]⟩,
        centralModel_GL_component_two_le hp hp2 (by omega) hE h2' (Or.inr (by omega)) hN⟩

end CFSG.ComponentClassification.CatLeafProof.X10Lin
