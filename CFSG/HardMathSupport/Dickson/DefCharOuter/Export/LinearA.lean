module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearModel
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem conjAut_eq_conj_proj_of_pow_eq_scalar' {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {A : Matrix.GeneralLinearGroup (Fin n) K} {c : Kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
      LinearFlag.conjAut n K A = MulAut.conj (LinearFlag.proj n K g) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ^ p = c := by
    have hcop := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.coprime_card_units (K := K) p
    refine ⟨(powCoprime hcop).symm c, ?_⟩
    have h := (powCoprime hcop).apply_symm_apply c
    rwa [powCoprime_apply] at h
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix.GeneralLinearGroup (Fin n) K,
      A' = Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A := ⟨_, rfl⟩
  have hA'p : A' ^ p = 1 := by
    rw [hA', (CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.scalar_commute' μ⁻¹ A).mul_pow, ← map_pow, hA,
      ← map_mul, inv_pow, hμ, inv_mul_cancel, map_one]
  have hMp : (A' : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hA'p]
    rfl
  have hdet : (A' : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h2 : (A' : Matrix (Fin n) (Fin n) K).det ^ p = 1 := by
      rw [← Matrix.det_pow, hMp, Matrix.det_one]
    have h3 : ((A' : Matrix (Fin n) (Fin n) K).det - 1) ^ p = 0 := by
      rw [sub_pow_char, h2, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h3)
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K) = (A' : Matrix (Fin n) (Fin n) K) :=
    ⟨⟨(A' : Matrix (Fin n) (Fin n) K), hdet⟩, rfl⟩
  refine ⟨g, ?_⟩
  have htoGL : Matrix.SpecialLinearGroup.toGL g = A' := Units.ext hg
  have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin n) μ * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [← LinearFlag.conjAut_toGL, htoGL, hAeq, map_mul,
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.conjAut_scalar', one_mul]

theorem exists_conj_fieldAut_of_outer {n p f : ℕ} (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = p ^ f)
    {β : MulAut (projectiveSL n K)} (hβ : β ^ p = 1) (hout : β ∉ innerAut (projectiveSL n K)) :
    ∃ (τ : K ≃+* K) (h : MulAut (projectiveSL n K)), orderOf τ = p ∧
      β = h * fieldAut n K τ * h⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  haveI : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    (ℓ := p) (f := f) hp hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n K
  · exfalso
    obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.1 hlin
    have hAp : A ^ p ∈ (LinearFlag.conjAut n K).ker := by
      rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    obtain ⟨g, hg⟩ := conjAut_eq_conj_proj_of_pow_eq_scalar' hc.symm
    exact hout ⟨LinearFlag.proj n K g, hg.symm⟩
  · obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ∈
        LinearFlag.semilinearAutGroup n K :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A))
        (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
    have hne : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ≠ 1 :=
      fun h => hlin (h ▸ one_mem _)
    have hord : orderOf (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) = p :=
      orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
        hp hf hn hK hp _ hmem hlin hord
    exact ⟨τ, h, hτ, hβτ⟩

theorem outerCentData_projectiveSL_of_three_le {n p f : ℕ} (hn : 3 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = p ^ f)
    {β : MulAut (projectiveSL n K)} (hβ : orderOf β = p) (hout : β ∉ innerAut (projectiveSL n K)) :
    OuterCentData p β := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  have hβp : β ^ p = 1 := hβ ▸ pow_orderOf_eq_one β
  obtain ⟨τ, h, hτ, rfl⟩ := exists_conj_fieldAut_of_outer hn hp hp2 hf hK hβp hout
  refine OuterCentData.of_conj hp h⁻¹ _ ?_
  have hf' : h⁻¹ * (h * fieldAut n K τ * h⁻¹) * h⁻¹⁻¹ = fieldAut n K τ := by group
  rw [hf']
  refine outerCentData_fieldAut_of_three_le hn hp hp2 hf hK hτ ?_
  rintro ⟨a, ha⟩
  apply hout
  refine ⟨h a, ?_⟩
  rw [← CFSG.HardMathSupport.Dickson.I271.mulAut_mul_conj_mul_inv, ha]

theorem outerCentData_A_of_two_le {r : ℕ} (hr : 2 ≤ r) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p = q.p) {β : MulAut S} (hβ : orderOf β = p) (hout : β ∉ innerAut S) :
    OuterCentData p β := by
  subst hpq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e' : S ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  refine OuterCentData.of_congr hp e' ?_
  refine outerCentData_projectiveSL_of_three_le (by omega) hp hp2 q.exponent_pos hK ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hβ
  · rintro ⟨g, hg⟩
    apply hout
    refine ⟨e'.symm g, ?_⟩
    apply (MulAut.congr e').injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e'.apply_symm_apply]
    exact hg

theorem exists_noncomm_of_isPerfect {G : Type*} [Group G] [Nontrivial G] (h : Group.IsPerfect G) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isSolvable (G := G) (Group.isSolvable_of_comm hcon)

theorem carrier_A (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid) :
    Finite (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group ∧
      IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group ∧
      ∃ a b : (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group, a * b ≠ b * a := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hcond : 3 ≤ r + 1 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    rcases Nat.lt_or_ge r 2 with h | h
    · right
      have h1 : r = 1 := by omega
      have h4 : 4 ≤ q.card := hr.2 h1
      rw [TauCeti.PrimePower.card_def, ← hK] at h4
      haveI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ] at h4
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
      exact ⟨t, ht⟩
    · left
      omega
  obtain ⟨hnt, hsimp, hfin⟩ := CFSG.LinearGroups.linear_projective_simple
    (K := GaloisField q.p q.exponent) (n := r + 1) (by omega) hcond
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := GaloisField q.p q.exponent)
    (n := r + 1) (by omega) hcond
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv
  haveI := hnt
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isPerfect hperf
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
