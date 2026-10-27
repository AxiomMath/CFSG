module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

private theorem mulAut_congr_conj' {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.conj_apply]

private theorem exists_card_pow_of_charP {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = p ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, -, hK⟩ := FiniteField.card K p
  exact ⟨(f : ℕ), f.pos, by rw [Nat.card_eq_fintype_card, hK]⟩

private theorem conjAut_eq_conj_proj_of_pow_eq_scalar {n : ℕ} {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p] {A : Matrix.GeneralLinearGroup (Fin n) K} {c : Kˣ}
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

private theorem perfectInLayer_projectiveSL_outer {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    {β : MulAut (LinearFlag.projectiveSL n K)} (hβ : β ^ p = 1)
    (hout : ∀ a : LinearFlag.projectiveSL n K, MulAut.conj a ≠ β) : PerfectInLayer β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hf, hK⟩ := exists_card_pow_of_charP (K := K) p
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    (ℓ := p) (f := f) hp hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n K
  · exfalso
    obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.1 hlin
    have hAp : A ^ p ∈ (LinearFlag.conjAut n K).ker := by
      rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    obtain ⟨g, hg⟩ := conjAut_eq_conj_proj_of_pow_eq_scalar hc.symm
    exact hout (LinearFlag.proj n K g) hg.symm
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
    rw [hβτ]
    exact LieSemisimple.perfectInLayer_conj h _
      (LieSemisimple.perfectInLayer_fieldAut hn hp hp2 τ hτ)

private theorem perfectInLayer_projectiveSL_two_outer {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) [CharP K p] {β : MulAut (LinearFlag.projectiveSL 2 K)} (hβ : β ^ p = 1)
    (hout : ∀ a : LinearFlag.projectiveSL 2 K, MulAut.conj a ≠ β) : PerfectInLayer β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (PSL2 K),
      MulAut.congr (LieSemisimple.psl2Equiv K) β₀ = β :=
    ⟨(MulAut.congr (LieSemisimple.psl2Equiv K)).symm β,
      (MulAut.congr (LieSemisimple.psl2Equiv K)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ p = 1 :=
    (MulAut.congr (LieSemisimple.psl2Equiv K)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  have hcongr : ∀ A : Matrix.GeneralLinearGroup (Fin 2) K,
      MulAut.congr (LieSemisimple.psl2Equiv K) (pglAction K (Matrix.ProjGenLinGroup.mk A)) =
        LinearFlag.conjAut 2 K A :=
    fun A => LieSemisimple.congr_pglAction_mk A
  by_cases hD : β₀ ∈ (pglAction K).range
  · exfalso
    obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 K A := by
      rw [← hββ₀, ← hg]
      exact hcongr A
    have hAp : A ^ p ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) := by
      have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ p)) = pglAction K 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    obtain ⟨g', hg'⟩ := conjAut_eq_conj_proj_of_pow_eq_scalar hc.symm
    exact hout (LinearFlag.proj 2 K g') (hg'.symm.trans hβA.symm)
  · have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = p := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, -, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent hp β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβ' : β = LinearFlag.conjAut 2 K A * LinearFlag.fieldAut 2 K σ *
        (LinearFlag.conjAut 2 K A)⁻¹ := by
      rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, LieSemisimple.congr_psl2FieldAut]
    rw [hβ']
    exact LieSemisimple.perfectInLayer_conj _ _ (LieSemisimple.perfectInLayer_fieldAut_two σ)

theorem perfectInLayer_A_outer (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  subst hpc
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  refine LieSemisimple.perfectInLayer_of_congr e' β ?_
  have hβ' : MulAut.congr e' β ^ q.p = 1 := by
    rw [← map_pow, hβ, map_one]
  have hout' : ∀ a : LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent),
      MulAut.conj a ≠ MulAut.congr e' β := by
    intro a ha
    apply hout (e'.symm a)
    apply (MulAut.congr e').injective
    rw [mulAut_congr_conj', e'.apply_symm_apply]
    exact ha
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · obtain rfl : r = 1 := by omega
    exact perfectInLayer_projectiveSL_two_outer hp hβ' hout'
  · exact perfectInLayer_projectiveSL_outer (by omega) hp hp2 hβ' hout'

end CFSG.HardMathSupport.Dickson.DefCharOuter
