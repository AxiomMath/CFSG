module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutLift
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
public import CFSG.ClassicalInvolution.ModelFacts.CentralLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.Assembly.LowTwoRank
open scoped Matrix

section Group

theorem eq_one_of_perfect_center {K G : Type*} [Group K] [Group.IsPerfect K] [Group G]
    (f : K →* Subgroup.center G) : f = 1 := by
  have hp : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext x
  have h1 : (⟨f x, x, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1

theorem eq_of_inv_mul_mem_center {K G : Type*} [Group K] [Group.IsPerfect K] [Group G]
    (M N : K →* G) (h : ∀ x, (N x)⁻¹ * M x ∈ Subgroup.center G) : N = M := by
  let f : K →* Subgroup.center G :=
    { toFun := fun x => ⟨(N x)⁻¹ * M x, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.mp (h x) (N y)⁻¹
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        calc (N y)⁻¹ * (N x)⁻¹ * (M x * M y)
            = (N y)⁻¹ * ((N x)⁻¹ * M x) * M y := by group
          _ = (N x)⁻¹ * M x * (N y)⁻¹ * M y := by rw [hc]
          _ = (N x)⁻¹ * M x * ((N y)⁻¹ * M y) := by group }
  have h1 : f = 1 := eq_one_of_perfect_center f
  ext x
  have h2 := congrArg (fun g : K →* Subgroup.center G => ((g x : Subgroup.center G) : G)) h1
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, Subgroup.coe_one] at h2
  exact (inv_mul_eq_one.mp h2)

theorem map_center_eq_center {K : Type*} [Group K] (α : K ≃* K) :
    Subgroup.map (α : K →* K) (Subgroup.center K) = Subgroup.center K := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg α (Subgroup.mem_center_iff.mp hx (α.symm g))
    simpa using h2
  · intro hy
    refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg α.symm (Subgroup.mem_center_iff.mp hy (α g))
    simpa using h2

theorem exists_descend {K P : Type*} [Group K] [Group P] (π : K →* P)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K) (α : K ≃* K) :
    ∃ β : P ≃* P, ∀ x, β (π x) = π (α x) := by
  have hα : Subgroup.map (α : K →* K) π.ker = π.ker := by
    rw [hker]
    exact map_center_eq_center α
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨e.symm.trans ((QuotientGroup.congr π.ker π.ker α hα).trans e), fun x => ?_⟩
  have h1 : e.symm (π x) = (QuotientGroup.mk x : K ⧸ π.ker) := e.symm_apply_eq.mpr rfl
  rw [MulEquiv.trans_apply, h1, MulEquiv.trans_apply, QuotientGroup.congr_mk]
  rfl

end Group

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem spin_aut_similarity (Q : QuadraticForm F (ι → F)) {Q₀ : (ι → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀) [Group.IsPerfect (spinGroup Q)]
    (hsurj : Function.Surjective (spinToStatedProj Q hR))
    (hker : (spinToStatedProj Q hR).ker = Subgroup.center (spinGroup Q))
    (hsim : ∀ β : MulAut (StatedProj (StatedOmega Q₀)),
      ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
        ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
          (y : GL ι F) = A * glFieldEquiv ι φ (x : GL ι F) * A⁻¹ ∧
            β (QuotientGroup.mk x) = QuotientGroup.mk y)
    (α : spinGroup Q ≃* spinGroup Q) :
    ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
      ∀ x, spinMatrix Q (α x) = A * glFieldEquiv ι φ (spinMatrix Q x) * A⁻¹ := by
  obtain ⟨β, hβ⟩ := exists_descend (spinToStatedProj Q hR) hsurj hker α
  obtain ⟨A, φ, μ, hQ, hA⟩ := hsim β
  refine ⟨A, φ, μ, hQ, fun x => ?_⟩
  let M : spinGroup Q →* GL ι F := (MulAut.conj A).toMonoidHom.comp
    ((glFieldEquiv ι φ).toMonoidHom.comp (spinMatrix Q))
  have hN : (spinMatrix Q).comp α.toMonoidHom = M := by
    refine eq_of_inv_mul_mem_center M _ fun x => ?_
    obtain ⟨y, hy, hβy⟩ := hA ⟨spinMatrix Q x, spinMatrix_mem_of_range_eq Q hR x⟩
    have h1 := hβ x
    rw [spinToStatedProj_apply, spinToStatedProj_apply] at h1
    rw [h1] at hβy
    have h2 := QuotientGroup.eq.mp hβy
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : (((⟨spinMatrix Q (α x), spinMatrix_mem_of_range_eq Q hR (α x)⟩ :
        StatedOmega Q₀)⁻¹ * y : StatedOmega Q₀) : GL ι F) =
        (spinMatrix Q (α x))⁻¹ * M x := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy]
      rfl
    rw [h3] at h2
    show (spinMatrix Q (α x))⁻¹ * M x ∈ Subgroup.center (GL ι F)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact h2
  exact DFunLike.congr_fun hN x

end Generic

section Center

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem scalar_injective_of_nonempty [Nonempty ι] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Fˣ →* GL ι F) := by
  intro a b h
  obtain ⟨i⟩ := ‹Nonempty ι›
  apply Units.ext
  have := congrArg (fun M : GL ι F => (M : Matrix ι ι F) i i) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar] using this

theorem not_dvd_card_center_spin [Nonempty ι] (Q : QuadraticForm F (ι → F)) {Q₀ : (ι → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀) [Finite (spinGroup Q)]
    (hker : (spinToStatedProj Q hR).ker = Subgroup.center (spinGroup Q))
    (hcomap : (spinToStatedProj Q hR).ker = (StatedScalars ι F).comap (spinMatrix Q))
    (hker2 : ∀ x ∈ (spinMatrix Q).ker, x * x = 1) {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Subgroup.center (spinGroup Q)) := by
  refine not_dvd_card_center_of_forall (p := p) fun x hx hxp => ?_
  have hx' : x ∈ (StatedScalars ι F).comap (spinMatrix Q) := by
    rw [← hcomap, hker]
    exact hx
  obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hx'
  have hcp : c ^ p = 1 := by
    apply scalar_injective_of_nonempty (ι := ι)
    rw [map_pow, hc, ← map_pow, hxp, map_one, map_one]
  have hc1 : c = 1 := by
    apply Units.ext
    have h0 : ((c : F) - 1) ^ p = 0 := by
      rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hcp]
      simp
    have := pow_eq_zero_iff (n := p) (Fact.out : p.Prime).ne_zero |>.mp h0
    simpa [sub_eq_zero] using this
  have hxm : spinMatrix Q x = 1 := by
    rw [← hc, hc1, map_one]
  have hk : x * x = 1 := hker2 x hxm
  obtain ⟨k, hk'⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  calc x = x ^ p := by
        rw [hk', pow_succ, pow_mul, sq, hk, one_pow, one_mul]
    _ = 1 := hxp

end Center

section Types

theorem spin_mul_self_eq_one {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {x : spinGroup Q}
    (h : x = 1 ∨ (x : CliffordAlgebra Q) = -1) : x * x = 1 := by
  rcases h with rfl | h
  · exact one_mul 1
  · apply Subtype.ext
    change (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) = 1
    rw [h]
    simp

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem spinOdd_aut_similarity (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (α : spinGroup (quadOdd n F) ≃* spinGroup (quadOdd n F)) :
    ∃ (A : GL (Fin n ⊕ Fin n ⊕ Unit) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadOdd n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadOdd n F v)) ∧
      ∀ x, spinMatrix (quadOdd n F) (α x) =
        A * glFieldEquiv _ φ (spinMatrix (quadOdd n F) x) * A⁻¹ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have : Group.IsPerfect (spinGroup (quadOdd n F)) := isPerfect_spinGroup_quadOdd h2 hn
  obtain ⟨hsurj, -, hker⟩ := spinToStatedProj_quadOdd h2 hn
  exact spin_aut_similarity (quadOdd n F) (range_spinMatrix_quadOdd h2 hn) hsurj hker
    (fun β => exists_similarity_odd ⟨Fact.out, hf, hn, hp2⟩ hF β) α

omit [CharP F p] in
theorem spinPlus_aut_similarity {n : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (α : spinGroup (quadPlus n F) ≃* spinGroup (quadPlus n F)) :
    ∃ (A : GL (Fin n ⊕ Fin n) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadPlus n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus n F v)) ∧
      ∀ x, spinMatrix (quadPlus n F) (α x) =
        A * glFieldEquiv _ φ (spinMatrix (quadPlus n F) x) * A⁻¹ := by
  have hn3 : 3 ≤ n := by omega
  have : Group.IsPerfect (spinGroup (quadPlus n F)) := isPerfect_spinGroup_quadPlus hn3
  obtain ⟨hsurj, -, hker⟩ := spinToStatedProj_quadPlus (K := F) hn3
  exact spin_aut_similarity (quadPlus n F) (range_spinMatrix_quadPlus hn3) hsurj hker
    (fun β => exists_similarity_plus ⟨Fact.out, hf, by omega⟩ hn hF β) α

omit [CharP F p] in
theorem spinMinus_aut_similarity {n : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c)) :
    ∃ (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadMinus n F b c (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadMinus n F b c v)) ∧
      ∀ x, spinMatrix (quadMinus n F b c) (α x) =
        A * glFieldEquiv _ φ (spinMatrix (quadMinus n F b c) x) * A⁻¹ := by
  have : Group.IsPerfect (spinGroup (quadMinus n F b c)) := isPerfect_spinGroup_quadMinus hn hirr
  obtain ⟨hsurj, -, hker⟩ := spinToStatedProj_quadMinus hn hirr
  exact spin_aut_similarity (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr) hsurj hker
    (fun β => exists_similarity_minus ⟨Fact.out, hf, hn⟩ hF hirr β) α

theorem spinOdd_exists_lift_similarity (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (θ : spinGroup (quadOdd n F) →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd n F)))
    (σ : X ≃* X) :
    ∃ α : spinGroup (quadOdd n F) ≃* spinGroup (quadOdd n F), (∀ x, θ (α x) = σ (θ x)) ∧
      ∃ (A : GL (Fin n ⊕ Fin n ⊕ Unit) F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v, quadOdd n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadOdd n F v)) ∧
        ∀ x, spinMatrix (quadOdd n F) (α x) =
          A * glFieldEquiv _ φ (spinMatrix (quadOdd n F) x) * A⁻¹ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have : Finite (spinGroup (quadOdd n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Nonempty (Fin n ⊕ Fin n ⊕ Unit) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadOdd h2 hn
  have hC : ¬ p ∣ Nat.card θ.ker := fun hd =>
    not_dvd_card_center_spin (quadOdd n F) (range_spinMatrix_quadOdd h2 hn) hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2
      (hd.trans (Subgroup.card_dvd_of_le hker))
  obtain ⟨α, hα⟩ := (centralPSection_spinOdd hp2 hn).exists_mulEquiv_lift θ hθ hker hC σ
  exact ⟨α, hα, spinOdd_aut_similarity hp2 hn hf hF α⟩

theorem spinPlus_exists_lift_similarity (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (θ : spinGroup (quadPlus n F) →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus n F)))
    (σ : X ≃* X) :
    ∃ α : spinGroup (quadPlus n F) ≃* spinGroup (quadPlus n F), (∀ x, θ (α x) = σ (θ x)) ∧
      ∃ (A : GL (Fin n ⊕ Fin n) F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v, quadPlus n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus n F v)) ∧
        ∀ x, spinMatrix (quadPlus n F) (α x) =
          A * glFieldEquiv _ φ (spinMatrix (quadPlus n F) x) * A⁻¹ := by
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := F) hn3
  have hC : ¬ p ∣ Nat.card θ.ker := fun hd =>
    not_dvd_card_center_spin (quadPlus n F) (range_spinMatrix_quadPlus hn3) hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2
      (hd.trans (Subgroup.card_dvd_of_le hker))
  obtain ⟨α, hα⟩ := (centralPSection_spinPlus hn3).exists_mulEquiv_lift θ hθ hker hC σ
  exact ⟨α, hα, spinPlus_aut_similarity hn hf hF α⟩

theorem spinMinus_exists_lift_similarity (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type}
    [Group X] (θ : spinGroup (quadMinus n F b c) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) (σ : X ≃* X) :
    ∃ α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c),
      (∀ x, θ (α x) = σ (θ x)) ∧
      ∃ (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v, quadMinus n F b c (A.val *ᵥ (fun i => φ (v i))) =
          μ * φ (quadMinus n F b c v)) ∧
        ∀ x, spinMatrix (quadMinus n F b c) (α x) =
          A * glFieldEquiv _ φ (spinMatrix (quadMinus n F b c) x) * A⁻¹ := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus hn hirr
  have hC : ¬ p ∣ Nat.card θ.ker := fun hd =>
    not_dvd_card_center_spin (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr) hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadMinus_iff hirr x).mp hx)) hp2
      (hd.trans (Subgroup.card_dvd_of_le hker))
  obtain ⟨α, hα⟩ := (centralPSection_spinMinus hp2 hn hirr).exists_mulEquiv_lift θ hθ hker hC σ
  exact ⟨α, hα, spinMinus_aut_similarity hn hf hF hirr α⟩

end Types

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
