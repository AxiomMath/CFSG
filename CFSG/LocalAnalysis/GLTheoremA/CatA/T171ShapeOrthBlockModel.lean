module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonalModel
open CFSG.SeitzReduction.OmegaPilot

abbrev orthDModel (m n : ℕ) : TauCeti.LieTypeIndex → Prop :=
  fun i => ∃ q : TauCeti.PrimePower, i = .D m q ∧ q.card = 2 ^ n

abbrev orthTwistedDModel (m n : ℕ) : TauCeti.LieTypeIndex → Prop :=
  fun i => ∃ q : TauCeti.PrimePower, i = .twistedD m q ∧ q.card = 2 ^ n

theorem finite_projOrthDerived_of_finite {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite V] (Q : QuadraticForm K V) : Finite (ProjOrthDerived Q) := by
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  haveI : Finite (orthDerived Q) := inferInstance
  infer_instance

theorem exists_orthDModel_or_twistedDModel {S : Type} [Group S]
    (hcat : catalogIs S (onLie fun i => isOrthDIdx i ∧ i.characteristic = 2)) :
    (∃ m n : ℕ, catalogIs S (onLie (orthDModel m n))) ∨
      (∃ m n : ℕ, catalogIs S (onLie (orthTwistedDModel m n))) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | D m q =>
      left
      refine ⟨m, q.exponent, .lie ⟨.D m q, hv⟩, ⟨q, rfl, ?_⟩, ⟨e⟩⟩
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_D m q]
        exact hP.2
      rw [TauCeti.PrimePower.card_def, hq2]
  | twistedD m q =>
      right
      refine ⟨m, q.exponent, .lie ⟨.twistedD m q, hv⟩, ⟨q, rfl, ?_⟩, ⟨e⟩⟩
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_twistedD m q]
        exact hP.2
      rw [TauCeti.PrimePower.card_def, hq2]
  | _ => simp [isOrthDIdx] at hP

theorem largeEvenInduces_trans {L : Type*} [Group L] {R R' : Type} [Group R] [Group R']
    {θ : L ⧸ Subgroup.center L ≃* R} (e : R ≃* R') {rel : L → L → Prop} {φ : MulAut R}
    (h : LargeEvenInduces θ rel φ) :
    LargeEvenInduces (θ.trans e) rel (MulAut.congr e φ) := by
  intro l l' hl
  simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_apply_apply]
  rw [h l l' hl]

theorem mulAut_congr_conj {R R' : Type} [Group R] [Group R'] (e : R ≃* R') (r : R) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext x
  change e (r * e.symm x * r⁻¹) = e r * x * (e r)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem pow_eq_one_of_conj_pow_eq_one {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    {x : R} {p : ℕ} (h : (MulAut.conj x) ^ p = 1) : x ^ p = 1 := by
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  apply hinj
  rw [map_pow, h, map_one]

theorem mul_comm_of_conj_commute {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    {x y : R} (h : Commute (MulAut.conj x) (MulAut.conj y)) : x * y = y * x := by
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  apply hinj
  rw [map_mul, map_mul]
  exact h.eq

section Certificates


theorem orthModelMarking_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m n : ℕ} (hS : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) (onLie (orthDModel m n))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
          ProjOrthDerived (quadPlus m K),
        ∀ a ∈ A, ∃ x : ProjOrthDerived (quadPlus m K),
          LargeEvenInduces θ (conjRel a) (MulAut.conj x) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, θ, hBI⟩ := orthMarking_holds.1 G p L J A d b m n hS hcat
  letI := hKfield
  letI := hKfinite
  let e := orthModelEquivPlus m K
  refine ⟨K, hKfield, hKfinite, hKcard, θ.trans e, fun a ha => ?_⟩
  obtain ⟨x, hxmem, hind⟩ := hBI a ha
  obtain ⟨r, rfl⟩ := hxmem
  refine ⟨e r, ?_⟩
  have h := largeEvenInduces_trans e hind
  rw [mulAut_congr_conj] at h
  exact h

theorem orthModelMarking_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m n : ℕ} (hS : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) (onLie (orthTwistedDModel m n))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (b₀ c₀ : K), (∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
          ProjOrthDerived (quadMinus m K b₀ c₀),
        ∀ a ∈ A, ∃ x : ProjOrthDerived (quadMinus m K b₀ c₀),
          LargeEvenInduces θ (conjRel a) (MulAut.conj x) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, b₀, c₀, hbc, θ, hBI⟩ :=
    orthMarking_holds.2 G p L J A d b m n hS hcat
  letI := hKfield
  letI := hKfinite
  let e := orthModelEquivMinus m K b₀ c₀
  refine ⟨K, hKfield, hKfinite, hKcard, b₀, c₀, hbc, θ.trans e, fun a ha => ?_⟩
  obtain ⟨x, hxmem, hind⟩ := hBI a ha
  obtain ⟨r, rfl⟩ := hxmem
  refine ⟨e r, ?_⟩
  have h := largeEvenInduces_trans e hind
  rw [mulAut_congr_conj] at h
  exact h

theorem orthModelLifts_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m : ℕ} (K : Type) [Field K] [Finite K]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ProjOrthDerived (quadPlus m K))
    (hS : Setup p L J A d b) (hm4 : 4 ≤ m)
    (hBI : ∀ a ∈ A, ∃ x : ProjOrthDerived (quadPlus m K),
      LargeEvenInduces θ (conjRel a) (MulAut.conj x)) :
    ∃ x y : ProjOrthDerived (quadPlus m K),
      LargeEvenInduces θ (conjRel d) (MulAut.conj x) ∧
        LargeEvenInduces θ (conjRel b) (MulAut.conj y) ∧
          x ^ p = 1 ∧ y ^ p = 1 ∧ x * y = y * x := by
  haveI : Finite (ProjOrthDerived (quadPlus m K)) :=
    finite_projOrthDerived_of_finite (quadPlus m K)
  have hreg := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m) (by omega)
  have hZ : Subgroup.center (ProjOrthDerived (quadPlus m K)) = ⊥ :=
    center_projOrthDerived_eq_bot hreg.1 hreg.2
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAN hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAN hS.b_mem
  obtain ⟨x, hx⟩ := hBI d hS.d_mem
  obtain ⟨y, hy⟩ := hBI b hS.b_mem
  have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hxp : x ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one hZ (largeEvenInduces_pow_eq_one hdN hx hdp)
  have hyp : y ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one hZ (largeEvenInduces_pow_eq_one hbN hy hbp)
  have hdb : d * b = b * d :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hS.d_mem hS.b_mem
  have hxy : x * y = y * x := by
    apply mul_comm_of_conj_commute hZ
    have h1 := largeEvenInduces_mul hdN hbN hdb hx hy
    have h2 := largeEvenInduces_mul hbN hdN hdb.symm hy hx
    rw [← hdb] at h2
    exact largeEvenInduces_unique h1 h2 (conjRel_total (Subgroup.mul_mem _ hdN hbN))
  exact ⟨x, y, hx, hy, hxp, hyp, hxy⟩

theorem orthModelDescent_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m : ℕ} (K : Type) [Field K] [Finite K]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ProjOrthDerived (quadPlus m K))
    (hS : Setup p L J A d b) (x : ProjOrthDerived (quadPlus m K))
    (hx : LargeEvenInduces θ (conjRel d) (MulAut.conj x)) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (Subgroup.centralizer ({x} : Set (ProjOrthDerived (quadPlus m K)))) := by
  haveI : Finite (ProjOrthDerived (quadPlus m K)) :=
    finite_projOrthDerived_of_finite (quadPlus m K)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag
  exact isComponentOf_map_piCenterQuot_of_conj (p := p) θ (hAN hS.d_mem) x hx hS.comp.1

theorem orthModelLifts_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m : ℕ} (K : Type) [Field K] [Finite K]
    (b₀ c₀ : K) (hbc : ∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ProjOrthDerived (quadMinus m K b₀ c₀))
    (hS : Setup p L J A d b) (hm4 : 4 ≤ m)
    (hBI : ∀ a ∈ A, ∃ x : ProjOrthDerived (quadMinus m K b₀ c₀),
      LargeEvenInduces θ (conjRel a) (MulAut.conj x)) :
    ∃ x y : ProjOrthDerived (quadMinus m K b₀ c₀),
      LargeEvenInduces θ (conjRel d) (MulAut.conj x) ∧
        LargeEvenInduces θ (conjRel b) (MulAut.conj y) ∧
          x ^ p = 1 ∧ y ^ p = 1 ∧ x * y = y * x := by
  haveI : Finite (ProjOrthDerived (quadMinus m K b₀ c₀)) :=
    finite_projOrthDerived_of_finite (quadMinus m K b₀ c₀)
  have hreg := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := m) (b := b₀)
    (c := c₀) (by omega) hbc
  have hZ : Subgroup.center (ProjOrthDerived (quadMinus m K b₀ c₀)) = ⊥ :=
    center_projOrthDerived_eq_bot hreg.1 hreg.2
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAN hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAN hS.b_mem
  obtain ⟨x, hx⟩ := hBI d hS.d_mem
  obtain ⟨y, hy⟩ := hBI b hS.b_mem
  have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hxp : x ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one hZ (largeEvenInduces_pow_eq_one hdN hx hdp)
  have hyp : y ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one hZ (largeEvenInduces_pow_eq_one hbN hy hbp)
  have hdb : d * b = b * d :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hS.d_mem hS.b_mem
  have hxy : x * y = y * x := by
    apply mul_comm_of_conj_commute hZ
    have h1 := largeEvenInduces_mul hdN hbN hdb hx hy
    have h2 := largeEvenInduces_mul hbN hdN hdb.symm hy hx
    rw [← hdb] at h2
    exact largeEvenInduces_unique h1 h2 (conjRel_total (Subgroup.mul_mem _ hdN hbN))
  exact ⟨x, y, hx, hy, hxp, hyp, hxy⟩

theorem orthModelDescent_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m : ℕ} (K : Type) [Field K] [Finite K]
    (b₀ c₀ : K) (θ : ↥L ⧸ Subgroup.center ↥L ≃* ProjOrthDerived (quadMinus m K b₀ c₀))
    (hS : Setup p L J A d b) (x : ProjOrthDerived (quadMinus m K b₀ c₀))
    (hx : LargeEvenInduces θ (conjRel d) (MulAut.conj x)) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (Subgroup.centralizer ({x} : Set (ProjOrthDerived (quadMinus m K b₀ c₀)))) := by
  haveI : Finite (ProjOrthDerived (quadMinus m K b₀ c₀)) :=
    finite_projOrthDerived_of_finite (quadMinus m K b₀ c₀)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag
  exact isComponentOf_map_piCenterQuot_of_conj (p := p) θ (hAN hS.d_mem) x hx hS.comp.1

theorem orthModelData_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m n : ℕ} (hS : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) (onLie (orthDModel m n))) (hm4 : 4 ≤ m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (θ : ↥L ⧸ Subgroup.center ↥L ≃*
          ProjOrthDerived (quadPlus m K)) (x y : ProjOrthDerived (quadPlus m K)),
        LargeEvenInduces θ (conjRel d) (MulAut.conj x) ∧
          LargeEvenInduces θ (conjRel b) (MulAut.conj y) ∧
          x ^ p = 1 ∧ y ^ p = 1 ∧ x * y = y * x ∧
          CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
            (Subgroup.centralizer ({x} : Set (ProjOrthDerived (quadPlus m K)))) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, θ, hBI⟩ := orthModelMarking_plus hS hcat
  letI := hKfield
  letI := hKfinite
  obtain ⟨x, y, hx, hy, hxp, hyp, hxy⟩ := orthModelLifts_plus K θ hS hm4 hBI
  exact ⟨K, hKfield, hKfinite, hKcard, θ, x, y, hx, hy, hxp, hyp, hxy,
    orthModelDescent_plus K θ hS x hx⟩

theorem orthModelData_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} {m n : ℕ} (hS : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) (onLie (orthTwistedDModel m n))) (hm4 : 4 ≤ m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (b₀ c₀ : K), (∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0) ∧
      ∃ (θ : ↥L ⧸ Subgroup.center ↥L ≃*
          ProjOrthDerived (quadMinus m K b₀ c₀)) (x y : ProjOrthDerived (quadMinus m K b₀ c₀)),
        LargeEvenInduces θ (conjRel d) (MulAut.conj x) ∧
          LargeEvenInduces θ (conjRel b) (MulAut.conj y) ∧
          x ^ p = 1 ∧ y ^ p = 1 ∧ x * y = y * x ∧
          CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
            (Subgroup.centralizer ({x} : Set (ProjOrthDerived (quadMinus m K b₀ c₀)))) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, b₀, c₀, hbc, θ, hBI⟩ :=
    orthModelMarking_minus hS hcat
  letI := hKfield
  letI := hKfinite
  obtain ⟨x, y, hx, hy, hxp, hyp, hxy⟩ := orthModelLifts_minus K b₀ c₀ hbc θ hS hm4 hBI
  exact ⟨K, hKfield, hKfinite, hKcard, b₀, c₀, hbc, θ, x, y, hx, hy, hxp, hyp, hxy,
    orthModelDescent_minus K b₀ c₀ θ hS x hx⟩

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
