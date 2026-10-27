module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.GorensteinWalter CFSG.Open Matrix
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (index_powRange_dvd_gcd)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

theorem card_le_mul_card_ker {H C : Type*} [Group H] [Group C] [Finite H] [IsCyclic C]
    {p : ℕ} (hp : p.Prime) (hexp : ∀ h : H, h ^ p = 1) (α : H →* C) :
    Nat.card H ≤ p * Nat.card α.ker := by
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    rw [← map_pow, hexp x, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card H = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  rw [hsplit]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hp.pos hexpα)

theorem mem_range_toPGL_of_pow_eq_one' {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (g : PGL2 K) (hg : g ^ p = 1) :
    g ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd (hp.odd_of_ne_two hp2) hg

theorem exists_inner_of_elemAbelian_psl2_all {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (D : Subgroup (MulAut (PSL2 K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range, x ≠ 1 := by
  classical
  have : Finite D := Nat.finite_of_card_ne_zero (by omega)
  let Ψ : PGammaL2 K ≃* MulAut (PSL2 K) := semilinearEquivAut K
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let α : D →* (K ≃+* K) :=
    ((SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).comp Ψ.symm.toMonoidHom).comp D.subtype
  have hle := card_le_mul_card_ker hp (fun h : D => Subtype.ext (hexp h h.2)) α
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle'
    have : Nat.card D ≤ p * 1 := hle.trans (Nat.mul_le_mul_left _ (by omega))
    omega
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdk' : SemidirectProduct.rightHom (Ψ.symm (d : MulAut (PSL2 K))) = 1 := hdk
  have hmem : Ψ.symm (d : MulAut (PSL2 K)) ∈ (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hdk'
  obtain ⟨g, hg⟩ := hmem
  have hdg : (d : MulAut (PSL2 K)) = pglAction K g := by
    have : (d : MulAut (PSL2 K)) = Ψ (SemidirectProduct.inl g) := by
      rw [hg]; simp
    rw [this]
    exact semilinearAction_inl K g
  have hgp : g ^ p = 1 := by
    have h1 : Ψ.symm ((d : MulAut (PSL2 K)) ^ p) = 1 := by
      rw [hexp d d.2, map_one]
    rw [map_pow, ← hg, ← map_pow] at h1
    exact SemidirectProduct.inl_injective (by rw [map_one]; exact h1)
  obtain ⟨y, hy⟩ := mem_range_toPGL_of_pow_eq_one' hp hp2 g hgp
  refine ⟨d, ⟨d.2, y, ?_⟩, fun h => hd1' (Subtype.ext h)⟩
  rw [hdg, ← hy, pglAction_toPGL]

theorem conjAut_mem_inner_of_det_mem {k : Type} [Field k] {n : ℕ} (hn : 1 ≤ n) (A : GL (Fin n) k)
    (hA : GeneralLinearGroup.det A ∈ (powMonoidHom n : kˣ →* kˣ).range) :
    conjAut n k A ∈ Inn (projectiveSL n k) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := hA
  have hdet : (((GeneralLinearGroup.scalar (Fin n) u⁻¹ * A : GL (Fin n) k)) :
      Matrix (Fin n) (Fin n) k).det = 1 := by
    have h1 := congrArg (fun v : kˣ => (v : k)) hu
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.val_det_apply] at h1
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← h1, Units.val_inv_eq_inv_val,
      inv_pow, inv_mul_cancel₀ (pow_ne_zero _ u.ne_zero)]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin n) k,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin n) u⁻¹ * A :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  have hA : A = GeneralLinearGroup.scalar (Fin n) u * SpecialLinearGroup.toGL g := by
    rw [hg, map_inv, mul_inv_cancel_left]
  rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  exact ⟨_, rfl⟩

theorem isCyclic_linearAutGroup_quotient {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 ≤ n) :
    IsCyclic (linearAutGroup n k ⧸
      (Inn (projectiveSL n k)).subgroupOf (linearAutGroup n k)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set P : Subgroup kˣ := (powMonoidHom n : kˣ →* kˣ).range with hP
  have hD : linearAutGroup n k = (conjAut n k).range := linearAutGroup_eq_range
  have hQ : IsCyclic (kˣ ⧸ P) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  let θ : GL (Fin n) k →* kˣ ⧸ P := (QuotientGroup.mk' P).comp GeneralLinearGroup.det
  have hθ : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective P).comp GeneralLinearGroup.det_surjective
  let ψ : GL (Fin n) k →* linearAutGroup n k ⧸
      (Inn (projectiveSL n k)).subgroupOf (linearAutGroup n k) :=
    (QuotientGroup.mk' _).comp
      ((conjAut n k).codRestrict (linearAutGroup n k) conjAut_mem_linearAutGroup)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hx
    exact ⟨A, rfl⟩
  have hker : θ.ker ≤ ψ.ker := by
    intro A hA
    have hA' : GeneralLinearGroup.det A ∈ P := (QuotientGroup.eq_one_iff _).1 hA
    change QuotientGroup.mk _ = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact conjAut_mem_inner_of_det_mem hn A hA'
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let ψ' := (QuotientGroup.lift θ.ker ψ hker).comp e.symm.toMonoidHom
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨A, rfl⟩ := hψ y
    refine ⟨θ A, ?_⟩
    have h1 : e.symm (θ A) = QuotientGroup.mk A := e.symm_apply_eq.2 rfl
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  exact isCyclic_of_surjective ψ' hψ'

theorem exists_inner_of_elemAbelian_projectiveSL_all {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut (projectiveSL n K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p ^ 2 < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range, x ≠ 1 := by
  classical
  have hpos : 0 < p := hp.pos
  have : Finite D := Nat.finite_of_card_ne_zero (by omega)
  set Dl := linearAutGroup n K with hDl
  set Es := semilinearAutGroup n K with hEs
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, -, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at hDnorm
  have hDlN : Dl.Normal := ⟨fun d hd x =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hDE : D ≤ Es := fun x hx => by
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hexp x hx)
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  let α : D →* Es ⧸ Dl.subgroupOf Es :=
    (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hDE)
  have hle1 := card_le_mul_card_ker hp (fun h : D => Subtype.ext (hexp h h.2)) α
  have hk1 : p < Nat.card α.ker := by
    by_contra hle'
    have : Nat.card D ≤ p * p := hle1.trans (Nat.mul_le_mul_left _ (by omega))
    nlinarith
  have : Finite α.ker := Finite.of_injective _ α.ker.subtype_injective
  have hmemDl : ∀ k : α.ker, ((k : D) : MulAut (projectiveSL n K)) ∈ Dl := by
    intro ⟨d, hd⟩
    have h : α d = 1 := hd
    change QuotientGroup.mk (Subgroup.inclusion hDE d) = (1 : Es ⧸ Dl.subgroupOf Es) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  let f : α.ker →* MulAut (projectiveSL n K) := D.subtype.comp α.ker.subtype
  have hDlN : ∀ k : α.ker, f k ∈ Dl := hmemDl
  have : IsCyclic (Dl ⧸ (Inn (projectiveSL n K)).subgroupOf Dl) :=
    isCyclic_linearAutGroup_quotient (by omega)
  let β : α.ker →* Dl ⧸ (Inn (projectiveSL n K)).subgroupOf Dl :=
    (QuotientGroup.mk' _).comp (f.codRestrict Dl hDlN)
  have hle2 := card_le_mul_card_ker hp
    (fun h : α.ker => Subtype.ext (Subtype.ext (hexp h.1 h.1.2))) β
  have hk2 : 1 < Nat.card β.ker := by
    by_contra hle'
    have : Nat.card α.ker ≤ p * 1 := hle2.trans (Nat.mul_le_mul_left _ (by omega))
    omega
  have : Nontrivial β.ker := Finite.one_lt_card_iff_nontrivial.1 hk2
  obtain ⟨⟨⟨d, hdα⟩, hdβ⟩, hd1⟩ := exists_ne (1 : β.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext (Subtype.ext h))
  have hdI : (d : MulAut (projectiveSL n K)) ∈ Inn (projectiveSL n K) := by
    have h : β ⟨d, hdα⟩ = 1 := hdβ
    change QuotientGroup.mk _ = (1 : Dl ⧸ (Inn (projectiveSL n K)).subgroupOf Dl) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  exact ⟨d, ⟨d.2, hdI⟩, fun h => hd1' (Subtype.ext h)⟩

theorem exists_inner_of_mulEquiv {S G : Type} [Group S] [Group G] (e : S ≃* G) {p : ℕ}
    (hp : p.Prime) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3)
    (h : ∀ D' : Subgroup (MulAut G), (∀ a ∈ D', a ^ p = 1) → p ^ 2 < Nat.card D' →
      ∃ x ∈ D' ⊓ (MulAut.conj : G →* MulAut G).range, x ≠ 1) :
    ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1 := by
  set φ : MulAut S ≃* MulAut G := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := h (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by
      rw [hcardD]
      exact Nat.pow_lt_pow_right hp.one_lt (by norm_num))
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

theorem lieOuterRankFam_A : LieOuterRankFam .A := by
  intro S _ _ _ hnab idx hidx hS p hp hp2 D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  let e : S ≃* ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
  have hr1 : 1 ≤ r := by
    by_contra h0
    have : r = 0 := by omega
    subst this
    obtain ⟨a, b, hab⟩ := hnab
    have hsub : ∀ x : ProjectiveSpecialLinearGroup (Fin (0 + 1)) (GaloisField q.p q.exponent),
        x = 1 := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hg : g = 1 := by
        ext i j
        have hdet := g.2
        rw [Matrix.det_fin_one] at hdet
        fin_cases i; fin_cases j
        simpa using hdet
      rw [hg]; rfl
    exact hab (e.injective ((hsub _).trans (hsub _).symm))
  rcases Nat.lt_or_ge r 2 with h1 | h2
  · have : r = 1 := by omega
    subst this
    exact exists_inner_of_mulEquiv e hp D hD hcard fun D' hexp hc =>
      exists_inner_of_elemAbelian_psl2_all hp hp2 D' hexp (lt_of_le_of_lt
        (Nat.le_self_pow (by norm_num) p) hc)
  · let e' := e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _)
    exact exists_inner_of_mulEquiv e' hp D hD hcard fun D' hexp hc =>
      exists_inner_of_elemAbelian_projectiveSL_all (by omega) hp hp2 D' hexp hc

end CFSG.HardMathSupport.Timmesfeld.DefChar
