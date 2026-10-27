module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc8Sp
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalGL
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs
import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Basic
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import Certificates.Certificate41501
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc8

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp multiplier ker_multiplier mem_gsp)
open scoped commutatorElement

local notation "V₄" => Fin 2 ⊕ Fin 2

section Parabolic

@[expose] def R1 : Subgroup (GL V₄ (ZMod 3)) where
  carrier := {g | ∃ p : Par, p.2.2.2 = 0 ∧ uG p = g}
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    refine ⟨law p q, ?_, (uG_mul p q).symm⟩
    simp [law, hp, hq]
  one_mem' := ⟨0, rfl, uG_zero⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨uinv p, by simp [uinv, hp], (uG_inv p).symm⟩

@[expose] def R2 : Subgroup (GL V₄ (ZMod 3)) where
  carrier := {g | ∃ p : Par, p.1 = 0 ∧ uG p = g}
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    refine ⟨law p q, ?_, (uG_mul p q).symm⟩
    simp [law, hp, hq]
  one_mem' := ⟨0, rfl, uG_zero⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨uinv p, by simp [uinv, hp], (uG_inv p).symm⟩

theorem R1_le_U0 : R1 ≤ U0 := by
  rintro _ ⟨p, -, rfl⟩
  exact ⟨p, rfl⟩

theorem R2_le_U0 : R2 ≤ U0 := by
  rintro _ ⟨p, -, rfl⟩
  exact ⟨p, rfl⟩

theorem card_par_c : Nat.card {p : Par // p.2.2.2 = 0} = 27 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_par_x : Nat.card {p : Par // p.1 = 0} = 27 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_R1 : Nat.card R1 = 27 := by
  rw [← card_par_c]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨uG p.1, p.1, p.2, rfl⟩) ⟨?_, ?_⟩)
  · intro p q h
    exact Subtype.ext (uG_injective (congrArg Subtype.val h))
  · rintro ⟨_, p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

theorem card_R2 : Nat.card R2 = 27 := by
  rw [← card_par_x]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨uG p.1, p.1, p.2, rfl⟩) ⟨?_, ?_⟩)
  · intro p q h
    exact Subtype.ext (uG_injective (congrArg Subtype.val h))
  · rintro ⟨_, p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

theorem n1M_symp : n1Mᵀ * Jm * n1M = Jm := by decide +kernel

theorem n2M_symp : n2Mᵀ * Jm * n2M = Jm := by decide +kernel

@[expose] def n1G : GL V₄ (ZMod 3) := spUnit n1M n1M_symp

@[expose] def n2G : GL V₄ (ZMod 3) := spUnit n2M n2M_symp

theorem tG_eq_n1G_mul_n2G : tG = n1G * n2G := Units.ext tM_eq

theorem n1M_conj : ∀ x a b : ZMod 3,
    n1M * uM (x, a, b, 0) = uM (b, a - x * b, -x, 0) * n1M := by
  decide +kernel

theorem n2M_conj : ∀ a b c : ZMod 3,
    n2M * uM (0, a, b, c) = uM (0, c, b + c, a + 2 * b + c) * n2M := by
  decide +kernel

@[expose] def dM : M4 := fromBlocks 1 0 0 (-1)

theorem dM_sq : dM * dM = 1 := by decide +kernel

@[expose] def dG : GL V₄ (ZMod 3) := ⟨dM, dM, dM_sq, dM_sq⟩

theorem dM_conj : ∀ p : Par, dM * uM p = uM (p.1, -p.2.1, -p.2.2.1, -p.2.2.2) * dM := by
  decide +kernel

theorem dM_mult : dMᵀ * CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ 2 (ZMod 3) * dM =
    ((-1 : (ZMod 3)ˣ) : ZMod 3) • CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ 2 (ZMod 3) := by
  decide +kernel

theorem dG_mem_gsp : dG ∈ gsp 2 (ZMod 3) := mem_gsp.mpr ⟨-1, dM_mult⟩

theorem dM_not_symp : dMᵀ * fromBlocks 0 1 (-1) 0 * dM ≠ fromBlocks 0 1 (-1) 0 := by decide +kernel

theorem conj_mem_of_mat {g : GL V₄ (ZMod 3)} {p q : Par} (h : (g : M4) * uM p = uM q * (g : M4)) :
    g * uG p * g⁻¹ = uG q := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext h

theorem n1G_mem : n1G ∈ Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3))) := by
  refine ClassicalGL.mem_normalizer_of_conj_mem fun r hr => ?_
  obtain ⟨⟨x, a, b, c⟩, hc, rfl⟩ := hr
  simp only at hc
  subst hc
  exact ⟨(b, a - x * b, -x, 0), rfl, (conj_mem_of_mat (n1M_conj x a b)).symm⟩

theorem n2G_mem : n2G ∈ Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3))) := by
  refine ClassicalGL.mem_normalizer_of_conj_mem fun r hr => ?_
  obtain ⟨⟨x, a, b, c⟩, hx, rfl⟩ := hr
  simp only at hx
  subst hx
  exact ⟨(0, c, b + c, a + 2 * b + c), rfl, (conj_mem_of_mat (n2M_conj a b c)).symm⟩

theorem dG_mem_R1 : dG ∈ Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3))) := by
  refine ClassicalGL.mem_normalizer_of_conj_mem fun r hr => ?_
  obtain ⟨p, hc, rfl⟩ := hr
  exact ⟨(p.1, -p.2.1, -p.2.2.1, -p.2.2.2), by simp [hc], (conj_mem_of_mat (dM_conj p)).symm⟩

theorem tau0_mem_R1 : tau0 ∈ R1 := ⟨(0, 1, 0, 0), rfl, tau0_eq.symm⟩

theorem dG_mul_mem {x : GL V₄ (ZMod 3)} (hx : x ∈ gsp 2 (ZMod 3)) (hxs : x ∉ StatedSp 2 (ZMod 3)) :
    dG * x ∈ StatedSp 2 (ZMod 3) := by
  have hd := dG_mem_gsp
  have hm : multiplier 2 (ZMod 3) ⟨x, hx⟩ = -1 := by
    rcases units_zmod_three' (multiplier 2 (ZMod 3) ⟨x, hx⟩) with h | h
    · exfalso
      apply hxs
      have hmem : (⟨x, hx⟩ : gsp 2 (ZMod 3)) ∈ (multiplier 2 (ZMod 3)).ker := h
      rw [ker_multiplier, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · exact h
  have hmd : multiplier 2 (ZMod 3) ⟨dG, hd⟩ = -1 := by
    rcases units_zmod_three' (multiplier 2 (ZMod 3) ⟨dG, hd⟩) with h | h
    · exfalso
      have hmem : (⟨dG, hd⟩ : gsp 2 (ZMod 3)) ∈ (multiplier 2 (ZMod 3)).ker := h
      rw [ker_multiplier, Subgroup.mem_subgroupOf, CFSG.Open.StatedAPI.mem_statedSp_iff] at hmem
      exact dM_not_symp hmem
    · exact h
  have hmem : (⟨dG, hd⟩ * ⟨x, hx⟩ : gsp 2 (ZMod 3)) ∈ (multiplier 2 (ZMod 3)).ker := by
    rw [MonoidHom.mem_ker, map_mul, hm, hmd]
    decide
  rw [ker_multiplier, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem le_sup_normalizers {X : Subgroup (GL V₄ (ZMod 3))} (hX : StatedSp 2 (ZMod 3) ≤ X)
    (hXg : X ≤ gsp 2 (ZMod 3)) :
    X ≤ (Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3))) ⊓ X) ⊔
      (Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3))) ⊓ X) := by
  set J := (Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3))) ⊓ X) ⊔
    (Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3))) ⊓ X) with hJ
  have hSpJ : StatedSp 2 (ZMod 3) ≤ J := by
    rw [← closure_tG_tau0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, tG_eq_n1G_mul_n2G]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨n1G_mem, hX (spUnit_mem _ _)⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨n2G_mem, hX (spUnit_mem _ _)⟩))
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer tau0_mem_R1,
        hX (spTrans_mem_statedSp _ _)⟩)
  intro x hx
  by_cases hxs : x ∈ StatedSp 2 (ZMod 3)
  · exact hSpJ hxs
  · have hdx := dG_mul_mem (hXg hx) hxs
    have hdX : dG ∈ X := by
      have := X.mul_mem (hX hdx) (X.inv_mem hx)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at this
    have hdJ : dG ∈ J := Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨dG_mem_R1, hdX⟩)
    have e : x = dG * (dG * x) := by
      rw [← mul_assoc, show dG * dG = 1 from Units.ext dM_sq, one_mul]
    rw [e]
    exact J.mul_mem hdJ (hSpJ hdx)

theorem factorization_103680_three : (103680 : ℕ).factorization 3 = 4 := by
  rw [show (103680 : ℕ) = 3 ^ 4 * 1280 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem genProp_of_sp_le {X : Subgroup (GL V₄ (ZMod 3))} (hX : StatedSp 2 (ZMod 3) ≤ X)
    (hXg : X ≤ gsp 2 (ZMod 3)) : ClassicalGL.GenProp X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU0X : U0 ≤ X := U0_le_statedSp.trans hX
  have hXc : Nat.card X = 51840 ∨ Nat.card X = 103680 := by
    have h1 : Nat.card X ∣ 103680 := (Subgroup.card_dvd_of_le hXg).trans card_gsp_dvd
    have h2 : 51840 ∣ Nat.card X := card_Sp43 ▸ Subgroup.card_dvd_of_le hX
    obtain ⟨k, hk⟩ := h2
    rw [hk] at h1 ⊢
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 51840)
      (show 51840 * k ∣ 51840 * 2 by norm_num; exact h1)
    rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl <;> simp
  have hfac : (Nat.card X).factorization 3 = 4 := by
    rcases hXc with h | h <;> rw [h]
    · exact factorization_51840_three
    · exact factorization_103680_three
  have hUc : Nat.card (U0.subgroupOf X) = 3 ^ (Nat.card X).factorization 3 := by
    rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0X).toEquiv, card_U0]
    norm_num
  set S₀ : Sylow 3 X := Sylow.ofCard (U0.subgroupOf X) hUc with hS₀
  have hSc : (S₀ : Subgroup X) = U0.subgroupOf X := rfl
  have hidx : ∀ {R : Subgroup (GL V₄ (ZMod 3))}, R ≤ U0 → Nat.card R = 27 →
      R.subgroupOf X ≤ S₀ ∧ (R.subgroupOf X).relIndex S₀ = 3 := by
    intro R hRU hR
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hSc, Subgroup.mem_subgroupOf]
      exact hRU (Subgroup.mem_subgroupOf.1 hx)
    · rw [hSc, Subgroup.relIndex_subgroupOf hU0X]
      have h := Subgroup.relIndex_mul_card (H := R) (K := U0)
      rw [inf_of_le_left hRU, hR, card_U0] at h
      omega
  refine ClassicalGL.genProp_of_one S₀ ?_
  intro y _
  have hy : (y : GL V₄ (ZMod 3)) ∈ (Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3))) ⊓ X) ⊔
      (Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3))) ⊓ X) := le_sup_normalizers hX hXg y.2
  have hmap : ((Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3)))).subgroupOf X ⊔
      (Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3)))).subgroupOf X).map X.subtype =
      (Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3))) ⊓ X) ⊔
        (Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3))) ⊓ X) := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
  rw [← hmap] at hy
  have hy' := (Subgroup.mem_map_iff_mem X.subtype_injective).1 hy
  have hle : (Subgroup.normalizer (R1 : Set (GL V₄ (ZMod 3)))).subgroupOf X ⊔
      (Subgroup.normalizer (R2 : Set (GL V₄ (ZMod 3)))).subgroupOf X ≤
      ⨆ (Q : Subgroup X) (_ : Q ≤ S₀ ∧ Q.relIndex S₀ = 3), Subgroup.normalizer (Q : Set X) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.subgroupOf_normalizer_eq (R1_le_U0.trans hU0X)]
      exact le_iSup₂_of_le (R1.subgroupOf X) (hidx R1_le_U0 card_R1) le_rfl
    · rw [Subgroup.subgroupOf_normalizer_eq (R2_le_U0.trans hU0X)]
      exact le_iSup₂_of_le (R2.subgroupOf X) (hidx R2_le_U0 card_R2) le_rfl
  exact hle hy'

end Parabolic

section Action

open CFSG.OddSolvableUnitary

variable {Y : Type} [Group Y] {W : Subgroup Y}

theorem map_commutator_subtype (W : Subgroup Y) : (commutator ↥W).map W.subtype = ⁅W, W⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem center_eq_commutator_of_ext (hext : Lemma1211.IsExtraspecialThreeFive W) :
    Subgroup.center ↥W = commutator ↥W := by
  apply Subgroup.map_injective W.subtype_injective
  rw [map_commutator_subtype, hext.2.2.1]
  rfl

theorem toMatrixAlgEquiv_eq {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (b : Module.Basis ι (ZMod 3) M) (f : Module.End (ZMod 3) M) :
    LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := by
  ext i j
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

theorem zmod3_additive (ψ : ZMod 3 → ZMod 3) (h : ∀ a b, ψ (a + b) = ψ a + ψ b) (a : ZMod 3) :
    ψ a = a * ψ 1 := by
  have h0 : ψ 0 = 0 := by
    have := h 0 0
    simp only [add_zero] at this
    linear_combination -this
  fin_cases a
  · show ψ 0 = 0 * ψ 1
    rw [h0, zero_mul]
  · show ψ 1 = 1 * ψ 1
    rw [one_mul]
  · show ψ 2 = 2 * ψ 1
    rw [show (2 : ZMod 3) = 1 + 1 by decide, h]
    ring

theorem formJ_eq_neg_J : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ 2 (ZMod 3) =
    -Matrix.J (Fin 2) (ZMod 3) := by
  decide +kernel

theorem map_mem_center {G : Type*} [Group G] (φ : MulAut G) {z : G} (hz : z ∈ Subgroup.center G) :
    φ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz g']

theorem exists_hom_gsp [Finite Y] (hWn : W.Normal) (hext : Lemma1211.IsExtraspecialThreeFive W) :
    ∃ ρ : Y →* GL V₄ (ZMod 3), (∀ y, ρ y ∈ gsp 2 (ZMod 3)) ∧
      ∀ y, ρ y = 1 → ∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hWn
  have hZ := center_eq_commutator_of_ext hext
  have hc : Nat.card (Subgroup.center ↥W) = 3 := by
    have := hext.2.2.2
    rwa [centerOf, Subgroup.card_map_of_injective W.subtype_injective] at this
  have hD : ∀ x : W, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hext.2.1 x x.2)
  letI : Module (ZMod 3) (Additive (Abelianization W)) :=
    AddCommGroup.zmodModule (nsmul_abelianization_eq_zero hD)
  obtain ⟨ε⟩ := nonempty_center_mulEquiv hc
  obtain ⟨B, hBa, hBn, hB⟩ := exists_commForm hZ ε
  haveI : Finite (Additive (Abelianization W)) :=
    Finite.of_surjective (fun x : W => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  haveI : Module.Finite (ZMod 3) (Additive (Abelianization W)) := Module.Finite.of_finite
  obtain ⟨m, bs, hbs⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (K := ZMod 3) hBa hBn
  have hm : m = 2 := by
    have h1 : Nat.card (Additive (Abelianization W)) = 3 ^ (2 * m) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod,
        Module.finrank_eq_card_basis bs, Fintype.card_sum, Fintype.card_fin, two_mul]
    have h2 := card_eq_card_abelianization_mul hZ hc
    change Nat.card (Abelianization W) = _ at h1
    rw [h1, hext.1, ← pow_succ] at h2
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
    omega
  subst hm
  have hof : ∀ v : Additive (Abelianization W), ∃ x : W, Additive.ofMul (Abelianization.of x) = v :=
    fun v => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      exact ⟨x, hx⟩
  let L : Y → Module.End (ZMod 3) (Additive (Abelianization W)) := fun y =>
    AddMonoidHom.toZModLinearMap 3
      (MonoidHom.toAdditive (Abelianization.map (MulAut.conjNormal y : MulAut W).toMonoidHom))
  have hL : ∀ y (x : W), L y (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of ((MulAut.conjNormal y : MulAut W) x)) := fun y x => rfl
  have hLext : ∀ f g : Module.End (ZMod 3) (Additive (Abelianization W)),
      (∀ x : W, f (Additive.ofMul (Abelianization.of x)) = g (Additive.ofMul (Abelianization.of x))) →
        f = g := by
    intro f g h
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := hof v
    exact h x
  let ρ₀ : Y →* Module.End (ZMod 3) (Additive (Abelianization W)) :=
    { toFun := L
      map_one' := hLext _ _ fun x => by rw [hL, map_one]; rfl
      map_mul' := fun y y' => hLext _ _ fun x => by
        rw [Module.End.mul_apply, hL, hL, hL, map_mul]
        rfl }
  let ρ : Y →* GL V₄ (ZMod 3) :=
    ((LinearMap.toMatrixAlgEquiv bs).toRingEquiv.toMonoidHom.comp ρ₀).toHomUnits
  have hρ : ∀ y, ((ρ y : GL V₄ (ZMod 3)) : M4) = LinearMap.toMatrix bs bs (L y) := fun y =>
    toMatrixAlgEquiv_eq bs (L y)
  refine ⟨ρ, fun y => ?_, fun y hy w hw => ?_⟩
  · set φ : MulAut W := MulAut.conjNormal y with hφ
    let ψ : ZMod 3 → ZMod 3 := fun a => Multiplicative.toAdd
      (ε ⟨φ (ε.symm (Multiplicative.ofAdd a)), map_mem_center φ (ε.symm (Multiplicative.ofAdd a)).2⟩)
    have hψadd : ∀ a b, ψ (a + b) = ψ a + ψ b := by
      intro a b
      simp only [ψ]
      rw [← toAdd_mul, ← map_mul]
      congr 2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ofAdd_add, map_mul]
    have hψ : ∀ z : Subgroup.center W, Multiplicative.toAdd (ε ⟨φ z, map_mem_center φ z.2⟩) =
        Multiplicative.toAdd (ε z) * ψ 1 := by
      intro z
      rw [← zmod3_additive ψ hψadd]
      simp only [ψ, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    have hψ1 : ψ 1 ≠ 0 := by
      intro h0
      set g : Subgroup.center W := ε.symm (Multiplicative.ofAdd 1) with hg
      have h := hψ g
      rw [h0, mul_zero] at h
      have h1' : ε ⟨φ g, map_mem_center φ g.2⟩ = 1 :=
        Multiplicative.toAdd.injective (h.trans toAdd_one.symm)
      have h1 : (⟨φ g, map_mem_center φ g.2⟩ : Subgroup.center W) = 1 :=
        (MulEquiv.map_eq_one_iff ε).mp h1'
      have h2 : φ g = 1 := congrArg Subtype.val h1
      rw [map_eq_one_iff φ φ.injective] at h2
      have h3 : g = 1 := Subtype.ext h2
      have h4 := congrArg ε h3
      rw [hg, MulEquiv.apply_symm_apply, map_one ε] at h4
      have h5 := congrArg Multiplicative.toAdd h4
      rw [toAdd_ofAdd, toAdd_one] at h5
      exact one_ne_zero h5
    have hBy : ∀ u v, B (L y u) (L y v) = ψ 1 * B u v := by
      intro u v
      obtain ⟨x, rfl⟩ := hof u
      obtain ⟨x', rfl⟩ := hof v
      rw [hL, hL, hB, hB]
      have e : (⟨⁅φ x, φ x'⁆, commutatorElement_mem_center hZ _ _⟩ : Subgroup.center W) =
          ⟨φ ⁅x, x'⁆, map_mem_center φ (commutatorElement_mem_center hZ x x')⟩ :=
        Subtype.ext (map_commutatorElement φ x x').symm
      rw [e, hψ ⟨⁅x, x'⁆, commutatorElement_mem_center hZ x x'⟩, mul_comm]
    have hcomp : B.comp (L y) (L y) = ψ 1 • B := by
      refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
      rw [LinearMap.BilinForm.comp_apply, hBy, LinearMap.smul_apply, LinearMap.smul_apply,
        smul_eq_mul]
    have hmat := LinearMap.BilinForm.toMatrix_comp bs bs B (L y) (L y)
    rw [hcomp, map_smul, hbs] at hmat
    refine mem_gsp.mpr ⟨Units.mk0 (ψ 1) hψ1, ?_⟩
    rw [hρ, formJ_eq_neg_J, Units.val_mk0, Matrix.mul_neg, Matrix.neg_mul, ← hmat, smul_neg]
  ·
    have hLy : L y = 1 := by
      apply (LinearMap.toMatrix bs bs).injective
      rw [← hρ, hy, Units.val_one, LinearMap.toMatrix_one]
    have h1 := congrArg (fun f : Module.End (ZMod 3) (Additive (Abelianization W)) =>
      f (Additive.ofMul (Abelianization.of (⟨w, hw⟩ : W)))) hLy
    simp only [hL, Module.End.one_apply] at h1
    have h2 : Abelianization.of ((MulAut.conjNormal y : MulAut W) ⟨w, hw⟩ * (⟨w, hw⟩ : W)⁻¹) = 1 := by
      rw [map_mul, map_inv, Additive.ofMul.injective h1, mul_inv_cancel]
    have h3 : (MulAut.conjNormal y : MulAut W) ⟨w, hw⟩ * (⟨w, hw⟩ : W)⁻¹ ∈ commutator W := by
      rw [← Abelianization.ker_of]
      exact h2
    have h4 := Subgroup.mem_map_of_mem W.subtype h3
    rw [map_commutator_subtype] at h4
    simpa [MulAut.conjNormal_apply, commutatorElement_def] using h4

end Action

section Assembly

open CFSG.GH74.GLS (oPrimeResidual)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5 (isPSolvable_of_isSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_normal)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)

theorem isElemAbelian_map' {G H : Type*} [Group G] [Group H] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) (φ : G →* H) : CFSG.Open.IsElemAbelian 3 (E.map φ) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨x', hx', rfl⟩⟩ := x
    obtain ⟨_, ⟨y', hy', rfl⟩⟩ := y
    apply Subtype.ext
    have hc := congrArg Subtype.val (hE.1.is_comm.comm (⟨x', hx'⟩ : E) ⟨y', hy'⟩)
    simp only [Subgroup.coe_mul] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_mono' {G : Type*} [Group G] {E F : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hFE : F ≤ E) : CFSG.Open.IsElemAbelian 3 F := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  have := congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hFE x.2⟩ : E) ⟨y, hFE y.2⟩)
  simpa using this

theorem eq_bot_of_normal_pGroup {X : Type} [Group X] [Finite X]
    (e : ↥(oPrimeResidual 3 X) ≃* CA0) {N : Subgroup X} (hN : N.Normal) (hp : IsPGroup 3 N) :
    N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNO : N ≤ oPrimeResidual 3 X := fun x hx => by
    obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
    exact Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩
  set N₁ := N.subgroupOf (oPrimeResidual 3 X) with hN₁def
  have hN₁ : N₁.Normal := hN.subgroupOf _
  set N₂ := N₁.map e.toMonoidHom with hN₂def
  have hN₂ : N₂.Normal := hN₁.map _ e.surjective
  have hN₁p : IsPGroup 3 N₁ := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNO).symm
  have hN₂p : IsPGroup 3 N₂ := hN₁p.map _
  obtain ⟨k, hk⟩ := hN₂p.exists_card_eq
  rcases normal_eq_top_or_le_center isQuasisimple_CA0 hN₂ with h | h
  · exfalso
    rw [h, Subgroup.card_top, card_CA0] at hk
    have hk7 : k < 7 := by
      by_contra h7
      push Not at h7
      have : 3 ^ 7 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h7
      omega
    interval_cases k <;> norm_num at hk
  · have hc := (Subgroup.card_le_of_le h).trans card_center_CA0_le
    rw [hk] at hc
    have hk0 : k = 0 := by
      by_contra hk0
      have : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hk0)
      omega
    have hN₂b : N₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
    have hN₁b : N₁ = ⊥ := by
      rwa [hN₂def, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hN₂b
    rw [eq_bot_iff]
    intro x hx
    have hx1 : (⟨x, hNO hx⟩ : oPrimeResidual 3 X) ∈ N₁ := hx
    rw [hN₁b, Subgroup.mem_bot] at hx1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)

theorem input30_14_Out_holds : Claims1211b.Input30_14_Out := by
  intro Y _ _ W hWn hext hker hE hns
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hE, hE9⟩ := hE
  obtain ⟨ρ, hρg, hρk⟩ := exists_hom_gsp hWn hext
  have hkerp : IsPGroup 3 ρ.ker := fun k => by
    obtain ⟨m, hm⟩ := hker k (hρk k k.2)
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  have hRg : ρ.range ≤ gsp 2 (ZMod 3) := by
    rintro _ ⟨y, rfl⟩
    exact hρg y
  have hRns : ¬ Group.IsSolvable ρ.range := by
    intro h
    apply hns
    haveI := hkerp.isNilpotent
    exact isPSolvable_of_normal ρ.ker (isPSolvable_of_isSolvable Nat.prime_three inferInstance)
      (isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange ρ).symm
        (isPSolvable_of_isSolvable Nat.prime_three h))
  have hkO : ρ.ker ≤ CFSG.pCore 3 Y := le_sSup ⟨inferInstance, hkerp⟩
  obtain ⟨E', hE'le, hE'a, hE'9⟩ : ∃ E' : Subgroup (GL V₄ (ZMod 3)), E' ≤ ρ.range ∧
      CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
    set Em := E.map ρ with hEm
    have hEma : CFSG.Open.IsElemAbelian 3 Em := isElemAbelian_map' hE ρ
    have hcard : Nat.card E = Nat.card Em * Nat.card ↥(ρ.ker ⊓ E) := by
      have h1 := Subgroup.relIndex_mul_card ρ.ker E
      have hk : (ρ.comp E.subtype).ker = ρ.ker.subgroupOf E := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, Subgroup.coe_subtype,
          MonoidHom.mem_ker]
      have h2 : ρ.ker.relIndex E = Nat.card Em := by
        rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_comp,
          Subgroup.range_subtype]
      rw [← h1, h2]
    have hle : Nat.card ↥(ρ.ker ⊓ E) ≤ Nat.card ↥(E ⊓ CFSG.pCore 3 Y) :=
      Subgroup.card_le_of_le (le_inf inf_le_right (inf_le_left.trans hkO))
    have hpos : 0 < Nat.card ↥(ρ.ker ⊓ E) := Nat.card_pos
    have h9 : 9 ≤ Nat.card Em := by
      by_contra h
      push Not at h
      have : Nat.card E < 9 * Nat.card ↥(ρ.ker ⊓ E) := by
        rw [hcard]
        exact Nat.mul_lt_mul_of_pos_right h hpos
      omega
    have hEmp : IsPGroup 3 Em := fun y => ⟨1, Subtype.ext (by simpa using hEma.2 y y.2)⟩
    obtain ⟨j, hj⟩ := hEmp.exists_card_eq
    have hj2 : 2 ≤ j := by
      by_contra hj2
      push Not at hj2
      have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3
      (show 3 ^ 2 ∣ Nat.card Em by rw [hj]; exact pow_dvd_pow 3 hj2)
    refine ⟨K.map Em.subtype, (Subgroup.map_subtype_le _).trans (Subgroup.map_le_range ρ E), ?_, ?_⟩
    · exact isElemAbelian_mono hEma (Subgroup.map_subtype_le _)
    · rw [Subgroup.card_map_of_injective Em.subtype_injective, hK]
      norm_num
  rcases sp_le_or_equiv_CA0 hRg hRns hE'le hE'a hE'9 with hsp | heC
  · left
    have hgen := genProp_of_sp_le hsp hRg
    haveI : Nontrivial ρ.range := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hRns inferInstance
    exact ClassicalGL.genProp_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      (by rwa [MonoidHom.ker_rangeRestrict]) hgen
  · right
    right
    obtain ⟨eC⟩ := heC
    have hO3 : CFSG.pCore 3 Y = ρ.ker := by
      refine le_antisymm ?_ hkO
      have hN : ((CFSG.pCore 3 Y).map ρ.rangeRestrict).Normal :=
        (CFSG.pCore_normal (p := 3)).map _ ρ.rangeRestrict_surjective
      have hNp : IsPGroup 3 ((CFSG.pCore 3 Y).map ρ.rangeRestrict) :=
        (CFSG.pCore_isPGroup (p := 3)).map _
      have hNb := eq_bot_of_normal_pGroup eC hN hNp
      intro y hy
      have hy' : ρ.rangeRestrict y ∈ (CFSG.pCore 3 Y).map ρ.rangeRestrict := ⟨y, hy, rfl⟩
      rw [hNb, Subgroup.mem_bot] at hy'
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hy'
    have e1 : Y ⧸ CFSG.pCore 3 Y ≃* ρ.range :=
      (QuotientGroup.quotientMulEquivOfEq hO3).trans (QuotientGroup.quotientKerEquivRange ρ)
    obtain ⟨e2⟩ := Claims1211b.oPrimeResidual_equiv e1
    obtain ⟨F, hF, hFin, hF9, ⟨e⟩⟩ := isSL2Nine_CA0
    exact ⟨F, hF, hFin, hF9, ⟨e2.trans (eC.trans e)⟩⟩

end Assembly

section I295

open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def Input29_5'Spor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ s : TauCeti.SporadicName,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S → Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) → False

@[expose] def Input29_5'Lie : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S → Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) →
      x ∉ L ∧ CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 4 ∧
      (∀ Q : Subgroup X, IsSylowIn 3 (L ⊓ Subgroup.centralizer ({x} : Set X)) Q →
        (∀ q ∈ Q, q ^ 3 = 1) ∧ ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂ ≠ q₂ * q₁) ∧
      (∀ D : Subgroup X, D ≤ L → CFSG.Open.IsElemAbelian 3 D → Nat.card D = 9 →
        ∃ E₀ : Subgroup X, D ≤ E₀ ∧ E₀ ≤ L ∧ CFSG.Open.IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 81)

theorem false_of_alt {X : Type} [Group X] [Finite X] {L : Subgroup X} (hLn : L.Normal)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hC : ∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1)
    {n : ℕ} (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n))
    (hrk : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {x : X} (hx : orderOf x = 3)
    (hrk3 : CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hLn
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  have hn5 : 5 ≤ n := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.five_le_of_centerQuotient hq.1 e
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hC z fun l hl => ?_
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l, hl⟩).symm
  have hLalt : IsAltType n ↥L :=
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩
  obtain ⟨eL⟩ := hLalt
  set ψ : X →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp MulAut.conjNormal with hψ
  have hker : ∀ y : X, ψ y = 1 → y ∈ L := by
    intro y hy
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨l, hl⟩ := hy
    have hc : ∀ m ∈ L, ((l : X)⁻¹ * y) * m = m * ((l : X)⁻¹ * y) := by
      intro m hm
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨m, hm⟩ : ↥L) : X)) hl
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc (l : X)⁻¹ * y * m = (l : X)⁻¹ * (y * m * y⁻¹) * y := by group
        _ = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * y := by rw [h1]
        _ = m * ((l : X)⁻¹ * y) := by group
    have h1 := hC _ hc
    have : y = l := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    rw [this]
    exact l.2
  have hOut : Nat.card (Outer ↥L) = Nat.card (Outer (alternatingGroup (Fin n))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eL).toEquiv
  haveI : Finite (Outer ↥L) := by
    haveI : Finite (MulAut ↥L) := MulEquiv.finite_left
    infer_instance
  obtain ⟨E₁, -, hE₁, hE₁c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup X)
  have hE₁p : IsPGroup 3 E₁ := fun y => ⟨1, Subtype.ext (by simpa using hE₁.2 y y.2)⟩
  obtain ⟨E₂, hE₂⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 4 ∣ Nat.card E₁ by rw [hE₁c]; exact pow_dvd_pow 3 hrk)
  set E := E₂.map E₁.subtype with hEdef
  have hEa : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_mono' hE₁ (Subgroup.map_subtype_le _)
  have hEc : Nat.card E = 81 := by
    rw [hEdef, Subgroup.card_map_of_injective E₁.subtype_injective, hE₂]
    norm_num
  have hcard : Nat.card E = Nat.card (E.map ψ) * Nat.card ↥(ψ.ker ⊓ E) := by
    have h1 := Subgroup.relIndex_mul_card ψ.ker E
    have hk : (ψ.comp E.subtype).ker = ψ.ker.subgroupOf E := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MonoidHom.mem_ker]
    have h2 : ψ.ker.relIndex E = Nat.card (E.map ψ) := by
      rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, h2]
  have hEψp : IsPGroup 3 (E.map ψ) :=
    (IsPGroup.of_card (n := 4) (by rw [hEc]; norm_num) : IsPGroup 3 E).map ψ
  have hEψ : Nat.card (E.map ψ) ≤ 3 := by
    have hle : Nat.card (E.map ψ) ≤ 4 :=
      (Subgroup.card_le_card_group _).trans (hOut ▸ CFSG.RankThree.PartOne.card_outer_alternating_le_four hn5)
    obtain ⟨j, hj⟩ := hEψp.exists_card_eq
    rw [hj] at hle ⊢
    have : j ≤ 1 := by
      by_contra h
      push Not at h
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases j <;> norm_num
  have hkerL : ψ.ker ⊓ E ≤ L ⊓ E := fun y hy => ⟨hker y hy.1, hy.2⟩
  have h27 : 27 ≤ Nat.card ↥(L ⊓ E) := by
    have hpos : 0 < Nat.card ↥(ψ.ker ⊓ E) := Nat.card_pos
    have h1 : 27 ≤ Nat.card ↥(ψ.ker ⊓ E) := by
      by_contra h
      push Not at h
      have : Nat.card E ≤ 3 * 26 := by
        rw [hcard]
        exact Nat.mul_le_mul hEψ (by omega)
      omega
    exact h1.trans (Subgroup.card_le_of_le hkerL)
  have hrank := (Lemma118R.Input10_6AltRank_holds n 3 X L hn5 Nat.prime_three (by norm_num)
    ⟨eL⟩).1
  have hLE := hrank (L ⊓ E) inf_le_left (isElemAbelian_mono' hEa inf_le_right)
  have hn9 : 3 ≤ n / 3 := by
    by_contra h
    push Not at h
    have : 3 ^ (n / 3) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn6 : n ≠ 6 := by omega
  have hOut2 : Nat.card (Outer ↥L) ∣ 2 := by
    rw [hOut]
    exact (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (by omega)).2
  have h3L : ∀ y : X, y ^ 3 = 1 → y ∈ L := by
    intro y hy
    apply hker
    have h1 : orderOf (ψ y) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy, map_one])
    have h2 : orderOf (ψ y) ∣ 2 := (orderOf_dvd_natCard (ψ y)).trans hOut2
    have h3 : orderOf (ψ y) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have hEL : E ≤ L := fun y hy => h3L y (hEa.2 y hy)
  have hn12 : 4 ≤ n / 3 := by
    have := hrank E hEL hEa
    rw [hEc] at this
    by_contra h
    push Not at h
    have : 3 ^ (n / 3) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxL : x ∈ L := h3L x (by rw [← hx]; exact pow_orderOf_eq_one x)
  obtain ⟨E', hE'L, hE'a, hE'c, hxE'⟩ := (Lemma118R.Input10_5AltMax_holds n 3 X L hn5
    Nat.prime_three (by norm_num) ⟨eL⟩).2 x hxL (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hE'C : E' ≤ Subgroup.centralizer ({x} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE'a.1.is_comm.comm (⟨y, hy⟩ : E') ⟨x, hxE'⟩)
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hE'C hE'a hE'c
  omega

theorem input29_5'_of_spor_lie (hS : Input29_5'Spor) (hL : Input29_5'Lie) :
    Claims1113.Input29_5' := by
  intro X _ _ L hLn hq hK hC hchev hrk x hx hC4 hrk3 hsolv
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hq
  obtain ⟨i, ⟨f⟩⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isCatalogGroup_center_quotient_of_isKGroup hK hq
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn => exact (false_of_alt hLn hq hC f hrk hx hrk3).elim
  | lie d => exact hL X L hLn hq hK hC d ⟨f⟩ hchev hrk x hx hC4 hrk3 hsolv
  | sporadic s => exact (hS X L hLn hq hK hC s ⟨f⟩ hchev hrk x hx hC4 hrk3 hsolv).elim

@[expose] def Input29_5'Rest : Prop := Input29_5'Spor ∧ Input29_5'Lie

end I295

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc8
