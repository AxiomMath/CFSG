module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightPointTwoGroup
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveSplitting

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒟₁" => ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
local notation "τ₁" => ptTr hzC hsup hinf hz hb hnd hV φ he halt

abbrev ptθD : (ptSub φ z hb e).subgroupOf 𝒟₁ ≃* Multiplicative ((𝔼 × ZMod 2) × ZMod 2) :=
  ptLabelOf he hb φ hzC hz hinf (ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt)

local notation "θD" => ptθD hzC hsup hinf hz hb hnd hV φ he halt

theorem coe_bv_ptθD (x : (𝔼 × ZMod 2) × ZMod 2) :
    ((OddQuadraticFive.bv θD x : 𝒟₁) : G) = pt₁ hzC hz hb φ he x :=
  rfl

theorem zmod_two_label_identity (t c c' q : ZMod 2) (h : c = c') :
    t + c + q = t + q + c' := by
  rw [h, add_right_comm]

@[expose] def ptLabels : OddQuadraticFive.Labels θD (b.restrict 𝔼) 1 where
  lab d := (Multiplicative.toAdd (τ₁ d), ptQuad e (Multiplicative.toAdd (τ₁ d)))
  conj d v := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, coe_bv_ptθD, coe_bv_ptθD,
      inv_mul_pt₁_mul hzC hsup hinf hz hb hnd hV φ he halt]
    congr 1
    obtain ⟨w, t⟩ := v
    simp only [trMap_apply, one_smul, one_mul, OddQuadraticFive.rV, Prod.smul_mk, smul_zero,
      smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply]
    refine Prod.ext (Prod.ext rfl ?_) rfl
    exact zmod_two_label_identity _ _ _ _ (BinarySymplecticTransvection.symm_apply hb _ _)

theorem ptLabels_lab (d : 𝒟₁) :
    (ptLabels hzC hsup hinf hz hb hnd hV φ he halt).lab d =
      (Multiplicative.toAdd (τ₁ d), ptQuad e (Multiplicative.toAdd (τ₁ d))) :=
  rfl

theorem mem_B_iff (d : 𝒟₁) : d ∈ (ptSub φ z hb e).subgroupOf 𝒟₁ ↔ τ₁ d = 1 := by
  rw [← ker_ptTr hzC hsup hinf hz hb hnd hV φ he halt, MonoidHom.mem_ker]

theorem ptLabels_faith (d : 𝒟₁)
    (h : ∀ v, d⁻¹ * OddQuadraticFive.bv θD (v, 1) * d = OddQuadraticFive.bv θD (v, 1)) :
    d ∈ (ptSub φ z hb e).subgroupOf 𝒟₁ := by
  have h0 := h 0
  rw [(ptLabels hzC hsup hinf hz hb hnd hV φ he halt).conj] at h0
  have h1 := congrArg Prod.fst (OddQuadraticFive.bv_injective _ h0)
  simp only [zero_add, Prod.fst_zero, map_zero, mul_zero, zero_smul, add_zero,
    ptLabels_lab] at h1
  rw [mem_B_iff]
  exact Multiplicative.toAdd.injective (congrArg Prod.fst h1)

@[expose] def ptActD : bilinIsometryGroup (b.restrict 𝔼) →* MulAut 𝒟₁ where
  toFun s :=
    { toFun := fun d => ⟨ptLevi he hb φ s * d * (ptLevi he hb φ s)⁻¹,
        conj_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
          (ptLevi_mem_normalizer he hb φ hzC hz s) d.2⟩
      invFun := fun d => ⟨(ptLevi he hb φ s)⁻¹ * d * ptLevi he hb φ s, by
        simpa using conj_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
          (inv_mem (ptLevi_mem_normalizer he hb φ hzC hz s)) d.2⟩
      left_inv := fun d => Subtype.ext (by
        change (ptLevi he hb φ s)⁻¹ * (ptLevi he hb φ s * d * (ptLevi he hb φ s)⁻¹) *
          ptLevi he hb φ s = d
        group)
      right_inv := fun d => Subtype.ext (by
        change ptLevi he hb φ s * ((ptLevi he hb φ s)⁻¹ * d * ptLevi he hb φ s) *
          (ptLevi he hb φ s)⁻¹ = d
        group)
      map_mul' := fun d d' => Subtype.ext (by
        change ptLevi he hb φ s * (d * d') * (ptLevi he hb φ s)⁻¹ =
          ptLevi he hb φ s * d * (ptLevi he hb φ s)⁻¹ *
            (ptLevi he hb φ s * d' * (ptLevi he hb φ s)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun d => Subtype.ext (by
    change ptLevi he hb φ 1 * d * (ptLevi he hb φ 1)⁻¹ = d
    rw [map_one, one_mul, inv_one, mul_one])
  map_mul' s t := MulEquiv.ext fun d => Subtype.ext (by
    change ptLevi he hb φ (s * t) * d * (ptLevi he hb φ (s * t))⁻¹ =
      ptLevi he hb φ s * (ptLevi he hb φ t * d * (ptLevi he hb φ t)⁻¹) *
        (ptLevi he hb φ s)⁻¹
    rw [map_mul]
    group)

theorem ptActD_bv (s : bilinIsometryGroup (b.restrict 𝔼)) (v : 𝔼 × ZMod 2) (ε : ZMod 2) :
    ptActD hzC hsup hinf hz hb hnd hV φ he halt s (OddQuadraticFive.bv θD (v, ε)) =
      OddQuadraticFive.bv θD (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, ε) :=
  Subtype.ext (ptLevi_conj_ptHom he hb φ hzC hz s v ε)

theorem map_subA : (OddQuadraticFive.subA θD).map (𝒟₁).subtype = 𝒜₁ := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact pt₁_mem_ptA hzC hz hb φ he v
  · intro hx
    obtain ⟨v, hv⟩ := (mem_ptA_iff he hb φ).1 hx
    refine ⟨OddQuadraticFive.bv θD (v, 0), ⟨v, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, coe_bv_ptθD, pt₁, ptHom_pt, hv]

theorem commutator_eq_subA : commutator 𝒟₁ = OddQuadraticFive.subA θD := by
  apply Subgroup.map_injective (𝒟₁).subtype_injective
  rw [Subgroup.map_subtype_commutator, commutator_ptD₁, map_subA]

omit [FiniteDimensional (ZMod 2) V] in
include hb hnd he in
theorem four_lt_card : 4 < Nat.card 𝔼 := by
  rw [card_pairOrth_eq he hb hnd]
  norm_num

theorem ptTr_zz : τ₁ (OddQuadraticFive.zz θD) = 1 :=
  (mem_B_iff hzC hsup hinf hz hb hnd hV φ he halt _).1 (OddQuadraticFive.zz_mem θD)

theorem exists_lift_sig_zero (w : 𝔼) :
    ∃ d : 𝒟₁, Multiplicative.toAdd (τ₁ d) = w ∧ OddQuadraticFive.sig θD d = 0 := by
  have : Finite 𝔼 := Module.finite_of_finite (ZMod 2)
  set Lb := ptLabels hzC hsup hinf hz hb hnd hV φ he halt with hLb
  obtain ⟨d, hd⟩ := ptTr_surjective hzC hsup hinf hz hb hnd hV φ he halt (Multiplicative.ofAdd w)
  have hlab : (Lb.lab d).1 = w := by
    rw [hLb, ptLabels_lab, hd, toAdd_ofAdd]
  rcases Lb.sig_eq_zero_or_eq (polarBilin_ptQuad he) (ptActD hzC hsup hinf hz hb hnd hV φ he halt)
      (ptActD_bv hzC hsup hinf hz hb hnd hV φ he halt) (restrict_isAlt hb)
      (restrict_nondegenerate hb hnd he) (ptLabels_faith hzC hsup hinf hz hb hnd hV φ he halt)
      (four_lt_card hb hnd he) d with h | h
  · exact ⟨d, by rw [hd, toAdd_ofAdd], h⟩
  · refine ⟨d * OddQuadraticFive.zz θD, ?_, ?_⟩
    · rw [map_mul, ptTr_zz, mul_one, hd, toAdd_ofAdd]
    · rw [Lb.sig_mul_zz (restrict_isAlt hb) (ptLabels_faith hzC hsup hinf hz hb hnd hV φ he halt),
        h, add_self_eq_zero_zmod_two]

theorem exists_split_lifts (eb : Module.Basis (Fin 4) (ZMod 2) 𝔼) :
    ∃ (y : Fin 4 → 𝒟₁) (α : ZMod 2), (∀ i, Multiplicative.toAdd (τ₁ (y i)) = eb i) ∧
      (∀ i, OddQuadraticFive.sig θD (y i) = α • eb i) ∧
      (∀ i j, OddQuadraticFive.om θD (y i) (y j) = 0) := by
  classical
  have : Finite 𝔼 := Module.finite_of_finite (ZMod 2)
  set Lb := ptLabels hzC hsup hinf hz hb hnd hV φ he halt with hLb
  have hb' := restrict_isAlt (e := e) hb
  have hnd' := restrict_nondegenerate hb hnd he
  have hfaith := ptLabels_faith hzC hsup hinf hz hb hnd hV φ he halt
  have hE := four_lt_card hb hnd he
  have hQ := polarBilin_ptQuad he
  have hact := ptActD_bv hzC hsup hinf hz hb hnd hV φ he halt
  set act := ptActD hzC hsup hinf hz hb hnd hV φ he halt with hactdef
  choose x hxτ hxσ using fun i : Fin 4 =>
    exists_lift_sig_zero hzC hsup hinf hz hb hnd hV φ he halt (eb i)
  have hxl : ∀ i, (Lb.lab (x i)).1 = eb i := fun i => by
    rw [hLb, ptLabels_lab, hxτ]
  have hpair : ∀ i j, ∃ c : ZMod 2, i ≠ j →
      OddQuadraticFive.om θD (x i) (x j) = c • (eb i + eb j) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h⟩
    · have h := Lb.sig_eq_zero_or_eq hQ act hact hb' hnd' hfaith hE (x i * x j)
      rw [Lb.sig_mul hb' hfaith, hxσ, hxσ, zero_add, zero_add, Lb.om_comm hb' hfaith,
        Lb.lab_mul_fst hb', hxl, hxl] at h
      obtain ⟨c, hc⟩ := OddQuadraticFive.exists_smul_of_eq_zero_or_eq h
      exact ⟨c, fun _ => hc⟩
  choose cf hcf using hpair
  have htriple : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → cf i j = cf i k ∧ cf i k = cf j k := by
    intro i j k hij hik hjk
    have h := Lb.sig_eq_zero_or_eq hQ act hact hb' hnd' hfaith hE (x i * x j * x k)
    have hs : OddQuadraticFive.sig θD (x i * x j * x k) =
        OddQuadraticFive.om θD (x i) (x j) + OddQuadraticFive.om θD (x i) (x k) +
          OddQuadraticFive.om θD (x j) (x k) := by
      rw [Lb.sig_mul hb' hfaith, Lb.sig_mul hb' hfaith, hxσ, hxσ, hxσ,
        Lb.om_mul_right hb' hfaith, Lb.om_comm hb' hfaith (x i) (x j),
        Lb.om_comm hb' hfaith (x i) (x k), Lb.om_comm hb' hfaith (x j) (x k)]
      abel
    have hl : (Lb.lab (x i * x j * x k)).1 = eb i + eb j + eb k := by
      rw [Lb.lab_mul_fst hb', Lb.lab_mul_fst hb', hxl, hxl, hxl]
    rw [hs, hl, hcf i j hij, hcf i k hik, hcf j k hjk] at h
    obtain ⟨t, ht⟩ := OddQuadraticFive.exists_smul_of_eq_zero_or_eq h
    exact OddQuadraticFive.coeff_triple eb hij hik hjk ht
  obtain ⟨h1, h2⟩ := htriple 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨h3, h4⟩ := htriple 0 1 3 (by decide) (by decide) (by decide)
  obtain ⟨-, h6⟩ := htriple 0 2 3 (by decide) (by decide) (by decide)
  set α := cf 0 1 with hα
  have hlt : ∀ i j : Fin 4, i < j → cf i j = α := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact h1.symm
      | exact (h1.trans h2).symm
      | exact h3.symm
      | exact (h3.trans h4).symm
      | exact (h3.trans h6).symm
      | exact absurd hij (by decide)
  have hom : ∀ i j, i ≠ j → OddQuadraticFive.om θD (x i) (x j) = α • (eb i + eb j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [hcf i j hij, hlt i j h]
    · rw [← Lb.om_comm hb' hfaith, hcf j i hij.symm, hlt j i h, add_comm]
  set y : Fin 4 → 𝒟₁ := fun i => x i * OddQuadraticFive.bv θD (0, α) with hy
  have hyτ : ∀ i, Multiplicative.toAdd (τ₁ (y i)) = eb i := fun i => by
    rw [hy, map_mul, (mem_B_iff hzC hsup hinf hz hb hnd hV φ he halt _).1
      (OddQuadraticFive.bv_mem θD _), mul_one, hxτ]
  have hzω : ∀ d, OddQuadraticFive.om θD d (OddQuadraticFive.bv θD (0, α)) =
      α • (Lb.lab d).1 := fun d => by
    rw [← Lb.om_comm hb' hfaith, Lb.om_bv]
  refine ⟨y, α, hyτ, fun i => ?_, fun i j => ?_⟩
  · rw [hy, Lb.sig_mul hb' hfaith, hxσ, OddQuadraticFive.sig_of_mem (OddQuadraticFive.bv_mem θD _),
      Lb.om_bv, hxl, zero_add, zero_add]
  · by_cases hij : i = j
    · rw [hij, OddQuadraticFive.om_self]
    · rw [hy, Lb.om_mul_left hb' hfaith, Lb.om_mul_right hb' hfaith, hom i j hij, hzω, hxl,
        Lb.om_bv, Lb.lab_mul_bv hb', hxl]
      simp only [smul_add]
      rw [add_assoc (α • eb i + α • eb j)]
      exact add_self_eq_zero_zmod_two (α • eb i + α • eb j)

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
