module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightAbelian
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightGraph
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointStabilizer

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

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

abbrev ptGr (w : 𝔼) : G :=
  ptHom he hb φ hzC hz (Multiplicative.ofAdd (grV (ptQuad e) w))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptGr_zero : ptGr hzC hz hb φ he 0 = z := by
  rw [ptGr, grV, QuadraticMap.map_zero, Prod.mk_zero_zero, ptHom_z]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf in
theorem ptGr_injective : Function.Injective (ptGr hzC hz hb φ he) := fun _ _ h =>
  grV_injective (Q := ptQuad e) (Multiplicative.ofAdd.injective
    (ptHom_injective he hb φ hzC hz hinf h))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptGr_mem (w : 𝔼) : ptGr hzC hz hb φ he w ∈ ptSub φ z hb e := by
  rw [← range_ptHom he hb φ hzC hz]
  exact ⟨_, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptLevi_conj_ptGr (s : bilinIsometryGroup (b.restrict 𝔼)) (w : 𝔼) :
    ptLevi he hb φ s * ptGr hzC hz hb φ he w * (ptLevi he hb φ s)⁻¹ =
      ptGr hzC hz hb φ he (OddQuadraticFive.sE s w) := by
  have h : ((OddQuadraticFive.hV (polarBilin_ptQuad he) s (w, ptQuad e w), 1) :
      (𝔼 × ZMod 2) × ZMod 2) = grV (ptQuad e) (OddQuadraticFive.sE s w) := by
    rw [OddQuadraticFive.hV_apply, grV]
    refine Prod.ext (Prod.ext rfl ?_) rfl
    change ptQuad e w + ptQuad e w + _ = _
    rw [OddQuadraticFive.zmod2_add_self, zero_add]
  rw [ptGr, grV, ptLevi_conj_ptHom, h]

omit [Finite G] in
include hb he hnd in
theorem exists_sE_eq {w w' : 𝔼} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ∃ s : bilinIsometryGroup (b.restrict 𝔼), OddQuadraticFive.sE s w = w' := by
  obtain ⟨k, hk, hkw⟩ := exists_pairStabilizer_apply_eq hb hnd (bilin_f_u he) w.2 w'.2
    (fun h => hw (Subtype.ext h)) (fun h => hw' (Subtype.ext h))
  exact ⟨pairRestrict b _ _ ⟨k, hk⟩, Subtype.ext hkw⟩

include hzC hsup hinf hz hb hnd hV he in
theorem not_conj_z_mul_tauHom
    (halt : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0))
    (B : binarySymMatrices 3) (hB : ¬ ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) :
    ¬ ∃ g : G, g * z * g⁻¹ = z * tauHom φ he (Multiplicative.ofAdd B) := by
  rintro ⟨g, hg⟩
  have hR : z * tauHom φ he (Multiplicative.ofAdd B) ∈ (ℛ : Set G) :=
    mul_mem (mem_sup_right (mem_zpowers z))
      (mem_sup_left ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩))
  have heq := conj_set_eq hzC hsup hinf hz hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hN : z * tauHom φ he (Multiplicative.ofAdd B) ∈ conjClass 𝒩 z := by
    have h : z * tauHom φ he (Multiplicative.ofAdd B) ∈
        {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (ℛ : Set G) := ⟨⟨g, hg⟩, hR⟩
    rw [← heq] at h
    exact h
  rw [halt] at hN
  rcases hN with h | ⟨y, hy, hyx⟩
  · have h1 : tauHom φ he (Multiplicative.ofAdd B) = 1 := by
      have h2 := Set.mem_singleton_iff.1 h
      rwa [mul_eq_left] at h2
    rw [← map_one (tauHom φ he)] at h1
    have h3 := ofAdd_eq_one.1 (tauHom_injective φ he h1)
    apply hB
    intro i
    rw [h3]
    rfl
  · change z * y = z * tauHom φ he (Multiplicative.ofAdd B) at hyx
    rw [mul_right_inj] at hyx
    obtain ⟨B', hB', hB'y⟩ := (mem_tauSet_iff φ he).1 hy
    rw [hyx] at hB'y
    have h4 := tauHom_injective φ he hB'y
    have h5 := hB'.2
    rw [h4] at h5
    exact hB h5

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptHom_b₁_z :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), (1 : ZMod 2)), 1)) =
      z * tauHom φ he (Multiplicative.ofAdd symE₁₁) := by
  rw [ptHom_apply, RadicalLabels.zPow_one, tauHom_symE₁₁ he hb φ,
    RadicalLabels.mul_comm_z hzC (φ.symm _).2]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptHom_e₂_one_z :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd ((ptE₂ he, (1 : ZMod 2)), 1)) =
      z * tauHom φ he (Multiplicative.ofAdd (symE₁₂ + symE₁₁)) := by
  have hsplit : ((ptE₂ he, (1 : ZMod 2)) : 𝔼 × ZMod 2) = (ptE₂ he, 0) + (0, 1) := by
    simp
  rw [ptHom_apply, RadicalLabels.zPow_one, hsplit, ofAdd_add, map_mul, map_mul,
    Subgroup.coe_mul, ofAdd_add, map_mul, tauHom_symE₁₁ he hb φ, tauHom_symE₁₂ he hb φ,
    RadicalLabels.mul_comm_z hzC (mul_mem (φ.symm _).2 (φ.symm _).2)]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptGr_e₂ :
    ptGr hzC hz hb φ he (ptE₂ he) = z * tauHom φ he (Multiplicative.ofAdd symE₁₂) := by
  rw [ptGr, grV, ptQuad_ptE₂, ptHom_apply, RadicalLabels.zPow_one, tauHom_symE₁₂ he hb φ,
    RadicalLabels.mul_comm_z hzC (φ.symm _).2]

theorem zmod_two_eq_add_one_of_add_eq_one : ∀ t q : ZMod 2, t + q = 1 → t = q + 1 := by
  decide

theorem symE₁₁_diag :
    ¬ ∀ i, ((symE₁₁ : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0 :=
  fun h => absurd (h 0) (by decide)

theorem symE₁₂_add_symE₁₁_diag :
    ¬ ∀ i, ((symE₁₂ + symE₁₁ : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0 :=
  fun h => absurd (h 0) (by decide)

include hzC hsup hinf hz hb hnd hV he in
theorem conj_inter_ptSub_eq
    (halt : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)) :
    {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (ptSub φ z hb e : Set G) =
      Set.range (ptGr hzC hz hb φ he) := by
  have hE₂ : ptE₂ he ≠ 0 := fun h => e.ne_zero (Sum.inl 1) (congrArg Subtype.val h)
  ext x
  constructor
  · rintro ⟨⟨g, rfl⟩, hx⟩
    obtain ⟨⟨w, t⟩, hwt⟩ := (mem_smul_ptA_iff he hb φ hzC hz).1
      (conj_mem_ptSub he hb hnd φ hzC hsup hinf hz hV hx)
    rcases zmod_two_cases (t + ptQuad e w) with h0 | h1
    · refine ⟨w, ?_⟩
      rw [← hwt, ptGr, grV, OddQuadraticFive.eq_of_add_eq_zero_zmod2 h0]
    · exfalso
      have ht : t = ptQuad e w + 1 := zmod_two_eq_add_one_of_add_eq_one _ _ h1
      by_cases hw : w = 0
      · subst hw
        rw [QuadraticMap.map_zero, zero_add] at ht
        subst ht
        rw [ptHom_b₁_z] at hwt
        exact not_conj_z_mul_tauHom hzC hsup hinf hz hb hnd hV φ he halt _ symE₁₁_diag
          ⟨g, hwt.symm⟩
      · obtain ⟨s, hs⟩ := exists_sE_eq hb hnd he hw hE₂
        have h2 := ptLevi_conj_ptHom he hb φ hzC hz s (w, t) 1
        rw [hwt, OddQuadraticFive.hV_apply] at h2
        dsimp only at h2
        rw [hs, ht, ptQuad_ptE₂] at h2
        have h3 : ptQuad e w + 1 + ptQuad e w + 0 = 1 := by
          rw [add_zero, add_right_comm, OddQuadraticFive.zmod2_add_self, zero_add]
        rw [h3, ptHom_e₂_one_z] at h2
        refine not_conj_z_mul_tauHom hzC hsup hinf hz hb hnd hV φ he halt _
          symE₁₂_add_symE₁₁_diag ⟨ptLevi he hb φ s * g, ?_⟩
        rw [← h2]
        group
  · rintro ⟨w, rfl⟩
    refine ⟨?_, ptGr_mem hzC hz hb φ he w⟩
    by_cases hw : w = 0
    · subst hw
      exact ⟨1, by rw [ptGr_zero]; group⟩
    · obtain ⟨s, hs⟩ := exists_sE_eq hb hnd he hE₂ hw
      have hN : ptGr hzC hz hb φ he (ptE₂ he) ∈ conjClass 𝒩 z := by
        rw [halt, ptGr_e₂]
        refine Or.inr ⟨_, (mem_tauSet_iff φ he).2 ⟨_, ?_, rfl⟩, rfl⟩
        exact (sym_rank_two_alternating_iff _).2 ⟨Pi.single 2 1, by decide, by decide⟩
      obtain ⟨n, -, hn⟩ := hN
      refine ⟨ptLevi he hb φ s * n, ?_⟩
      rw [← hs, ← ptLevi_conj_ptGr, ← hn]
      group

include hzC hsup hinf hz hb hnd hV he in
theorem conjClass_ptSub_eq
    (halt : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)) :
    conjClass 𝒩₁ z = Set.range (ptGr hzC hz hb φ he) := by
  classical
  have hE₂ : ptE₂ he ≠ 0 := fun h => e.ne_zero (Sum.inl 1) (congrArg Subtype.val h)
  apply le_antisymm
  · rw [← conj_inter_ptSub_eq hzC hsup hinf hz hb hnd hV φ he halt]
    rintro x ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (mem_normalizer_iff.1 hg z).1 (mem_sup_right (mem_zpowers z))⟩
  obtain ⟨ν, hν1, hν2, hν3, -, -, -, -⟩ :=
    translation_group_structure hzC hsup hinf hz hb hnd hV φ he halt
  set ν' : G → binarySymMatrices 3 := fun g => if h : g ∈ 𝒟 then
    ((Multiplicative.toAdd (ν ⟨g, h⟩) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3)
    else 0 with hν'def
  have hν' : ∀ (g : G) (h : g ∈ 𝒟), ν' g =
      ((Multiplicative.toAdd (ν ⟨g, h⟩) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) :=
    fun g h => by simp only [hν'def, h, ↓reduceDIte]
  have hDN : 𝒟 ≤ 𝒩 := map_subtype_le _
  have hDn : ∀ n ∈ 𝒩, ∀ d ∈ 𝒟, n * d * n⁻¹ ∈ 𝒟 := by
    intro n hn d hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact ⟨⟨n, hn⟩ * d' * ⟨n, hn⟩⁻¹,
      (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 𝒩).conj_mem d'
        hd' ⟨n, hn⟩, rfl⟩
  have hνz : ∀ d ∈ 𝒟, d⁻¹ * z * d =
      RadicalLabels.radHom φ he hzC hz (Multiplicative.ofAdd (ν' d, 1)) := by
    intro d hd
    have h := hν1 ⟨d, hd⟩
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one, ← hν' d hd] at h
    change z⁻¹ * d⁻¹ * z * d = _ at h
    rw [RadicalLabels.radHom_apply, RadicalLabels.zPow_one,
      RadicalLabels.mul_comm_z hzC (tauHom_mem φ he _), ← h]
    group
  have hνeq : ∀ d ∈ 𝒟, ∀ d' ∈ 𝒟, ν' d = ν' d' ↔ d⁻¹ * d' ∈ ℛ := by
    intro d hd d' hd'
    rw [hν' d hd, hν' d' hd']
    have hmem : d⁻¹ * d' ∈ ℛ ↔ (⟨d, hd⟩ : 𝒟)⁻¹ * ⟨d', hd'⟩ ∈ ν.ker := by
      rw [hν3, mem_subgroupOf]
      rfl
    rw [hmem, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    constructor
    · intro h
      exact Multiplicative.toAdd.injective (Subtype.ext h)
    · intro h
      rw [h]
  have hS₁₂ : symE₁₂ ∈ BinarySymThreeOrbit.altSym :=
    BinarySymThreeOrbit.mem_altSym_iff.2 (by decide)
  obtain ⟨⟨d, hd⟩, hdν⟩ := hν2 (Multiplicative.ofAdd ⟨symE₁₂, hS₁₂⟩)
  have hdS : ν' d = symE₁₂ := by
    rw [hν' d hd, hdν]
    rfl
  have hdz : d⁻¹ * z * d = ptGr hzC hz hb φ he (ptE₂ he) := by
    rw [hνz d hd, hdS, RadicalLabels.radHom_apply, RadicalLabels.zPow_one, ptGr_e₂,
      RadicalLabels.mul_comm_z hzC (tauHom_mem φ he _)]
  have hdA : tauHom φ he (Multiplicative.ofAdd (ν' d)) ∈ 𝒜₁ := by
    rw [hdS, tauHom_symE₁₂ he hb φ]
    exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
  have hdN₁ : d ∈ 𝒩₁ := mem_normalizer_ptSub_of_mem he hb hnd φ hzC hinf hz hDN hDn hνz hνeq hd hdA
  have he₂ : ptGr hzC hz hb φ he (ptE₂ he) ∈ conjClass 𝒩₁ z :=
    ⟨d⁻¹, inv_mem hdN₁, by rw [inv_inv]; exact hdz⟩
  rintro _ ⟨w, rfl⟩
  by_cases hw : w = 0
  · rw [hw, ptGr_zero]
    exact self_mem_conjClass 𝒩₁ z
  · obtain ⟨s, hs⟩ := exists_sE_eq hb hnd he hE₂ hw
    rw [← hs, ← ptLevi_conj_ptGr]
    exact conj_mem_conjClass (ptLevi_mem_normalizer he hb φ hzC hz s) he₂

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
