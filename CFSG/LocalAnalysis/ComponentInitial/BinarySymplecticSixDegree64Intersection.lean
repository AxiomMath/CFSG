module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointTwoGroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64VectorStabilizer
import CFSG.GroupTheory.PCore.Transport
import CFSG.GroupTheory.PCore.OpenTransport

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

section PCore

variable {X : Type*} [Group X]

theorem pCoreOf_le (p : ℕ) (Y : Subgroup X) : CFSG.Assembly.pCoreOf p Y ≤ Y :=
  CFSG.openPCoreOf_le p Y

theorem isPGroup_pCoreOf (p : ℕ) [Fact p.Prime] (Y : Subgroup X) :
    IsPGroup p (CFSG.Assembly.pCoreOf p Y) := by
  rw [CFSG.Assembly.pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem conj_mem_pCoreOf (p : ℕ) {Y : Subgroup X} {y x : X} (hy : y ∈ Y)
    (hx : x ∈ CFSG.Assembly.pCoreOf p Y) : y * x * y⁻¹ ∈ CFSG.Assembly.pCoreOf p Y := by
  rw [CFSG.Assembly.pCoreOf] at hx ⊢
  obtain ⟨x', hx', rfl⟩ := hx
  exact ⟨⟨y, hy⟩ * x' * ⟨y, hy⟩⁻¹, CFSG.pCore_normal.conj_mem _ hx' _, rfl⟩

theorem le_pCoreOf (p : ℕ) {Y K : Subgroup X} (hKY : K ≤ Y)
    (hn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hp : IsPGroup p K) :
    K ≤ CFSG.Assembly.pCoreOf p Y := by
  intro k hk
  refine ⟨⟨k, hKY hk⟩, ?_, rfl⟩
  have hnorm : (K.subgroupOf Y).Normal := ⟨fun x hx y => by
    rw [mem_subgroupOf] at hx ⊢
    exact hn y y.2 x hx⟩
  have hpK : IsPGroup p (K.subgroupOf Y) := hp.of_equiv (subgroupOfEquivOfLe hKY).symm
  have hle : K.subgroupOf Y ≤ CFSG.Assembly.pCore p Y :=
    le_sSup ⟨hnorm, hpK⟩
  exact hle (by rw [mem_subgroupOf]; exact hk)

theorem card_eq_card_conjClass_mul (M : Subgroup X) (z : X) :
    Nat.card M =
      Nat.card (conjClass M z) * Nat.card (M ⊓ centralizer ({z} : Set X) : Subgroup X) := by
  rw [card_conjClass, inf_comm, Subgroup.relIndex_mul_card]

theorem card_smul_set (z : X) (S : Set X) : Nat.card (z • S : Set X) = Nat.card S := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Set.image_smul,
    Set.ncard_image_of_injective _ (MulAction.injective z)]

end PCore

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

omit he hnd in
theorem pullSub_inf (P Q : Subgroup (bilinIsometryGroup b)) :
    pullSub φ (P ⊓ Q) = pullSub φ P ⊓ pullSub φ Q := by
  ext x
  simp only [mem_inf, mem_pullSub]
  constructor
  · rintro ⟨h, hP, hQ⟩
    exact ⟨⟨h, hP⟩, ⟨h, hQ⟩⟩
  · rintro ⟨⟨h, hP⟩, ⟨_, hQ⟩⟩
    exact ⟨h, hP, hQ⟩

omit hnd in
include he in
theorem card_ptA_inf_radA : Nat.card (𝒜₁ ⊓ 𝒜₂ : Subgroup G) = 8 := by
  rw [← pullSub_inf, card_pullSub, card_pointRadical_inf hb he]

abbrev jSym (c x x' : ZMod 2) : ↥(binarySymMatrices 3) :=
  ⟨jMat c x x', mem_binarySymMatrices.2 (jMat_transpose c x x')⟩

omit hnd in
theorem mem_ptA_inf_radA_iff {x : G} :
    x ∈ 𝒜₁ ⊓ 𝒜₂ ↔ ∃ c y y' : ZMod 2, tauHom φ he (Multiplicative.ofAdd (jSym c y y')) = x := by
  rw [← pullSub_inf, mem_pullSub]
  constructor
  · rintro ⟨h, hP⟩
    obtain ⟨c, y, y', hmat⟩ := (mem_pointRadical_inf_iff_jMat hb he).1 hP
    exact ⟨c, y, y', (eq_tauHom_of_toMatrix φ he h (jSym c y y') hmat).symm⟩
  · rintro ⟨c, y, y', rfl⟩
    refine ⟨tauHom_mem φ he _, (mem_pointRadical_inf_iff_jMat hb he).2 ⟨c, y, y', ?_⟩⟩
    exact toMatrix_tauHom φ he _

omit he hnd in
theorem symThreeDiag_jMat (c y y' : ZMod 2) : symThreeDiag (jMat c y y') = ![c, 0, 0] := by
  funext k
  fin_cases k <;> rfl

theorem zmod_two_polar_single : ∀ c c' : ZMod 2,
    symThreePolar ![c, 0, 0] ![c', 0, 0] = 0 := by
  decide

omit he hnd in
theorem polarSym_jSym (c y y' c' x x' : ZMod 2) :
    symThreePolarSym (symThreeDiag (jSym c y y' : M₃)) (symThreeDiag (jSym c' x x' : M₃)) = 0 :=
  Subtype.ext (by
    change symThreePolar (symThreeDiag (jMat c y y')) (symThreeDiag (jMat c' x x')) = 0
    rw [symThreeDiag_jMat, symThreeDiag_jMat]
    exact zmod_two_polar_single c c')

include he hzC hinf hz in
theorem card_ptSub_inf_radSub : Nat.card (ptSub φ z hb e ⊓ radSub φ z e : Subgroup G) = 16 := by
  have hinj := hModel_injective φ hzC hinf hz
  rw [← map_hModel_pointRadicalProd hb φ hzC hz, ← map_hModel_lagrangianRadicalProd φ hzC hz,
    ← Subgroup.map_inf_eq _ _ _ hinj, card_map_of_injective hinj]
  have h : pointRadicalProd hb e ⊓ lagrangianRadicalProd b e =
      (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) ⊓
        pointwiseStabilizer b (lagrangianOf e)).prod ⊤ := by
    ext x
    simp only [mem_inf, mem_pointRadicalProd, mem_lagrangianRadicalProd, Subgroup.mem_prod,
      mem_top, and_true]
  rw [h, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_pointRadical_inf hb he, Subgroup.card_top, card_zetaGroup]

omit hnd in
include he in
theorem exists_ptHomV_of_mem_ptA_inf_radA {x : G} (hx : x ∈ 𝒜₁ ⊓ 𝒜₂) :
    ∃ v : 𝔼 × ZMod 2, ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) = x ∧
      e.repr (v.1 : V) (Sum.inr 1) = 0 ∧ e.repr (v.1 : V) (Sum.inr 2) = 0 := by
  obtain ⟨hxA, hxR⟩ := mem_inf.1 hx
  obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 hxA
  obtain ⟨_, hR⟩ := mem_pullSub.1 hxR
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ptHomV_apply, ptElt_eq] at hR
  have hfix : ∀ j : Fin 3, j ≠ 0 → e.repr (v.1 : V) (Sum.inr j) = 0 := by
    intro j hj
    have h1 := hR (e (Sum.inl j)) (Submodule.subset_span ⟨j, rfl⟩)
    change pointMap b (e (Sum.inl 0)) (v.1 : V) _ (e (Sum.inl j)) = e (Sum.inl j) at h1
    have hu0 : b (e (Sum.inl 0)) (e (Sum.inl j)) = 0 := by
      simp [bilin_inl he]
    rw [pointMap_apply, hu0, zero_smul, add_zero, add_eq_left, bilin_inl he] at h1
    exact (smul_eq_zero.1 h1).resolve_right (e.ne_zero _)
  exact ⟨v, rfl, hfix 1 (by decide), hfix 2 (by decide)⟩

theorem mem_pairOrth_inl_two (he : IsSymplecticBasis b e) : e (Sum.inl 2) ∈ 𝔼 := by
  rw [mem_pairOrth, bilin_inl he, bilin_inr he]
  simp

abbrev ptE₃ (he : IsSymplecticBasis b e) : 𝔼 := ⟨e (Sum.inl 2), mem_pairOrth_inl_two he⟩

omit hnd in
include he in
theorem ptLevi_mem_radA {s : bilinIsometryGroup (b.restrict 𝔼)}
    (h2 : OddQuadraticFive.sE s (ptE₂ he) = ptE₂ he)
    (h3 : OddQuadraticFive.sE s (ptE₃ he) = ptE₃ he) : ptLevi he hb φ s ∈ 𝒜₂ := by
  set k := (MulEquiv.ofBijective (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)))
    (pairRestrict_bijective hb (bilin_f_u he))).symm s with hk
  have hks : pairRestrict b _ _ k = s := pairRestrict_ptLevi he hb s
  refine mem_pullSub.2 ⟨ptLevi_mem he hb φ s, ?_⟩
  have hφ : φ ⟨ptLevi he hb φ s, ptLevi_mem he hb φ s⟩ = (k : bilinIsometryGroup b) := by
    change φ (φ.symm (k : bilinIsometryGroup b)) = _
    exact MulEquiv.apply_symm_apply φ _
  rw [hφ]
  have hfix : ∀ j : Fin 3, (((k : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) (e (Sum.inl j)) = e (Sum.inl j) := by
    intro j
    fin_cases j
    · exact (mem_pairStabilizer.1 k.2).1
    · have h := congrArg Subtype.val h2
      rw [← hks] at h
      exact h
    · have h := congrArg Subtype.val h3
      rw [← hks] at h
      exact h
  have hle : lagrangianOf e ≤ LinearMap.eqLocus (((k : bilinIsometryGroup b) :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) LinearMap.id := by
    rw [lagrangianOf, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hfix j
  intro w hw
  exact hle hw

omit hnd in
include he in
theorem pointElt_mem_ptA_inf_radA {w : 𝔼} (h1 : e.repr (w : V) (Sum.inr 1) = 0)
    (h2 : e.repr (w : V) (Sum.inr 2) = 0) (c : ZMod 2) :
    ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G) ∈ 𝒜₁ ⊓ 𝒜₂ := by
  have hwW : (w : V) ∈ lagrangianOf e := by
    rw [mem_lagrangianOf, mem_lagrangianZero]
    intro j
    fin_cases j
    · exact repr_inr_zero he w
    · exact h1
    · exact h2
  refine mem_inf.2 ⟨mem_pullSub.2 ⟨(φ.symm _).2, ?_⟩, mem_pullSub.2 ⟨(φ.symm _).2, ?_⟩⟩
  · rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact pointElt_mem_pointRadical hb w.2 c
  · rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact pointElt_mem_pointwiseStabilizer he hb w.2 hwW c

include hnd hsup hinf in
theorem exists_mem_inf_conj_eq [Finite G] {D₁ D₂ : Subgroup G} {ν₁ : G → 𝔼 × ZMod 2}
    {ν₂ : G → ↥(binarySymMatrices 3)} {κ₂ lam : ZMod 2}
    (hD₂N : D₂ ≤ 𝒩₂) (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂eq : ∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ ℛ)
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂)
    (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hBD₁ : ℬ₁ ≤ D₁)
    (hν₁z : ∀ d ∈ D₁, d⁻¹ * z * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd (ν₁ d, 1)))
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      m = d * c)
    {j : G} (hj : j ∈ 𝒜₁ ⊓ 𝒜₂) :
    ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j := by
  obtain ⟨c₀, y₀, y₀', rfl⟩ := (mem_ptA_inf_radA_iff he hb φ).1 hj
  obtain ⟨u, hu, hνu⟩ := hν₂surj (jSym c₀ y₀ y₀')
  have huN : u ∈ 𝒩₁ := mem_normalizer_ptSub_of_mem he hb hnd φ hzC hinf hz hD₂N hD₂n hν₂z hν₂eq
    hu (by rw [hνu]; exact (mem_inf.1 hj).1)
  have hzu : u⁻¹ * z * u = z * tauHom φ he (Multiplicative.ofAdd (jSym c₀ y₀ y₀')) := by
    rw [hν₂z u hu, hνu, radHom_one_eq φ he hzC hz]
  have huJ : ∀ x ∈ 𝒜₁ ⊓ 𝒜₂, u⁻¹ * x * u = x := by
    intro x hx
    obtain ⟨c, y, y', rfl⟩ := (mem_ptA_inf_radA_iff he hb φ).1 hx
    have h := hact₂ u hu (jSym c y y') 0
    rw [hνu, polarSym_jSym, smul_zero, add_zero, zero_smul, add_zero, radHom_tau] at h
    exact h
  obtain ⟨d', hd', c, hc, hu_eq⟩ := hprod₁ u huN
  have hcN : c ∈ 𝒩₁ := (mem_inf.1 hc).1
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  have hd : c⁻¹ * d' * c ∈ D₁ := by
    have h := hD₁n c⁻¹ (inv_mem hcN) d' hd'
    rwa [inv_inv] at h
  have hu_cd : u = c * (c⁻¹ * d' * c) := by rw [hu_eq]; group
  set d := c⁻¹ * d' * c with hd_def
  have hzd : d⁻¹ * z * d = z * tauHom φ he (Multiplicative.ofAdd (jSym c₀ y₀ y₀')) := by
    have h1 : d = c⁻¹ * u := by rw [hu_cd]; group
    have hcz' : c * z * c⁻¹ = z := by rw [hcz, mul_inv_cancel_right]
    rw [h1, ← hzu]
    calc (c⁻¹ * u)⁻¹ * z * (c⁻¹ * u) = u⁻¹ * (c * z * c⁻¹) * u := by group
      _ = u⁻¹ * z * u := by rw [hcz']
  obtain ⟨vj, hvj, hvj1, hvj2⟩ := exists_ptHomV_of_mem_ptA_inf_radA he hb φ hj
  have hνd : ν₁ d = vj := by
    have h2 : z * tauHom φ he (Multiplicative.ofAdd (jSym c₀ y₀ y₀')) =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (vj, 1)) := by
      rw [ptHom_apply, zPow_one, ← hvj, mul_comm_z hzC (φ.symm _).2]
    have h3 := ptHom_injective he hb φ hzC hz hinf (((hν₁z d hd).symm.trans hzd).trans h2)
    exact congrArg Prod.fst (Multiplicative.ofAdd.injective h3)
  have hdJ : ∀ x ∈ 𝒜₁ ⊓ 𝒜₂, d⁻¹ * x * d = x := by
    intro x hx
    obtain ⟨v, hv, hv1, hv2⟩ := exists_ptHomV_of_mem_ptA_inf_radA he hb φ hx
    have h := hact₁ d hd v 0
    have hb0 : b ((ν₁ d).1 : V) (v.1 : V) = 0 := by
      rw [hνd, form_pointSpan he, hvj1, hvj2, hv1, hv2]
      ring
    rw [hb0, mul_zero, zero_smul, add_zero, zero_smul, add_zero, ptHom_pt, hv] at h
    exact h
  have hcJ : ∀ x ∈ 𝒜₁ ⊓ 𝒜₂, c * x * c⁻¹ = x := by
    intro x hx
    have h1 := huJ x hx
    have h2 := hdJ x hx
    rw [hu_cd] at h1
    have h3 : c⁻¹ * x * c = x := by
      have h4 : d⁻¹ * (c⁻¹ * x * c) * d = d⁻¹ * x * d := by
        rw [h2]
        calc d⁻¹ * (c⁻¹ * x * c) * d = (c * d)⁻¹ * x * (c * d) := by group
          _ = x := h1
      have h5 := congrArg (fun y => d * y * d⁻¹) h4
      simpa [mul_assoc] using h5
    calc c * x * c⁻¹ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [h3]
      _ = x := by group
  set cN : (𝒩₁ ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G) := ⟨c, hc⟩ with hcN_def
  set s := ptStab he hb hnd φ hzC hsup hinf hz cN with hs
  have hfixw : ∀ w : 𝔼, e.repr (w : V) (Sum.inr 1) = 0 → e.repr (w : V) (Sum.inr 2) = 0 →
      OddQuadraticFive.sE s w = w := by
    intro w hw1 hw2
    have hx := pointElt_mem_ptA_inf_radA he hb φ hw1 hw2 0
    have h1 := ptStab_conj_pointElt he hb hnd φ hzC hsup hinf hz cN w 0
    rw [← hs] at h1
    change c * _ * c⁻¹ = _ at h1
    rw [hcJ _ hx] at h1
    have h2 : pointElt hb (mem_pairOrth_left w.2) 0 =
        pointElt hb (mem_pairOrth_left (OddQuadraticFive.sE s w).2) 0 :=
      φ.symm.injective (Subtype.ext h1)
    have h3 := pointMap_inj hb (bilin_f_u he) w.2 (OddQuadraticFive.sE s w).2
      (congrArg (fun g : bilinIsometryGroup b =>
        ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) h2)
    exact (Subtype.ext h3.1).symm
  have hℓA : ptLevi he hb φ s ∈ 𝒜₂ := ptLevi_mem_radA he hb φ
    (hfixw _ (by simp [Basis.repr_self])
      (by simp [Basis.repr_self]))
    (hfixw _ (by simp [Basis.repr_self])
      (by simp [Basis.repr_self]))
  have hℓN := ptLevi_mem_ptStabSub he hb φ hzC hz s
  have hb' : (ptLevi he hb φ s)⁻¹ * c ∈ ℬ₁ := by
    have hker : (⟨ptLevi he hb φ s, hℓN⟩ : (𝒩₁ ⊓ centralizer (Singleton.singleton z : Set G) :
        Subgroup G))⁻¹ * cN ∈ (ptStab he hb hnd φ hzC hsup hinf hz).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ptStab_ptLevi, ← hs, inv_mul_cancel]
    rw [ker_ptStab, mem_subgroupOf] at hker
    exact hker
  refine ⟨(ptLevi he hb φ s)⁻¹ * u, mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · have h : (ptLevi he hb φ s)⁻¹ * u = ((ptLevi he hb φ s)⁻¹ * c) * d := by
      rw [hu_cd]
      group
    rw [h]
    exact mul_mem (hBD₁ hb') hd
  · exact mul_mem (inv_mem (hRD₂ (mem_sup_left hℓA))) hu
  · have hℓz : ptLevi he hb φ s * z = z * ptLevi he hb φ s := ptLevi_mul_z he hb φ hzC s
    calc ((ptLevi he hb φ s)⁻¹ * u)⁻¹ * z * ((ptLevi he hb φ s)⁻¹ * u) =
        u⁻¹ * (ptLevi he hb φ s * z * (ptLevi he hb φ s)⁻¹) * u := by group
      _ = u⁻¹ * z * u := by rw [hℓz, mul_inv_cancel_right]
      _ = _ := hzu

omit hb hnd in
include he hzC hinf hz in
theorem card_radSub : Nat.card (radSub φ z e) = 128 := by
  rw [← map_hModel_lagrangianRadicalProd φ hzC hz,
    card_map_of_injective (hModel_injective φ hzC hinf hz), card_lagrangianRadicalProd he]

include he hzC hinf hz in
theorem card_ptSub_sup_radSub : Nat.card (ptSub φ z hb e ⊔ radSub φ z e : Subgroup G) = 512 := by
  rw [← map_hModel_radicalProduct hb φ hzC hz,
    card_map_of_injective (hModel_injective φ hzC hinf hz), card_radicalProduct hb he]

include he hnd hsup in
theorem ptSub_le_centralizer : ptSub φ z hb e ≤ centralizer ({z} : Set G) := by
  rw [← hsup]
  exact sup_le_sup_right ((ptA_facts he hb hnd φ).1) _

omit he hb hnd in
include hsup in
theorem radSub_le_centralizer : radSub φ z e ≤ centralizer ({z} : Set G) := by
  rw [← hsup]
  exact sup_le_sup_right (pullSub_le φ _) _

omit he hb hnd hsup hinf hz in
include hzC in
theorem mem_normalizer_zpowers {a : G} (ha : a ∈ L) :
    a ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
  centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ ht =>
    (mem_centralizer_iff.1 (zpowers_le_centralizer hzC ht) a ha).symm)

include he hnd hzC in
theorem radSub_le_normalizer_ptSub :
    radSub φ z e ≤ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, hAN, -⟩ := ptA_facts he hb hnd φ
  refine sup_le (fun a ha => ?_) (fun _ ht => le_normalizer (mem_sup_right ht))
  obtain ⟨haL, haP⟩ := mem_pullSub.1 ha
  have haV : a ∈ pullSub φ (vecStabilizer b (e (Sum.inl 0))) := mem_pullSub.2 ⟨haL, by
    rw [mem_vecStabilizer]
    exact haP _ (Submodule.subset_span ⟨0, rfl⟩)⟩
  rw [← hAN] at haV
  exact inf_normalizer_le_normalizer_sup _ _
    (mem_inf.2 ⟨(mem_inf.1 haV).1, mem_normalizer_zpowers hzC haL⟩)

omit hsup in
include he hnd hzC hinf hz in
theorem mem_normalizer_ptSub_iff_of_mem {l : G} (hl : l ∈ L) :
    l ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ↔
      l ∈ normalizer (pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) : Set G) := by
  obtain ⟨-, -, -, hBL⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  constructor
  · intro hlN
    rw [mem_normalizer_iff]
    intro x
    rw [← hBL, mem_inf, mem_inf]
    constructor
    · rintro ⟨hx, hxL⟩
      exact ⟨(mem_normalizer_iff.1 hlN x).1 hx, mul_mem (mul_mem hl hxL) (inv_mem hl)⟩
    · rintro ⟨hx, hxL⟩
      refine ⟨(mem_normalizer_iff.1 hlN x).2 hx, ?_⟩
      have h := mul_mem (mul_mem (inv_mem hl) hxL) hl
      simpa [mul_assoc] using h
  · intro hlA
    exact inf_normalizer_le_normalizer_sup _ _ (mem_inf.2 ⟨hlA, mem_normalizer_zpowers hzC hl⟩)

section Sigma

variable (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
  (hσcol : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (hn : (n : G) ∈ L) (j : Fin 3),
    linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i))
  (hσker : σ.ker = (radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G)))
  (hσsurj : Function.Surjective σ)

local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

omit hb hnd in
include hσcol in
theorem sigma_apply_of_mem (n : 𝒩₂₀) (hn : (n : G) ∈ L) (i j : Fin 3) :
    (σ n : M₃) i j = e.repr (linOf (φ ⟨n, hn⟩) (e (Sum.inl j))) (Sum.inl i) := by
  rw [hσcol n hn j, map_sum]
  simp [Basis.repr_self, Finsupp.single_apply]

omit he hb hnd hsup hinf hz in
include hσker in
theorem sigma_eq_one_of_mem (n : 𝒩₂₀) (hn : (n : G) ∈ radSub φ z e) : σ n = 1 := by
  have h : n ∈ σ.ker := by
    rw [hσker, mem_subgroupOf]
    exact hn
  exact h

include he hnd hzC hsup hinf hz hσcol hσker in
theorem mem_normalizer_ptSub_iff_sigma (n : 𝒩₂₀) :
    (n : G) ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ↔ σ n ∈ vecStabGL := by
  obtain ⟨-, -, -, -, hAN, -⟩ := ptA_facts he hb hnd φ
  have hnH : (n : G) ∈ L ⊔ zpowers z := by
    rw [hsup]
    exact (mem_inf.1 n.2).2
  obtain ⟨l, hl, t, ht, hlt⟩ := (mem_sup_of_le_centralizer (zpowers_le_centralizer hzC)).1 hnH
  have htR : t ∈ radSub φ z e := mem_sup_right ht
  have htN : t ∈ 𝒩₂₀ := mem_inf.2 ⟨le_normalizer htR,
    radSub_le_centralizer φ hsup htR⟩
  have hlN : l ∈ 𝒩₂₀ := by
    have h := mul_mem n.2 (inv_mem htN)
    rwa [← hlt, mul_inv_cancel_right] at h
  have hσn : σ n = σ ⟨l, hlN⟩ := by
    have h1 : n = ⟨l, hlN⟩ * ⟨t, htN⟩ := Subtype.ext hlt.symm
    rw [h1, map_mul, sigma_eq_one_of_mem φ σ hσker ⟨t, htN⟩ htR, mul_one]
  have htB : t ∈ ptSub φ z hb e := mem_sup_right ht
  have hN1 : (n : G) ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ↔
      l ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
    rw [← hlt]
    constructor
    · intro h
      have h' := mul_mem h (inv_mem (le_normalizer htB))
      rwa [mul_inv_cancel_right] at h'
    · intro h
      exact mul_mem h (le_normalizer htB)
  rw [hN1, mem_normalizer_ptSub_iff_of_mem he hb hnd φ hzC hinf hz hl, hσn]
  have hmem : l ∈ normalizer (pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) :
      Set G) ↔ l ∈ pullSub φ (vecStabilizer b (e (Sum.inl 0))) := by
    rw [← hAN, mem_inf]
    exact ⟨fun h => ⟨h, hl⟩, fun h => h.1⟩
  rw [hmem, mem_pullSub, mem_vecStabGL]
  have hcol : ∀ i : Fin 3, (σ ⟨l, hlN⟩ : M₃) i 0 =
      e.repr (linOf (φ ⟨l, hl⟩) (e (Sum.inl 0))) (Sum.inl i) :=
    fun i => sigma_apply_of_mem φ σ hσcol ⟨l, hlN⟩ hl i 0
  constructor
  · rintro ⟨_, h⟩
    change linOf (φ ⟨l, hl⟩) (e (Sum.inl 0)) = e (Sum.inl 0) at h
    rw [hcol, hcol, hcol, h]
    simp [Basis.repr_self]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨hl, ?_⟩
    change linOf (φ ⟨l, hl⟩) (e (Sum.inl 0)) = e (Sum.inl 0)
    rw [hσcol ⟨l, hlN⟩ hl 0, Fin.sum_univ_three, h0, h1, h2]
    simp

include he hσcol in
theorem sigma_mem_lagrangianT0_of_mem_ptA (a : 𝒩₂₀)
    (ha : (a : G) ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))) :
    σ a ∈ lagrangianT0 := by
  obtain ⟨haL, haP⟩ := mem_pullSub.1 ha
  obtain ⟨w, hw, c, hwc⟩ := (mem_pointRadical hb).1 haP
  have hw0 : e.repr w (Sum.inr 0) = 0 := repr_inr_zero he ⟨w, hw⟩
  have hent : ∀ i j : Fin 3, (σ a : M₃) i j =
      e.repr (e (Sum.inl j) + e.repr w (Sum.inr j) • e (Sum.inl 0)) (Sum.inl i) := by
    intro i j
    rw [sigma_apply_of_mem φ σ hσcol a haL i j, hwc]
    change e.repr (pointMap b (e (Sum.inl 0)) w c (e (Sum.inl j))) (Sum.inl i) = _
    rw [pointMap_apply, bilin_inl he j w, bilin_inl he 0 (e (Sum.inl j)), Basis.repr_self]
    simp
  refine (mem_lagrangianT0).2 ⟨e.repr w (Sum.inr 1), e.repr w (Sum.inr 2), Units.ext ?_⟩
  rw [coe_t0Unit]
  ext i j
  rw [hent]
  fin_cases i <;> fin_cases j <;> simp [t0Mat, hw0, Basis.repr_self]

include he hnd hzC hsup hz hσcol hσker in
theorem sigma_mem_lagrangianT0 (n : 𝒩₂₀) (hn : (n : G) ∈ ptSub φ z hb e ⊔ radSub φ z e) :
    σ n ∈ lagrangianT0 := by
  have hBR : ptSub φ z hb e ⊔ radSub φ z e =
      pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊔ radSub φ z e := by
    rw [ptSub, sup_assoc, sup_eq_right.2 (le_sup_right : zpowers z ≤ radSub φ z e)]
  have hAN : pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ≤ 𝒩₂₀ :=
    fun a ha => mem_inf.2 ⟨ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left ha),
      ptSub_le_centralizer he hb hnd φ hsup (mem_sup_left ha)⟩
  have hRN : radSub φ z e ≤ 𝒩₂₀ :=
    fun r hr => mem_inf.2 ⟨le_normalizer hr, radSub_le_centralizer φ hsup hr⟩
  have hle : (ptSub φ z hb e ⊔ radSub φ z e).subgroupOf 𝒩₂₀ ≤ lagrangianT0.comap σ := by
    rw [hBR, subgroupOf_sup hAN hRN]
    refine sup_le (fun a ha => ?_) (fun r hr => ?_)
    · rw [mem_subgroupOf] at ha
      exact sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol a ha
    · rw [mem_comap, sigma_eq_one_of_mem φ σ hσker r (by rwa [mem_subgroupOf] at hr)]
      exact one_mem _
  exact hle (by rw [mem_subgroupOf]; exact hn)

include he hnd hzC hsup hinf hz hσcol hσker hσsurj in
theorem subgroupOf_ptSub_sup_radSub [Finite G] :
    (ptSub φ z hb e ⊔ radSub φ z e).subgroupOf 𝒩₂₀ = lagrangianT0.comap σ := by
  have hXN : ptSub φ z hb e ⊔ radSub φ z e ≤ 𝒩₂₀ := sup_le
    (fun a ha => mem_inf.2 ⟨ptSub_le_normalizer_radSub he hb φ hzC hz ha,
      ptSub_le_centralizer he hb hnd φ hsup ha⟩)
    (fun r hr => mem_inf.2 ⟨le_normalizer hr, radSub_le_centralizer φ hsup hr⟩)
  have hRN : radSub φ z e ≤ 𝒩₂₀ := le_sup_right.trans hXN
  have hTr : lagrangianT0 ≤ σ.range := by
    rw [MonoidHom.range_eq_top.2 hσsurj]
    exact le_top
  apply Subgroup.eq_of_le_of_card_ge (fun x hx => sigma_mem_lagrangianT0 he hb hnd φ hzC hsup hz σ
    hσcol hσker x (by rwa [mem_subgroupOf] at hx))
  rw [OddQuadraticFive.FullCoset.card_comap_eq σ hTr, card_lagrangianT0, hσker,
    Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv, card_radSub he φ hzC hinf hz,
    Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv, card_ptSub_sup_radSub he hb φ hzC hinf hz]

include he hnd hzC hsup hinf hz hσcol hσker hσsurj in
theorem card_normalizer_inf_centralizer :
    Nat.card ((normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
      normalizer ((radSub φ z e : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G) :
        Subgroup G) = 3072 := by
  have hY : (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
      normalizer ((radSub φ z e : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G) ≤ 𝒩₂₀ :=
    fun x hx => mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).2, (mem_inf.1 hx).2⟩
  have hR : radSub φ z e ≤ 𝒩₂₀ :=
    fun r hr => mem_inf.2 ⟨le_normalizer hr, radSub_le_centralizer φ hsup hr⟩
  have heq : ((normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
      normalizer ((radSub φ z e : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G)).subgroupOf
        𝒩₂₀ = vecStabGL.comap σ := by
    ext n
    rw [mem_subgroupOf, mem_comap, ← mem_normalizer_ptSub_iff_sigma he hb hnd φ hzC hsup hinf hz σ
      hσcol hσker n]
    constructor
    · intro h
      exact (mem_inf.1 (mem_inf.1 h).1).1
    · intro h
      exact mem_inf.2 ⟨mem_inf.2 ⟨h, (mem_inf.1 n.2).1⟩, (mem_inf.1 n.2).2⟩
  have hSr : vecStabGL ≤ σ.range := by
    rw [MonoidHom.range_eq_top.2 hσsurj]
    exact le_top
  rw [← Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv, heq,
    OddQuadraticFive.FullCoset.card_comap_eq σ hSr, card_vecStabGL, hσker,
    Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv, card_radSub he φ hzC hinf hz]

include he hnd hzC hsup hinf hz hσcol hσker hσsurj in
theorem le_ptSub_sup_radSub_of_normal [Finite G] {P : Subgroup G}
    (hPY : P ≤ (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
      normalizer ((radSub φ z e : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G))
    (hn : ∀ y ∈ (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
      normalizer ((radSub φ z e : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G),
        ∀ p ∈ P, y * p * y⁻¹ ∈ P)
    (h2 : IsPGroup 2 P) : P ≤ ptSub φ z hb e ⊔ radSub φ z e := by
  have hPN : P ≤ 𝒩₂₀ := fun x hx =>
    mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 (hPY hx)).1).2, (mem_inf.1 (hPY hx)).2⟩
  set Q := (P.subgroupOf 𝒩₂₀).map σ with hQ
  have hQS : Q ≤ vecStabGL := by
    rintro _ ⟨p, hp, rfl⟩
    have hp : (p : G) ∈ P := hp
    exact (mem_normalizer_ptSub_iff_sigma he hb hnd φ hzC hsup hinf hz σ hσcol hσker p).1
      (mem_inf.1 (mem_inf.1 (hPY hp)).1).1
  have hQn : ∀ g ∈ vecStabGL, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    rintro g hg _ ⟨p, hp, rfl⟩
    obtain ⟨y, rfl⟩ := hσsurj g
    have hyY : (y : G) ∈ (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
        normalizer ((radSub φ z e : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G) :=
      mem_inf.2 ⟨mem_inf.2 ⟨(mem_normalizer_ptSub_iff_sigma he hb hnd φ hzC hsup hinf hz σ hσcol
        hσker y).2 hg, (mem_inf.1 y.2).1⟩, (mem_inf.1 y.2).2⟩
    have hp : (p : G) ∈ P := hp
    refine ⟨y * p * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (mem_subgroupOf.2 (hn _ hyY _ hp) : y * p * y⁻¹ ∈ P.subgroupOf 𝒩₂₀)
  have hQ2 : IsPGroup 2 Q :=
    (h2.of_equiv (subgroupOfEquivOfLe hPN).symm).map σ
  have hQT := le_lagrangianT0_of_normal hQS hQn hQ2
  intro p hp
  have h1 : σ ⟨p, hPN hp⟩ ∈ lagrangianT0 :=
    hQT ⟨⟨p, hPN hp⟩, (mem_subgroupOf.2 hp : (⟨p, hPN hp⟩ : 𝒩₂₀) ∈ P.subgroupOf 𝒩₂₀), rfl⟩
  have h2' : (⟨p, hPN hp⟩ : 𝒩₂₀) ∈ (ptSub φ z hb e ⊔ radSub φ z e).subgroupOf 𝒩₂₀ := by
    rw [subgroupOf_ptSub_sup_radSub he hb hnd φ hzC hsup hinf hz σ hσcol hσker hσsurj]
    exact h1
  rwa [mem_subgroupOf] at h2'

end Sigma

include he hnd hsup hinf in
theorem degree64_intersections [Finite G] {D₁ D₂ : Subgroup G} {ν₁ : G → 𝔼 × ZMod 2}
    {ν₂ : G → ↥(binarySymMatrices 3)} {κ₂ lam : ZMod 2}
    (hD₂N : D₂ ≤ 𝒩₂) (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂eq : ∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ ℛ)
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hBD₁ : ℬ₁ ≤ D₁)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hν₁z : ∀ d ∈ D₁, d⁻¹ * z * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd (ν₁ d, 1)))
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      m = d * c)
    (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
    (hσcol : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
        centralizer (Singleton.singleton z : Set G) : Subgroup G)) (hn : (n : G) ∈ L)
        (j : Fin 3),
      linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i))
    (hσker : σ.ker = (radSub φ z e).subgroupOf
      (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
        centralizer (Singleton.singleton z : Set G)))
    (hσsurj : Function.Surjective σ)
    (hfull₁ : conjClass 𝒩₁ z = z • (𝒜₁ : Set G))
    (hfull : conjClass 𝒩₂ z = z • (𝒜₂ : Set G)) :
    conjClass (D₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) ∧
      Nat.card (D₁ ⊓ D₂ : Subgroup G) = 128 ∧
      Nat.card (𝒩₁ ⊓ 𝒩₂ : Subgroup G) = 24576 ∧
      Nat.card (CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂)) = 4096 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := card_ptA_inf_radA he hb φ
  have hsub : ∀ {M : Subgroup G}, M ≤ 𝒩₁ → M ≤ 𝒩₂ →
      conjClass M z ⊆ z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) := by
    intro M h1 h2 x hx
    have hx1 := conjClass_mono h1 z hx
    have hx2 := conjClass_mono h2 z hx
    rw [hfull₁] at hx1
    rw [hfull] at hx2
    rw [coe_inf, Set.smul_set_inter]
    exact ⟨hx1, hx2⟩
  have hK1 : D₁ ⊓ D₂ ≤ 𝒩₁ := inf_le_left.trans hD₁N
  have hK2 : D₁ ⊓ D₂ ≤ 𝒩₂ := inf_le_right.trans hD₂N
  have hKconj : conjClass (D₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) := by
    refine Set.Subset.antisymm (hsub hK1 hK2) ?_
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hkz⟩ := exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z
      hν₂eq hν₂surj hact₂ hRD₂ hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
    change z * j ∈ conjClass (D₁ ⊓ D₂) z
    exact mem_conjClass_iff_right.2 ⟨k, hk, hkz⟩
  have hKH : (D₁ ⊓ D₂) ⊓ centralizer ({z} : Set G) = ℬ₁ ⊓ ℛ := by
    rw [inf_inf_distrib_right, hD₁H, hD₂H]
  have hKc : Nat.card (D₁ ⊓ D₂ : Subgroup G) = 128 := by
    rw [card_eq_card_conjClass_mul _ z, hKconj, card_smul_set, SetLike.coe_sort_coe, hJ, hKH,
      card_ptSub_inf_radSub he hb φ hzC hinf hz]
  have hKY : D₁ ⊓ D₂ ≤ 𝒩₁ ⊓ 𝒩₂ := le_inf hK1 hK2
  have hYconj : conjClass (𝒩₁ ⊓ 𝒩₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) :=
    Set.Subset.antisymm (hsub inf_le_left inf_le_right) (hKconj ▸ conjClass_mono hKY z)
  have hYc : Nat.card (𝒩₁ ⊓ 𝒩₂ : Subgroup G) = 24576 := by
    rw [card_eq_card_conjClass_mul _ z, hYconj, card_smul_set, SetLike.coe_sort_coe, hJ,
      card_normalizer_inf_centralizer he hb hnd φ hzC hsup hinf hz σ hσcol hσker hσsurj]
  have hPY := pCoreOf_le 2 (𝒩₁ ⊓ 𝒩₂)
  have hKP : D₁ ⊓ D₂ ≤ CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂) := by
    refine le_pCoreOf 2 hKY (fun y hy k hk => mem_inf.2 ⟨hD₁n y (mem_inf.1 hy).1 k (mem_inf.1 hk).1,
      hD₂n y (mem_inf.1 hy).2 k (mem_inf.1 hk).2⟩) (IsPGroup.of_card (n := 7) ?_)
    rw [hKc]
    norm_num
  have hXY : ptSub φ z hb e ⊔ radSub φ z e ≤ 𝒩₁ ⊓ 𝒩₂ :=
    sup_le (le_inf le_normalizer (ptSub_le_normalizer_radSub he hb φ hzC hz))
      (le_inf (radSub_le_normalizer_ptSub he hb hnd φ hzC) le_normalizer)
  have hXc := card_ptSub_sup_radSub he hb φ hzC hinf hz
  have hXP : ptSub φ z hb e ⊔ radSub φ z e ≤ CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂) := by
    refine le_pCoreOf 2 hXY (fun y hy x hx => ?_) (IsPGroup.of_card (n := 9) ?_)
    · have hyN : y ∈ normalizer ((ptSub φ z hb e ⊔ radSub φ z e : Subgroup G) : Set G) :=
        inf_normalizer_le_normalizer_sup _ _ hy
      exact (mem_normalizer_iff.1 hyN x).1 hx
    · rw [hXc]
      norm_num
  have hXH : ptSub φ z hb e ⊔ radSub φ z e ≤ centralizer ({z} : Set G) :=
    sup_le (ptSub_le_centralizer he hb hnd φ hsup) (radSub_le_centralizer φ hsup)
  have hPH : CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂) ⊓ centralizer ({z} : Set G) =
      ptSub φ z hb e ⊔ radSub φ z e := by
    refine le_antisymm (le_ptSub_sup_radSub_of_normal he hb hnd φ hzC hsup hinf hz σ hσcol hσker
      hσsurj (inf_le_inf_right _ hPY) (fun y hy p hp => mem_inf.2 ⟨conj_mem_pCoreOf 2
        (mem_inf.1 hy).1 (mem_inf.1 hp).1, mul_mem (mul_mem (mem_inf.1 hy).2 (mem_inf.1 hp).2)
          (inv_mem (mem_inf.1 hy).2)⟩) ((isPGroup_pCoreOf 2 _).to_le inf_le_left))
      (le_inf hXP hXH)
  have hPconj : conjClass (CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂)) z =
      z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) :=
    Set.Subset.antisymm (hsub (hPY.trans inf_le_left) (hPY.trans inf_le_right))
      (hKconj ▸ conjClass_mono hKP z)
  refine ⟨hKconj, hKc, hYc, ?_⟩
  rw [card_eq_card_conjClass_mul _ z, hPconj, card_smul_set, SetLike.coe_sort_coe, hJ, hPH, hXc]

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
