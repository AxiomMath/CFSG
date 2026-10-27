module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64Intersection
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveNoncentral

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem zmod_two_congr_alt_faithful : ∀ a b c d e f g h i : ZMod 2,
    !![a, b, c; d, e, f; g, h, i] * !![(0 : ZMod 2), 1, 0; 1, 0, 0; 0, 0, 0] *
        (!![a, b, c; d, e, f; g, h, i])ᵀ = !![(0 : ZMod 2), 1, 0; 1, 0, 0; 0, 0, 0] →
    !![a, b, c; d, e, f; g, h, i] * !![(0 : ZMod 2), 0, 1; 0, 0, 0; 1, 0, 0] *
        (!![a, b, c; d, e, f; g, h, i])ᵀ = !![(0 : ZMod 2), 0, 1; 0, 0, 0; 1, 0, 0] →
    !![a, b, c; d, e, f; g, h, i] * !![(0 : ZMod 2), 0, 0; 0, 0, 1; 0, 1, 0] *
        (!![a, b, c; d, e, f; g, h, i])ᵀ = !![(0 : ZMod 2), 0, 0; 0, 0, 1; 0, 1, 0] →
    !![a, b, c; d, e, f; g, h, i] = 1 := by
  decide

abbrev altSym (x y t : ZMod 2) : ↥(binarySymMatrices 3) :=
  ⟨alt3Mat x y t, mem_binarySymMatrices.2 (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)⟩

theorem symThreeDiag_altSym (x y t : ZMod 2) : symThreeDiag (altSym x y t : M₃) = 0 := by
  funext k
  fin_cases k <;> rfl

theorem eq_one_of_congr_alt {D : GL (Fin 3) (ZMod 2)}
    (h : ∀ B : ↥(binarySymMatrices 3), symThreeDiag (B : M₃) = 0 → symThreeCongr D B = B) :
    D = 1 := by
  have h1 := congrArg Subtype.val (h (altSym 1 0 0) (symThreeDiag_altSym 1 0 0))
  have h2 := congrArg Subtype.val (h (altSym 0 1 0) (symThreeDiag_altSym 0 1 0))
  have h3 := congrArg Subtype.val (h (altSym 0 0 1) (symThreeDiag_altSym 0 0 1))
  change (D : M₃) * alt3Mat 1 0 0 * (D : M₃)ᵀ = alt3Mat 1 0 0 at h1
  change (D : M₃) * alt3Mat 0 1 0 * (D : M₃)ᵀ = alt3Mat 0 1 0 at h2
  change (D : M₃) * alt3Mat 0 0 1 * (D : M₃)ᵀ = alt3Mat 0 0 1 at h3
  simp only [alt3Mat] at h1 h2 h3
  apply Units.ext
  rw [Units.val_one]
  rw [Matrix.eta_fin_three (D : M₃)] at h1 h2 h3 ⊢
  exact zmod_two_congr_alt_faithful _ _ _ _ _ _ _ _ _ h1 h2 h3

theorem map_center_map_subtype {X : Type*} [Group X] {N : Subgroup X} (K : Subgroup N) :
    ((center K).map K.subtype).map N.subtype =
      (center (K.map N.subtype)).map (K.map N.subtype).subtype := by
  ext x
  rw [mem_map_center_subtype_iff, mem_map_subtype_iff]
  constructor
  · rintro ⟨h, h'⟩
    obtain ⟨hK, hc⟩ := mem_map_center_subtype_iff.1 h'
    refine ⟨mem_map_subtype_iff.2 ⟨h, hK⟩, fun k hk => ?_⟩
    obtain ⟨hkN, hkK⟩ := mem_map_subtype_iff.1 hk
    exact congrArg Subtype.val (hc ⟨k, hkN⟩ hkK)
  · rintro ⟨hx, hc⟩
    obtain ⟨h, hK⟩ := mem_map_subtype_iff.1 hx
    exact ⟨h, mem_map_center_subtype_iff.2 ⟨hK, fun k hk =>
      Subtype.ext (hc k (mem_map_subtype_iff.2 ⟨k.2, hk⟩))⟩⟩

theorem card_center_map_subtype {X : Type*} [Group X] {N : Subgroup X} (K : Subgroup N) :
    Nat.card (center (K.map N.subtype)) = Nat.card (center K) :=
  Nat.card_congr (Subgroup.centerCongr (K.equivMapOfInjective N.subtype
    N.subtype_injective)).symm.toEquiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

omit hb hnd hsup hinf in
theorem conj_altSub_of_mem {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)} {κ₂ : ZMod 2}
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    {d : G} (hd : d ∈ D₂) {x : G} (hx : x ∈ altSub φ he) : d * x * d⁻¹ = x := by
  obtain ⟨B, hB, rfl⟩ := hx
  have h := hact₂ d hd B 0
  rw [hB, symThreePolarSym_zero_right, smul_zero, add_zero, zero_smul, add_zero, radHom_tau] at h
  calc d * tauHom φ he (Multiplicative.ofAdd B) * d⁻¹ =
      d * (d⁻¹ * tauHom φ he (Multiplicative.ofAdd B) * d) * d⁻¹ := by rw [h]
    _ = _ := by group

omit hb hnd hsup hinf in
include hzC hz in
theorem conj_mem_altSub {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)} {κ₂ : ZMod 2}
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (σ : 𝒩₂₀ →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : 𝒩₂₀) (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
    {n : G} (hn : n ∈ 𝒩₂) {x : G} (hx : x ∈ altSub φ he) : n * x * n⁻¹ ∈ altSub φ he := by
  obtain ⟨d, hd, c, hc, rfl⟩ := hprod₂ n hn
  obtain ⟨B, hB, rfl⟩ := hx
  have h1 := conj_tauHom_of_sigma φ he σ hσ ⟨c, hc⟩ B
  have hB' : symThreeDiag (symThreeCongr (σ ⟨c, hc⟩) B : M₃) = 0 := by
    change symThreeDiag ((σ ⟨c, hc⟩ : M₃) * B * (σ ⟨c, hc⟩ : M₃)ᵀ) = 0
    rw [symThreeDiag_congr _ _ B.2, hB, mulVec_zero]
  have h2 : (d * c) * tauHom φ he (Multiplicative.ofAdd B) * (d * c)⁻¹ =
      d * (c * tauHom φ he (Multiplicative.ofAdd B) * c⁻¹) * d⁻¹ := by group
  change (c : G) * _ * (c : G)⁻¹ = _ at h1
  rw [h2, h1, conj_altSub_of_mem he φ hzC hz hact₂ hd ⟨_, hB', rfl⟩]
  exact ⟨_, hB', rfl⟩

omit hb hnd hsup hinf in
include hzC hz in
theorem mem_of_centralizes_altSub {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    {κ₂ : ZMod 2}
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (σ : 𝒩₂₀ →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : 𝒩₂₀) (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
    (hσker : σ.ker = (radSub φ z e).subgroupOf 𝒩₂₀)
    {n : G} (hn : n ∈ 𝒩₂) (hcent : ∀ x ∈ altSub φ he, n * x * n⁻¹ = x) : n ∈ D₂ := by
  obtain ⟨d, hd, c, hc, rfl⟩ := hprod₂ n hn
  have hcI : ∀ B : ↥(binarySymMatrices 3), symThreeDiag (B : M₃) = 0 →
      symThreeCongr (σ ⟨c, hc⟩) B = B := by
    intro B hB
    have h1 := conj_tauHom_of_sigma φ he σ hσ ⟨c, hc⟩ B
    change (c : G) * _ * (c : G)⁻¹ = _ at h1
    have h2 := hcent _ ⟨B, hB, rfl⟩
    have h4 := conj_altSub_of_mem he φ hzC hz hact₂ hd ⟨B, hB, rfl⟩
    have h3 : c * tauHom φ he (Multiplicative.ofAdd B) * c⁻¹ =
        tauHom φ he (Multiplicative.ofAdd B) := by
      have h5 : d⁻¹ * tauHom φ he (Multiplicative.ofAdd B) * d =
          tauHom φ he (Multiplicative.ofAdd B) := by
        calc d⁻¹ * tauHom φ he (Multiplicative.ofAdd B) * d =
            d⁻¹ * (d * tauHom φ he (Multiplicative.ofAdd B) * d⁻¹) * d := by rw [h4]
          _ = _ := by group
      calc c * tauHom φ he (Multiplicative.ofAdd B) * c⁻¹ =
          d⁻¹ * ((d * c) * tauHom φ he (Multiplicative.ofAdd B) * (d * c)⁻¹) * d := by group
        _ = _ := by rw [h2, h5]
    rw [h3] at h1
    exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h1)).symm
  have hσc : σ ⟨c, hc⟩ = 1 := eq_one_of_congr_alt hcI
  have hcR : c ∈ ℛ := by
    have h : (⟨c, hc⟩ : 𝒩₂₀) ∈ σ.ker := hσc
    rw [hσker, mem_subgroupOf] at h
    exact h
  exact mul_mem hd (hRD₂ hcR)

section Labels

variable {M : Subgroup G} (hBM : ptSub φ z hb e ≤ M)

omit hnd hsup in
theorem mem_subA_ptLabelOf_iff (x : M) :
    x ∈ OddQuadraticFive.subA (ptLabelOf he hb φ hzC hz hinf hBM) ↔ (x : G) ∈ 𝒜₁ := by
  rw [OddQuadraticFive.mem_subA]
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_ptA_iff he hb φ).2 ⟨v, (ptHom_pt he hb φ hzC hz v).symm⟩
  · intro hx
    obtain ⟨v, hv⟩ := (mem_ptA_iff he hb φ).1 hx
    exact ⟨v, Subtype.ext ((ptHom_pt he hb φ hzC hz v).trans hv)⟩

omit hnd hsup in
theorem map_subA_ptLabelOf :
    (OddQuadraticFive.subA (ptLabelOf he hb φ hzC hz hinf hBM)).map M.subtype = 𝒜₁ := by
  ext x
  rw [mem_map_subtype_iff]
  constructor
  · rintro ⟨hx, hxA⟩
    exact (mem_subA_ptLabelOf_iff he hb φ hzC hinf hz hBM _).1 hxA
  · intro hx
    have hxM : x ∈ M := hBM (mem_sup_left hx)
    exact ⟨hxM, (mem_subA_ptLabelOf_iff he hb φ hzC hinf hz hBM ⟨x, hxM⟩).2 hx⟩

omit hnd hsup in
theorem map_subI_ptLabelOf :
    (OddQuadraticFive.subI (ptLabelOf he hb φ hzC hz hinf hBM)).map M.subtype =
      zpowers (ptB₁ he hb φ hzC hz) := by
  refine le_antisymm ?_ (zpowers_le.2 ⟨OddQuadraticFive.bv (ptLabelOf he hb φ hzC hz hinf hBM)
    ((1 : ZMod 2) • OddQuadraticFive.rV, 0), ⟨1, rfl⟩, by rw [one_smul]; rfl⟩)
  rintro _ ⟨x, ⟨c, rfl⟩, rfl⟩
  rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, Prod.mk_zero_zero, OddQuadraticFive.bv_zero, map_one]
    exact one_mem _
  · rw [one_smul]
    exact mem_zpowers _

omit hnd hsup in
theorem mem_subI_ptLabelOf_iff (x : M) :
    x ∈ OddQuadraticFive.subI (ptLabelOf he hb φ hzC hz hinf hBM) ↔
      (x : G) ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  rw [← map_subI_ptLabelOf he hb φ hzC hinf hz hBM]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

omit he hnd hsup in
include hBM in
theorem map_ptSub_subgroupOf' : ((ptSub φ z hb e).subgroupOf M).map M.subtype = ℬ₁ := by
  rw [subgroupOf_map_subtype, inf_of_le_left hBM]

end Labels

include he hnd hzC hsup hinf hz in
theorem exists_ptLevi_mul [Finite G] {c : G}
    (hc : c ∈ (𝒩₁ ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)) :
    ∃ s : bilinIsometryGroup (b.restrict 𝔼), ∃ b' ∈ ℬ₁, c = ptLevi he hb φ s * b' := by
  set s := ptStab he hb hnd φ hzC hsup hinf hz ⟨c, hc⟩ with hs
  have hℓN := ptLevi_mem_ptStabSub he hb φ hzC hz s
  have hker : (⟨ptLevi he hb φ s, hℓN⟩ : (𝒩₁ ⊓ centralizer (Singleton.singleton z : Set G) :
      Subgroup G))⁻¹ * ⟨c, hc⟩ ∈ (ptStab he hb hnd φ hzC hsup hinf hz).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ptStab_ptLevi, ← hs, inv_mul_cancel]
  rw [ker_ptStab, mem_subgroupOf] at hker
  exact ⟨s, _, hker, by simp⟩

include hnd hsup hinf in
theorem degree64_noncentral_point [Finite G] [FiniteDimensional (ZMod 2) V] {D₁ : Subgroup G}
    {ν₁ : G → 𝔼 × ZMod 2} {lam : ZMod 2} (hlam : lam = 1)
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hBD₁ : ℬ₁ ≤ D₁)
    (hν₁surj : ∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v)
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      m = d * c) :
    ∃ C₁ : Subgroup G, C₁ ≤ D₁ ∧ (∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧
      Nat.card C₁ = 1024 ∧ zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ ℬ₁ = 𝒜₁ ∧
      ⁅C₁, C₁⁆ = zpowers (ptB₁ he hb φ hzC hz) ∧
      closure {x | ∃ y ∈ C₁, y ^ 2 = x} = zpowers (ptB₁ he hb φ hzC hz) ∧
      Nat.card (center C₁) = 4 ∧
      (C₁ : Set G) ∩ {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} =
        ((𝒜₁ ⊔ (center C₁).map C₁.subtype : Subgroup G) : Set G) := by
  subst hlam
  have hE : finrank (ZMod 2) 𝔼 = 4 := finrank_pairOrth_eq he hb hnd
  have hb' : (b.restrict 𝔼).IsAlt := fun x => hb x
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  have hBn : ((ptSub φ z hb e).subgroupOf D₁).Normal := ⟨fun x hx d => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.1 (hD₁N d.2) x).1 hx⟩
  set θ := ptLabelOf he hb φ hzC hz hinf hBD₁ with hθ
  have hθv : ∀ x, ((OddQuadraticFive.bv θ x : D₁) : G) =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd x) := fun x => rfl
  have hzz : ((OddQuadraticFive.zz θ : D₁) : G) = z := ptHom_z he hb φ hzC hz
  have hconj : ∀ d : D₁, ∃ a : 𝔼 × ZMod 2, ∀ v : 𝔼 × ZMod 2,
      d⁻¹ * OddQuadraticFive.bv θ (v, 1) * d =
        OddQuadraticFive.bv θ (v + a + (b.restrict 𝔼) a.1 v.1 • OddQuadraticFive.rV, 1) := by
    intro d
    refine ⟨ν₁ d, fun v => Subtype.ext ?_⟩
    have h := hact₁ d d.2 v 1
    rw [one_mul, one_smul, add_right_comm] at h
    exact h
  have hsurj : ∀ a : 𝔼 × ZMod 2, ∃ d : D₁, ∀ v : 𝔼 × ZMod 2,
      d⁻¹ * OddQuadraticFive.bv θ (v, 1) * d =
        OddQuadraticFive.bv θ (v + a + (b.restrict 𝔼) a.1 v.1 • OddQuadraticFive.rV, 1) := by
    intro a
    obtain ⟨d, hd, hda⟩ := hν₁surj a
    refine ⟨⟨d, hd⟩, fun v => Subtype.ext ?_⟩
    have h := hact₁ d hd v 1
    rw [hda, one_mul, one_smul, add_right_comm] at h
    exact h
  have hfaith : ∀ d : D₁, (∀ v : 𝔼 × ZMod 2,
      d⁻¹ * OddQuadraticFive.bv θ (v, 1) * d = OddQuadraticFive.bv θ (v, 1)) →
        d ∈ (ptSub φ z hb e).subgroupOf D₁ := by
    intro d h
    rw [mem_subgroupOf]
    refine mem_ptSub_of_forall_conj he hb hnd φ hzC hsup hinf hz fun v => ?_
    have h1 : (d : G)⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) := congrArg Subtype.val (h v)
    rw [mul_assoc, inv_mul_eq_iff_eq_mul] at h1
    exact h1.symm
  have hLD : ∀ s, ptLevi he hb φ s ∈ normalizer (D₁ : Set G) := fun s =>
    mem_normalizer_of_map_le (by
      rintro _ ⟨d, hd, rfl⟩
      exact hD₁n _ (ptLevi_mem_normalizer he hb φ hzC hz s) d hd)
  set act : bilinIsometryGroup (b.restrict 𝔼) →* MulAut D₁ :=
    (conjNormalizer D₁).comp ((ptLevi he hb φ).codRestrict _ hLD) with hact_def
  have hact : ∀ (s : bilinIsometryGroup (b.restrict 𝔼)) (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      act s (OddQuadraticFive.bv θ (v, ε)) =
        OddQuadraticFive.bv θ (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, ε) := by
    intro s v ε
    apply Subtype.ext
    exact ptLevi_conj_ptHom he hb φ hzC hz s v ε
  obtain ⟨-, -, -, F, hF, -, -, -, -, -, -, C, hCn, hCs, hCc, hCz, hBC, hCC, hCsq, hZc, hCF, -⟩ :=
    binary_odd_quadratic_five_noncentral_action_normal_index_two_subgroup hE (b.restrict 𝔼) hb'
      hnd' (ptQuad e) (polarBilin_ptQuad he) ((ptSub φ z hb e).subgroupOf D₁) θ hconj hsurj
      hfaith act hact
  have hmemC : ∀ {x : G}, x ∈ C.map D₁.subtype ↔ ∃ h : x ∈ D₁, (⟨x, h⟩ : D₁) ∈ C :=
    mem_map_subtype_iff
  refine ⟨C.map D₁.subtype, map_subtype_le _, fun m hm c hc => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨d, hd, c', hc', rfl⟩ := hprod₁ m hm
    obtain ⟨s, b', hb'B, rfl⟩ := exists_ptLevi_mul he hb hnd φ hzC hsup hinf hz hc'
    obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    have h1 : b' * c * b'⁻¹ ∈ C.map D₁.subtype :=
      hmemC.2 ⟨_, hCn.conj_mem _ hcC ⟨b', hBD₁ hb'B⟩⟩
    obtain ⟨h1D, h1C⟩ := hmemC.1 h1
    have h2 : ptLevi he hb φ s * (b' * c * b'⁻¹) * (ptLevi he hb φ s)⁻¹ ∈ C.map D₁.subtype :=
      hmemC.2 ⟨_, hCs s _ h1C⟩
    obtain ⟨h2D, h2C⟩ := hmemC.1 h2
    have h3 := hmemC.2 ⟨_, hCn.conj_mem _ h2C ⟨d, hd⟩⟩
    have h4 : d * (ptLevi he hb φ s * b') * c * (d * (ptLevi he hb φ s * b'))⁻¹ =
        d * (ptLevi he hb φ s * (b' * c * b'⁻¹) * (ptLevi he hb φ s)⁻¹) * d⁻¹ := by group
    rw [h4]
    exact h3
  · rw [card_map_of_injective D₁.subtype_injective, hCc]
  · have h := congrArg (Subgroup.map D₁.subtype) hCz
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    have h' : D₁.subtype (OddQuadraticFive.zz θ) = z := hzz
    rw [h'] at h
    exact h
  · have h := congrArg (Subgroup.map D₁.subtype) hBC
    rw [Subgroup.map_inf_eq _ _ _ D₁.subtype_injective, map_ptSub_subgroupOf' hb φ hBD₁,
      map_subA_ptLabelOf he hb φ hzC hinf hz hBD₁] at h
    rw [inf_comm]
    exact h
  · rw [← Subgroup.map_commutator, hCC, map_subI_ptLabelOf he hb φ hzC hinf hz hBD₁]
  · have himg : (D₁.subtype) '' {x | ∃ y ∈ C, y ^ 2 = x} =
        {x | ∃ y ∈ C.map D₁.subtype, y ^ 2 = x} := by
      ext x
      constructor
      · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨f, ⟨f, hf, rfl⟩, (map_pow D₁.subtype f 2).symm⟩
      · rintro ⟨f, ⟨f', hf', rfl⟩, rfl⟩
        exact ⟨f' ^ 2, ⟨f', hf', rfl⟩, map_pow D₁.subtype f' 2⟩
    rw [← himg, ← MonoidHom.map_closure, hCsq, map_subI_ptLabelOf he hb φ hzC hinf hz hBD₁]
  · rw [card_center_map_subtype, hZc]
  · have hFmap : ((F.map D₁.subtype : Subgroup G) : Set G) =
        {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} := by
      ext x
      rw [SetLike.mem_coe, mem_map_subtype_iff]
      constructor
      · rintro ⟨h, hxF⟩
        obtain ⟨y, hy, hxy⟩ := (hF _).1 hxF
        refine ⟨h, ?_⟩
        have h1 := (mem_subI_ptLabelOf_iff he hb φ hzC hinf hz hBD₁ y).1 hy
        have h2 := congrArg Subtype.val hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz] at h2
        have h3 : z⁻¹ * (x⁻¹ * z * x) = (y : G) := by
          change z⁻¹ * ((⟨x, h⟩ : D₁)⁻¹.1 * z * x) = _
          rw [show ((⟨x, h⟩ : D₁)⁻¹ : D₁).1 = x⁻¹ from rfl] at *
          rw [h2]
          group
        rw [h3]
        exact h1
      · rintro ⟨h, hx⟩
        refine ⟨h, (hF _).2 ⟨⟨z⁻¹ * (x⁻¹ * z * x), mul_mem (inv_mem (hBD₁
          (mem_sup_right (mem_zpowers z)))) (mul_mem (mul_mem (inv_mem h) (hBD₁ (mem_sup_right
            (mem_zpowers z)))) h)⟩, (mem_subI_ptLabelOf_iff he hb φ hzC hinf hz hBD₁ _).2 hx,
              Subtype.ext ?_⟩⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz]
        group
    have h := congrArg (Subgroup.map D₁.subtype) hCF
    rw [Subgroup.map_inf_eq _ _ _ D₁.subtype_injective, Subgroup.map_sup,
      map_subA_ptLabelOf he hb φ hzC hinf hz hBD₁, map_center_map_subtype] at h
    rw [← hFmap, ← coe_inf, h]

abbrev symE₂₂ : ↥(binarySymMatrices 3) :=
  ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], mem_binarySymMatrices.2 (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)⟩

theorem zmod_two_kappa_E22 : ∀ κ : ZMod 2,
    !![(0 : ZMod 2), 0, 0; 0, 1, 0; 0, 0, 0] = !![(0 : ZMod 2), 0, 0; 0, 1, 0; 0, 0, 0] +
      κ • symThreePolar ![1, 0, 0] ![0, 1, 0] +
        (0 : ZMod 2) • !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] →
    κ = 0 := by
  decide

theorem zmod_two_kappa_E22' : ∀ κ : ZMod 2,
    !![(0 : ZMod 2), 0, 0; 0, 1, 0; 0, 0, 0] + !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] ≠
      !![(0 : ZMod 2), 0, 0; 0, 1, 0; 0, 0, 0] +
        κ • symThreePolar ![1, 0, 0] ![0, 1, 0] +
          (0 : ZMod 2) • !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] := by
  decide

omit hnd hsup hinf in
theorem ptB₁_eq_tauHom : ptB₁ he hb φ hzC hz = tauHom φ he (Multiplicative.ofAdd symE₁₁) := by
  rw [ptB₁, ptHom_pt, tauHom_symE₁₁]

omit hnd hsup hinf in
theorem ptB₁_mem_radA : ptB₁ he hb φ hzC hz ∈ 𝒜₂ := by
  rw [ptB₁, ptHom_pt]
  exact ptB_mem_radA he hb φ

omit hnd hsup hinf in
theorem ptB₁_not_mem_altSub : ptB₁ he hb φ hzC hz ∉ altSub φ he := by
  rintro ⟨B, hB, hBb⟩
  rw [ptB₁_eq_tauHom] at hBb
  have h := Multiplicative.ofAdd.injective (tauHom_injective φ he hBb)
  have h1 := congrFun hB 0
  rw [h] at h1
  exact absurd h1 (by decide)

omit hnd hsup hinf in
include hzC hz in
theorem orderOf_ptB₁ : orderOf (ptB₁ he hb φ hzC hz) = 2 := by
  have h2 : ptB₁ he hb φ hzC hz ^ 2 = 1 := by
    rw [sq, ptB₁, ← map_mul, ← ofAdd_add, add_self_eq_zero_zmod_two, ofAdd_zero, map_one]
  have h1 : ptB₁ he hb φ hzC hz ≠ 1 := fun h => by
    have := ptB₁_not_mem_altSub he hb φ hzC hz
    rw [h] at this
    exact this (one_mem _)
  exact orderOf_eq_prime h2 h1

omit hsup in
include hnd hinf in
theorem kappa_eq_zero_of_lam_eq_one [Finite G] [FiniteDimensional (ZMod 2) V]
    {D₁ D₂ C₁ : Subgroup G} {ν₁ : G → 𝔼 × ZMod 2} {ν₂ : G → ↥(binarySymMatrices 3)}
    {κ κ₂ lam : ZMod 2} (hlam : lam = 1)
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hν₁surj : ∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v)
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    (hC₁D : C₁ ≤ D₁) (hC₁n : ∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hZc : Nat.card (center C₁) = 4)
    (hCF : (C₁ : Set G) ∩ {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} =
      ((𝒜₁ ⊔ (center C₁).map C₁.subtype : Subgroup G) : Set G))
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (σ : 𝒩₂₀ →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : 𝒩₂₀) (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
    (hσker : σ.ker = (radSub φ z e).subgroupOf 𝒩₂₀)
    (hκ : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε))) :
    κ₂ = 0 := by
  subst hlam
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  have hb₁A := ptB₁_mem_radA he hb φ hzC hz
  have hZsC : (center C₁).map C₁.subtype ≤ C₁ := map_subtype_le _
  have hZcomm : ∀ x ∈ (center C₁).map C₁.subtype, ∀ c ∈ C₁, c * x = x * c :=
    fun x hx c hc => (mem_map_center_subtype_iff.1 hx).2 c hc
  have hZn : ∀ m ∈ 𝒩₁, ∀ x ∈ (center C₁).map C₁.subtype,
      m * x * m⁻¹ ∈ (center C₁).map C₁.subtype := by
    intro m hm x hx
    refine mem_map_center_subtype_iff.2 ⟨hC₁n m hm x (hZsC hx), fun c hc => ?_⟩
    have h1 := hZcomm x hx (m⁻¹ * c * m⁻¹⁻¹) (hC₁n m⁻¹ (inv_mem hm) c hc)
    rw [inv_inv] at h1
    calc c * (m * x * m⁻¹) = m * ((m⁻¹ * c * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * c * m)) * m⁻¹ := by rw [h1]
      _ = m * x * m⁻¹ * c := by group
  have hZB : ∀ x ∈ (center C₁).map C₁.subtype, x ∈ ℬ₁ → x ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    intro x hxZ hxB
    have hxA : x ∈ 𝒜₁ := hC₁B ▸ mem_inf.2 ⟨hZsC hxZ, hxB⟩
    have hxL : x ∈ L := (ptA_facts he hb hnd φ).1 hxA
    have hcent : D₁ ≤ centralizer ({x} : Set G) := by
      rw [← hC₁z]
      refine sup_le ?_ fun c hc => mem_centralizer_singleton_iff.2 (hZcomm x hxZ c hc)
      rw [zpowers_le, mem_centralizer_singleton_iff]
      exact (mul_comm_z hzC hxL).symm
    obtain ⟨v, hv⟩ := (mem_ptA_iff he hb φ).1 hxA
    have hv0 : ∀ w : 𝔼, (b.restrict 𝔼) w v.1 = 0 := by
      intro w
      obtain ⟨d, hd, hdw⟩ := hν₁surj (w, 0)
      have hdx : d⁻¹ * x * d = x := by
        have h1 := mem_centralizer_singleton_iff.1 (hcent hd)
        rw [mul_assoc, ← h1, inv_mul_cancel_left]
      have h1 := hact₁ d hd v 0
      rw [ptHom_pt, hv, hdx, ← hv, ← ptHom_pt he hb φ hzC hz] at h1
      have h2 := congrArg (fun p => p.1.2)
        (Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h1))
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, one_mul, zero_mul,
        add_zero] at h2
      rw [hdw] at h2
      change v.2 = v.2 + b (w : V) (v.1 : V) at h2
      exact (add_eq_left.1 h2.symm)
    have hv1 : v.1 = 0 := hnd'.2 _ hv0
    obtain ⟨⟨w, t⟩, rfl⟩ : ∃ p, p = v := ⟨v, rfl⟩
    simp only at hv1
    subst hv1
    rw [← hv, ← ptHom_pt he hb φ hzC hz]
    rcases zmod_two_eq_zero_or_eq_one t with rfl | rfl
    · rw [Prod.mk_zero_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]
      exact one_mem _
    · exact mem_zpowers _
  obtain ⟨g, hgZ, hgB⟩ : ∃ g ∈ (center C₁).map C₁.subtype, g ∉ ℬ₁ := by
    by_contra hne
    push Not at hne
    have hle : (center C₁).map C₁.subtype ≤ zpowers (ptB₁ he hb φ hzC hz) :=
      fun x hx => hZB x hx (hne x hx)
    have h1 := Subgroup.card_le_of_le hle
    rw [card_map_of_injective C₁.subtype_injective, hZc, Nat.card_zpowers, hb₁ord] at h1
    omega
  have hgC : g ∈ C₁ := hZsC hgZ
  have hgD : g ∈ D₁ := hC₁D hgC
  have hgN : g ∈ 𝒩₁ := hD₁N hgD
  have hgF : z⁻¹ * (g⁻¹ * z * g) ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    have h : g ∈ (C₁ : Set G) ∩ {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈
        zpowers (ptB₁ he hb φ hzC hz)} := by
      rw [hCF]
      exact mem_sup_right hgZ
    exact h.2.2
  have hgz : g⁻¹ * z * g = z * ptB₁ he hb φ hzC hz := by
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hgF with h | h
    · exfalso
      apply hgB
      rw [← hD₁H]
      refine mem_inf.2 ⟨hgD, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : g⁻¹ * z * g = z := by
        have := congrArg (fun y => z * y) h
        simpa [mul_assoc] using this
      calc g * z = g * (g⁻¹ * z * g) := by rw [h1]
        _ = z * g := by group
    · calc g⁻¹ * z * g = z * (z⁻¹ * (g⁻¹ * z * g)) := by group
        _ = _ := by rw [h]
  have hb₁inv : (ptB₁ he hb φ hzC hz)⁻¹ = ptB₁ he hb φ hzC hz := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ← hb₁ord, pow_orderOf_eq_one]
  have hcomA : ∀ a ∈ 𝒜₂, g⁻¹ * a⁻¹ * g * a ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    intro a ha
    have haN : a ∈ 𝒩₁ := radSub_le_normalizer_ptSub he hb hnd φ hzC (mem_sup_left ha)
    have haL : a ∈ L := pullSub_le φ _ ha
    have haz : a * z = z * a := mul_comm_z hzC haL
    have hab : a * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * a := hb₁c a haN
    have hgb : g * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * g := hb₁c g hgN
    have hga : a⁻¹ * g * a ∈ (center C₁).map C₁.subtype := by
      have h := hZn a⁻¹ (inv_mem haN) g hgZ
      rwa [inv_inv] at h
    have hgaD : a⁻¹ * g * a ∈ D₁ := by
      have h := hD₁n a⁻¹ (inv_mem haN) g hgD
      rwa [inv_inv] at h
    have hmem : g⁻¹ * (a⁻¹ * g * a) ∈ (center C₁).map C₁.subtype := mul_mem (inv_mem hgZ) hga
    have hD : g⁻¹ * (a⁻¹ * g * a) ∈ D₁ := mul_mem (inv_mem hgD) hgaD
    have hbb : ptB₁ he hb φ hzC hz * ptB₁ he hb φ hzC hz = 1 := by
      calc ptB₁ he hb φ hzC hz * ptB₁ he hb φ hzC hz =
          ptB₁ he hb φ hzC hz * (ptB₁ he hb φ hzC hz)⁻¹ := by rw [hb₁inv]
        _ = 1 := mul_inv_cancel _
    have hk : (a⁻¹ * g * a)⁻¹ * z * (a⁻¹ * g * a) = z * ptB₁ he hb φ hzC hz := by
      have haz' : a * z * a⁻¹ = z := by rw [haz, mul_inv_cancel_right]
      calc (a⁻¹ * g * a)⁻¹ * z * (a⁻¹ * g * a) = a⁻¹ * (g⁻¹ * (a * z * a⁻¹) * g) * a := by group
        _ = a⁻¹ * z * (ptB₁ he hb φ hzC hz * a) := by rw [haz', hgz]; group
        _ = a⁻¹ * (z * a) * ptB₁ he hb φ hzC hz := by rw [← hab]; group
        _ = z * ptB₁ he hb φ hzC hz := by rw [← haz]; group
    have hgz' : g * z * g⁻¹ = z * ptB₁ he hb φ hzC hz := by
      have h1 : z = g * (z * ptB₁ he hb φ hzC hz) * g⁻¹ := by rw [← hgz]; group
      have h2 : g * ptB₁ he hb φ hzC hz * g⁻¹ = ptB₁ he hb φ hzC hz := by
        rw [hgb, mul_inv_cancel_right]
      calc g * z * g⁻¹ = (g * (z * ptB₁ he hb φ hzC hz) * g⁻¹) *
          (g * ptB₁ he hb φ hzC hz * g⁻¹)⁻¹ := by group
        _ = z * (ptB₁ he hb φ hzC hz)⁻¹ := by rw [← h1, h2]
        _ = z * ptB₁ he hb φ hzC hz := by rw [hb₁inv]
    have hkb : (a⁻¹ * g * a)⁻¹ * ptB₁ he hb φ hzC hz * (a⁻¹ * g * a) = ptB₁ he hb φ hzC hz := by
      have hkN : a⁻¹ * g * a ∈ 𝒩₁ := mul_mem (mul_mem (inv_mem haN) hgN) haN
      have h := hb₁c _ hkN
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    have hhz : (g⁻¹ * (a⁻¹ * g * a))⁻¹ * z * (g⁻¹ * (a⁻¹ * g * a)) = z := by
      calc (g⁻¹ * (a⁻¹ * g * a))⁻¹ * z * (g⁻¹ * (a⁻¹ * g * a)) =
          (a⁻¹ * g * a)⁻¹ * (g * z * g⁻¹) * (a⁻¹ * g * a) := by group
        _ = ((a⁻¹ * g * a)⁻¹ * z * (a⁻¹ * g * a)) *
            ((a⁻¹ * g * a)⁻¹ * ptB₁ he hb φ hzC hz * (a⁻¹ * g * a)) := by rw [hgz']; group
        _ = z * (ptB₁ he hb φ hzC hz * ptB₁ he hb φ hzC hz) := by rw [hk, hkb]; group
        _ = z := by rw [hbb, mul_one]
    have hB : g⁻¹ * (a⁻¹ * g * a) ∈ ℬ₁ := by
      rw [← hD₁H]
      refine mem_inf.2 ⟨hD, mem_centralizer_singleton_iff.2 ?_⟩
      calc g⁻¹ * (a⁻¹ * g * a) * z =
          g⁻¹ * (a⁻¹ * g * a) * ((g⁻¹ * (a⁻¹ * g * a))⁻¹ * z * (g⁻¹ * (a⁻¹ * g * a))) := by
            rw [hhz]
        _ = z * (g⁻¹ * (a⁻¹ * g * a)) := by group
    have h := hZB _ hmem hB
    have he' : g⁻¹ * a⁻¹ * g * a = g⁻¹ * (a⁻¹ * g * a) := by group
    rw [he']
    exact h
  have hgR : g ∈ 𝒩₂ := by
    have hmap : (radSub φ z e).map (MulAut.conj g⁻¹).toMonoidHom ≤ radSub φ z e := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) ?_
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have h2 : g⁻¹ * a * g = a * (g⁻¹ * a⁻¹ * g * a)⁻¹ := by group
        rw [h2]
        exact mem_sup_left (mul_mem ha (inv_mem (zpowers_le.2 hb₁A (hcomA a ha))))
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgz]
        exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hb₁A)
    have h := inv_mem (mem_normalizer_of_map_le hmap)
    rwa [inv_inv] at h
  have hgI : ∀ x ∈ altSub φ he, g * x * g⁻¹ = x := by
    intro x hx
    have hxA : x ∈ 𝒜₂ := by
      obtain ⟨B, -, rfl⟩ := hx
      exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have h1 := hcomA x hxA
    have h2 : g⁻¹ * x * g ∈ altSub φ he := by
      have h := conj_mem_altSub he φ hzC hz hact₂ hprod₂ σ hσ (inv_mem hgR) hx
      rwa [inv_inv] at h
    have h3 : (g⁻¹ * x⁻¹ * g * x)⁻¹ ∈ altSub φ he := by
      have h4 : (g⁻¹ * x⁻¹ * g * x)⁻¹ = x⁻¹ * (g⁻¹ * x * g) := by group
      rw [h4]
      exact mul_mem (inv_mem hx) h2
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord h1 with h | h
    · calc g * x * g⁻¹ = x * (g * (g⁻¹ * x⁻¹ * g * x)) * g⁻¹ := by group
        _ = x := by rw [h]; group
    · exfalso
      rw [h, hb₁inv] at h3
      exact ptB₁_not_mem_altSub he hb φ hzC hz h3
  have hgD₂ : g ∈ D₂ :=
    mem_of_centralizes_altSub he φ hzC hz hact₂ hRD₂ hprod₂ σ hσ hσker hgR hgI
  have hlab : g⁻¹ * z * g = radHom φ he hzC hz (Multiplicative.ofAdd (symE₁₁, 1)) := by
    rw [hgz, radHom_one_eq φ he hzC hz, ptB₁_eq_tauHom]
  have hτ := hκ g hgD₂ symE₁₁ symE₂₂ 0 hlab
  rw [radHom_tau, radHom_tau] at hτ
  have hτA : tauHom φ he (Multiplicative.ofAdd symE₂₂) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hc := hcomA _ hτA
  have hconjτ : g⁻¹ * tauHom φ he (Multiplicative.ofAdd symE₂₂) * g =
      tauHom φ he (Multiplicative.ofAdd symE₂₂) *
        (g⁻¹ * (tauHom φ he (Multiplicative.ofAdd symE₂₂))⁻¹ * g *
          tauHom φ he (Multiplicative.ofAdd symE₂₂))⁻¹ := by group
  have hX : symThreeDiag ((symE₁₁ : ↥(binarySymMatrices 3)) : M₃) = ![1, 0, 0] :=
    symThreeDiag_jMat 1 0 0
  have hY : symThreeDiag ((symE₂₂ : ↥(binarySymMatrices 3)) : M₃) = ![0, 1, 0] := by
    funext k
    fin_cases k <;> rfl
  rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hc with h | h
  · rw [h, inv_one, mul_one] at hconjτ
    rw [hconjτ] at hτ
    have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he hτ))
    change (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃) = !![0, 0, 0; 0, 1, 0; 0, 0, 0] +
      κ₂ • symThreePolar (symThreeDiag ((symE₁₁ : ↥(binarySymMatrices 3)) : M₃))
        (symThreeDiag ((symE₂₂ : ↥(binarySymMatrices 3)) : M₃)) +
          (0 : ZMod 2) • !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] at h1
    rw [hX, hY] at h1
    exact zmod_two_kappa_E22 κ₂ h1
  · exfalso
    rw [h, hb₁inv, ptB₁_eq_tauHom, ← map_mul, ← ofAdd_add] at hconjτ
    rw [hconjτ] at hτ
    have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he hτ))
    change (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃) + !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] =
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] +
      κ₂ • symThreePolar (symThreeDiag ((symE₁₁ : ↥(binarySymMatrices 3)) : M₃))
        (symThreeDiag ((symE₂₂ : ↥(binarySymMatrices 3)) : M₃)) +
          (0 : ZMod 2) • !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] at h1
    rw [hX, hY] at h1
    exact zmod_two_kappa_E22' κ₂ h1

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
