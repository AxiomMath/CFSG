module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointTwoGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

section Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

omit hnd in
theorem fst_eq_zero_iff_eq_smul {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (v : E × ZMod 2) :
    v.1 = 0 ↔ ∃ c : ZMod 2, v = c • ((0 : E), (1 : ZMod 2)) := by
  constructor
  · intro h
    exact ⟨v.2, Prod.ext (h.trans (smul_zero _).symm) (mul_one _).symm⟩
  · rintro ⟨c, rfl⟩
    exact smul_zero c

omit hnd in
include he hb in
theorem linOf_pointElt (w : 𝔼) (c : ZMod 2) :
    linOf (pointElt hb (mem_pairOrth_left w.2) c) (e (Sum.inl 0)) = e (Sum.inl 0) ∧
      (∀ x ∈ 𝔼, linOf (pointElt hb (mem_pairOrth_left w.2) c) x = x + b x w • e (Sum.inl 0)) ∧
      linOf (pointElt hb (mem_pairOrth_left w.2) c) (e (Sum.inr 0)) =
        e (Sum.inr 0) + w + c • e (Sum.inl 0) := by
  obtain ⟨huw, hfw⟩ := mem_pairOrth.1 w.2
  have huf : b (e (Sum.inl 0)) (e (Sum.inr 0)) = 1 := by
    rw [bilin_symm hb, bilin_f_u he]
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · change pointMap b (e (Sum.inl 0)) w c (e (Sum.inl 0)) = _
    rw [pointMap_apply, huw, hb.self_eq_zero, zero_smul, zero_smul, add_zero, add_zero]
  · change pointMap b (e (Sum.inl 0)) w c x = _
    rw [pointMap_apply, (mem_pairOrth.1 hx).1, zero_smul, add_zero]
  · change pointMap b (e (Sum.inl 0)) w c (e (Sum.inr 0)) = _
    rw [pointMap_apply, hfw, huf, zero_smul, add_zero, one_smul, add_assoc]

omit he hnd in
theorem coe_pullSub_pointRadical {G : Type*} [Group G] {L : Subgroup G}
    (φ : L ≃* bilinIsometryGroup b) :
    (pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) : Set G) =
      {x | ∃ (w : 𝔼) (c : ZMod 2),
        ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G) = x} := by
  ext x
  rw [SetLike.mem_coe, mem_pullSub]
  constructor
  · rintro ⟨hx, hP⟩
    obtain ⟨w, hw, c, hc⟩ := (mem_pointRadical hb).1 hP
    refine ⟨⟨w, hw⟩, c, ?_⟩
    rw [← hc, MulEquiv.symm_apply_apply]
  · rintro ⟨w, c, rfl⟩
    refine ⟨(φ.symm _).2, ?_⟩
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact pointElt_mem_pointRadical hb w.2 c

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

@[expose] def ptAHom : Multiplicative (𝔼 × ZMod 2) →* G :=
  L.subtype.comp (φ.symm.toMonoidHom.comp (ptHomV he hb))

theorem ptAHom_injective : Function.Injective (ptAHom he hb φ) := fun _ _ h =>
  ptHomV_injective he hb (φ.symm.injective (Subtype.ext h))

theorem range_ptAHom :
    (ptAHom he hb φ).range = pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) := by
  ext x
  rw [MonoidHom.mem_range, mem_ptA_iff he hb φ]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.toAdd y, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.ofAdd v, rfl⟩

@[expose] def ptPsi :
    pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ≃*
      Multiplicative (𝔼 × ZMod 2) :=
  ((MonoidHom.ofInjective (ptAHom_injective he hb φ)).trans
    (MulEquiv.subgroupCongr (range_ptAHom he hb φ))).symm

theorem coe_ptPsi_symm (v : 𝔼 × ZMod 2) :
    (((ptPsi he hb φ).symm (Multiplicative.ofAdd v) :
        pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))) : G) =
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) :=
  rfl

theorem ptHomV_ptQuad (w : 𝔼) (c : ZMod 2) :
    ptHomV he hb (Multiplicative.ofAdd (w, c + ptQuad e w)) =
      pointElt hb (mem_pairOrth_left w.2) c := by
  rw [ptHomV_apply, ptElt_eq]
  apply pointElt_ext
  change pointMap b (e (Sum.inl 0)) (w : V) (c + ptQuad e w + ptQuad e w) =
    pointMap b (e (Sum.inl 0)) (w : V) c
  rw [add_assoc, zmod_two_add_self_eq_zero, add_zero]

theorem ptHomV_r :
    ptHomV he hb (Multiplicative.ofAdd ((0 : 𝔼), (1 : ZMod 2))) =
      pointElt hb (mem_pairOrth_left (0 : 𝔼).2) 1 := by
  have h := ptHomV_ptQuad he hb (0 : 𝔼) 1
  rwa [show ptQuad e (0 : 𝔼) = 0 from QuadraticMap.map_zero _, add_zero] at h

omit hnd in
theorem coe_ptPsi_symm_pointElt (w : 𝔼) (c : ZMod 2) :
    (((ptPsi he hb φ).symm (Multiplicative.ofAdd (w, c + ptQuad e w)) : 𝒜₁) : G) =
      ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G) := by
  rw [coe_ptPsi_symm, ptHomV_ptQuad]

omit hnd in
theorem ptB₁_eq :
    ptB₁ he hb φ hzC hz = ((φ.symm (pointElt hb (mem_pairOrth_left (0 : 𝔼).2) 1) : L) : G) := by
  rw [ptB₁, ptHom_pt, ptHomV_r]

include he hnd hzC hsup hinf hz in
theorem conjClass_ptSub_eq_inter [Finite G] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) (hfull₁ : conjClass 𝒩₁ z = z • (𝒜₁ : Set G)) :
    conjClass 𝒩₁ z = {x | ∃ g : G, g * z * g⁻¹ = x} ∩ ((ptSub φ z hb e : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (mem_normalizer_iff.1 hg z).1 (mem_sup_right (mem_zpowers z))⟩
  · rintro ⟨⟨g, rfl⟩, hB⟩
    rw [hfull₁]
    exact conj_mem_ptSub he hb hnd φ hzC hsup hinf hz hV hB

include hnd hsup hinf in
theorem degree64_point_fusion_of_lagrangian [Finite G] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {κ₂ : ZMod 2} {D₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₂N : D₂ ≤ normalizer ((radSub φ z e : Subgroup G) : Set G))
    (hD₂n : ∀ n ∈ normalizer ((radSub φ z e : Subgroup G) : Set G), ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂eq : ∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ radSub φ z e)
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : Matrix (Fin 3) (Fin 3) (ZMod 2)))
            (symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) + ε • ν₂ d, ε))) :
    (∃ d ∈ D₂, d ∈ 𝒩₁ ∧
      d⁻¹ * z * d = z * ((φ.symm (pointElt hb (mem_pairOrth_left (0 : 𝔼).2) 1) : L) : G) ∧
      d⁻¹ * ((φ.symm (pointElt hb (mem_pairOrth_left (0 : 𝔼).2) 1) : L) : G) * d =
        ((φ.symm (pointElt hb (mem_pairOrth_left (0 : 𝔼).2) 1) : L) : G)) ∧
    conjClass 𝒩₁ z = z • (𝒜₁ : Set G) := by
  have hA₁ : ∀ v : 𝔼 × ZMod 2, ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) ∈ 𝒜₁ :=
    fun v => (mem_ptA_iff he hb φ).2 ⟨v, rfl⟩
  have hR1 : ∀ B : ↥(binarySymMatrices 3), radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) =
      z * tauHom φ he (Multiplicative.ofAdd B) := fun B => by
    rw [radHom_apply, zPow_one, mul_comm_z hzC (tauHom_mem φ he _)]
  obtain ⟨d₁, hd₁, hν₁d⟩ := hν₂surj symE₁₁
  obtain ⟨d₂, hd₂, hν₂d⟩ := hν₂surj symE₁₂
  have hd₁N := mem_normalizer_ptSub_of_mem he hb hnd φ hzC hinf hz hD₂N hD₂n hν₂z hν₂eq hd₁
    (by rw [hν₁d, tauHom_symE₁₁ he hb φ]; exact hA₁ _)
  have hd₂N := mem_normalizer_ptSub_of_mem he hb hnd φ hzC hinf hz hD₂N hD₂n hν₂z hν₂eq hd₂
    (by rw [hν₂d, tauHom_symE₁₂ he hb φ]; exact hA₁ _)
  have hz₁ : d₁⁻¹ * z * d₁ =
      z * ((φ.symm (ptHomV he hb (Multiplicative.ofAdd ((0 : 𝔼), (1 : ZMod 2)))) : L) : G) := by
    rw [hν₂z d₁ hd₁, hν₁d, hR1, tauHom_symE₁₁ he hb φ]
  have hz₂ : d₂⁻¹ * z * d₂ =
      z * ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (ptE₂ he, (0 : ZMod 2)))) : L) : G) := by
    rw [hν₂z d₂ hd₂, hν₂d, hR1, tauHom_symE₁₂ he hb φ]
  have hc₁ : ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), (1 : ZMod 2)), 1)) ∈
      conjClass 𝒩₁ z := by
    rw [ptHom_apply, zPow_one, mul_comm_z hzC (φ.symm _).2, ← hz₁]
    exact mem_conjClass_iff_right.2 ⟨d₁, hd₁N, rfl⟩
  have hc₂ : ptHom he hb φ hzC hz (Multiplicative.ofAdd ((ptE₂ he, (0 : ZMod 2)), 1)) ∈
      conjClass 𝒩₁ z := by
    rw [ptHom_apply, zPow_one, mul_comm_z hzC (φ.symm _).2, ← hz₂]
    exact mem_conjClass_iff_right.2 ⟨d₂, hd₂N, rfl⟩
  have hact₁ := hact₂ d₁ hd₁ symE₁₁ 0
  rw [hν₁d, symThreePolarSym_self, smul_zero, add_zero, zero_smul, add_zero, radHom_tau,
    tauHom_symE₁₁ he hb φ, ptHomV_r] at hact₁
  refine ⟨⟨d₁, hd₁, hd₁N, by rw [hz₁, ptHomV_r], hact₁⟩, ?_⟩
  exact conjClass_ptSub_eq he hb hnd φ hzC hsup hinf hz hV hc₁ hc₂

end Aux

theorem standard_binary_symplectic_six_degree64_other_parabolic_normalizer {G : Type} [Group G]
    [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let N₂ := normalizer ((A₂ ⊔ zpowers z : Subgroup G) : Set G)
    let A₁ := pullSub φ (pointRadical b hb u f)
    let b₁ : G := ((φ.symm (n 0 1) : L) : G)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let N₁₀ := N₁ ⊓ centralizer ({z} : Set G)
    let I₁ := zpowers b₁
    E = Submodule.span (ZMod 2) (e '' {Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inr 2}) ∧
    (A₂ : Set G) = tauSet φ e (fun _ => True) ∧
    (∀ (w : E) (c : ZMod 2), linOf (n w c) u = u ∧
      (∀ x ∈ E, linOf (n w c) x = x + b x w • u) ∧ linOf (n w c) f = f + w + c • u) ∧
    (A₁ : Set G) = {x | ∃ (w : E) (c : ZMod 2), ((φ.symm (n w c) : L) : G) = x} ∧
    A₁ ≤ L ∧ A₁ ⊓ zpowers z = ⊥ ∧ IsElementaryAbelian 2 B₁ ∧ Nat.card B₁ = 64 ∧
    centralizer (B₁ : Set G) = B₁ ∧
    conjClass N₁ z = {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (B₁ : Set G) ∧
    conjClass N₁ z = z • (A₁ : Set G) ∧
    (MulAction.toPermHom N₁ (conjClass N₁ z)).ker = B₁.subgroupOf N₁ ∧
    MulAction.stabilizer N₁ (⟨z, self_mem_conjClass N₁ z⟩ : conjClass N₁ z) = N₁₀.subgroupOf N₁ ∧
    (∃ ρ : N₁₀ →* bilinIsometryGroup (b.restrict E), Function.Surjective ρ ∧
      ρ.ker = B₁.subgroupOf N₁₀ ∧ ∀ (m : N₁₀) (w : E) (c : ZMod 2),
        (m : G) * ((φ.symm (n w c) : L) : G) * (m : G)⁻¹ =
          ((φ.symm (n (linOf (ρ m) w) c) : L) : G)) ∧
    (∃ d ∈ CFSG.Assembly.pCoreOf 2 N₂, d ∈ N₁ ∧ d⁻¹ * z * d = z * b₁ ∧ d⁻¹ * b₁ * d = b₁) ∧
    ∃ (ψ : A₁ ≃* Multiplicative (E × ZMod 2))
      (θ₁ : B₁ ≃* Multiplicative ((E × ZMod 2) × ZMod 2)),
      (∀ (w : E) (c : ZMod 2), ((ψ.symm (Multiplicative.ofAdd (w, c + Q w)) : A₁) : G) =
        ((φ.symm (n w c) : L) : G)) ∧
      (∀ (v : E × ZMod 2) (ε : ZMod 2), ((θ₁.symm (Multiplicative.ofAdd (v, ε)) : B₁) : G) =
        ((ψ.symm (Multiplicative.ofAdd v) : A₁) : G) * z ^ ε.val) ∧
      ∃ (lam : ZMod 2) (D₁ F₁ : Subgroup G) (ν₁ : G → E × ZMod 2),
        D₁ = CFSG.Assembly.pCoreOf 2 N₁ ∧ F₁ ≤ D₁ ∧ D₁ ≤ N₁ ∧ B₁ ≤ F₁ ∧
        (∀ m ∈ N₁, ∀ d ∈ D₁, m * d * m⁻¹ ∈ D₁) ∧ (∀ m ∈ N₁, ∀ x ∈ F₁, m * x * m⁻¹ ∈ F₁) ∧
        Nat.card D₁ = 2048 ∧ Nat.card F₁ = 128 ∧
        ((∀ d ∈ D₁, d ^ 2 ∈ B₁) ∧ (∀ d ∈ D₁, ∀ d' ∈ D₁, ⁅d, d'⁆ ∈ B₁) ∧ B₁.relIndex D₁ = 32) ∧
        B₁.relIndex F₁ = 2 ∧
        ((∀ d ∈ D₁, d ^ 2 ∈ F₁) ∧ (∀ d ∈ D₁, ∀ d' ∈ D₁, ⁅d, d'⁆ ∈ F₁) ∧ F₁.relIndex D₁ = 16) ∧
        (∀ d ∈ D₁, d⁻¹ * z * d = ((θ₁.symm (Multiplicative.ofAdd (ν₁ d, 1)) : B₁) : G)) ∧
        (∀ d ∈ D₁, ∀ d' ∈ D₁, ν₁ d = ν₁ d' ↔ d⁻¹ * d' ∈ B₁) ∧
        (∀ v : E × ZMod 2, ∃ d ∈ D₁, ν₁ d = v) ∧
        (∀ d ∈ D₁, ∀ (v : E × ZMod 2) (ε : ZMod 2),
          d⁻¹ * ((θ₁.symm (Multiplicative.ofAdd (v, ε)) : B₁) : G) * d =
            ((θ₁.symm (Multiplicative.ofAdd
              (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • r + ε • ν₁ d, ε)) : B₁) : G)) ∧
        (∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ ∃ c : ZMod 2, ν₁ d = c • r) ∧
        (∀ m ∈ N₁, ∃ d ∈ D₁, ∃ c ∈ N₁₀, m = d * c) ∧
        D₁ ⊓ centralizer ({z} : Set G) = B₁ ∧
        (∀ m ∈ N₁, ∀ a ∈ A₁, m * a * m⁻¹ ∈ A₁) ∧ (∀ m ∈ N₁, m * b₁ = b₁ * m) ∧
        (center F₁).map F₁.subtype = A₁ ∧ closure {x | ∃ y ∈ F₁, y ^ 2 = x} = I₁ ∧
        ⁅B₁, D₁⁆ = A₁ ∧ ⁅I₁, D₁⁆ = ⊥ ∧
        (lam = 0 → (center D₁).map D₁.subtype = A₁ ∧ ⁅A₁, D₁⁆ = ⊥) ∧
        (lam = 1 → (center D₁).map D₁.subtype = I₁ ∧ ⁅A₁, D₁⁆ = I₁ ∧
          A₁ ≤ (Subgroup.upperCentralSeries D₁ 2).map D₁.subtype) ∧
        ((∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ A₁) ∧
          (∀ d ∈ D₁, ∀ d' ∈ D₁, z⁻¹ * ((d * d')⁻¹ * z * (d * d')) *
            (z⁻¹ * (d⁻¹ * z * d) * (z⁻¹ * (d'⁻¹ * z * d')))⁻¹ ∈ I₁) ∧
          (∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ I₁ ↔ d ∈ F₁) ∧
          (∀ a ∈ A₁, ∃ d ∈ D₁, (z⁻¹ * (d⁻¹ * z * d))⁻¹ * a ∈ I₁)) ∧
        ((∀ y ∈ F₁, z⁻¹ * (y⁻¹ * z * y) ∈ I₁) ∧
          (∀ y ∈ F₁, ∀ y' ∈ F₁, z⁻¹ * ((y * y')⁻¹ * z * (y * y')) =
            z⁻¹ * (y⁻¹ * z * y) * (z⁻¹ * (y'⁻¹ * z * y'))) ∧
          (∀ y ∈ F₁, z⁻¹ * (y⁻¹ * z * y) = 1 ↔ y ∈ B₁) ∧
          (∀ i ∈ I₁, ∃ y ∈ F₁, z⁻¹ * (y⁻¹ * z * y) = i)) ∧
        (∀ c ∈ N₁₀, ∀ d : G,
          z⁻¹ * ((c⁻¹ * d * c)⁻¹ * z * (c⁻¹ * d * c)) = c⁻¹ * (z⁻¹ * (d⁻¹ * z * d)) * c) := by
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨hA₂, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ₂, D₂, F₂, ν₂, hD₂, -, hD₂N, -, hD₂n, -, -, -, hν₂z, hν₂eq, hν₂surj, hact₂, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  obtain ⟨⟨d₁, hd₁, hd₁N, hz₁, hb₁d⟩, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ
    hzC hsup hinf hz hV hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂
  have h2g := degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  rw [ptB₁_eq he hb φ hzC hz] at h2g
  obtain ⟨lam, D₁, F₁, ν₁, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16,
    c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29⟩ := h2g
  have hBfacts := ptSub_facts he hb hnd φ hzC hinf hz
  intro u f E n Q r A₂ N₂ A₁ b₁ B₁ N₁ N₁₀ I₁
  exact ⟨(pointSpan_eq_pairOrth he).symm, hA₂, fun w c => linOf_pointElt he hb w c,
    coe_pullSub_pointRadical hb φ,
    (ptA_facts he hb hnd φ).1, hBfacts.1, hBfacts.2.1, hBfacts.2.2.1,
    centralizer_ptSub he hb hnd φ hzC hsup hinf hz,
    conjClass_ptSub_eq_inter he hb hnd φ hzC hsup hinf hz hV hfull₁, hfull₁,
    ker_toPermHom_conjClass_ptSub he hb hnd φ hzC hsup hinf hz hfull₁,
    stabilizer_conjClass_ptSub hb φ,
    ⟨ptStab he hb hnd φ hzC hsup hinf hz, ptStab_surjective he hb hnd φ hzC hsup hinf hz,
      ker_ptStab he hb hnd φ hzC hsup hinf hz, ptStab_conj_pointElt he hb hnd φ hzC hsup hinf hz⟩,
    ⟨d₁, hD₂ ▸ hd₁, hd₁N, hz₁, hb₁d⟩,
    ptPsi he hb φ, ptLabel he hb φ hzC hz hinf, coe_ptPsi_symm_pointElt he hb φ,
    fun v ε => rfl, lam, D₁, F₁, ν₁, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, fun d => (c16 d).trans (and_congr_right fun _ => fst_eq_zero_iff_eq_smul (ν₁ d)), c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
