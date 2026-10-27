module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralLift

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

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

section Main

variable (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
  (hσ : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (a : G) (ha : a ∈ L) (B : M₃),
    Bᵀ = B →
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
  (hσcol : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (hn : (n : G) ∈ L) (j : Fin 3),
    linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i))
  (hσker : σ.ker = (radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G)))

include hnd hsup hinf hσ hσcol hσker in
theorem degree64_central_lift_full [Finite G] [FiniteDimensional (ZMod 2) V] {D₁ D₂ : Subgroup G}
    {ν₁ : G → 𝔼 × ZMod 2} {ν₂ : G → ↥(binarySymMatrices 3)} {κ κ₂ lam : ZMod 2}
    (hlam : lam = 0)
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hBD₁ : ℬ₁ ≤ D₁)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hν₁z : ∀ d ∈ D₁, d⁻¹ * z * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd (ν₁ d, 1)))
    (hν₁surj : ∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v)
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      m = d * c)
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    (hD₂N : D₂ ≤ 𝒩₂) (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂eq : ∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ ℛ)
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (hκ₂ : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε))) :
    κ₂ = 0 ∧ ∃ (C₁ : Subgroup G) (τ₁ : G → 𝔼 × ZMod 2) (β : ZMod 2), C₁ ≤ D₁ ∧
      (∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧
      Nat.card C₁ = 1024 ∧ zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ ℬ₁ = 𝒜₁ ∧
      (∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c = ptHom he hb φ hzC hz (Multiplicative.ofAdd (τ₁ c, 0))) ∧
      (∀ c ∈ C₁, ∀ c' ∈ C₁, τ₁ (c * c') = τ₁ c + τ₁ c') ∧
      (∀ v : 𝔼 × ZMod 2, ∃ c ∈ C₁, τ₁ c = v) ∧ (∀ c ∈ C₁, τ₁ c = 0 ↔ c ∈ 𝒜₁) ∧
      (∀ c ∈ C₁, c ^ 2 = ptHom he hb φ hzC hz (Multiplicative.ofAdd
        ((β * OddQuadraticFive.qV (ptQuad e) (τ₁ c)) • OddQuadraticFive.rV, 0))) ∧
      ⁅C₁, C₁⁆ ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
      closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
      (∀ x ∈ C₁, z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) →
        ∀ y ∈ C₁, x * y = y * x) ∧
      Nat.card ↥((C₁ : Set G) ∩ {d | d ∈ D₁ ∧
        z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)}) = 64 ∧
      ∃ e₀ ∈ C₁, τ₁ e₀ = ((0 : 𝔼), (1 : ZMod 2)) ∧
        (∀ x ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
          e₀⁻¹ * x⁻¹ * e₀ * x ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧ e₀ ∈ D₂ := by
  have hb' : (b.restrict 𝔼).IsAlt := fun x => hb x
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  obtain ⟨C₁, τ₁, α, β, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hτz, hτmul, hτsurj, hτker, hτs, hEc,
    hEcard, hsqf, hCC, hα1, hα0⟩ :=
    degree64_central_point he hb hnd φ hzC hsup hinf hz hlam hD₁N hD₁n hBD₁ hν₁surj hact₁ hprod₁
  have hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j := fun j hj =>
    exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂
      hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
  subst hlam
  have hA₁c : ∀ d ∈ D₁, ∀ a ∈ 𝒜₁, d * a = a * d := by
    intro d hd a ha
    obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 ha
    have h := hact₁ d hd v 0
    rw [zero_mul, zero_smul, add_zero, zero_smul, add_zero, ptHom_pt] at h
    exact comm_of_inv_mul_mul_eq h
  have hγA : ∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c ∈ 𝒜₁ := fun c hc => by
    rw [hτz c hc, ptHom_pt]
    exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
  have hγsurj : ∀ a ∈ 𝒜₁, ∃ c ∈ C₁, z⁻¹ * c⁻¹ * z * c = a := fun a ha => by
    obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 ha
    obtain ⟨c, hc, hcv⟩ := hτsurj v
    exact ⟨c, hc, by rw [hτz c hc, hcv, ptHom_pt]⟩
  have hα : α = 0 := by
    rcases zmod_two_eq_zero_or_eq_one α with h | h
    · exact h
    · exact (false_of_alpha_eq_one he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker hact₂ hRD₂
        hprod₂ hD₁H hA₁c hKz hC₁D hC₁n hC₁z hC₁B hγA hγsurj (hα1 h)).elim
  have hsq₀ := hα0 hα
  have hAC : 𝒜₁ ≤ C₁ := fun a ha => by
    have h : a ∈ C₁ ⊓ ℬ₁ := by
      rw [hC₁B]
      exact ha
    exact (mem_inf.1 h).1
  have hptA : ∀ v : 𝔼 × ZMod 2, ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) ∈ 𝒜₁ :=
    fun v => by
      rw [ptHom_pt]
      exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
  have hIA : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ := zpowers_le.2 (hptA _)
  have hpt : ∀ (w : 𝔼) (t : ZMod 2),
      (ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, 0), 0)))⁻¹ *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, t), 0)) ∈
          zpowers (ptB₁ he hb φ hzC hz) := by
    intro w t
    have h : (ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, 0), 0)))⁻¹ *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, t), 0)) =
          ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), t), 0)) := by
      rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
      congr 2
      ext <;> simp
    rw [h]
    rcases zmod_two_eq_zero_or_eq_one t with rfl | rfl
    · rw [Prod.mk_zero_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]
      exact one_mem _
    · exact mem_zpowers _
  have hℓI : ∀ (s : bilinIsometryGroup (b.restrict 𝔼)), ∀ i ∈ zpowers (ptB₁ he hb φ hzC hz),
      ptLevi he hb φ s * i * (ptLevi he hb φ s)⁻¹ ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    intro s i hi
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hi
    have h : ptLevi he hb φ s * ptB₁ he hb φ hzC hz ^ n = ptB₁ he hb φ hzC hz ^ n *
        ptLevi he hb φ s :=
      Commute.zpow_right (hb₁c _ (ptLevi_mem_normalizer he hb φ hzC hz s)) n
    rw [h, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) n
  have hκinj : ∀ x : 𝔼, ptHom he hb φ hzC hz (Multiplicative.ofAdd ((x, 0), 0)) ∈
      zpowers (ptB₁ he hb φ hzC hz) → x = 0 := by
    intro x hx
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hx with h | h
    · rw [← map_one (ptHom he hb φ hzC hz), ← ofAdd_zero] at h
      have h2 := Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h)
      exact congrArg (fun p => p.1.1) h2
    · have h2 := Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h)
      have h3 : (0 : ZMod 2) = 1 := congrArg (fun p => p.1.2) h2
      exact absurd h3 (by decide)
  obtain ⟨e₀, he₀C, hρe, hfix⟩ := exists_fixed_lift_of_group (Q := ptQuad e) hb' hnd'
    (polarBilin_ptQuad he) (C := C₁) (I := zpowers (ptB₁ he hb φ hzC hz))
    (fun i hi c hc => (hA₁c c (hC₁D hc) i (hIA hi)).symm)
    (fun x hx y hy => hCC (commutator_mem_commutator hx hy))
    (fun x hx => hsq₀ (subset_closure ⟨x, hx, rfl⟩))
    (ptLevi he hb φ) (fun s c hc => hC₁n _ (ptLevi_mem_normalizer he hb φ hzC hz s) c hc) hℓI
    (fun x => ptHom he hb φ hzC hz (Multiplicative.ofAdd ((x, 0), 0))) (fun x => hAC (hptA _))
    (fun x y => by
      rw [show ((x + y, (0 : ZMod 2)), (0 : ZMod 2)) = ((x, 0), 0) + ((y, 0), 0) by simp,
        ofAdd_add, map_mul, inv_mul_cancel]
      exact one_mem _)
    hκinj
    (fun s x => by
      rw [ptLevi_conj_ptHom he hb φ hzC hz s (x, 0) 0, OddQuadraticFive.hV_apply]
      exact hpt _ _)
    τ₁ hτmul hτsurj (fun s c hc => hτs s c hc)
    (fun i hi => (hτker i (hAC (hIA hi))).2 (hIA hi))
    (fun x => (hτker _ (hAC (hptA _))).2 (hptA _))
    (fun c hc hc0 => by
      obtain ⟨⟨w, t⟩, hv⟩ := (mem_ptA_iff he hb φ).1 ((hτker c hc).1 hc0)
      refine ⟨w, ?_⟩
      rw [← hv, ← ptHom_pt he hb φ hzC hz]
      exact hpt w t)
  have hγe : z⁻¹ * e₀⁻¹ * z * e₀ = ptB₁ he hb φ hzC hz := by
    rw [hτz e₀ he₀C, hρe]
  have hgz : e₀⁻¹ * z * e₀ = z * ptB₁ he hb φ hzC hz := by
    rw [← hγe]
    group
  have hcomN : ∀ x ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      e₀⁻¹ * x⁻¹ * e₀ * x ∈ zpowers (ptB₁ he hb φ hzC hz) := fun x hx =>
    comm_mem_zpowers_of_fixed he hb hnd φ hzC hsup hinf hz hA₁c hb₁c (hC₁D he₀C) hgz hfix hx
  have hcomA : ∀ a ∈ 𝒜₂, e₀⁻¹ * a⁻¹ * e₀ * a ∈ zpowers (ptB₁ he hb φ hzC hz) := fun a ha =>
    hcomN a (mem_inf.2 ⟨radSub_le_normalizer_ptSub he hb hnd φ hzC (mem_sup_left ha),
      radSub_le_centralizer φ hsup (mem_sup_left ha)⟩)
  obtain ⟨he₀D₂, hκ0⟩ := kappa_eq_zero_of_comm he hb φ hzC hz σ hσ hσker hact₂ hRD₂ hprod₂ hκ₂
    hgz hcomA
  refine ⟨hκ0, C₁, τ₁, β, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hτz, hτmul, hτsurj, hτker,
    fun c hc => ?_, hCC, hsq₀, hEc, hEcard, e₀, he₀C, hρe, hcomN, he₀D₂⟩
  rw [hsqf c hc, hα, zero_smul, zero_add]

end Main

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
