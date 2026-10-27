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

include hnd hinf in
theorem noncentral_center_facts [Finite G] [FiniteDimensional (ZMod 2) V]
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
    (center C₁).map C₁.subtype ⊓ ℬ₁ ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
      (∀ g ∈ (center C₁).map C₁.subtype, g ∉ ℬ₁ →
        z⁻¹ * (g⁻¹ * z * g) = ptB₁ he hb φ hzC hz) ∧
      (∃ g ∈ (center C₁).map C₁.subtype, g ∉ ℬ₁) ∧
      (center C₁).map C₁.subtype ≤ D₂ := by
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
  have hex : ∃ g ∈ (center C₁).map C₁.subtype, g ∉ ℬ₁ := by
    by_contra hne
    push Not at hne
    have hle : (center C₁).map C₁.subtype ≤ zpowers (ptB₁ he hb φ hzC hz) :=
      fun x hx => hZB x hx (hne x hx)
    have h1 := Subgroup.card_le_of_le hle
    rw [card_map_of_injective C₁.subtype_injective, hZc, Nat.card_zpowers, hb₁ord] at h1
    omega
  have hgen : ∀ g ∈ (center C₁).map C₁.subtype, g ∉ ℬ₁ →
      g⁻¹ * z * g = z * ptB₁ he hb φ hzC hz ∧
        ∀ a ∈ 𝒜₂, g⁻¹ * a⁻¹ * g * a ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    intro g hgZ hgB
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
    exact ⟨hgz, hcomA⟩
  refine ⟨fun x hx => hZB x (mem_inf.1 hx).1 (mem_inf.1 hx).2, fun g hgZ hgB => ?_, hex,
    fun g hgZ => ?_⟩
  · have h := (hgen g hgZ hgB).1
    rw [h]
    group
  · by_cases hgB : g ∈ ℬ₁
    · have h := hZB g hgZ hgB
      have hb₁R : zpowers (ptB₁ he hb φ hzC hz) ≤ ℛ :=
        zpowers_le.2 (mem_sup_left (ptB₁_mem_radA he hb φ hzC hz))
      exact hRD₂ (hb₁R h)
    · obtain ⟨hgz, hcomA⟩ := hgen g hgZ hgB
      exact (kappa_eq_zero_of_comm he hb φ hzC hz σ hσ hσker hact₂ hRD₂ hprod₂ hκ hgz hcomA).1

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
