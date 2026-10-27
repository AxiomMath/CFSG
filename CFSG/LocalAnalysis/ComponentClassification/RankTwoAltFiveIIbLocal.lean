module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbOuter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveInner

public section

open Subgroup Equiv CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

theorem mul_self_mem_sup {m : G} (hm : m ∈ normalizer (A : Set G)) :
    m * m ∈ A ⊔ centralizer (A : Set G) := by
  obtain ⟨eA⟩ := h.equiv
  apply (mem_sup_iff_sign eA ⟨m * m, mul_mem hm hm⟩).mpr
  have e : (⟨m * m, mul_mem hm hm⟩ : ↥(normalizer (A : Set G))) = ⟨m, hm⟩ * ⟨m, hm⟩ := rfl
  rw [e, map_mul, map_mul]
  exact Int.units_mul_self _

theorem inv_mul_mem_sup {m m' : G} (hm : m ∈ normalizer (A : Set G))
    (hm' : m' ∈ normalizer (A : Set G)) (hmA : m ∉ A ⊔ centralizer (A : Set G))
    (hm'A : m' ∉ A ⊔ centralizer (A : Set G)) : m⁻¹ * m' ∈ A ⊔ centralizer (A : Set G) := by
  obtain ⟨eA⟩ := h.equiv
  have hs : ∀ u : ↥(normalizer (A : Set G)), (u : G) ∉ A ⊔ centralizer (A : Set G) →
      Perm.sign (autPerm eA u) = -1 := fun u hu =>
    (Int.units_eq_one_or _).resolve_left fun h1 => hu ((mem_sup_iff_sign eA u).mpr h1)
  apply (mem_sup_iff_sign eA ⟨m⁻¹ * m', mul_mem (inv_mem hm) hm'⟩).mpr
  have e : (⟨m⁻¹ * m', mul_mem (inv_mem hm) hm'⟩ : ↥(normalizer (A : Set G))) =
      (⟨m, hm⟩ : ↥(normalizer (A : Set G)))⁻¹ * ⟨m', hm'⟩ := rfl
  rw [e, map_mul, map_mul, map_inv, map_inv, hs ⟨m, hm⟩ hmA, hs ⟨m', hm'⟩ hm'A]
  simp

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem commP_mem {x y : G} (hx : x ∈ P) (hy : y ∈ P) : ⁅x, y⁆ ∈ V₀ := by
  rw [commutatorElement_def]
  exact h.P_comm_mem_V₀_of_sq hP hPC hx hy

theorem commP_mul_right {x y z : G} (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hc := h.P_comm_mem_V₀_of_sq hP hPC hx hz
  have hcy : y⁻¹ * (x * z * x⁻¹ * z⁻¹) = (x * z * x⁻¹ * z⁻¹) * y⁻¹ := P_comm_V₀ hP hc (inv_mem hy)
  simp only [commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * (x * z * x⁻¹ * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * (y⁻¹ * (x * z * x⁻¹ * z⁻¹)) := by rw [hcy]; group
    _ = x * y * x⁻¹ * y⁻¹ * (x * z * x⁻¹ * z⁻¹) := by group

theorem commP_mul_left {x y z : G} (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hc := h.P_comm_mem_V₀_of_sq hP hPC hy hz
  have hcx : x * (y * z * y⁻¹ * z⁻¹) = (y * z * y⁻¹ * z⁻¹) * x := P_comm_V₀ hP hc hx
  have hc' := h.P_comm_mem_V₀_of_sq hP hPC hx hz
  have hcomm := h.comm (h.V₀_le hc) (h.V₀_le hc')
  simp only [commutatorElement_def]
  calc x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹ * z⁻¹) * z * x⁻¹ * z⁻¹ := by group
    _ = (y * z * y⁻¹ * z⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [hcx]; group
    _ = (x * z * x⁻¹ * z⁻¹) * (y * z * y⁻¹ * z⁻¹) := hcomm

theorem commP_inv_right {x y : G} (hx : x ∈ P) (hy : y ∈ P) : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have h1 := h.commP_mul_right hP hPC hx hy (inv_mem hy)
  rw [mul_inv_cancel, commutatorElement_one_right] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

theorem mem_V₀_of_commP_eq_one {y v : G} (hy : y ∈ P) (hyV : y ∉ R ⊔ T) (hv : v ∈ R ⊔ T)
    (h1 : ⁅y, v⁆ = 1) : v ∈ V₀ := by
  refine h.P_fixed hP hPC hy hyV hv ?_
  rw [commutatorElement_def] at h1
  calc y * v * y⁻¹ = y * v * y⁻¹ * v⁻¹ * v := by group
    _ = v := by rw [h1, one_mul]

theorem commP_injective {y r r' : G} (hy : y ∈ P) (hyV : y ∉ R ⊔ T) (hr : r ∈ R) (hr' : r' ∈ R)
    (he : ⁅y, r⁆ = ⁅y, r'⁆) : r = r' := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hr'P : r' ∈ P := hVP (mem_sup_left hr')
  have h1 : ⁅y, r * r'⁻¹⁆ = 1 := by
    rw [h.commP_mul_right hP hPC hy hrP (inv_mem hr'P), h.commP_inv_right hP hPC hy hr'P, he,
      mul_inv_cancel]
  have h2 := h.mem_V₀_of_commP_eq_one hP hPC hy hyV (mem_sup_left (mul_mem hr (inv_mem hr'))) h1
  have h3 : r * r'⁻¹ ∈ R ⊓ V₀ := mem_inf.mpr ⟨mul_mem hr (inv_mem hr'), h2⟩
  rw [h.inf_R_V₀, mem_bot] at h3
  calc r = r * r'⁻¹ * r' := by group
    _ = r' := by rw [h3, one_mul]

theorem exists_commP_eq {y : G} (hy : y ∈ P) (hyV : y ∉ R ⊔ T) {w : G} (hw : w ∈ V₀) :
    ∃ r ∈ R, ⁅y, r⁆ = w := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  let φ : ↥R → ↥V₀ := fun r => ⟨⁅y, (r : G)⁆, h.commP_mem hP hPC hy (hVP (mem_sup_left r.2))⟩
  have hinj : Function.Injective φ := fun r r' he =>
    Subtype.ext (h.commP_injective hP hPC hy hyV r.2 r'.2 (congrArg Subtype.val he))
  have hbij := hinj.bijective_of_nat_card_le (le_of_eq (by rw [h.cardR, h.card_V₀]))
  obtain ⟨r, hr⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

end PStructure

section IIb

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIb

theorem mem_centralizer_R_of_mem_sup {m : G} (hmN : m ∈ normalizer (R : Set G))
    (hm : m ∈ A ⊔ centralizer (A : Set G)) : m ∈ centralizer (R : Set G) := by
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_mul_of_mem_sup hm
  have haR : a ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le ha
  have hkN : k ∈ normalizer (R : Set G) := by
    have := mul_mem (inv_mem (centralizer_le_normalizer _ haR)) hmN
    rwa [inv_mul_cancel_left] at this
  exact mul_mem haR (hIIb (mem_inf.mpr ⟨hk, hkN⟩))

theorem mul_self_mem_centralizer_R {m : G} (hm : m ∈ normalizer (R : Set G)) :
    m * m ∈ centralizer (R : Set G) :=
  h.mem_centralizer_R_of_mem_sup hIIb (mul_mem hm hm) (h.mul_self_mem_sup (h.normalizer_R_le hm))

theorem conj_eq_of_not_mem_sup {m m' : G} (hm : m ∈ normalizer (R : Set G))
    (hm' : m' ∈ normalizer (R : Set G)) (hmA : m ∉ A ⊔ centralizer (A : Set G))
    (hm'A : m' ∉ A ⊔ centralizer (A : Set G)) {r : G} (hr : r ∈ R) :
    m * r * m⁻¹ = m' * r * m'⁻¹ := by
  have hu := h.mem_centralizer_R_of_mem_sup hIIb (mul_mem (inv_mem hm) hm')
    (h.inv_mul_mem_sup (h.normalizer_R_le hm) (h.normalizer_R_le hm') hmA hm'A)
  have hur : m⁻¹ * m' * r = r * (m⁻¹ * m') := (mem_centralizer_iff.mp hu r hr).symm
  calc m * r * m⁻¹ = m * (r * (m⁻¹ * m')) * m'⁻¹ := by group
    _ = m * (m⁻¹ * m' * r) * m'⁻¹ := by rw [hur]
    _ = m' * r * m'⁻¹ := by group

end IIb

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
