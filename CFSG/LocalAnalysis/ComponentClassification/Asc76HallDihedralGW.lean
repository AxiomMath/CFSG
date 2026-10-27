module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76HallDihedralAut
public import CFSG.Goldschmidt75.CorollaryB3
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

namespace CFSG.ComponentClassification.Asc76X.HallDihedral

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76.Sec4
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {Ω : Set (Subgroup G)} {S K R U : Subgroup G} {t z : G}

theorem zinv_conj (h : Hyp Ω S K R U t z) {x : G} (hx : IsZInv Ω x) :
    ∃ g : G, g⁻¹ * z * g = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, T, V, hT, hV, hxV, hx1, hxx⟩ := hx
  obtain ⟨K₀, -, hall⟩ := h.single
  obtain ⟨a, ha⟩ := hall K h.mem
  obtain ⟨b, hb⟩ := hall M hM
  set g₀ := a⁻¹ * b with hg₀
  have hMK : M = AschbacherTightEmbedding.rightConjugate K g₀ := by
    rw [hb, ha, rightConjugate_mul, hg₀, mul_inv_cancel_left]
  have hR₁ : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate R g₀) M := by
    rw [hMK]
    exact isSylowOf_rightConjugate h.sylowR g₀
  have hU₁ := h.rot.rightConjugate g₀
  obtain ⟨m, -, hm⟩ := L26.IsSylowOf.exists_conj_mem hR₁ hT
  have hTR : AschbacherTightEmbedding.rightConjugate T m =
      AschbacherTightEmbedding.rightConjugate R g₀ := by
    ext w
    rw [mem_rightConjugate_iff, hm]
    have e : m⁻¹ * (m * w * m⁻¹) * m = w := by group
    rw [e]
  have hVU : AschbacherTightEmbedding.rightConjugate V m =
      AschbacherTightEmbedding.rightConjugate U g₀ := by
    have h1 := hV.rightConjugate m
    rw [hTR] at h1
    exact hU₁.eq_of_isCyclic h1.le h1.isCyclic h1.relIndex_eq
  obtain ⟨z₁, -, -, -, huniq, -⟩ := hU₁.exists_involution
  have hz₁ : g₀⁻¹ * z * g₀ = z₁ := by
    refine (huniq _ ?_ ?_).resolve_left fun e => h.z_ne ?_
    · rw [mem_rightConjugate_iff]
      have e : g₀ * (g₀⁻¹ * z * g₀) * g₀⁻¹ = z := by group
      rw [e]
      exact h.z_mem
    · calc g₀⁻¹ * z * g₀ * (g₀⁻¹ * z * g₀) = g₀⁻¹ * (z * z) * g₀ := by group
        _ = 1 := by rw [h.z_mul]; group
    · calc z = g₀ * (g₀⁻¹ * z * g₀) * g₀⁻¹ := by group
        _ = 1 := by rw [e]; group
  have hx₁ : m⁻¹ * x * m = z₁ := by
    refine (huniq _ ?_ ?_).resolve_left fun e => hx1 ?_
    · rw [← hVU, mem_rightConjugate_iff]
      have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
      rw [e]
      exact hxV
    · calc m⁻¹ * x * m * (m⁻¹ * x * m) = m⁻¹ * (x * x) * m := by group
        _ = 1 := by rw [hxx]; group
    · calc x = m * (m⁻¹ * x * m) * m⁻¹ := by group
        _ = 1 := by rw [e]; group
  refine ⟨g₀ * m⁻¹, ?_⟩
  calc (g₀ * m⁻¹)⁻¹ * z * (g₀ * m⁻¹) = m * (g₀⁻¹ * z * g₀) * m⁻¹ := by group
    _ = m * (m⁻¹ * x * m) * m⁻¹ := by rw [hz₁, hx₁]
    _ = x := by group

theorem zinv_of_mem_rPrime (h : Hyp Ω S K R U t z) {a : G} (ha : a ∈ h.rPrime) (haU : a ∉ U) :
    IsZInv Ω a := by
  have hat : a * t ∈ U := (h.mem_rPrime.mp ha).resolve_left haU
  have hta : t * a ∈ U := by
    have e : t * a = t * (a * t) * t⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp h.t_mem_normalizer _).mp hat
  have e : a = t * (t * a) := by rw [← mul_assoc, h.t_mul, one_mul]
  rw [e]
  exact h.outer_t.mul_zinv h hta

theorem isSylowOf_rPrime
    (h : Hyp Ω S K R U t z) : IsSylowOf 2 h.rPrime (normalClosure (h.rPrime : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isSylowOf_top h.sylow
  have hB3 := CFSG.Goldschmidt75.corollaryB3 P (by rw [hP]; exact h.rPrime_le)
    (by rw [hP]; exact h.stronglyClosed) h.pow_mem_centralizer
  obtain ⟨Q, hQ, hRQ⟩ := Asc76.Sec4.exists_isSylowOf_le h.rot_rPrime.isPGroup
    (subset_normalClosure : (h.rPrime : Set G) ⊆ normalClosure (h.rPrime : Set G))
  have e := hB3.2.2 Q hQ.le hQ.isPGroup hRQ
  rwa [e] at hQ

variable (h : Hyp Ω S K R U t z) (hB : IsSylowOf 2 h.rPrime (normalClosure (h.rPrime : Set G)))
include h hB

theorem inf_normalClosure : S ⊓ normalClosure (h.rPrime : Set G) = h.rPrime := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hB.eq_of_le (le_inf h.rPrime_le hB.le) inf_le_right (h.sylow.isPGroup.to_le inf_le_left)

theorem z_mem_of_normal {Q : Subgroup G} [hQn : Q.Normal]
    (hQ : Q ≤ normalClosure (h.rPrime : Set G)) (hQS : Q ⊓ S ≠ ⊥) : z ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := h.sylow.isPGroup
  have hN : S ≤ normalizer ((Q ⊓ S : Subgroup G) : Set G) := fun s hs =>
    inf_le_normalizer_inf (mem_inf.mpr ⟨by rw [normalizer_eq_top_iff.mpr hQn]; exact mem_top s,
      le_normalizer hs⟩)
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_center_ne_bot' hS2 inf_le_right hN hQS)
  have hq1' : q ≠ 1 := fun e => hq1 (Subtype.ext e)
  obtain ⟨⟨hqQ, hqS⟩, hqS', hqC⟩ := hq
  have hqR : q ∈ h.rPrime := by
    rw [← h.inf_normalClosure hB]
    exact mem_inf.mpr ⟨hqS, hQ hqQ⟩
  have hc : ∀ y ∈ h.rPrime, q * y = y * q := fun y hy =>
    (mem_centralizer_iff.mp hqC y (h.rPrime_le hy)).symm
  rcases h.rot_rPrime.eq_of_central h.z_unique hqR hc with e | e
  · exact absurd e hq1'
  · rw [← e]
    exact hqQ

omit hB in
theorem le_of_z_mem {Q : Subgroup G} [hQn : Q.Normal] (hz : z ∈ Q) :
    normalClosure (h.rPrime : Set G) ≤ Q := by
  have hzinv : ∀ x, IsZInv Ω x → x ∈ Q := fun x hx => by
    obtain ⟨g, rfl⟩ := h.zinv_conj hx
    have h1 := hQn.conj_mem z hz g⁻¹
    rwa [inv_inv] at h1
  refine normalClosure_le_normal fun a ha => ?_
  by_cases haU : a ∈ U
  · have hat : a * t ∈ h.rPrime := mul_mem ha h.t_mem_rPrime
    have hatU : a * t ∉ U := fun hU => h.t_not_mem (by
      have e : t = a⁻¹ * (a * t) := by group
      rw [e]
      exact mul_mem (inv_mem haU) hU)
    have e : a = a * t * t⁻¹ := by group
    rw [e]
    exact mul_mem (hzinv _ (h.zinv_of_mem_rPrime hat hatU)) (inv_mem (hzinv t h.zinv))
  · exact hzinv a (h.zinv_of_mem_rPrime ha haU)

omit hB in
theorem normal_of_eq (he : normalClosure (h.rPrime : Set G) = h.rPrime) : K.Normal := by
  have hRn : h.rPrime.Normal := by
    rw [← he]
    exact normalClosure_normal
  have hUg : ∀ g : G, AschbacherTightEmbedding.rightConjugate U g = U := by
    intro g
    have hUgS : AschbacherTightEmbedding.rightConjugate U g ≤ S := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have h1 : g * x * g⁻¹ ∈ h.rPrime := h.rot_rPrime.le hx
      have h2 := hRn.conj_mem _ h1 g⁻¹
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at h2
      exact h.rPrime_le h2
    have hrot := isRot_of (h.asm.conj_mem K h.mem g) (isSylowOf_rightConjugate h.sylowR g)
      (h.rot.rightConjugate g)
    have h1 := le_sec4W hUgS hrot
    rw [h.weak] at h1
    exact eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  refine Asc76.Sec4.centralizer_le_normalizer h.tight h.z_mem_K h.z_ne h.z_mul ?_
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have h1 : g * z * g⁻¹ ∈ U := by
    have h2 : z ∈ AschbacherTightEmbedding.rightConjugate U g := by rw [hUg g]; exact h.z_mem
    rwa [mem_rightConjugate_iff] at h2
  have h2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_mul]; group
  rcases h.z_unique _ h1 h2 with e | e
  · exfalso
    apply h.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · calc z * g = g * z * g⁻¹ * g := by rw [e]
      _ = g * z := by group

theorem hasDihedralSylowTwo :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (normalClosure (h.rPrime : Set G)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h.isDihedralTwoGroup_rPrime
  obtain ⟨Q₀, hQ₀⟩ := hB
  intro S'
  refine ⟨n - 1, by omega, ⟨?_⟩⟩
  exact ((Sylow.equiv S' Q₀).trans ((Q₀ : Subgroup _).equivMapOfInjective
    (normalClosure (h.rPrime : Set G)).subtype (normalClosure _).subtype_injective)).trans
    ((MulEquiv.subgroupCongr hQ₀).trans e)

omit hB in
theorem oddCore_eq_bot : CFSG.oddCore (normalClosure (h.rPrime : Set G)) = ⊥ := by
  have : (normalClosure (h.rPrime : Set G)).Normal := normalClosure_normal
  exact CFSG.ABGDGroups.oddCore_eq_bot_of_normal h.asm.oddCore _

end Hyp

end CFSG.ComponentClassification.Asc76X.HallDihedral
