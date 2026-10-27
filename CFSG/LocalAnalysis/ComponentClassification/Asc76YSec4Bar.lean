module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Local

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

abbrev cInN (W : Subgroup G) : Subgroup (normalizer (W : Set G)) :=
  (centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))

omit [Finite G] in
theorem cInN_normal (W : Subgroup G) : (cInN W).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [mem_subgroupOf] at hc ⊢
  simp only [coe_mul, coe_inv]
  exact conj_mem_centralizer g.2 hc

instance (W : Subgroup G) : (cInN W).Normal := cInN_normal W

abbrev NBar (W : Subgroup G) : Type := normalizer (W : Set G) ⧸ cInN W

@[expose] def DBar (Ω : Set (Subgroup G)) (W : Subgroup G) : Set (NBar W) :=
  {d | ∃ J ∈ Ω, ∃ T V : Subgroup G, IsSylowOf 2 T J ∧ IsDihedralRot V T ∧
    T ≤ normalizer (W : Set G) ∧ ∃ t : normalizer (W : Set G), (t : G) ∈ T ∧ (t : G) ∉ V ∧
      d = (t : NBar W)}

abbrev MBar (Ω : Set (Subgroup G)) (W : Subgroup G) : Subgroup (NBar W) := closure (DBar Ω W)

omit [Finite G] in
theorem mk_eq_one_iff {W : Subgroup G} (x : normalizer (W : Set G)) :
    (x : NBar W) = 1 ↔ (x : G) ∈ centralizer (W : Set G) := by
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem DBar.orderOf_eq_two (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {d : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S)) : orderOf d = 2 := by
  obtain ⟨J, hJ, T, V, hT, hV, hTW, t, htT, htV, rfl⟩ := hd
  have hVW := rot_le_sec4W hΩ hS hJ hT hV hTW
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have : t * t = 1 := Subtype.ext (hV.mul_self t htT htV)
    rw [this]
    exact one_mem _
  · rw [Ne, mk_eq_one_iff]
    exact not_mem_centralizer hV hVW htT htV

theorem DBar.conj_mem (hΩ : Assumption41 Ω) {W : Subgroup G} {d : NBar W} (hd : d ∈ DBar Ω W)
    (x : NBar W) : x * d * x⁻¹ ∈ DBar Ω W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJ, T, V, hT, hV, hTW, t, htT, htV, rfl⟩ := hd
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  have hTn : AschbacherTightEmbedding.rightConjugate T (n : G)⁻¹ ≤ normalizer (W : Set G) := by
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have : y = n * ((n : G)⁻¹ * y * n) * (n : G)⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem n.2 (hTW hy)) (inv_mem n.2)
  refine ⟨_, hΩ.conj_mem J hJ (n : G)⁻¹, _, _, isSylowOf_rightConjugate hT _,
    hV.rightConjugate _, hTn, n * t * n⁻¹, ?_, ?_, ?_⟩
  · rw [mem_rightConjugate_iff, inv_inv]
    simpa [mul_assoc] using htT
  · rw [mem_rightConjugate_iff, inv_inv]
    simpa [mul_assoc] using htV
  · rfl

theorem DBar.orderOf_mul_le_three (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    (hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {d e : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S))
    (he : e ∈ DBar Ω (sec4W Ω S)) : orderOf (d * e) ≤ 3 := by
  obtain ⟨K, hK, R, U, hR, hU, hRW, r, hrR, hrU, rfl⟩ := hd
  obtain ⟨J, hJ, T, V, hT, hV, hTW, s, hsT, hsV, rfl⟩ := he
  have hW2 : IsPGroup 2 (sec4W Ω S) := hS.isPGroup.to_le (sec4W_le S)
  have hWab : ∀ a ∈ (sec4W Ω S), ∀ b ∈ (sec4W Ω S), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isMulCommutative_sec4W hΩ hS.isPGroup).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWC : (sec4W Ω S) ≤ centralizer ((sec4W Ω S) : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => hWab b hb a ha
  have hUW := rot_le_sec4W hΩ hS hK hR hU hRW
  have hVW := rot_le_sec4W hΩ hS hJ hT hV hTW
  have hpow : ∀ n : ℕ, ((r : NBar (sec4W Ω S)) * (s : NBar (sec4W Ω S))) ^ n = 1 ↔
      ((r : G) * s) ^ n ∈ centralizer ((sec4W Ω S) : Set G) := by
    intro n
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, mk_eq_one_iff]
    simp
  have hle : ∀ n : ℕ, 0 < n → n ≤ 3 → ((r : G) * s) ^ n ∈ centralizer ((sec4W Ω S) : Set G) →
      orderOf ((r : NBar (sec4W Ω S)) * (s : NBar (sec4W Ω S))) ≤ 3 := fun n hn h3 h =>
    (orderOf_le_of_pow_eq_one hn ((hpow n).mpr h)).trans h3
  have hrr : (r : G) * r = 1 := hU.mul_self r hrR hrU
  have hss : (s : G) * s = 1 := hV.mul_self s hsT hsV
  by_cases hKJ : K = J
  · subst hKJ
    obtain ⟨o, ho, r', hr', hseq⟩ := hnil K hK R hR s (hT.le hsT)
    have hoW : o ∈ normalizer ((sec4W Ω S) : Set G) := by
      have : o = (s : G) * r'⁻¹ := by rw [hseq]; group
      rw [this]
      exact mul_mem s.2 (inv_mem (hRW hr'))
    have hoC : o ∈ centralizer ((sec4W Ω S) : Set G) := oddCoreIn_normalizer_le_centralizer hW2
      (oddCoreIn_inf_normalizer_le hΩ hK hR hU hW2 hUW (mem_inf.mpr ⟨ho, hoW⟩))
    have hr'U : r' ∉ U := fun h => not_mem_centralizer hV hVW hsT hsV (by
      rw [hseq]
      exact mul_mem hoC (hWC (hUW h)))
    have h1 : (r : G) * s ∈ centralizer ((sec4W Ω S) : Set G) := by
      have : (r : G) * s = ((r : G) * o * (r : G)⁻¹) * ((r : G) * r') := by rw [hseq]; group
      rw [this]
      exact mul_mem (conj_mem_centralizer (hRW hrR) hoC)
        (hWC (hUW (hU.mul_mem_of_not_mem hrR hr' hrU hr'U)))
    exact hle 1 one_pos (by norm_num) (by rwa [pow_one])
  by_cases hA : T ≤ normalizer (K : Set G)
  · obtain ⟨hJK, hKJ'⟩ := le_normalizer_of_sylow h22 hΩ hK hJ hKJ hT hA
    have h1 := commutator_mem_centralizer hΩ hK hJ hKJ hR hU hW2 hUW hJK hKJ' (hR.le hrR)
      (hT.le hsT) (hRW hrR) (hTW hsT)
    rw [inv_eq_of_mul_eq_one_right hrr, inv_eq_of_mul_eq_one_right hss] at h1
    exact hle 2 two_pos (by norm_num) (by rwa [pow_two, show (r : G) * s * (r * s) =
      r * s * r * s by group])
  · exact hle 3 three_pos le_rfl (pow_three_mem_centralizer h22 hΩ hK hJ hKJ hR hT hU hV
      (hnil K hK R hR) (hnil J hJ T hT) hRW hTW hW2 hWab hUW hVW hA hrR hrU hsT hsV)

end CFSG.ComponentClassification.Asc76.Sec4
