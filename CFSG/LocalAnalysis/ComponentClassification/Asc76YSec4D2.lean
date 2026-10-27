module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D1

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem card_sec4W_eq (hΩ : Assumption41 Ω) {S S' : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hS' : IsSylowOf 2 S' ⊤) : Nat.card (sec4W Ω S') = Nat.card (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hg⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem hS hS'
  have hS'eq : S' = AschbacherTightEmbedding.rightConjugate S g⁻¹ := by
    ext x
    rw [hg, mem_rightConjugate_iff, inv_inv]
  rw [hS'eq, ← rightConjugate_sec4W hΩ.conj_mem, rightConjugate_card]

theorem sec4W_eq_of_le (hΩ : Assumption41 Ω) {S S' : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hS' : IsSylowOf 2 S' ⊤) (hWS' : sec4W Ω S ≤ S') : sec4W Ω S' = sec4W Ω S := by
  have hle : sec4W Ω S ≤ sec4W Ω S' :=
    iSup_le fun U => iSup_le fun hUS => iSup_le fun hU =>
      le_sec4W ((le_sec4W hUS hU).trans hWS') hU
  exact (eq_of_le_of_card_ge hle (card_sec4W_eq hΩ hS hS').le).symm

theorem rightConjugate_sec4W_eq_of_le (hΩ : Assumption41 Ω) {S S' : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hS' : IsSylowOf 2 S' ⊤) (hWS' : sec4W Ω S ≤ S') {h : G}
    (hh : AschbacherTightEmbedding.rightConjugate (sec4W Ω S) h ≤ S') :
    AschbacherTightEmbedding.rightConjugate (sec4W Ω S) h = sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSh : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate S h) ⊤ := by
    have := isSylowOf_rightConjugate hS h
    rwa [show AschbacherTightEmbedding.rightConjugate (⊤ : Subgroup G) h = ⊤ from
      (rightConjugate_eq_self_iff _ h).mpr (le_normalizer (mem_top h))] at this
  rw [rightConjugate_sec4W hΩ.conj_mem] at hh ⊢
  rw [← sec4W_eq_of_le hΩ hS hS' hWS', sec4W_eq_of_le hΩ hSh hS' hh]

theorem exists_isSylowOf_le_normalizer_of_isRot (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {K R₀ U : Subgroup G} (hK : K ∈ Ω) (hR₀ : IsSylowOf 2 R₀ K)
    (hU : IsDihedralRot U R₀) (hUW : U ≤ sec4W Ω S) :
    ∃ R, IsSylowOf 2 R K ∧ IsDihedralRot U R ∧ R ≤ normalizer (sec4W Ω S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
  have hWz : W ≤ centralizer ({z} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    exact sec4W_mul_comm hΩ hS hw (hUW hzU)
  have hWK : W ≤ normalizer (K : Set G) :=
    hWz.trans (Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK)
      (hR₀.le (hU.le hzU)) hz1 hzz)
  obtain ⟨R, hR, hWR⟩ := exists_isSylowOf_normalized hW2 hWK
  have hWR2 : IsPGroup 2 (W ⊔ R : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hW2 hR.isPGroup hWR
  have hUR : U ≤ R := by
    have h1 : (W ⊔ R) ⊓ K = R :=
      hR.eq_of_le (le_inf le_sup_right hR.le) inf_le_right (hWR2.to_le inf_le_left)
    intro u hu
    rw [← h1]
    exact ⟨mem_sup_left (hUW hu), hR₀.le (hU.le hu)⟩
  have hURot : IsDihedralRot U R := by
    obtain ⟨U', hU'⟩ := Assumption41.exists_rot hΩ hK hR
    have hidx : U.relIndex R = 2 := by
      have h1 := Subgroup.relIndex_mul_card U R
      rw [inf_eq_left.mpr hUR, Assumption41.card_sylow_eq hΩ hK hK hR hR₀, hU.card_eq] at h1
      have hpos : 0 < Nat.card U := by have := hU.four_le; omega
      have h2 : U.relIndex R * Nat.card U = 2 * Nat.card U := h1
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    exact (hU'.eq_of_isCyclic hUR hU.isCyclic hidx) ▸ hU'
  obtain ⟨S', hS', hWRS'⟩ := exists_isSylowOf_le hWR2 (le_top : W ⊔ R ≤ ⊤)
  have hWS' : W ≤ S' := le_sup_left.trans hWRS'
  have heq := sec4W_eq_of_le hΩ hS hS' hWS'
  refine ⟨R, hR, hURot, ?_⟩
  have := le_normalizer_sec4W hΩ.conj_mem S'
  rw [heq] at this
  exact (le_sup_right.trans hWRS').trans this

end CFSG.ComponentClassification.Asc76.Sec4
