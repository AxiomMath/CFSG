module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEnd
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.GrSLit.HeZ

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_comm_ne (hs : IsSimpleGroup X) (hnab : ∃ x y : X, x * y ≠ y * x) {a : X}
    (ha : orderOf a = 2) : ∃ g : X, g * a * g⁻¹ * a = a * (g * a * g⁻¹) ∧ g * a * g⁻¹ ≠ a := by
  by_contra h
  simp only [not_exists, not_and, ne_eq, not_not] at h
  have : Fintype X := Fintype.ofFinite X
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  have ha2 : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  obtain ⟨N, hN, hodd, hcomm⟩ := CFSG.Milestones.glauberman_zStar X a ha1 ha2 h
  rcases hs.eq_bot_or_eq_top_of_normal N with hb | ht
  · have hc : a ∈ center X := by
      rw [mem_center_iff]
      intro g
      have h1 := hcomm g
      rw [hb, mem_bot] at h1
      calc g * a = g * a * g⁻¹ * a⁻¹ * (a * g) := by group
        _ = a * g := by rw [h1, one_mul]
    rcases hs.eq_bot_or_eq_top_of_normal (center X) with h0 | h0
    · rw [h0, mem_bot] at hc
      exact ha1 hc
    · obtain ⟨x, y, hxy⟩ := hnab
      have hy : y ∈ center X := by rw [h0]; exact mem_top y
      exact hxy (mem_center_iff.mp hy x)
  · rw [ht, card_top] at hodd
    have h2 : 2 ∣ Nat.card X := ha ▸ orderOf_dvd_natCard a
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

omit [Finite X] in
theorem centralizer_le_normalizer {L : Subgroup X} (hstd : IsStandardSubgroup L) {c : X}
    (hc : c ∈ centralizer (L : Set X)) (hc2 : orderOf c = 2) :
    centralizer ({c} : Set X) ≤ normalizer (L : Set X) :=
  fun _ hy => CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
    (CFSG.IsStandardSubgroup.standardComponentIsStandard hstd) hc hc2
    (mem_centralizer_singleton_iff.1 hy)

theorem false_of_pair {C : Subgroup X} (hC : pRank 2 ↥C = 1) {y₁ y₂ : X} (h₁ : y₁ ∈ C)
    (h₂ : y₂ ∈ C) (hy₁ : y₁ * y₁ = 1) (hy₂ : y₂ * y₂ = 1) (h1 : y₁ ≠ 1) (h2 : y₂ ≠ 1)
    (hne : y₁ ≠ y₂) (hc : y₁ * y₂ = y₂ * y₁) : False := by
  have := HeEnd.two_le_pRank_of_pair h₁ h₂ hy₁ hy₂ h1 h2 hne hc
  omega

section Prod

variable {Y : Type*} [Group Y] (L C : Subgroup Y) (hc : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l)

@[expose] noncomputable def prodHom : ↥L × ↥C →* Y :=
  MonoidHom.noncommCoprod L.subtype C.subtype fun l c => hc l l.2 c c.2

theorem prodHom_apply (p : ↥L × ↥C) : prodHom L C hc p = (p.1 : Y) * p.2 := rfl

theorem prodHom_injective (hinf : L ⊓ C = ⊥) : Function.Injective (prodHom L C hc) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨l, c⟩ h
  rw [MonoidHom.mem_ker, prodHom_apply] at h
  have hl : (l : Y) = (c : Y)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hlC : (l : Y) ∈ L ⊓ C := mem_inf.mpr ⟨l.2, hl ▸ inv_mem c.2⟩
  rw [hinf, mem_bot] at hlC
  have hc1 : (c : Y) = 1 := by rw [hlC, one_mul] at h; exact h
  exact (mem_bot).mpr (Prod.ext (Subtype.ext hlC) (Subtype.ext hc1))

theorem prodHom_range : (prodHom L C hc).range = L ⊔ C := by
  apply le_antisymm
  · rintro _ ⟨⟨l, c⟩, rfl⟩
    exact mul_mem_sup l.2 c.2
  · rw [sup_le_iff]
    constructor
    · intro l hl
      exact ⟨(⟨l, hl⟩, 1), by rw [prodHom_apply]; simp⟩
    · intro c hcC
      exact ⟨(1, ⟨c, hcC⟩), by rw [prodHom_apply]; simp⟩

variable {L C hc} in
@[expose] noncomputable def decomp (hinf : L ⊓ C = ⊥) {Q : Subgroup Y} (hQ : Q ≤ L ⊔ C) :
    ↥Q →* ↥L × ↥C :=
  (MonoidHom.ofInjective (prodHom_injective L C hc hinf)).symm.toMonoidHom.comp
    (inclusion (hQ.trans (prodHom_range L C hc).ge))

variable {L C hc} in
theorem decomp_spec (hinf : L ⊓ C = ⊥) {Q : Subgroup Y} (hQ : Q ≤ L ⊔ C) (q : ↥Q) :
    ((decomp (hc := hc) hinf hQ q).1 : Y) * (decomp (hc := hc) hinf hQ q).2 = q := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective (prodHom_injective L C hc hinf))
    (inclusion (hQ.trans (prodHom_range L C hc).ge) q)
  have h2 := congrArg Subtype.val h
  rw [MonoidHom.ofInjective_apply] at h2
  exact h2

end Prod

theorem eq_top_of_index_le_four {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : 24 < Nat.card S) {H : Subgroup S} (hH : H.index ≤ 4) : H = ⊤ := by
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  have hdvd := H.index_normalCore_dvd_factorial_index
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
  · exfalso
    rw [h, index_bot] at hdvd
    have hf : Nat.factorial H.index ≤ 24 := by
      calc Nat.factorial H.index ≤ Nat.factorial 4 := Nat.factorial_le hH
        _ = 24 := by decide
    have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    omega
  · exact eq_top_iff.mpr (h ▸ H.normalCore_le)

end CFSG.ComponentClassification.GrSLit.HeZ
