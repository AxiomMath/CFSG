module

public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueFinal
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B.TwoA.Amalgam

namespace Stroth21Aux

theorem orderOf_cE'_eq_two :
    orderOf cE' = 2 := by
  rw [← Nat.card_zpowers, natCard_zpowers_cE'_eq_two]

theorem cE'_comm
    (y : Eam) : y * cE' = cE' * y := by
  have h : cE' ∈ center Eam := by
    rw [short_F4_derived_standard_perfect_cover.2.2.1]
    exact mem_zpowers _
  exact (mem_center_iff.1 h y)

theorem centralizer_commutator_le :
    centralizer ((commutator Eam : Subgroup Eam) : Set Eam) ≤ commutator Eam := by
  rw [centralizer_commutator_Eam]
  exact zpowers_le.2 cE'_mem_commutator

theorem index_commutator_Eam :
    (commutator Eam).index = 2 :=
  short_F4_derived_standard_perfect_cover.1

end Stroth21Aux

open Stroth21Aux

section Generic

variable {E : Type*} [Group E] {D : Subgroup E} [D.Normal]

theorem exists_eq_conj_of_mulAut_gen [Finite (MulAut D)]
    (hO : (MulAut.conj : D →* MulAut D).range.index ≤ 2)
    (hCD : centralizer (D : Set E) ≤ D) {b₀ : E} (hb₀ : b₀ ∉ D) (σ : MulAut D) :
    ∃ b : E, ∀ y : D, ((σ y : D) : E) = b * y * b⁻¹ := by
  by_cases hσ : σ ∈ (MulAut.conj : D →* MulAut D).range
  · obtain ⟨e, he⟩ := MonoidHom.mem_range.1 hσ
    refine ⟨e, fun y => ?_⟩
    rw [← he, MulAut.conj_apply, coe_mul, coe_mul, coe_inv]
  · have hσ₀ : (MulAut.conjNormal b₀ : MulAut D) ∉ (MulAut.conj : D →* MulAut D).range :=
      fun h => hb₀ (mem_of_conjNormal_mem_range hCD h)
    have hInn2 : (MulAut.conj : D →* MulAut D).range.index = 2 := by
      have h0 : (MulAut.conj : D →* MulAut D).range.index ≠ 0 := FiniteIndex.index_ne_zero
      have h1 : (MulAut.conj : D →* MulAut D).range.index ≠ 1 := by
        intro h
        rw [index_eq_one] at h
        rw [h] at hσ
        exact hσ (mem_top _)
      omega
    have hmem : σ * (MulAut.conjNormal b₀)⁻¹ ∈ (MulAut.conj : D →* MulAut D).range := by
      rw [mul_mem_iff_of_index_two hInn2, inv_mem_iff]
      exact iff_of_false hσ hσ₀
    obtain ⟨e, he⟩ := MonoidHom.mem_range.1 hmem
    refine ⟨e * b₀, fun y => ?_⟩
    have h1 : σ = MulAut.conj e * MulAut.conjNormal b₀ := by rw [he, inv_mul_cancel_right]
    rw [h1, MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv,
      MulAut.conjNormal_apply]
    group

omit [D.Normal] in
theorem eq_or_eq_of_conj_eq_gen {c : E} (hCD : centralizer (D : Set E) = zpowers c)
    (hc2 : orderOf c = 2) (hcc : ∀ y : E, y * c = c * y) {a b : E}
    (h : ∀ y : D, b * (y : E) * b⁻¹ = a * y * a⁻¹) : b = a ∨ b = c * a := by
  have hmem : a⁻¹ * b ∈ centralizer (D : Set E) := by
    rw [mem_centralizer_iff]
    intro y hy
    have e := h ⟨y, hy⟩
    calc y * (a⁻¹ * b) = a⁻¹ * (a * y * a⁻¹) * b := by group
      _ = a⁻¹ * (b * y * b⁻¹) * b := by rw [e]
      _ = a⁻¹ * b * y := by group
  rw [hCD] at hmem
  rcases CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers hc2 hmem with h1 | h1
  · left
    calc b = a * (a⁻¹ * b) := by group
      _ = a := by rw [h1, mul_one]
  · right
    calc b = a * (a⁻¹ * b) := by group
      _ = a * c := by rw [h1]
      _ = c * a := hcc a

theorem fourGroupCondition_gen [Finite (MulAut D)] {c : E} (hidx : D.index = 2)
    (hO : (MulAut.conj : D →* MulAut D).range.index ≤ 2)
    (hCD : centralizer (D : Set E) = zpowers c) (hZ : (center D).map D.subtype = zpowers c)
    (hc2 : orderOf c = 2) (hcD : c ∈ D) (hsq : ∀ y : E, y * y ≠ c)
    (hV : ∀ b : E, b ∉ D → b * b = 1 → ∃ V : Subgroup E, V ≤ D ∧ Nat.card V = 4 ∧
      V ≤ centralizer ({b} : Set E) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * b) b) :
    FoursGroupCondition D := by
  intro φ hφφ hout
  have hCD' : centralizer (D : Set E) ≤ D := by rw [hCD]; exact zpowers_le.2 hcD
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : E, b₀ ∉ D := by
    by_contra! h
    rw [(eq_top_iff' D).2 h, index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨b, hb⟩ := exists_eq_conj_of_mulAut_gen hO hCD' hb₀ φ
  have hbE : b ∉ D := by
    intro hbm
    apply hout ⟨b, hbm⟩
    ext y
    rw [hb, MulAut.conj_apply, coe_mul, coe_mul, coe_inv]
  have hb2c : b * b ∈ centralizer (D : Set E) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : φ (φ ⟨y, hy⟩) = ⟨y, hy⟩ := by
      rw [← MulAut.mul_apply, hφφ, MulAut.one_apply]
    have h2 : ((φ (φ ⟨y, hy⟩) : D) : E) = b * b * y * (b * b)⁻¹ := by
      rw [hb, hb]
      group
    rw [h1] at h2
    calc y * (b * b) = b * b * y * (b * b)⁻¹ * (b * b) := by rw [← h2]
      _ = b * b * y := by group
  rw [hCD] at hb2c
  have hb2 : b * b = 1 := by
    rcases CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers hc2 hb2c with h | h
    · exact h
    · exact absurd h (hsq b)
  obtain ⟨V, hVE, hV4, hVc, hVconj⟩ := hV b hbE hb2
  obtain ⟨v, hvV, hv1, hvc⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set E) ⊆ {1, c} := by
      intro v hv
      by_cases h1 : v = 1
      · exact Or.inl h1
      · exact Or.inr (hcon v hv h1)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hV4] at hle
    have h2 : ({1, c} : Set E).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : E) ({c} : Set E)
      rwa [Set.ncard_singleton] at this
    omega
  have hvb : v * b = b * v := mem_centralizer_singleton_iff.1 (hVc hvV)
  obtain ⟨e, he⟩ := isConj_iff.1 (hVconj v hvV hv1)
  have hve : v * b = e⁻¹ * b * e := by
    calc v * b = e⁻¹ * (e * (v * b) * e⁻¹) * e := by group
      _ = e⁻¹ * b * e := by rw [he]
  have hvv : v * v = 1 := by
    have h1 : (v * b) * (v * b) = 1 := by
      rw [hve]
      calc e⁻¹ * b * e * (e⁻¹ * b * e) = e⁻¹ * (b * b) * e := by group
        _ = 1 := by rw [hb2]; group
    have h3 : (v * b) * (v * b) = v * v * (b * b) := by
      calc (v * b) * (v * b) = v * (b * v) * b := by group
        _ = v * (v * b) * b := by rw [hvb]
        _ = v * v * (b * b) := by group
    rw [h3, hb2, mul_one] at h1
    exact h1
  obtain ⟨l, hlE, hl⟩ : ∃ l ∈ D, l * b * l⁻¹ = v * b := by
    have h0 : e⁻¹ * b * e⁻¹⁻¹ = v * b := by rw [hve, inv_inv]
    by_cases heE : e⁻¹ ∈ D
    · exact ⟨e⁻¹, heE, h0⟩
    · refine ⟨e⁻¹ * b, ?_, ?_⟩
      · rw [mul_mem_iff_of_index_two hidx]
        exact iff_of_false heE hbE
      · calc e⁻¹ * b * b * (e⁻¹ * b)⁻¹ = e⁻¹ * b * e⁻¹⁻¹ := by group
          _ = v * b := h0
  have hlv : ((⟨l, hlE⟩ * (φ ⟨l, hlE⟩)⁻¹ : D) : E) = v := by
    rw [coe_mul, coe_inv, hb]
    calc l * (b * l * b⁻¹)⁻¹ = l * b * l⁻¹ * b⁻¹ := by group
      _ = v := by rw [hl]; group
  refine ⟨⟨l, hlE⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_pow, hlv, sq, hvv, coe_one]
  · intro hcen
    have hmem : ((⟨l, hlE⟩ * (φ ⟨l, hlE⟩)⁻¹ : D) : E) ∈ (center D).map D.subtype :=
      ⟨_, hcen, rfl⟩
    rw [hZ, hlv] at hmem
    rcases CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers hc2 hmem with h | h
    · exact hv1 h
    · exact hvc h

end Generic

theorem exists_eq_conj_of_mulAut
    (σ : MulAut (commutator Eam)) :
    ∃ b : Eam, ∀ y : commutator Eam, ((σ y : commutator Eam) : Eam) = b * y * b⁻¹ := by
  obtain ⟨b₀, hb₀, -⟩ := exists_mul_self_eq_one_not_mem_commutator
  have : Finite (MulAut (commutator Eam)) := inferInstance
  exact exists_eq_conj_of_mulAut_gen coverOuterLeTwo centralizer_commutator_le hb₀ σ

theorem eq_or_eq_of_conj_eq
    {a b : Eam}
    (h : ∀ y : commutator Eam, b * (y : Eam) * b⁻¹ = a * y * a⁻¹) : b = a ∨ b = cE' * a :=
  eq_or_eq_of_conj_eq_gen centralizer_commutator_Eam orderOf_cE'_eq_two cE'_comm h

theorem fourGroupCondition_commutator_Eam
    : FoursGroupCondition (commutator Eam) := by
  have : Finite (MulAut (commutator Eam)) := inferInstance
  exact fourGroupCondition_gen index_commutator_Eam coverOuterLeTwo centralizer_commutator_Eam
    short_F4_derived_standard_perfect_cover.2.2.2.1 orderOf_cE'_eq_two cE'_mem_commutator
    mul_self_ne_cE' fun b hb hb2 => exists_fours_group_of_outer_involution hb hb2

end CFSG.EvenSmallLie.TwoE6
