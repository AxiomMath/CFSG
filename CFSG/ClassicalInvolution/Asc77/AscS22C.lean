module

public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Pigeon

theorem four_ne_three {α : Type*} {a b c d x y w : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (ha : a = x ∨ a = y ∨ a = w)
    (hb : b = x ∨ b = y ∨ b = w) (hc : c = x ∨ c = y ∨ c = w) (hd : d = x ∨ d = y ∨ d = w) :
    False := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with h | h | h <;> simp_all

end Pigeon

section Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

@[expose] def Big (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  ∃ a b c d : Subgroup G, a ∈ twinSet Ω K ∧ b ∈ twinSet Ω K ∧ c ∈ twinSet Ω K ∧
    d ∈ twinSet Ω K ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

theorem Big.of_four (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (h1 : K₄ ≠ K) (h2 : K₄ ≠ K') (h3 : K₄ ≠ K₃) : Big Ω K :=
  ⟨K, K', K₃, K₄, mem_twinSet_self h.stand.mem h.hz, h.hK', h.hK₃, hK₄, h.hne.symm,
    h.hK₃K.symm, h1.symm, h.hK₃K'.symm, h2.symm, h3.symm⟩

theorem Big.fourth {K : Subgroup G} (hb : Big Ω K) (x y w : Subgroup G) :
    ∃ t ∈ twinSet Ω K, t ≠ x ∧ t ≠ y ∧ t ≠ w := by
  obtain ⟨a, b, c, d, ha, hb', hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := hb
  by_contra hcon
  push Not at hcon
  have key : ∀ t ∈ twinSet Ω K, t = x ∨ t = y ∨ t = w := by
    intro t ht
    by_cases h1 : t = x
    · exact Or.inl h1
    by_cases h2 : t = y
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hcon t ht h1 h2))
  exact four_ne_three hab hac had hbc hbd hcd (key a ha) (key b hb') (key c hc) (key d hd)

theorem Big.of_twin {K L : Subgroup G} {z : G} (hb : Big Ω K) (hz : IsUniqueInvolution K z)
    (hL : L ∈ twinSet Ω K) : Big Ω L := by
  have h := twinSet_eq_of_mem_twinSet hz hL
  unfold Big at hb ⊢
  rw [h]
  exact hb

theorem hyp22Setting_of_sylows {K K' K₃ : Subgroup G} {z : G} (hst : AscStand p f Ω K)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K = twinSet Ω K) (hK₃ : K₃ ∈ twinSet Ω K) (hK₃K : K₃ ≠ K)
    (hK₃K' : K₃ ≠ K') {R R' R₃ : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hR₃ : IsSylow2In R₃ K₃) (c₁₂ : Commutes R R') (c₁₃ : Commutes R R₃)
    (c₂₃ : Commutes R' R₃) {u₁ u₂ u₃ : G} (h₁ : u₁ ∈ R) (h₂ : u₂ ∈ R') (h₃ : u₃ ∈ R₃)
    (o₁ : orderOf u₁ = 4) (o₂ : orderOf u₂ = 4) (o₃ : orderOf u₃ = 4) :
    Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hzK₃ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hz hK₃
  have hB := T7B.isElemAbelian2_B hst.hyp hst.mem hK'.1 hK₃.1 hne hK₃K hK₃K' hz hzK' hzK₃
    (hR.1 h₁) (hR'.1 h₂) (hR₃.1 h₃) o₁ o₂ o₃ (c₁₂ u₁ h₁ u₂ h₂) (c₁₃ u₁ h₁ u₃ h₃)
    (c₂₃ u₂ h₂ u₃ h₃)
  exact
    { stand := hst
      hz := hz
      hK' := hK'
      hne := hne
      perp := hperp
      hK₃ := hK₃
      hK₃K := hK₃K
      hK₃K' := hK₃K'
      hu₁ := ⟨hR.1 h₁, o₁⟩
      hu₂ := ⟨hR'.1 h₂, o₂⟩
      hu₃ := ⟨hR₃.1 h₃, o₃⟩
      hB := hB }

theorem closure_rotate (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z, u₃ * u₁} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact T7B.mem_closure_thd
    · exact T7B.mem_closure_snd
    · rw [← T7J.comm₁₃ h]
      exact h.mem_B_13
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · have e : u₁ * u₂ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
        calc u₁ * u₂ = (z * z) * (u₁ * u₂) := by rw [h.hz.sq, one_mul]
          _ = z * (z * u₁ * u₂) := by group
          _ = z * (u₁ * z * u₂) := by rw [h.comm_z₁]
          _ = z * (u₂ * z * u₁) := by
              rw [show u₁ * z * u₂ = u₁ * (z * u₂) by group, h.comm_z₂,
                show u₂ * z * u₁ = u₂ * (z * u₁) by group, h.comm_z₁,
                show u₁ * (u₂ * z) = (u₁ * u₂) * z by group,
                show u₂ * (u₁ * z) = (u₂ * u₁) * z by group, h.comm₁₂]
          _ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
              rw [show (u₂ * u₃) * (u₃ * u₁) = u₂ * (u₃ * u₃) * u₁ by group, h.sq₃]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem closure_swap (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₁, z, u₁ * u₃} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · rw [← h.comm₁₂]
      exact T7B.mem_closure_fst
    · exact T7B.mem_closure_snd
    · exact h.mem_B_13
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · rw [h.comm₁₂]
      exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have e : u₂ * u₃ = z * ((u₂ * u₁) * (u₁ * u₃)) := by
        calc u₂ * u₃ = (z * z) * (u₂ * u₃) := by rw [h.hz.sq, one_mul]
          _ = z * (z * u₂ * u₃) := by group
          _ = z * (u₂ * z * u₃) := by rw [h.comm_z₂]
          _ = z * ((u₂ * u₁) * (u₁ * u₃)) := by
              rw [show (u₂ * u₁) * (u₁ * u₃) = u₂ * (u₁ * u₁) * u₃ by group, h.sq₁]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))

theorem rotate (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Hyp22Setting p f Ω K' K₃ K z u₂ u₃ u₁ := by
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hKK' : K ∈ twinSet Ω K' := by
    rw [twinSet_eq_of_mem_twinSet h.hz h.hK']
    exact mem_twinSet_self hK h.hz
  have hperp : KPerp Ω K' = KPerp Ω K := ((l6_3 p f hp hq G Ω hΩ K hK K' h.hK').1).symm
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz h.hK'
  refine
    { stand := h.stand.of_mem h.hK'.1
      hz := h.hzK'
      hK' := by rw [htw]; exact h.hK₃
      hne := h.hK₃K'
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := hKK'
      hK₃K := h.hne.symm
      hK₃K' := h.hK₃K.symm
      hu₁ := h.hu₂
      hu₂ := h.hu₃
      hu₃ := h.hu₁
      hB := ?_ }
  rw [closure_rotate h]
  exact h.hB

theorem swap (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Hyp22Setting p f Ω K' K K₃ z u₂ u₁ u₃ := by
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hperp : KPerp Ω K' = KPerp Ω K := ((l6_3 p f hp hq G Ω hΩ K hK K' h.hK').1).symm
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz h.hK'
  refine
    { stand := h.stand.of_mem h.hK'.1
      hz := h.hzK'
      hK' := by rw [htw]; exact mem_twinSet_self hK h.hz
      hne := h.hne.symm
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := by rw [htw]; exact h.hK₃
      hK₃K := h.hK₃K'
      hK₃K' := h.hK₃K
      hu₁ := h.hu₂
      hu₂ := h.hu₁
      hu₃ := h.hu₃
      hB := ?_ }
  rw [closure_swap h]
  exact h.hB

theorem isElemAbelian2_closure (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z} : Set G)) 2 := by
  have hne : u₁ * u₂ ≠ z := by
    intro he
    have hK' : K' ∈ Ω := h.hK'.1
    have hK : K ∈ Ω := h.stand.mem
    refine T7A.not_mem_inf_of_orderOf_four h.stand.hyp hK hK' h.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h.hu₁.1) h.hz.mem
  have h1 : u₁ * u₂ ≠ 1 := by
    intro he
    have hK' : K' ∈ Ω := h.hK'.1
    have hK : K ∈ Ω := h.stand.mem
    refine T7A.not_mem_inf_of_orderOf_four h.stand.hyp hK hK' h.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h.hu₁.1
  have hcomm : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [h.comm_z₂]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [h.comm_z₁]
      _ = z * (u₁ * u₂) := by group
  exact T7A.isElemAbelian2_closure_pair h.sq_12 h.hz.sq h1 h.hz.ne_one hne hcomm

end Setting

end S22

end CFSG.ClassicalInvolution.Asc77
