module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Class

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

namespace Pair

variable {t s : Two G} (h : Pair t s)
include h

theorem inf_V_W {z : G} (hz : z ∈ t.V₁ ∨ z ∈ t.V₂) (hw : z ∈ s.V₁ ∨ z ∈ s.V₂) : z = 1 := by
  by_contra hz1
  have hz2 : z * z = 1 := by
    rcases hz with hz | hz
    · exact h.cM.sq_V₁ hz
    · exact h.cM.sq_V₂ hz
  have hcs : (∀ x ∈ s.X₁, z * x = x * z) ∨ (∀ x ∈ s.X₂, z * x = x * z) := by
    rcases hw with hw | hw
    · exact Or.inr fun x hx => h.cN.comm z (s.V₁_le hw) x hx
    · exact Or.inl fun x hx => (h.cN.comm x hx z (s.V₂_le hw)).symm
  have hcent := h.cN.cent z hz1 hz2 hcs
  rcases hz with hz | hz
  · apply h.X₂nle
    intro y hy
    apply hcent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.cM.comm z (t.V₁_le hz) y hy).symm
  · apply h.X₁nle
    intro y hy
    apply hcent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.cM.comm y hy z (t.V₂_le hz)

theorem B_inf_V₁ [Finite G] {v : G} (hv : v ∈ t.V₁) (hvB : v ∈ s.A) : v = 1 := by
  by_contra hv1
  obtain ⟨w₁, hw₁, w₂, hw₂, hvw⟩ := h.cN.mem_A_iff.1 hvB
  have hw₁1 : w₁ ≠ 1 := by
    intro e
    rw [e, one_mul] at hvw
    exact hv1 (h.inf_V_W (Or.inl hv) (Or.inr (hvw ▸ hw₂)))
  have hw₂1 : w₂ ≠ 1 := by
    intro e
    rw [e, mul_one] at hvw
    exact hv1 (h.inf_V_W (Or.inl hv) (Or.inl (hvw ▸ hw₁)))
  have h9 := h.cN.class_nine hw₁ hw₁1 hw₂ hw₂1
  rw [← hvw] at h9
  have hv2 : v * v = 1 := h.cM.sq_V₁ hv
  have hcent : Subgroup.centralizer ({v} : Set G) ≤ t.M :=
    h.cM.cent v hv1 hv2 (Or.inr fun x hx => h.cM.comm v (t.V₁_le hv) x hx)
  have hKle : s.M ⊓ Subgroup.centralizer {v} ≤ Subgroup.normalizer (t.X₁ : Set G) ⊓ t.M := by
    intro k hk
    obtain ⟨-, hkC⟩ := Subgroup.mem_inf.1 hk
    have hkM : k ∈ t.M := hcent hkC
    refine Subgroup.mem_inf.2 ⟨?_, hkM⟩
    apply mem_normalizer_iff_conjSub.2
    rcases h.cM.perm k hkM with ⟨e1, -⟩ | ⟨e1, -⟩
    · exact e1
    · exfalso
      have hkv : k * v = v * k := Subgroup.mem_centralizer_singleton_iff.1 hkC
      have h1 : k * v * k⁻¹ ∈ conjSub k t.V₁ := conj_mem_conjSub hv
      have e : conjSub k t.V₁ = t.V₂ := by
        show conjSub k (pCoreOf 2 t.X₁) = pCoreOf 2 t.X₂
        rw [← pCoreOf_conjSub, e1]
      have e2 : k * v * k⁻¹ = v := by rw [hkv]; group
      rw [e2, e] at h1
      exact hv1 (h.cM.inf_V hv h1)
  have hD := Subgroup.relIndex_mul_card (Subgroup.normalizer (t.X₁ : Set G)) t.M
  rw [h.cM.relIndex_normalizer] at hD
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hKle
  have hpos : 0 < Nat.card ↥(s.M ⊓ Subgroup.centralizer {v}) := Nat.card_pos
  have h' : 2 * j * Nat.card ↥(s.M ⊓ Subgroup.centralizer {v}) =
      9 * Nat.card ↥(s.M ⊓ Subgroup.centralizer {v}) := by
    calc 2 * j * Nat.card ↥(s.M ⊓ Subgroup.centralizer {v})
        = 2 * (Nat.card ↥(s.M ⊓ Subgroup.centralizer {v}) * j) := by ring
      _ = 2 * Nat.card ↥(Subgroup.normalizer (t.X₁ : Set G) ⊓ t.M) := by rw [← hj]
      _ = Nat.card t.M := hD
      _ = Nat.card s.M := h.card
      _ = 9 * Nat.card ↥(s.M ⊓ Subgroup.centralizer {v}) := h9
  have := Nat.eq_of_mul_eq_mul_right hpos h'
  omega

theorem B_inf_V₂ [Finite G] {v : G} (hv : v ∈ t.V₂) (hvB : v ∈ s.A) : v = 1 :=
  h.swap_left.B_inf_V₁ hv hvB

theorem A_inf_W₁ [Finite G] {v : G} (hv : v ∈ s.V₁) (hvA : v ∈ t.A) : v = 1 :=
  h.symm.B_inf_V₁ hv hvA

theorem A_inf_W₂ [Finite G] {v : G} (hv : v ∈ s.V₂) (hvA : v ∈ t.A) : v = 1 :=
  h.symm.B_inf_V₂ hv hvA

end Pair

end CFSG.CGT.PushingUpLit.A4.L34
