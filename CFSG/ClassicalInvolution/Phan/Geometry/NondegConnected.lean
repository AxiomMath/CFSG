module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwo
public import CFSG.ClassicalInvolution.Phan.Phan3GQuad

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem exists_aniso_orth_orth {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) {a b : Fin m → K} (haW : a ∈ W) (ha : herm σ a a ≠ 0) (hbW : b ∈ W) :
    ∃ u ∈ W, herm σ u u ≠ 0 ∧ herm σ a u = 0 ∧ herm σ b u = 0 := by
  have hU : Nondeg σ (W ⊓ perp σ (K ∙ a)) := Nondeg.inf_perp_span_singleton hσ haW ha hW
  have hdim := finrank_eq_inf_perp_add_one hσ haW ha
  have hb : projPerp σ a b ∈ W ⊓ perp σ (K ∙ a) := by
    refine ⟨?_, mem_perp_span_singleton.mpr (herm_projPerp_left hσ ha b)⟩
    rw [projPerp_apply]
    exact W.sub_mem hbW (W.smul_mem _ haW)
  obtain ⟨u, huU, huu, hbu⟩ := Q3G.exists_aniso_orth hσ hU (by omega) hb
  have hau : herm σ a u = 0 :=
    (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp huU.2)
  refine ⟨u, huU.1, huu, hau, ?_⟩
  rwa [projPerp_apply, herm_sub_left, herm_smul_left, hau, mul_zero, sub_zero] at hbu

theorem exists_orth_orth_nsPts {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) {x y : Submodule K (Fin m → K)} (hx : x ∈ nsPts σ W)
    (hy : y ∈ nsPts σ W) :
    ∃ z ∈ nsPts σ W, Orth σ x z ∧ Orth σ z y ∧ IsCollinear σ x z ∧ IsCollinear σ z y := by
  obtain ⟨a, ha, haW, rfl⟩ := mem_nsPts_iff.mp hx
  obtain ⟨b, -, hbW, rfl⟩ := mem_nsPts_iff.mp hy
  obtain ⟨u, huW, huu, hau, hbu⟩ := exists_aniso_orth_orth hσ hW h4 haW ha hbW
  have hz : K ∙ u ∈ nsPts σ W := span_singleton_mem_nsPts huu huW
  have hxz : Orth σ (K ∙ a) (K ∙ u) := orth_span_singleton_iff.mpr hau
  have hzy : Orth σ (K ∙ u) (K ∙ b) :=
    orth_span_singleton_iff.mpr ((herm_eq_zero_iff hσ _ _).mp hbu)
  exact ⟨K ∙ u, hz, hxz, hzy, IsCollinear.of_orth hσ hx hz hxz, IsCollinear.of_orth hσ hz hy hzy⟩

theorem collGraph_edist_le_two_of_four_le {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) (x y : ↥(nsPts σ W)) : (collGraph σ W).edist x y ≤ 2 := by
  obtain ⟨z, hz, -, -, hxz, hzy⟩ := exists_orth_orth_nsPts hσ hW h4 x.2 y.2
  have h1 : (collGraph σ W).Adj x ⟨z, hz⟩ := hxz
  have h2 : (collGraph σ W).Adj ⟨z, hz⟩ y := hzy
  calc (collGraph σ W).edist x y ≤ (SimpleGraph.Walk.cons h1 h2.toWalk).length :=
      SimpleGraph.edist_le _
    _ = 2 := by simp

theorem collGraph_ediam_le_two_of_four_le {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) : (collGraph σ W).ediam ≤ 2 :=
  SimpleGraph.ediam_le_of_edist_le (collGraph_edist_le_two_of_four_le hσ hW h4)

theorem collGraph_connected_of_four_le {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) : (collGraph σ W).Connected := by
  have hne : (nsPts σ W).Nonempty :=
    nsPts_nonempty_of_nondeg hσ hW (fun h => by rw [h, finrank_bot] at h4; omega)
  have : Nonempty ↥(nsPts σ W) := hne.to_subtype
  refine ⟨fun x y => ?_⟩
  rw [← SimpleGraph.edist_ne_top_iff_reachable]
  exact ne_top_of_le_ne_top (by simp) (collGraph_edist_le_two_of_four_le hσ hW h4 x y)

theorem ndGraph_connected {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) : (ndGraph σ W).Connected := by
  have hpt : ∀ p ∈ nsPts σ W, ∃ P : NdVert σ W, P.1 = p := fun p hp =>
    ⟨⟨p, hp.1, fun h => by
        have h1 := hp.2.1
        rw [h, finrank_bot] at h1
        omega,
      fun h => by
        have h1 := hp.2.1
        rw [h] at h1
        omega, hp.2.2⟩, rfl⟩
  have hjoin : ∀ P Q : NdVert σ W, P.1 ∈ nsPts σ W → Q.1 ∈ nsPts σ W →
      (ndGraph σ W).Reachable P Q := by
    intro P Q hP hQ
    obtain ⟨z, hz, hPz, hzQ, hc₁, hc₂⟩ := exists_orth_orth_nsPts hσ hW h4 hP hQ
    obtain ⟨Z, rfl⟩ := hpt z hz
    obtain ⟨S, hPS, hZS⟩ := exists_ndVert_lt_of_orth hσ (by omega) hP hz hc₁.1 hPz
    obtain ⟨T, hZT, hQT⟩ := exists_ndVert_lt_of_orth hσ (by omega) hz hQ hc₂.1 hzQ
    have e₁ : (ndGraph σ W).Adj P S := Or.inl hPS
    have e₂ : (ndGraph σ W).Adj S Z := Or.inr hZS
    have e₃ : (ndGraph σ W).Adj Z T := Or.inl hZT
    have e₄ : (ndGraph σ W).Adj T Q := Or.inr hQT
    exact e₁.reachable.trans (e₂.reachable.trans (e₃.reachable.trans e₄.reachable))
  have hdown : ∀ S : NdVert σ W, ∃ P : NdVert σ W, P.1 ∈ nsPts σ W ∧
      (ndGraph σ W).Reachable S P := by
    intro S
    obtain ⟨p, hp, hpS⟩ := NdVert.exists_nsPts_le hσ S
    obtain ⟨P, rfl⟩ := hpt p hp
    refine ⟨P, hp, ?_⟩
    rcases hpS.lt_or_eq with h | h
    · have e : (ndGraph σ W).Adj S P := Or.inr h
      exact e.reachable
    · obtain rfl : P = S := Subtype.ext h
      exact SimpleGraph.Reachable.refl _
  obtain ⟨p, hp⟩ := nsPts_nonempty_of_nondeg hσ hW (fun h => by
    rw [h, finrank_bot] at h4
    omega)
  obtain ⟨P, -⟩ := hpt p ⟨hp.1, hp.2.1, hp.2.2⟩
  have : Nonempty (NdVert σ W) := ⟨P⟩
  refine ⟨fun S T => ?_⟩
  obtain ⟨S', hS', hSS'⟩ := hdown S
  obtain ⟨T', hT', hTT'⟩ := hdown T
  exact hSS'.trans ((hjoin S' T' hS' hT').trans hTT'.symm)

end CFSG.ClassicalInvolution.Phan
