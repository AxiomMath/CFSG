module

public import CFSG.LocalAnalysis.OddStandard.ONanLocOne

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2 CFSG.ABGLocalTools
  CFSG.ComponentClassification.GHarris

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

theorem exists_fusABC_out_of_not_closed (D : FusCtx G v1 v2 v3 s t)
    (hnc : ∃ a ∈ alpW v1 v2 v3, ∃ g : G, g⁻¹ * a * g ∈ alpP v1 v2 v3 s t ∧
      g⁻¹ * a * g ∉ alpW v1 v2 v3) :
    ∃ j : Fin 7, 3 ≤ j.val ∧ D.FusABC j := by
  obtain ⟨a, haW, g, hg, hgW⟩ := hnc
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [mul_one, inv_mul_cancel] at hgW
    exact hgW (one_mem _)
  obtain ⟨haV, ha2⟩ := D.mem_W_iff.1 haW
  obtain ⟨i, hi⟩ := D.exists_inClass (D.V_le_P haV) ha2 ha1
  have hi2 := D.le_two_of_inClass_mem_V hi haV
  have hy2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := by
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hy1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨j, hj⟩ := D.exists_inClass hg hy2 hy1
  have hj3 : 3 ≤ j.val := by
    by_contra hlt
    exact hgW (D.mem_W_of_inClass hj (by omega))
  exact ⟨j, hj3, D.fusABC_of_le_two hi2 (FusCtx.Fus.symm D (D.inClass_fus hi hj g rfl))⟩

theorem fus_all_of_out (D : FusCtx G v1 v2 v3 s t)
    (hout : ∃ j : Fin 7, 3 ≤ j.val ∧ D.FusABC j) : ∀ i : Fin 7, D.Fus 0 i := by
  have hAB := D.fus_AB
  have hAC := D.fus_AC hAB
  obtain ⟨j0, hj0, hABC0⟩ := hout
  have hE := D.fus_E_DFG hAB
  have hno : ∀ {i j : Fin 7}, D.Fus i j → ¬ D.FusABC j → ¬ D.FusABC i :=
    fun hij hj hi => hj (FusCtx.FusABC.of_fus D (FusCtx.Fus.symm D hij) hi)
  have hall : ∀ k : Fin 7, 3 ≤ k.val → D.FusABC k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk, hnk⟩ := hcon
    have h356 : ¬ D.FusABC 3 ∧ ¬ D.FusABC 5 ∧ ¬ D.FusABC 6 := by
      have : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · obtain ⟨h5, h6⟩ := D.fus_D hnk
        exact ⟨hnk, hno (FusCtx.Fus.symm D h5) hnk, hno (FusCtx.Fus.symm D h6) hnk⟩
      · obtain ⟨h3, h5, h6⟩ := D.fus_E hnk
        exact ⟨hno (FusCtx.Fus.symm D h3) hnk, hno (FusCtx.Fus.symm D h5) hnk,
          hno (FusCtx.Fus.symm D h6) hnk⟩
      · obtain ⟨h3, h6⟩ := D.fus_F hnk
        exact ⟨hno (FusCtx.Fus.symm D h3) hnk, hnk, hno (FusCtx.Fus.symm D h6) hnk⟩
      · obtain ⟨h3, h5⟩ := D.fus_G hnk
        exact ⟨hno (FusCtx.Fus.symm D h3) hnk, hno (FusCtx.Fus.symm D h5) hnk, hnk⟩
    obtain ⟨h3, h5, h6⟩ := h356
    have h4 : ¬ D.FusABC 4 := by
      rcases hE with h | h | h
      · exact hno h h3
      · exact hno h h5
      · exact hno h h6
    have : j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact h3 hABC0
    · exact h4 hABC0
    · exact h5 hABC0
    · exact h6 hABC0
  intro i
  by_cases hi : i.val ≤ 2
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact FusCtx.Fus.refl D 0
    · exact hAB
    · exact hAC
  · rcases hall i (by omega) with h | h | h
    · exact FusCtx.Fus.symm D h
    · exact hAB.trans D (FusCtx.Fus.symm D h)
    · exact hAC.trans D (FusCtx.Fus.symm D h)

theorem oneClass_of_fus_all (D : FusCtx G v1 v2 v3 s t) (hall : ∀ i : Fin 7, D.Fus 0 i) :
    OneClass G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ u : G, orderOf u = 2 → ∃ g : G, g * u * g⁻¹ = invRep v1 v2 v3 s t 0 := by
    intro u hu
    have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hu
      exact absurd hu (by decide)
    have hup : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_P le_top hup
    have hcuP : c * u * c⁻¹ ∈ alpP v1 v2 v3 s t := hc u (mem_zpowers u)
    have hcu2 : c * u * c⁻¹ * (c * u * c⁻¹) = 1 := by
      calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hcu1 : c * u * c⁻¹ ≠ 1 := by
      intro h1
      apply hu1
      calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨i, d, -, hd⟩ := D.exists_inClass hcuP hcu2 hcu1
    obtain ⟨g, hg⟩ := hall i
    refine ⟨g * d * c, ?_⟩
    calc g * d * c * u * (g * d * c)⁻¹ = g * (d * (c * u * c⁻¹) * d⁻¹) * g⁻¹ := by group
      _ = g * (d * (d⁻¹ * invRep v1 v2 v3 s t i * d) * d⁻¹) * g⁻¹ := by rw [hd]
      _ = g * invRep v1 v2 v3 s t i * g⁻¹ := by group
      _ = g * (g⁻¹ * invRep v1 v2 v3 s t 0 * g) * g⁻¹ := by rw [hg]
      _ = invRep v1 v2 v3 s t 0 := by group
  intro u w hu hw
  obtain ⟨g1, h1⟩ := key u hu
  obtain ⟨g2, h2⟩ := key w hw
  rw [isConj_iff]
  refine ⟨g2⁻¹ * g1, ?_⟩
  calc g2⁻¹ * g1 * u * (g2⁻¹ * g1)⁻¹ = g2⁻¹ * (g1 * u * g1⁻¹) * g2 := by group
    _ = g2⁻¹ * (g2 * w * g2⁻¹) * g2 := by rw [h1, h2]
    _ = w := by group

theorem oneClass_of_not_closed (D : FusCtx G v1 v2 v3 s t)
    (hnc : ∃ a ∈ alpW v1 v2 v3, ∃ g : G, g⁻¹ * a * g ∈ alpP v1 v2 v3 s t ∧
      g⁻¹ * a * g ∉ alpW v1 v2 v3) :
    OneClass G :=
  oneClass_of_fus_all D (fus_all_of_out D (exists_fusABC_out_of_not_closed D hnc))

end CFSG.ComponentClassification.GrSLit.ONanBal
