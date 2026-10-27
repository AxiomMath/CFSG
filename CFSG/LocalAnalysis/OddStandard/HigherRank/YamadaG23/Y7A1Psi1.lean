module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Dat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1NC1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_psi_data (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∃ (ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)) (lab : G → Fin 16), Y7APsi c ψ lab := by
  have h := c.y7acfg hH
  have hX1 : y7aX c ≤ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) := inf_le_left
  have hX2 : y7aX c ≤ normalizer (V1 c.e : Set G) := inf_le_right
  obtain ⟨ψ, lab, hker, hlab, hsurj, hact, htlab⟩ :=
    y7a_psi16 h hX1 hX2 (y7a_all16 c hH hF)
  have htU : c.s.t ∈ {w : G | w ∈ c.s.fr.A ⊔ C0 c.e ∧ w ∉ c.s.fr.A ⊔ V1 c.e} :=
    ⟨Subgroup.mem_sup_right (y7a_t_mem_C0 h), y7a_t_not_mem_AV h⟩
  have hK : CFSG.GH74.GLS.centralizerSection (c.s.fr.A ⊔ C0 c.e) (V1 c.e) = C1 c.e := by
    simpa only [y7aK, C1] using y7a_K_eq_C1 c hH
  have hC1X : C1 c.e ≤ y7aX c := by
    rw [← y7a_K_eq_C1 c hH]
    exact y7a_K_le_X c
  have hcardX : Nat.card ↥(y7aX c) = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hkercard : Nat.card ↥ψ.ker = Nat.card ↥(C1 c.e) := by
    rw [hker, hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC1X).toEquiv
  have hrange_card : Nat.card ↥ψ.range * Nat.card ↥(C1 c.e) = Nat.card ↥(y7aX c) := by
    rw [hcardX, hkercard]
  refine ⟨ψ, lab, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hker, hK]
  · simpa only [y7aU16] using hlab
  · simpa only [y7aU16] using hsurj
  · simpa only [y7aU16] using hact
  · exact htlab
  · intro x
    have hx1 : (x : G) ∈ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp x.property).1
    have hconjU : (x : G) * c.s.t * (x : G)⁻¹ ∈
        {w : G | w ∈ c.s.fr.A ⊔ C0 c.e ∧ w ∉ c.s.fr.A ⊔ V1 c.e} :=
      y7a_O_sub h hX1 hX2 ((x : G) * c.s.t * (x : G)⁻¹)
        (y7a_O_conj (X := y7aX c) (V := V1 c.e) (t := c.s.t) hX2 x.property
          (y7a_O_t (y7aX c) (V1 c.e) c.s.t))
    have h1 : ψ x 0 = lab ((x : G) * c.s.t * (x : G)⁻¹) := by
      rw [← htlab]
      exact hact x c.s.t htU
    rw [h1, show (0 : Fin 16) = lab c.s.t from htlab.symm,
      (hlab ((x : G) * c.s.t * (x : G)⁻¹) hconjU c.s.t htU)]
    have heq : ((x : G) * c.s.t * (x : G)⁻¹)⁻¹ * c.s.t =
        (c.s.t⁻¹ * ((x : G) * c.s.t * (x : G)⁻¹))⁻¹ := by group
    rw [heq, (V1 c.e).inv_mem_iff]
    exact y7a_stab_iff h hx1
  · intro i j
    obtain ⟨u, huU, hulab⟩ := hsurj i
    obtain ⟨u', hu'U, hu'lab⟩ := hsurj j
    obtain ⟨x, hxX, hxV⟩ := y7a_all16 c hH hF u huU.1 huU.2
    obtain ⟨x', hx'X, hx'V⟩ := y7a_all16 c hH hF u' hu'U.1 hu'U.2
    have hx0 : ψ ⟨x, hxX⟩ 0 = i := by
      have hcU : x * c.s.t * x⁻¹ ∈
          {w : G | w ∈ c.s.fr.A ⊔ C0 c.e ∧ w ∉ c.s.fr.A ⊔ V1 c.e} :=
        y7a_O_sub h hX1 hX2 (x * c.s.t * x⁻¹)
          (y7a_O_conj (X := y7aX c) (V := V1 c.e) (t := c.s.t) hX2 hxX
            (y7a_O_t (y7aX c) (V1 c.e) c.s.t))
      have h1 : ψ ⟨x, hxX⟩ 0 = lab (x * c.s.t * x⁻¹) := by
        rw [← htlab]
        exact hact ⟨x, hxX⟩ c.s.t htU
      rw [h1, (hlab (x * c.s.t * x⁻¹) hcU u huU).mpr hxV]
      exact hulab
    have hx'0 : ψ ⟨x', hx'X⟩ 0 = j := by
      have hc'U : x' * c.s.t * x'⁻¹ ∈
          {w : G | w ∈ c.s.fr.A ⊔ C0 c.e ∧ w ∉ c.s.fr.A ⊔ V1 c.e} :=
        y7a_O_sub h hX1 hX2 (x' * c.s.t * x'⁻¹)
          (y7a_O_conj (X := y7aX c) (V := V1 c.e) (t := c.s.t) hX2 hx'X
            (y7a_O_t (y7aX c) (V1 c.e) c.s.t))
      have h1 : ψ ⟨x', hx'X⟩ 0 = lab (x' * c.s.t * x'⁻¹) := by
        rw [← htlab]
        exact hact ⟨x', hx'X⟩ c.s.t htU
      rw [h1, (hlab (x' * c.s.t * x'⁻¹) hc'U u' hu'U).mpr hx'V]
      exact hu'lab
    refine ⟨ψ ⟨x', hx'X⟩ * (ψ ⟨x, hxX⟩)⁻¹, ?_, ?_⟩
    · exact ψ.range.mul_mem (MonoidHom.mem_range.mpr ⟨⟨x', hx'X⟩, rfl⟩)
        (ψ.range.inv_mem (MonoidHom.mem_range.mpr ⟨⟨x, hxX⟩, rfl⟩))
    · rw [Equiv.Perm.mul_apply]
      have hinv : (ψ ⟨x, hxX⟩)⁻¹ i = 0 := by
        rw [← hx0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rw [hinv, hx'0]
  · by_cases hRT : c.s.R = c.s.T
    · left
      have hY : Nat.card ↥(y7aY c) = 18 * Nat.card ↥(C1 c.e) := by
        simpa only [y7aY] using (y6_card_Y_m c.toCtx5 hH).1 hRT
      have hpos : 0 < Nat.card ↥(C1 c.e) := Nat.card_pos
      have key : Nat.card ↥ψ.range * Nat.card ↥(C1 c.e) = 288 * Nat.card ↥(C1 c.e) := by
        rw [hrange_card, y7a_card_X c hH hF, hY]
        ring
      exact Nat.eq_of_mul_eq_mul_right hpos key
    · right
      have hY : Nat.card ↥(y7aY c) = 36 * Nat.card ↥(C1 c.e) := by
        simpa only [y7aY] using (y6_card_Y_m c.toCtx5 hH).2 hRT
      have hpos : 0 < Nat.card ↥(C1 c.e) := Nat.card_pos
      have key : Nat.card ↥ψ.range * Nat.card ↥(C1 c.e) = 576 * Nat.card ↥(C1 c.e) := by
        rw [hrange_card, y7a_card_X c hH hF, hY]
        ring
      exact Nat.eq_of_mul_eq_mul_right hpos key

end CFSG.OddStandard.HigherRank.YamadaG23
