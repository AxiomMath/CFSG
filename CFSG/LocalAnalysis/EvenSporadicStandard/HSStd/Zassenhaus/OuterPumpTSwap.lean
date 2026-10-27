module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseCloseSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseClose
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSeitzAlt10
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTKillSylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd CFSG.Open

section Gen

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem false_of_swapSingle_gen
    (h : HSOuterSetup G L t S z n v s) {M : Subgroup G} (hM : SwapSingle h M)
    (hfix : FixerBound (↥M ⧸ center ↥M)) (hSH : StdHyp G M)
    (hC : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2) {g' : G}
    (hgv : g' ∈ centralizer ({v} : Set G))
    (hgL : g' ∈ centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G))
    (hgt : g' * t * g'⁻¹ = t * v) (hg2 : g' * g' = 1) : False := by
  have ht2 : t * t = 1 := t_sq h
  have hv2 : v * v = 1 := h.ctx.v_sq
  have ha : (t * g') * (t * g') = v := swap_mul_sq h hg2 hgt
  have ha2 : (t * g') * (t * g') ≠ 1 := by
    rw [ha]
    exact h.v_ne_one
  have ha4 : (t * g') ^ 4 = 1 := by
    calc (t * g') ^ 4 = ((t * g') * (t * g')) * ((t * g') * (t * g')) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [ha, hv2]
  have hta : t * (t * g') * t = (t * g')⁻¹ := by
    have h1 : (t * g') * (g' * t) = 1 := by
      calc (t * g') * (g' * t) = t * (g' * g') * t := by group
        _ = 1 := by rw [hg2, mul_one, ht2]
    rw [inv_eq_of_mul_eq_one_right h1]
    calc t * (t * g') * t = (t * t) * g' * t := by group
      _ = g' * t := by rw [ht2, one_mul]
  obtain ⟨Q, hQ8, hQp, hQle⟩ := exists_dihedral_subgroup t (t * g') ht2 ha2 ha4 hta
  have hMC : M ≤ centralizer ({v} : Set G) := hM.comp.1
  have : (M.subgroupOf (centralizer ({v} : Set G))).Normal := hM.normal
  have hg_norm : g' ∈ normalizer (M : Set G) :=
    le_normalizer_of_normal_subgroupOf hMC hgv
  have ht_norm : t ∈ normalizer (M : Set G) := mem_normalizer_of_involution ht2 hM.inv
  have ht_cent : t ∈ centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_iff.1 h.t_mem l (derivedCentralizerIn_le L v hl)
  have hQ : Q ≤ normalizer (M : Set G) ⊓
      centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G) :=
    hQle _ ⟨ht_norm, ht_cent⟩ ⟨mul_mem ht_norm hg_norm, mul_mem ht_cent hgL⟩
  have hperf : commutator ↥M = ⊤ := hSH.standard.1.1
  obtain ⟨e⟩ := derivedCentralizerIn_equiv h.ctx.v_cls
  have hC2 : ∀ R : Subgroup G, R ≤ centralizer (M : Set G) → IsPGroup 2 R → Nat.card R ≤ 2 :=
    fun R hR hRp => card_le_two_of_le_centralizer hC hR hRp
  have h4 := card_le_four_of_two_subgroup_gen hfix hperf hM.le ⟨e⟩ hC2 (hQ.trans inf_le_left)
    (hQ.trans inf_le_right) hQp
  omega

theorem not_alt8_of_swapSingle
    (h : HSOuterSetup G L t S z n v s) {M : Subgroup G} (hM : SwapSingle h M) :
    ¬ Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨e8⟩
  have h8 := Nat.card_congr e8.toEquiv
  rw [card_alt_eight_pump] at h8
  rcases hM.types with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | e | e
  · have := Nat.card_congr e.toEquiv
    rw [card_alt_ten_pump] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_alt_twelve_pump] at this
    omega
  · have := card_quotient_of_isSporadic_hs e
    omega
  · omega

end Gen

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
