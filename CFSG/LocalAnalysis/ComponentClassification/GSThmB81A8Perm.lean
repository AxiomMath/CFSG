module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8PermInputs
public import Certificates.Certificate2019
public import Certificates.Certificate2007
public import Certificates.Certificate2014

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

theorem tau_ok : tauSwapCheck t15 = true :=
  Certificates.certificate2019.1

theorem mem_t15_of_conj {γ : P8} (hγ : γ ∈ QA8.originalSubgroup)
    (h2 : s8 * (γ⁻¹ * s8 * γ) * (s8 * (γ⁻¹ * s8 * γ)) = 1) (h1 : s8 * (γ⁻¹ * s8 * γ) ≠ 1) :
    s8 * (γ⁻¹ * s8 * γ) ∈ t15 := by
  clear hγ
  have hsw : γ⁻¹ * s8 * γ = Equiv.swap (γ⁻¹ 0) (γ⁻¹ 1) := by
    rw [Equiv.swap_apply_apply, inv_inv, ← List.formPerm_pair]
    rfl
  have hne : γ⁻¹ 0 ≠ γ⁻¹ 1 := fun h => absurd (γ⁻¹.injective h) (by decide)
  have h := List.all_eq_true.1 (List.all_eq_true.1 tau_ok (γ⁻¹ 0) (List.mem_finRange _)) (γ⁻¹ 1)
    (List.mem_finRange _)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.any_eq_true] at h
  rw [← hsw] at h
  rcases h with ((h | h) | h) | ⟨u, hu, hut⟩
  · exact absurd h hne
  · exact absurd h2 h
  · exact absurd h h1
  · exact hut ▸ hu

theorem n3_ok : n3Check (elemsT QL8) QL8 n3Data = true :=
  Certificates.certificate2019.2.1

theorem exists_three_cycle {t : P8} (ht : t ∈ t15) :
    ∃ θ e₁ e₂ : P8, θ ∈ QL8.originalSubgroup ∧ e₁ ∈ QL8.originalSubgroup ∧
      e₂ ∈ QL8.originalSubgroup ∧ θ * t = t * θ ∧ e₁ * t = t * e₁ ∧ e₂ * t = t * e₂ ∧
      θ * e₁ * θ⁻¹ = e₂ ∧ θ * e₂ * θ⁻¹ = e₁ * e₂ ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧
      e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ ∧
      Nat.card ↥(QL8.originalSubgroup ⊓ centralizer ({t} : Set P8)) = 24 ∧
      ∀ c ∈ QL8.originalSubgroup, c * t = t * c →
        c * e₁ * c⁻¹ ∈ four e₁ e₂ ∧ c * e₂ * c⁻¹ ∈ four e₁ e₂ := by
  obtain ⟨⟨t', θ, e₁, e₂⟩, hx, rfl⟩ := List.mem_map.1 ht
  have h := List.all_eq_true.1 n3_ok _ hx
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hθ, he₁⟩, he₂⟩, hθt⟩, he₁t⟩, he₂t⟩, hθ₁⟩, hθ₂⟩, he₁₁⟩, he₂₂⟩, he₁₂⟩,
    he₁1⟩, he₂1⟩, hne⟩, hcard⟩, hnorm⟩ := h
  refine ⟨θ, e₁, e₂, (mem_iff_sift QL8 QL8_ok θ).2 hθ, (mem_iff_sift QL8 QL8_ok e₁).2 he₁,
    (mem_iff_sift QL8 QL8_ok e₂).2 he₂, hθt, he₁t, he₂t, hθ₁, hθ₂, he₁₁, he₂₂, he₁₂, he₁1, he₂1,
    hne, by rw [card_inf_centralizer QL8 QL8_ok]; exact hcard, fun c hc hct => ?_⟩
  rcases hnorm c ((mem_elemsT QL8 QL8_ok c).2 hc) with h1 | ⟨⟨u, hu, hcu⟩, ⟨w, hw, hcw⟩⟩
  · exact absurd hct h1
  · exact ⟨hcu ▸ hu, hcw ▸ hw⟩

theorem n4_ok : n4Check (elemsT QL8) t15 QA8 = true :=
  Certificates.certificate2019.2.2

theorem getD_take_map8 (p : P8) {k : Nat} {i : Fin 8} (hi : i.val < k) :
    (((List.finRange 8).map p).take k).getD i 0 = p i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_map8 (p : P8) (i : Fin 8) : ((List.finRange 8).map p).getD i 0 = p i := by
  simp [List.getD_eq_getElem?_getD]

theorem take_map_mem_sqRootVecs {t p : P8} (hpt : ∀ i, p (p i) = t i) :
    ∀ k, k ≤ 8 → ((List.finRange 8).map p).take k ∈ sqRootVecs t k := by
  intro k
  induction k with
  | zero => simp [sqRootVecs]
  | succ k ih =>
    intro hk
    have hL : ((List.finRange 8).map p).take (k + 1) =
        ((List.finRange 8).map p).take k ++ [p ⟨k, by omega⟩] := by
      rw [List.take_add_one]
      simp [show k < 8 by omega]
    rw [sqRootVecs, List.mem_flatMap]
    refine ⟨_, ih (by omega), ?_⟩
    rw [List.mem_filter, List.mem_map]
    refine ⟨⟨p ⟨k, by omega⟩, List.mem_finRange _, hL.symm⟩, ?_⟩
    simp only [sqRootOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, List.length_take, List.length_map,
      List.length_finRange]
    refine ⟨((List.nodup_finRange 8).map p.injective).sublist (List.take_sublist _ _), ?_⟩
    intro i _
    by_cases hi : i.val < min (k + 1) 8
    · rw [getD_take_map8 p (i := i) (by omega)]
      refine Or.inr ⟨?_, ?_⟩
      · by_cases hpi : (p i).val < min (k + 1) 8
        · right
          rw [getD_take_map8 p (i := p i) (by omega)]
          exact hpt i
        · exact Or.inl hpi
      · by_cases hti : (t i).val < min (k + 1) 8
        · right
          rw [getD_take_map8 p (i := t i) (by omega), ← hpt i]
          exact hpt (p i)
        · exact Or.inl hti
    · exact Or.inl hi

theorem map_mem_sqRootVecs {t p : P8} (hpt : ∀ i, p (p i) = t i) :
    (List.finRange 8).map p ∈ sqRootVecs t 8 := by
  have h := take_map_mem_sqRootVecs hpt 8 le_rfl
  rwa [List.take_of_length_le (by simp)] at h

theorem mem_QL8_of_pow_315 {θ : P8} (hθo : θ ^ 315 = 1) (hθs : θ * s8 = s8 * θ) :
    θ ∈ QL8.originalSubgroup := by
  have hsign : Equiv.Perm.sign θ = 1 := by
    have h := congrArg Equiv.Perm.sign hθo
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign θ) with h' | h'
    · exact h'
    · rw [h', Odd.neg_one_pow (by decide : Odd 315)] at h
      exact absurd h (by decide)
  set C := QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8)
  have hLC : QL8.originalSubgroup ≤ C := commutator_C0 ▸ commutator_le_self C
  have hC : θ ∈ C := mem_C0 hsign hθs
  have hidx : (QL8.originalSubgroup.subgroupOf C).index = 2 := by
    have h := (QL8.originalSubgroup.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv, card_QL8, card_C0] at h
    omega
  have hsq := Subgroup.mul_self_mem_of_index_two hidx ⟨θ ^ 157, pow_mem hC 157⟩
  rw [Subgroup.mem_subgroupOf] at hsq
  have heq : θ = θ ^ 315 * (θ ^ 157 * θ ^ 157)⁻¹ := by group
  rw [heq, hθo, one_mul]
  exact inv_mem hsq

theorem exists_conj_of_odd {t p θ : P8} (ht : t ∈ t15) (hpt : p * p = t)
    (hps : s8 * p * s8 = p⁻¹) (hθ1 : θ ≠ 1) (hθo : θ ^ 315 = 1) (hθp : θ * p = p * θ)
    (hθs : θ * s8 = s8 * θ) :
    ∃ π ∈ QA8.originalSubgroup, π * t * π⁻¹ = p * s8 := by
  clear hps
  have hpt' : ∀ i, p (p i) = t i := fun i => by
    rw [← hpt]
    rfl
  have hp := map_mem_sqRootVecs hpt'
  have hθL : θ ∈ elemsT QL8 := (mem_elemsT QL8 QL8_ok θ).2 (mem_QL8_of_pow_315 hθo hθs)
  have hθp' : ∀ i, θ (p i) = p (θ i) := fun i => by
    have h := congrArg (fun f : P8 => f i) hθp
    exact h
  have hθ4 : ¬ ∀ i, θ (θ (θ (θ i))) = i := fun h4 => by
    have h4' : θ ^ 4 = 1 := Equiv.ext fun i => by
      simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact h4 i
    have heq : θ = (θ ^ 315)⁻¹ * (θ ^ 4) ^ 79 := by group
    rw [hθo, h4', inv_one, one_pow, one_mul] at heq
    exact hθ1 heq
  have h := List.all_eq_true.1 (List.all_eq_true.1 n4_ok t ht) _ hp
  simp only [getD_map8, Bool.or_eq_true, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, decide_eq_true_eq, List.mem_finRange,
    forall_const] at h
  rcases h with h | ⟨hπ, hπp⟩
  · have hθt : θ ∈ (elemsT QL8).filter fun θ =>
        ((List.finRange 8).all fun i => decide (θ (t i) = t (θ i))) &&
          !((List.finRange 8).all fun i => decide (θ (θ (θ (θ i))) = i)) := by
      refine List.mem_filter.2 ⟨hθL, ?_⟩
      rw [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
      refine ⟨List.all_eq_true.2 fun i _ => decide_eq_true ?_, fun h4 => hθ4 fun i =>
        of_decide_eq_true (List.all_eq_true.1 h4 i (List.mem_finRange i))⟩
      rw [← hpt' i, ← hpt' (θ i), hθp', hθp']
    exact absurd (List.all_eq_true.2 fun i _ => decide_eq_true (hθp' i)) (h θ hθt)
  · exact ⟨_, (mem_iff_sift QA8 QA8_ok _).2 hπ, Equiv.ext fun i => hπp i⟩

end CFSG.ComponentClassification.GSThmB.A8
