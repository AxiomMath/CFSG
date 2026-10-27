module

public import CFSG.Certificates.CosetTableColumns
public import CFSG.Certificates.CosetTableCompact

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ) : Bool :=
  decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) &&
    checkC (colParams ws ((subsetOf m S).map fun x => [(x, true)])) cap n

@[expose] def subsetCheckShortCC (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ) :
    Bool :=
  decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) &&
    checkHLTC (colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k) cap n

theorem subsetCheckC_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {cap n : ℕ} (h : subsetCheckCC ws S cap n = true) : subsetCheckC ws S cap n = true := by
  unfold subsetCheckCC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcap, hc⟩ := h
  unfold subsetCheckC
  rw [← checkC_eq n hcap]
  exact hc

theorem subsetCheckShortC_of_subsetCheckShortCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShortCC ws S k cap n = true) :
    subsetCheckShortC ws S k cap n = true := by
  unfold subsetCheckShortCC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcap, hc⟩ := h
  unfold subsetCheckShortC
  rw [← checkHLTC_eq n hcap]
  exact hc

theorem card_le_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    (h : subsetCheckCC ws S cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) :=
  card_le_of_subsetCheckC ws S (subsetCheckC_of_subsetCheckCC ws S h)

theorem card_le_of_subsetCheckShortCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShortCC ws S k cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) :=
  card_le_of_subsetCheckShortC ws S (subsetCheckShortC_of_subsetCheckShortCC ws S h)

theorem card_le_of_subsetCheckCC_nil (ws : List (List (Fin m × Bool))) {cap n : ℕ}
    (h : subsetCheckCC ws [] cap n = true) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n :=
  card_le_of_subsetCheckC_nil ws (subsetCheckC_of_subsetCheckCC ws [] h)

@[expose] def cyclicColCheckC (ws : List (List (Fin m × Bool))) (u : List (Fin m × Bool))
    (k cap n : ℕ) : Bool :=
  ws.contains (List.replicate k u).flatten &&
    decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) && checkC (colParams ws [u]) cap n

theorem card_le_of_cyclicColCheckC (ws : List (List (Fin m × Bool))) (u : List (Fin m × Bool))
    {k cap n : ℕ} (hk0 : 0 < k) (h : cyclicColCheckC ws u k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * k := by
  unfold cyclicColCheckC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨hk, hcap⟩, hc⟩ := h
  have hc' : check (colParams ws [u]) cap n = true := by
    rw [← checkC_eq n hcap]
    exact hc
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set g : PG m ws := PresentedGroup.mk rels (FreeGroup.mk u)
  obtain ⟨hfi, hidx⟩ := index_le_of_check
    (goodColParams ws [u] (Subgroup.zpowers g)
      (by intro w hw; simp at hw; subst hw; exact Subgroup.mem_zpowers g))
    (by simpa [colParams, mkParams] using closure_colLetter ws) hc'
  have hg : g ^ k = 1 := by
    rw [show g ^ k = PresentedGroup.mk rels (FreeGroup.mk u ^ k) from (map_pow _ _ _).symm,
      ← mk_flatten_replicate]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hk)
  have hord : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hg
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hord hk0
  have hfinz : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hcard : Nat.card (Subgroup.zpowers g) ≤ k := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd hk0 hord
  have hG : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ Subgroup.zpowers g) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (Subgroup.zpowers g)
  refine ⟨hG, ?_⟩
  rw [← (Subgroup.zpowers g).index_mul_card]
  exact Nat.mul_le_mul hidx hcard

end CFSG.CosetTable
