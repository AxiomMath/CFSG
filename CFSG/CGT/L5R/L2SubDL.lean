module

public import CFSG.CGT.L5R.L2SubBL
public import CFSG.CGT.M24R.L2SubB

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

section Norm

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem normAll_iff {L : List Table} {K : Subgroup N8} (hL1 : ∀ Y ∈ L, ∃ y ∈ K, IsTab Y y)
    (hL2 : ∀ y ∈ K, ∃ Y ∈ L, IsTab Y y) {X : Table} {x : N8} (hX : IsTab X x) :
    normAll L X = true ↔ x ∈ Subgroup.normalizer (K : Set N8) := by
  rw [normAll, List.all_eq_true]
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨Y, hY, hYy⟩ := hL2 y hy
      have := h Y hY
      rw [Bool.and_eq_true] at this
      exact (conjIn_iff hcard hL1 hL2 hX hYy).1 this.1
    · intro hy
      obtain ⟨Y, hY, hYy⟩ := hL2 _ hy
      have := h Y hY
      rw [Bool.and_eq_true] at this
      have h2 := (conjInR_iff hcard hL1 hL2 hX hYy).1 this.2
      simpa [mul_assoc] using h2
  · intro hx P hP
    obtain ⟨y, hy, hPy⟩ := hL1 P hP
    rw [Bool.and_eq_true]
    refine ⟨(conjIn_iff hcard hL1 hL2 hX hPy).2 ((Subgroup.mem_normalizer_iff.1 hx y).1 hy),
      (conjInR_iff hcard hL1 hL2 hX hPy).2 ?_⟩
    have hx' := (Subgroup.normalizer (K : Set N8)).inv_mem hx
    simpa using (Subgroup.mem_normalizer_iff.1 hx' y).1 hy

theorem card_T8_inf_of {K : Subgroup N8} {p : ℕ → Bool}
    (hp : ∀ k < 16, p k = true ↔ n8 (tw k) ∈ K) :
    Nat.card ↥(T8 ⊓ K) = (List.range 16).countP p := by
  rw [List.countP_eq_length_filter]
  set L := (List.range 16).filter p with hL
  have hnd : L.Nodup := List.nodup_range.sublist List.filter_sublist
  have hmem : ∀ k ∈ L, k < 16 ∧ p k = true := fun k hk =>
    ⟨List.mem_range.1 (List.mem_filter.1 hk).1, (List.mem_filter.1 hk).2⟩
  let F : Fin L.length → ↥(T8 ⊓ K) := fun i =>
    ⟨n8 (tw L[i]), Subgroup.mem_inf.2 ⟨n8_tw_mem _,
      (hp _ (hmem _ (List.getElem_mem _)).1).1 (hmem _ (List.getElem_mem _)).2⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j hij
      have h1 := tw_inj hcard (hmem _ (List.getElem_mem i.isLt)).1
        (hmem _ (List.getElem_mem j.isLt)).1 (congrArg Subtype.val hij)
      exact Fin.ext ((hnd.getElem_inj_iff).1 h1)
    · rintro ⟨x, hxT, hxK⟩
      obtain ⟨k, hk, rfl⟩ := (mem_T8_iff hcard x).1 hxT
      have hkL : k ∈ L := List.mem_filter.2 ⟨List.mem_range.2 hk, (hp k hk).2 hxK⟩
      obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hkL
      exact ⟨⟨i, hi⟩, Subtype.ext (by simp [F, hik])⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fin]

theorem commCount_eq {X : Table} {x : N8} (hX : IsTab X x) :
    (mkCtx ()).commCount X = Nat.card ↥(T8 ⊓ Subgroup.centralizer ({x} : Set N8)) := by
  rw [card_T8_inf_of hcard (p := fun k => commT X (mkCtx ()).tt[k]!) ?_]
  · rfl
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff, hX.commT_iff hcard (isTab_tt hk)]
    exact ⟨fun h => h.symm, fun h => h.symm⟩


theorem normB8_iff {X : Table} {x : N8} (hX : IsTab X x) :
    normAll b8List X = true ↔ x ∈ DL :=
  normAll_iff hcard (b8_spec hcard).1 (b8_spec hcard).2 hX

theorem mem_dListL_iff {c : ℕ} :
    c ∈ dListL (mkCtx ()) ↔ c ∈ (mkCtx ()).codes ∧ el c ∈ DL := by
  rw [dListL, List.mem_filter]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, (normB8_iff hcard (isTab_tab (mem_codes.1 hc).1)).1 h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, (normB8_iff hcard (isTab_tab (mem_codes.1 hc).1)).2 h⟩

theorem el_of_mem_DL {x : N8} (hx : x ∈ DL) : ∃ c ∈ dListL (mkCtx ()), x = el c := by
  obtain ⟨c, hc, rfl⟩ := el_surj hcard x
  exact ⟨c, (mem_dListL_iff hcard).2 ⟨hc, hx⟩, rfl⟩

end Norm

end CFSG.CGT.L5R
