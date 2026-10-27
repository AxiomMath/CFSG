module

public import CFSG.LargeExtraspecial.O62Native

public section

namespace CFSG.LargeExtraspecial.O62

open Code Check

@[expose] def conjC (k : List ℕ) (e : ℕ) : ℕ := mul (mul (wordC k) e) (wordC k.reverse)

theorem certOK_spec {E k : List ℕ} (h : certOK E k = true) :
    (∀ e ∈ E, ∀ f ∈ E, mul (mul (conjC k e) f) (conjC k e) ∈ E) ∧
      ∃ e ∈ E, conjC k e ∉ E := by
  unfold certOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_map,
    List.contains_iff_mem, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Bool.not_eq_true', exists_exists_and_eq_and] at h
  obtain ⟨h1, e, he, h2⟩ := h
  refine ⟨fun e he f hf => h1 e he f hf, e, he, ?_⟩
  intro hmem
  have : E.contains (conjC k e) = true := List.contains_iff_mem.mpr hmem
  unfold conjC at this
  rw [this] at h2
  exact Bool.false_ne_true h2.symm

theorem wcTriple_spec {minus : Bool} {a b c : List ℕ} {x y z : ℕ} (hxy : comm x y = true)
    (hxz : comm x z = true) (hyz : comm y z = true) (hy : y ∉ spanC [x])
    (hz : z ∉ spanC [y, x]) (h : wcTriple minus a b c x y z = true) :
    (spanC [z, y, x]).Nodup ∧
      ((minus = false ∧ a.length % 2 = 0 ∧ b.length % 2 = 0 ∧ c.length % 2 = 0) ∨
        ∃ p ∈ certs minus, (∀ n ∈ p.2, qB minus n = true) ∧
          ((a.length % 2 = 0 ∧ b.length % 2 = 0 ∧ c.length % 2 = 0) → p.2.length % 2 = 0) ∧
          certOK (spanC [z, y, x]) p.2 = true) := by
  have hcond : (comm x y && comm x z && comm y z && !(spanC [x]).contains y &&
      !(spanC [y, x]).contains z) = true := by
    simp [hxy, hxz, hyz, hy, hz]
  unfold wcTriple at h
  rw [ite_eq_left hcond] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hnd, h⟩ := h
  refine ⟨hnd, ?_⟩
  rcases h with ⟨hm, ⟨ha, hb⟩, hc⟩ | ⟨p, hp, ⟨⟨⟨hkey, hlet⟩, hev⟩, hok⟩⟩
  · exact Or.inl ⟨by simpa using hm, ha, hb, hc⟩
  · refine Or.inr ⟨p, hp, hlet, fun ⟨ha, hb, hc⟩ => ?_, hok⟩
    simpa [ha, hb, hc] using hev

theorem wcTriple_eq_true
    {minus : Bool} {a b c : List ℕ} (ha : a ∈ sylowWords minus)
    (hb : b ∈ sylowWords minus) (hc : c ∈ sylowWords minus) (ia : isInv (wordC a) = true)
    (ib : isInv (wordC b) = true) (ic : isInv (wordC c) = true)
    (hab : comm (wordC a) (wordC b) = true) (hn : wordC b ∉ spanC [wordC a]) :
    wcTriple minus a b c (wordC a) (wordC b) (wordC c) = true := by
  have h := checkWC_eq_true minus
  have mem : ∀ {w : List ℕ}, w ∈ sylowWords minus → isInv (wordC w) = true →
      (w, wordC w) ∈ ((sylowWords minus).filter fun w => isInv (wordC w)).map
        fun w => (w, wordC w) :=
    fun hw hi => List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hw, hi⟩, rfl⟩
  unfold checkWC at h
  have h1 := List.all_eq_true.mp h _ (mem ha ia)
  have h2 := List.all_eq_true.mp h1 _ (mem hb ib)
  have hcond : (comm (a, wordC a).2 (b, wordC b).2 &&
      !(spanC [(a, wordC a).2]).contains (b, wordC b).2) = true := by
    simp [hab, hn]
  beta_reduce at h2
  simp only [hcond, ↓reduceIte] at h2
  have h3 := List.all_eq_true.mp h2 _ (mem hc ic)
  dsimp only at h3
  exact h3

end CFSG.LargeExtraspecial.O62
