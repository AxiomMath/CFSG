module

public import Certificates.Data.Kernel.Misc.G22C
public import CFSG.Certificates.Kernel.Misc.G22WSound
public import CFSG.Quasithin.H13.L32NKGConjInputs

public section

namespace CFSG.KC.G22C

open CFSG.KD.G22C CFSG.KD.G22W CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.KC.G22W
  CFSG.Quasithin.H13.KGCert

theorem eq_cols {x y : ℕ} {a b : List ℕ} (hx : unpackM x = a ++ [64, 128])
    (hy : unpackM y = b ++ [64, 128]) (h : x = y) : a = b := by
  subst h
  exact eq_of_unpack hx hy |>.symm

theorem mem_invs {x : List ℕ} :
    x ∈ g22Invs ↔ x ∈ g22Elems ∧ mulC x x = oneC ∧ x ≠ oneC := by
  simp [g22Invs, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]

section Recs

variable {R C : ℕ → ℕ} {n hi : ℕ}

theorem inv_num {t : ℕ} (hg : goodK (numX R t) = true) (h1 : mulC (E R t) (E R t) = oneC)
    (h2 : E R t ≠ oneC) : isInvP (numX R t) = true := by
  obtain ⟨hu, hv⟩ := good_facts hg
  have h1' : mulC (colsK (numX R t)) (colsK (numX R t)) = oneC := h1
  have hsq : mulP (numX R t) (numX R t) = oneP := by
    apply unpackM_inj (mulP_lt _ _) oneP_lt
    rw [mulP_cols hu hv.1 hu hv, h1', oneP_cols]
  have hne : numX R t ≠ oneP := by
    intro e
    apply h2
    rw [E, e, colsK_oneP]
  simp only [isInvP, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true']
  exact ⟨hsq, by cases hb : Nat.beq (numX R t) oneP <;> simp_all [Nat.beq_eq]⟩

theorem conj_facts (hEq : g22Elems = (List.range n).reverse.map (E R))
    (hg : ∀ t < n, goodK (numX R t) = true)
    (hT0 : unpackM (repT R C n false) = t0C ++ [64, 128])
    (hT1 : unpackM (repT R C n true) = t1C ++ [64, 128])
    (hC : conjK R C n hi = true) (hm : n ≤ 64 * hi) :
    ∀ x ∈ g22Invs, ∃ y ∈ g22Elems, ∃ y' ∈ g22Elems, mulC y y' = oneC ∧
      (mulC y x = mulC t0C y ∨ mulC y x = mulC t1C y) := by
  intro x hx
  obtain ⟨hxm, hxx, hx1⟩ := mem_invs.1 hx
  rw [hEq] at hxm
  obtain ⟨t, ht, rfl⟩ := mem_map_range.1 hxm
  have hinv := inv_num (hg t ht) hxx hx1
  simp only [conjK, Bool.and_eq_true] at hC
  obtain ⟨-, hall⟩ := hC
  have h := CFSG.KC.G2Three.allBelow_g2 hall hm t ht
  try dsimp only at h
  rw [hinv, cond_true] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hy, hy'⟩, hyy⟩, hc⟩ := h
  set y := cfld C 0 t
  set y' := cfld C 1 t
  obtain ⟨hu, hv⟩ := good_facts (hg t ht)
  obtain ⟨huy, hvy⟩ := good_facts (hg y hy)
  obtain ⟨huy', hvy'⟩ := good_facts (hg y' hy')
  refine ⟨E R y, hEq ▸ mem_map_range.2 ⟨y, hy, rfl⟩, E R y', hEq ▸ mem_map_range.2 ⟨y', hy', rfl⟩,
    eq_cols (mulP_cols huy hvy.1 huy' hvy') oneP_cols hyy, ?_⟩
  cases hb : Nat.beq (cfld C 2 t) 1
  · rw [hb] at hc
    exact Or.inl (eq_cols (mulP_cols huy hvy.1 hu hv) (mulP_cols hT0 rfl huy hvy) hc)
  · rw [hb] at hc
    exact Or.inr (eq_cols (mulP_cols huy hvy.1 hu hv) (mulP_cols hT1 rfl huy hvy) hc)

theorem conj_check (hEq : g22Elems = (List.range n).reverse.map (E R))
    (hg : ∀ t < n, goodK (numX R t) = true)
    (hT0 : unpackM (repT R C n false) = t0C ++ [64, 128])
    (hT1 : unpackM (repT R C n true) = t1C ++ [64, 128])
    (hC : conjK R C n hi = true) (hm : n ≤ 64 * hi) : g22ConjCheck = true := by
  rw [g22ConjCheck, List.all_eq_true]
  intro x hx
  obtain ⟨y, hy, -, -, -, h⟩ := conj_facts hEq hg hT0 hT1 hC hm x hx
  rw [List.any_eq_true]
  exact ⟨y, hy, by simpa only [Bool.or_eq_true, beq_iff_eq] using h⟩

end Recs

end CFSG.KC.G22C

end
