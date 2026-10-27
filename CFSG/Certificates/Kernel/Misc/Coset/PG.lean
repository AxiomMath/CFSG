module

public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable CFSG.Certificates

variable {m : ℕ}

@[expose] noncomputable def pgGen (ws : List (List (Fin m × Bool))) (g : ℕ) : PG m ws :=
  if h : g < m then PresentedGroup.of ⟨g, h⟩ else 1

@[expose] def encW (w : List (Fin m × Bool)) : List (ℕ × Bool) := w.map fun l => (l.1.val, l.2)

theorem sword_pgGen (ws : List (List (Fin m × Bool))) (w : List (Fin m × Bool)) :
    KB.sword (pgGen ws) (encW w) = PresentedGroup.mk _ (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [encW, List.map_cons, KB.sword, List.map_cons, List.prod_cons, ← KB.sword, ← encW, ih,
      show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj : pgGen ws j.val = PresentedGroup.of j := by simp [pgGen, j.isLt]
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      simp only [Bool.false_eq_true, ↓reduceIte, hj]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl]
      simp only [↓reduceIte, hj]
      rfl

theorem sword_rels (ws : List (List (Fin m × Bool))) {rels : List (List (ℕ × Bool))}
    (h : ws.map encW = rels) : ∀ r ∈ rels, KB.sword (pgGen ws) r = 1 := by
  rw [← h]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [sword_pgGen]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem closure_pgGen (ws : List (List (Fin m × Bool))) :
    Subgroup.closure (pgGen ws '' {g | g < m}) = ⊤ := by
  rw [← PresentedGroup.closure_range_of]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, by simp [pgGen, hg]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, by simp [pgGen, j.isLt]⟩

theorem alphaSub_top (ws : List (List (Fin m × Bool))) {amap : ℕ} (hm : m < 256)
    (h : KB.topOk amap m = true) : KB.alphaSub (pgGen ws) amap = ⊤ := by
  have hset : {g | KB.inAlpha amap g} = {g | g < m} := Set.ext fun g => KB.topOk_sound hm h g
  rw [KB.alphaSub, hset, closure_pgGen ws]

theorem index_le_of_tableOk (ws : List (List (Fin m × Bool))) {rels : List (List (ℕ × Bool))}
    (hrels : ws.map encW = rels) {inv L eps nLab nT N RW RM nR nS nW nF : ℕ}
    {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ} {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) :
    (KB.wordSub (pgGen ws) words).FiniteIndex ∧ (KB.wordSub (pgGen ws) words).index ≤ N := by
  obtain ⟨-, h0, hN⟩ := KB.tableOk_sound (pgGen ws) (sword_rels ws hrels) h
  rw [alphaSub_top ws hm htop, Subgroup.relIndex_top_right] at h0 hN
  exact ⟨⟨h0⟩, hN⟩

theorem wordSub_letters (ws : List (List (Fin m × Bool))) (S : List (Fin m)) :
    KB.wordSub (pgGen ws) (S.map fun x => [(x.val, true)]) =
      genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S := by
  rw [KB.wordSub, genSub]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [KB.sword, pgGen, x.isLt]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [KB.sword, pgGen, x.isLt]⟩

theorem wordSub_single (ws : List (List (Fin m × Bool))) (w : List (Fin m × Bool)) :
    KB.wordSub (pgGen ws) [encW w] =
      Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk w)) := by
  rw [KB.wordSub, Subgroup.zpowers_eq_closure]
  congr 1
  ext g
  simp [sword_pgGen]

theorem card_le_of_index_bot (ws : List (List (Fin m × Bool))) {N : ℕ}
    (h : (KB.wordSub (pgGen ws) []).FiniteIndex ∧ (KB.wordSub (pgGen ws) []).index ≤ N) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N := by
  rw [KB.wordSub_nil, Subgroup.index_bot] at h
  obtain ⟨⟨h0⟩, hN⟩ := h
  rw [Subgroup.index_bot] at h0
  exact ⟨Nat.finite_of_card_ne_zero h0, hN⟩

variable {rels : List (List (ℕ × Bool))} {inv L eps nLab nT N RW RM nR nS nW nF : ℕ}
  {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ} {words : List (List (ℕ × Bool))} {walk cov : List ℕ}

theorem card_le_of_tableOk (ws : List (List (Fin m × Bool))) (hrels : ws.map encW = rels)
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) (hw : words = []) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N := by
  have := index_le_of_tableOk ws hrels h hm htop
  rw [hw] at this
  exact card_le_of_index_bot ws this

theorem genSub_index_le_of_tableOk (ws : List (List (Fin m × Bool))) (hrels : ws.map encW = rels)
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) (T : List (Fin m))
    (hw : words = T.map fun x => [(x.val, true)]) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≤ N := by
  have := index_le_of_tableOk ws hrels h hm htop
  rwa [hw, wordSub_letters] at this

theorem zpowers_index_le_of_tableOk (ws : List (List (Fin m × Bool))) (hrels : ws.map encW = rels)
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) (u : List (Fin m × Bool))
    (hw : words = [encW u]) :
    (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).FiniteIndex ∧
      (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).index ≤ N := by
  have := index_le_of_tableOk ws hrels h hm htop
  rwa [hw, wordSub_single] at this

theorem card_le_of_zpowers_index (ws : List (List (Fin m × Bool))) (u : List (Fin m × Bool))
    {k n : ℕ} (hk : 0 < k) (hpow : (List.replicate k u).flatten ∈ ws)
    (h : (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).FiniteIndex ∧
      (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).index ≤ n) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * k := by
  set g := PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u)
  obtain ⟨hfi, hidx⟩ := h
  have hrep : ∀ j : ℕ, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk (List.replicate j u).flatten) = g ^ j := by
    intro j
    induction j with
    | zero =>
      rw [List.replicate_zero, List.flatten_nil, pow_zero]
      exact map_one _
    | succ j ih =>
      rw [pow_succ', List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, map_mul, ih]
  have hg : g ^ k = 1 := by
    rw [← hrep k]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hpow)
  have hord : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hg
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hord hk
  have hfinz : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hcard : Nat.card (Subgroup.zpowers g) ≤ k := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd hk hord
  have hG : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ Subgroup.zpowers g) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (Subgroup.zpowers g)
  refine ⟨hG, ?_⟩
  rw [← (Subgroup.zpowers g).index_mul_card]
  exact Nat.mul_le_mul hidx hcard

end CFSG.KC.MiscCoset

end
