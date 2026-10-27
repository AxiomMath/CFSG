module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem embed_eq_of_spec {n : ℕ} (ι : Fin 4 ↪ Fin n) (x : Wr 4) (w : Wr n)
    (hv : ∀ i, w.vec (ι i) = x.vec i) (hv0 : ∀ y, y ∉ Set.range ι → w.vec y = 0)
    (hp : ∀ i, w.perm (ι i) = ι (x.perm i)) (hp0 : ∀ y, y ∉ Set.range ι → w.perm y = y) :
    embed ι x = w := by
  refine Wr.ext (funext fun y => ?_) (Equiv.ext fun y => ?_)
  · rw [embed_vec]
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hy
      rw [embedVec_apply, hv]
    · rw [embedVec_of_not_mem _ _ hy, hv0 y hy]
  · rw [embed_perm]
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hy
      rw [embedPerm_apply, hp]
    · rw [embedPerm_of_not_mem _ _ hy, hp0 y hy]

theorem emb_eq {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) (f : Fin 4 → Fin n)
    (hf : ∀ i, f i ∈ α) (hm : StrictMono f) (i : Fin 4) : emb α h i = f i :=
  (congrFun (Finset.orderEmbOfFin_unique (s := α) h hf hm) i).symm

theorem mem_memAt_of_spec {α : Finset (Fin 8)} {h : α.card = 4} (b : Bool) (f : Fin 4 → Fin 8)
    (hf : ∀ i, emb α h i = f i) (k : Wr 4) (hk : k ∈ (bif b then kList else kStarList))
    (w : Wr 8) (hv : ∀ i, w.vec (f i) = k.vec i) (hv0 : ∀ y, (∀ i, y ≠ f i) → w.vec y = 0)
    (hp : ∀ i, w.perm (f i) = f (k.perm i)) (hp0 : ∀ y, (∀ i, y ≠ f i) → w.perm y = y) :
    w ∈ memAt α h b := by
  have hn : ∀ y, y ∉ Set.range (emb α h) → ∀ i, y ≠ f i := by
    intro y hy i hyi
    exact hy ⟨i, by rw [hf, hyi]⟩
  have he : embed (emb α h) k = w := by
    refine embed_eq_of_spec _ _ _ (fun i => ?_) (fun y hy => hv0 y (hn y hy))
      (fun i => ?_) (fun y hy => hp0 y (hn y hy))
    · rw [hf]; exact hv i
    · rw [hf, hp i]
      exact (hf _).symm
  cases b
  · exact ⟨k, mem_kQStar.mpr hk, he⟩
  · exact ⟨k, mem_kQ.mpr hk, he⟩

@[expose] def α0 : Finset (Fin 8) := {0, 2, 4, 6}

@[expose] def α1 : Finset (Fin 8) := {1, 3, 5, 7}

theorem α0_card : α0.card = 4 := by decide
theorem α1_card : α1.card = 4 := by decide

@[expose] def f0 : Fin 4 → Fin 8 := ![0, 2, 4, 6]
@[expose] def f1 : Fin 4 → Fin 8 := ![1, 3, 5, 7]

theorem emb_α0 (i : Fin 4) : emb α0 α0_card i = f0 i :=
  emb_eq α0 α0_card f0 (by intro x; fin_cases x <;> decide)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f0]) i

theorem emb_α1 (i : Fin 4) : emb α1 α1_card i = f1 i :=
  emb_eq α1 α1_card f1 (by intro x; fin_cases x <;> decide)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f1]) i

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
