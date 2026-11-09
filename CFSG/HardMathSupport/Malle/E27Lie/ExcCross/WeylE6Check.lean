module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Data

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

@[expose] def e6SylList (w : List Bool) : List (List ℤ) :=
  w.foldr (fun b acc => lmul Tag.E6.rank (if b then e6SylMY else e6SylMX) acc) (lid Tag.E6.rank)

@[expose] def e6SylS : List (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) :=
  e6SylWords.map fun w => toMat Tag.E6.rank (e6SylList w)

theorem card_fixed3_ge {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℤ} (b : Fin 4 → Fin n → ZMod 3)
    (p : Fin 4 → Fin n)
    (hsol : ∀ i j, ∑ k, b i k * (((C * (M - 1)) k j : ℤ) : ZMod 3) = 0)
    (hpiv : ∀ i i', b i (p i') = if i = i' then 1 else 0) : 81 ≤ (fixed3 C M).card := by
  let f : (Fin 4 → ZMod 3) → (Fin n → ZMod 3) := fun c k => ∑ i, c i * b i k
  have hinj : Function.Injective f := by
    intro c c' h
    funext i'
    have h1 := congrFun h (p i')
    simpa [f, hpiv] using h1
  have hsub : Finset.univ.image f ⊆ fixed3 C M := by
    intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
    simp only [fixed3, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    calc ∑ k, f c k * (((C * (M - 1)) k j : ℤ) : ZMod 3)
        = ∑ k, ∑ i, c i * (b i k * (((C * (M - 1)) k j : ℤ) : ZMod 3)) := by
          simp only [f, Finset.sum_mul, mul_assoc]
      _ = ∑ i, c i * ∑ k, b i k * (((C * (M - 1)) k j : ℤ) : ZMod 3) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = 0 := by simp [hsol]
  have hcard : (Finset.univ.image f).card = 81 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [Fintype.card_fun, ZMod.card]
  calc 81 = (Finset.univ.image f).card := hcard.symm
    _ ≤ (fixed3 C M).card := Finset.card_le_card hsub

set_option maxHeartbeats 4000000 in
@[expose] def e6Tab :
    List (List Bool × (Fin 4 → Fin Tag.E6.rank → ZMod 3) × (Fin 4 → Fin Tag.E6.rank)) := [
    ([], ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0]],
      ![0, 1, 2, 3]),
    ([false], ![![1, 1, 0, 0, 0, 0], ![1, 0, 2, 1, 0, 0], ![1, 0, 2, 0, 1, 0], ![0, 0, 0, 0, 0, 1]],
      ![1, 3, 4, 5]),
    ([true], ![![2, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, false], ![![1, 1, 0, 0, 0, 0], ![1, 0, 2, 1, 0, 0], ![1, 0, 2, 0, 1, 0], ![0, 0, 0, 0, 0, 1]],
      ![1, 3, 4, 5]),
    ([true, false], 0, fun _ => 0),
    ([false, true], 0, fun _ => 0),
    ([true, true], ![![2, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, false], 0, fun _ => 0),
    ([false, true, false], 0, fun _ => 0),
    ([true, true, false], 0, fun _ => 0),
    ([false, false, true], 0, fun _ => 0),
    ([true, false, true], 0, fun _ => 0),
    ([false, true, true], 0, fun _ => 0),
    ([false, true, false, false], ![![1, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0], ![0, 0, 0, 2, 1, 0], ![0, 1, 0, 2, 0, 1]],
      ![0, 2, 4, 5]),
    ([true, true, false, false], 0, fun _ => 0),
    ([false, false, true, false], ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]],
      ![0, 3, 4, 5]),
    ([true, false, true, false], 0, fun _ => 0),
    ([false, true, true, false], 0, fun _ => 0),
    ([true, false, false, true], 0, fun _ => 0),
    ([false, true, false, true], 0, fun _ => 0),
    ([true, true, false, true], ![![2, 1, 0, 0, 0, 0], ![0, 0, 2, 1, 0, 0], ![0, 0, 2, 0, 1, 0], ![2, 0, 0, 0, 0, 1]],
      ![1, 3, 4, 5]),
    ([false, false, true, true], 0, fun _ => 0),
    ([true, false, true, true], ![![0, 1, 0, 0, 0, 0], ![2, 0, 2, 1, 0, 0], ![2, 0, 2, 0, 1, 0], ![1, 0, 0, 0, 0, 1]],
      ![1, 3, 4, 5]),
    ([false, false, true, false, false], 0, fun _ => 0),
    ([true, false, true, false, false], ![![2, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, true, false, false], ![![1, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0], ![0, 0, 0, 2, 1, 0], ![0, 1, 0, 2, 0, 1]],
      ![0, 2, 4, 5]),
    ([true, false, false, true, false], ![![0, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, false, true, false], ![![1, 0, 0, 0, 0, 0], ![0, 2, 1, 1, 0, 0], ![0, 2, 1, 0, 1, 0], ![0, 2, 2, 0, 0, 1]],
      ![0, 3, 4, 5]),
    ([true, true, false, true, false], ![![0, 1, 1, 0, 0, 0], ![2, 2, 0, 1, 0, 0], ![2, 2, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, false, true, true, false], ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]],
      ![0, 3, 4, 5]),
    ([true, false, true, true, false], ![![2, 0, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, false, true], ![![2, 1, 0, 0, 0, 0], ![0, 0, 2, 1, 0, 0], ![0, 0, 2, 0, 1, 0], ![2, 0, 0, 0, 0, 1]],
      ![1, 3, 4, 5]),
    ([true, false, true, false, true], ![![2, 1, 1, 0, 0, 0], ![1, 2, 0, 1, 0, 0], ![1, 2, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, true, false, true], ![![0, 0, 1, 0, 0, 0], ![2, 1, 0, 1, 0, 0], ![2, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, false, true, true], ![![0, 1, 0, 0, 0, 0], ![2, 0, 2, 1, 0, 0], ![2, 0, 2, 0, 1, 0], ![1, 0, 0, 0, 0, 1]],
      ![1, 3, 4, 5]),
    ([false, true, false, true, true], ![![1, 1, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 2, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, true], 0, fun _ => 0),
    ([true, false, false, true, false, false], 0, fun _ => 0),
    ([false, true, false, true, false, false], 0, fun _ => 0),
    ([true, true, false, true, false, false], ![![2, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, false, true, true, false, false], 0, fun _ => 0),
    ([true, false, true, true, false, false], ![![2, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, false, true, false], ![![1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, true, false, true, false], ![![0, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, true, false, true, false], ![![1, 0, 0, 0, 0, 0], ![0, 1, 2, 1, 0, 0], ![0, 1, 2, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![0, 3, 4, 5]),
    ([true, false, false, true, true, false], ![![1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, false, true, true, false], ![![1, 0, 0, 0, 0, 0], ![0, 1, 2, 1, 0, 0], ![0, 1, 2, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![0, 3, 4, 5]),
    ([true, true, false, true, true, false], 0, fun _ => 0),
    ([true, true, false, true, false, true], 0, fun _ => 0),
    ([true, false, true, true, false, true], 0, fun _ => 0),
    ([true, true, false, false, true, true], 0, fun _ => 0),
    ([true, false, true, false, true, true], 0, fun _ => 0),
    ([false, true, true, false, true, true], 0, fun _ => 0),
    ([true, true, false, false, true, false, false], ![![0, 0, 1, 0, 0, 0], ![2, 1, 0, 1, 0, 0], ![2, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, true, false, true, false, false], ![![1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, true, false, true, false, false], ![![2, 0, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, false, true, true, false, false], ![![1, 1, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 2, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, false, true, true, false, false], ![![0, 1, 1, 0, 0, 0], ![2, 2, 0, 1, 0, 0], ![2, 2, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, true, false, false], ![![2, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, false, true, false], ![![1, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, true, true, false, true, false], ![![0, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, false, true, true, false], ![![0, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, true, false, true, true, false], ![![1, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([false, true, true, false, true, true, false], ![![1, 0, 0, 0, 0, 0], ![0, 2, 1, 1, 0, 0], ![0, 2, 1, 0, 1, 0], ![0, 2, 2, 0, 0, 1]],
      ![0, 3, 4, 5]),
    ([true, true, false, true, true, false, true], 0, fun _ => 0),
    ([true, true, false, true, false, true, true], 0, fun _ => 0),
    ([true, false, true, true, false, true, true], 0, fun _ => 0),
    ([true, true, false, true, false, true, false, false], 0, fun _ => 0),
    ([true, false, true, true, false, true, false, false], 0, fun _ => 0),
    ([true, true, false, false, true, true, false, false], 0, fun _ => 0),
    ([true, false, true, false, true, true, false, false], 0, fun _ => 0),
    ([false, true, true, false, true, true, false, false], 0, fun _ => 0),
    ([true, true, false, true, true, false, true, false], ![![1, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, false, true, true, false], ![![0, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, false, true, true, false, true, true, false], ![![1, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, true, false, true, true], ![![1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, true, false, true, false, false], 0, fun _ => 0),
    ([true, true, false, true, false, true, true, false, false], 0, fun _ => 0),
    ([true, false, true, true, false, true, true, false, false], 0, fun _ => 0),
    ([true, true, false, true, true, false, true, true, false], ![![0, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5]),
    ([true, true, false, true, true, false, true, true, false, false], ![![2, 1, 1, 0, 0, 0], ![1, 2, 0, 1, 0, 0], ![1, 2, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1]],
      ![2, 3, 4, 5])]

theorem e6Tab_fst : e6Tab.map Prod.fst = e6SylWords := by decide +kernel

set_option maxRecDepth 100000 in
theorem e6Tab_ok : ∀ q ∈ e6Tab,
    toMat Tag.E6.rank (e6SylList q.1) * toMat Tag.E6.rank (e6SylList q.1) *
        toMat Tag.E6.rank (e6SylList q.1) = 1 →
      (∀ (i : Fin 4) (j : Fin Tag.E6.rank), ∑ k, q.2.1 i k *
          (((Tag.E6.cartan * (toMat Tag.E6.rank (e6SylList q.1) - 1)) k j : ℤ) : ZMod 3) = 0) ∧
        ∀ i i' : Fin 4, q.2.1 i (q.2.2 i') = if i = i' then 1 else 0 := by
  decide +kernel

theorem e6S_fixed3 :
    ∀ M ∈ e6SylS, M * M * M = 1 → 81 ≤ (fixed3 Tag.E6.cartan M).card := by
  intro M hM h3
  have hM' : M ∈ (e6Tab.map Prod.fst).map fun w => toMat Tag.E6.rank (e6SylList w) := by
    rw [e6Tab_fst]
    exact hM
  rw [List.map_map, List.mem_map] at hM'
  obtain ⟨q, hq, rfl⟩ := hM'
  obtain ⟨hs, hp⟩ := e6Tab_ok q hq h3
  exact card_fixed3_ge q.2.1 q.2.2 hs hp


end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
