module

public import Certificates.Data.E8KilledPlanes
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6.Aux
  (nfE8 nfN lc1 lc2 lc3 lc4 lpi wc1 wc2 wc3 wc4 wpi)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (wordW wordW_replicate)

theorem e8PlanePermOf_spec {rt : Array ℕ}
    (h : ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
      e8Certificate.root (rt.getD (240 * b + x) 0) =
        rootReflection (e8Certificate.root b) • e8Certificate.root x)
    {w : List ℕ} (hw : ∀ b ∈ w, b < 240) {x : ℕ} (hx : x < 240) :
    e8PlanePermOf rt w x < 240 ∧
      e8Certificate.root (e8PlanePermOf rt w x) =
        (w.map fun b => rootReflection (e8Certificate.root b)).prod • e8Certificate.root x := by
  induction w with
  | nil => exact ⟨hx, by simp [e8PlanePermOf]⟩
  | cons b w ih =>
    obtain ⟨hlt, heq⟩ := ih fun b' hb' => hw b' (List.mem_cons_of_mem _ hb')
    obtain ⟨hlt', heq'⟩ := h b _ (hw b (by simp)) hlt
    have e : e8PlanePermOf rt (b :: w) x = rt.getD (240 * b + e8PlanePermOf rt w x) 0 := rfl
    rw [e]
    refine ⟨hlt', ?_⟩
    rw [heq', heq, List.map_cons, List.prod_cons, mul_smul]

theorem e8PlaneWord_lt (c : ℕ) : ∀ b ∈ e8PlaneWord c, b < 8 := by
  have hrep : ∀ {L : List ℕ}, (∀ b ∈ L, b < 8) →
      ∀ k, ∀ b ∈ (List.replicate k L).flatten, b < 8 := by
    intro L hL k b hb
    obtain ⟨l, hl, hbl⟩ := List.mem_flatten.1 hb
    rw [(List.mem_replicate.1 hl).2] at hbl
    exact hL b hbl
  have h1 : ∀ b ∈ e8PlaneL1, b < 8 := by decide
  have h2 : ∀ b ∈ e8PlaneL2, b < 8 := by decide
  have h3 : ∀ b ∈ e8PlaneL3, b < 8 := by decide
  have h4 : ∀ b ∈ e8PlaneL4, b < 8 := by decide
  have hP : ∀ b ∈ e8PlaneLP, b < 8 := by decide
  intro b hb
  simp only [e8PlaneWord, List.mem_append] at hb
  rcases hb with (((hb | hb) | hb) | hb) | hb
  · exact hrep h4 _ b hb
  · exact hrep h1 _ b hb
  · exact hrep h2 _ b hb
  · exact hrep h3 _ b hb
  · exact hrep hP _ b hb

theorem e8PlaneWord_prod (e : Fin 5 → Fin 3) :
    ((e8PlaneWord ((e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ))).map
      fun b => rootReflection (e8Certificate.root b)).prod = nfE8 e := by
  have b0 := (e 0).isLt
  have b1 := (e 1).isLt
  have b2 := (e 2).isLt
  have b3 := (e 3).isLt
  have b4 := (e 4).isLt
  have hsimple : ∀ j : Fin Tag.E8.rank,
      rootReflection (e8Certificate.root j) = simple Tag.E8 j := fun j => by
    rw [e8Certificate_root_single j, rootReflection_eq_conj (w := 1) (one_smul _ _), one_mul,
      inv_one, mul_one]
  have hmap : ∀ l : List (Fin Tag.E8.rank),
      (l.map Fin.val).map (fun b => rootReflection (e8Certificate.root b)) =
        l.map (simple Tag.E8) := fun l => by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => hsimple j
  have hletter : ∀ (l : List (Fin Tag.E8.rank)) (k : ℕ),
      ((List.replicate k (l.map Fin.val)).flatten.map
        fun b => rootReflection (e8Certificate.root b)).prod = wordW Tag.E8 l ^ k := fun l k => by
    rw [← wordW_replicate]
    simp only [wordW, List.map_flatten, List.map_replicate, hmap]
  have e1 : e8PlaneL1 = lc1.map Fin.val := by decide
  have e2 : e8PlaneL2 = lc2.map Fin.val := by decide
  have e3 : e8PlaneL3 = lc3.map Fin.val := by decide
  have e4 : e8PlaneL4 = lc4.map Fin.val := by decide
  have eP : e8PlaneLP = lpi.map Fin.val := by decide
  rw [e8PlaneWord,
    show ((e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ)) % 3 =
      (e 0 : ℕ) by omega,
    show ((e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ)) / 3 % 3 =
      (e 1 : ℕ) by omega,
    show ((e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ)) / 9 % 3 =
      (e 2 : ℕ) by omega,
    show ((e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ)) / 27 % 3 =
      (e 3 : ℕ) by omega,
    show ((e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ)) / 81 % 3 =
      (e 4 : ℕ) by omega,
    e1, e2, e3, e4, eP]
  simp only [List.map_append, List.prod_append, hletter]
  rfl

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

end
