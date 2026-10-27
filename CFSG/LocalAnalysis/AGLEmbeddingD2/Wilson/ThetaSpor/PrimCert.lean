module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCertDef
public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

open Equiv MulAction
open scoped Pointwise

theorem evalW_cons (L : Array (Array ℕ)) (l : ℕ) (w : List ℕ) (x : ℕ) :
    evalW L (l :: w) x = evalW L w ((L[l]!)[x]!) := rfl

theorem evalW_append (L : Array (Array ℕ)) (w₁ w₂ : List ℕ) (x : ℕ) :
    evalW L (w₁ ++ w₂) x = evalW L w₂ (evalW L w₁ x) := by
  simp [evalW, List.foldl_append]

@[expose] def LettersIn {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (L : Array (Array ℕ)) : Prop :=
  ∀ l < L.size, ∃ g ∈ G, ∀ x : Fin n, (L[l]!)[x.val]! = (g x).val

variable {n : ℕ}

theorem evalW_spec {G : Subgroup (Equiv.Perm (Fin n))} {L : Array (Array ℕ)}
    (hL : LettersIn G L) :
    ∀ w : List ℕ, (∀ l ∈ w, l < L.size) → ∃ g ∈ G, ∀ x : Fin n, evalW L w x.val = (g x).val
  | [], _ => ⟨1, G.one_mem, fun x => rfl⟩
  | l :: w, hw => by
    obtain ⟨gl, hgl, hl⟩ := hL l (hw l List.mem_cons_self)
    obtain ⟨g', hg', h'⟩ := evalW_spec hL w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    refine ⟨g' * gl, G.mul_mem hg' hgl, fun x => ?_⟩
    rw [evalW_cons, hl x]
    exact h' (gl x)

theorem wordsOK_iff {L : Array (Array ℕ)} {ws : List (List ℕ)} :
    wordsOK L ws = true ↔ ∀ w ∈ ws, ∀ l ∈ w, l < L.size := by
  simp [wordsOK, List.all_eq_true]

theorem getD_prop {α : Type*} (P : List α → Prop) (hP : P []) {ws : List (List α)}
    (h : ∀ w ∈ ws, P w) (i : ℕ) : P (ws.getD i []) := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hi)]
    exact hP

section Sound

variable [NeZero n] {G : Subgroup (Equiv.Perm (Fin n))} {L : Array (Array ℕ)}

theorem grow_sound (hL : LettersIn G L) (B : Set (Fin n)) (hB : MulAction.IsBlock G B)
    (q : Fin n) (h0 : (0 : Fin n) ∈ B) (hq : q ∈ B) :
    ∀ (ws : List (List ℕ)) (r r' : List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < L.size) →
      grow L q.val r ws = some r' → (∀ p ∈ r, ∃ y ∈ B, y.val = p) →
      ∀ p ∈ r', ∃ y ∈ B, y.val = p
  | [], r, r', _, h, hr => by
    simp only [grow, Option.some.injEq] at h
    subst h
    exact hr
  | w :: ws, r, r', hw, h, hr => by
    obtain ⟨g, hg, hgw⟩ := evalW_spec hL w (hw w List.mem_cons_self)
    have hx : evalW L w 0 = (g 0).val := by
      have := hgw 0
      simpa using this
    have hy : evalW L w q.val = (g q).val := hgw q
    have key : ∀ z : Fin n, z ∈ B → g z ∈ B → ∀ z' : Fin n, z' ∈ B → g z' ∈ B := by
      intro z hz hgz z' hz'
      have hdisj := hB.smul_eq_or_disjoint (⟨g, hg⟩ : G)
      have hgB : (⟨g, hg⟩ : G) • B = B := by
        rcases hdisj with h1 | h1
        · exact h1
        · exfalso
          have : g z ∈ ((⟨g, hg⟩ : G) • B) := ⟨z, hz, rfl⟩
          exact Set.disjoint_left.1 h1 this hgz
      rw [← hgB]
      exact ⟨z', hz', rfl⟩
    simp only [grow] at h
    split_ifs at h with h1 h2
    ·
      obtain ⟨hx1, -⟩ := h1
      obtain ⟨b, hbB, hbv⟩ := hr _ hx1
      have hgz : g 0 ∈ B := by
        have : b = g 0 := Fin.ext (by rw [hbv, hx])
        rw [← this]
        exact hbB
      have hgq : g q ∈ B := key 0 h0 hgz q hq
      refine grow_sound hL B hB q h0 hq ws _ r' (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
        h ?_
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨g q, hgq, hy.symm⟩
      · exact hr p hp
    · obtain ⟨hy1, -⟩ := h2
      obtain ⟨b, hbB, hbv⟩ := hr _ hy1
      have hgq : g q ∈ B := by
        have : b = g q := Fin.ext (by rw [hbv, hy])
        rw [← this]
        exact hbB
      have hgz : g 0 ∈ B := key q hq hgq 0 h0
      refine grow_sound hL B hB q h0 hq ws _ r' (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
        h ?_
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨g 0, hgz, hx.symm⟩
      · exact hr p hp

theorem isPreprimitive_of_primOK (hL : LettersIn G L) {tw : List (List ℕ)}
    {ew : List (List (List ℕ))} (h : primOK n L tw ew = true) :
    MulAction.IsPreprimitive G (Fin n) := by
  simp only [primOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hwtw, hwew⟩, htr⟩, hgrow⟩ := h
  have hwtw' := wordsOK_iff.1 hwtw
  have hwew' := wordsOK_iff.1 hwew
  have hzero : (0 : Fin n).val = 0 := rfl
  have hmove : ∀ q : Fin n, ∃ g ∈ G, g 0 = q := by
    intro q
    have hq := htr q.val q.2
    obtain ⟨g, hg, hgw⟩ := evalW_spec hL (tw.getD q.val [])
      (getD_prop (fun w => ∀ l ∈ w, l < L.size) (by simp) hwtw' _)
    refine ⟨g, hg, Fin.ext ?_⟩
    have := hgw 0
    rw [hzero] at this
    rw [← this, hq]
  have hpt : MulAction.IsPretransitive G (Fin n) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, hgx, hx⟩ := hmove x
    obtain ⟨gy, hgy, hy⟩ := hmove y
    refine ⟨⟨gy * gx⁻¹, G.mul_mem hgy (G.inv_mem hgx)⟩, ?_⟩
    show (gy * gx⁻¹) x = y
    rw [Equiv.Perm.mul_apply, ← hx]
    simp [hy]
  refine { toIsPretransitive := hpt, isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  rw [Set.not_subsingleton_iff] at hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := hsub
  obtain ⟨g, hgx⟩ := MulAction.exists_smul_eq G x (0 : Fin n)
  have hB' : MulAction.IsBlock G (g • B) := hB.translate g
  have h0 : (0 : Fin n) ∈ g • B := ⟨x, hx, hgx⟩
  set q : Fin n := g • y with hqdef
  have hq : q ∈ g • B := ⟨y, hy, rfl⟩
  have hq0 : q ≠ 0 := by
    intro h
    apply hxy
    exact MulAction.injective g (hgx.trans h.symm)
  have hgr := hgrow q.val q.2
  have hq0' : q.val ≠ 0 := fun h => hq0 (Fin.ext h)
  rcases hgr with h1 | h1
  · exact absurd h1 hq0'
  have hall : ∀ p : Fin n, p ∈ g • B := by
    cases hgo : grow L q.val [0] (ew.getD q.val []) with
    | none => rw [hgo] at h1; exact absurd h1 (by simp)
    | some r =>
      rw [hgo] at h1
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h1
      have hew2 : ∀ ws ∈ ew, ∀ w ∈ ws, ∀ l ∈ w, l < L.size :=
        fun ws hws w hw l hl => hwew' w (List.mem_flatten.2 ⟨ws, hws, hw⟩) l hl
      have hsound := grow_sound hL (g • B) hB' q h0 hq (ew.getD q.val [])
        [0] r (getD_prop (fun ws => ∀ w ∈ ws, ∀ l ∈ w, l < L.size) (by simp) hew2 q.val)
        hgo (by
          intro p hp
          simp only [List.mem_singleton] at hp
          exact ⟨0, h0, by rw [hp]; rfl⟩)
      · intro p
        obtain ⟨y', hy', hyv⟩ := hsound p.val (h1 p.val p.2)
        have : y' = p := Fin.ext hyv
        rw [← this]
        exact hy'
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨w, hw, hwz⟩ := hall (g • z)
  have : w = z := MulAction.injective g hwz
  rw [← this]
  exact hw

end Sound

theorem evalW_append_spec {L : Array (Array ℕ)} {w₁ w₂ : List ℕ} {g₁ g₂ : Equiv.Perm (Fin n)}
    (h₁ : ∀ x : Fin n, evalW L w₁ x.val = (g₁ x).val)
    (h₂ : ∀ x : Fin n, evalW L w₂ x.val = (g₂ x).val) :
    ∀ x : Fin n, evalW L (w₁ ++ w₂) x.val = ((g₂ * g₁) x).val := by
  intro x
  rw [evalW_append, h₁ x]
  exact h₂ (g₁ x)

theorem exists_order_four {G : Subgroup (Equiv.Perm (Fin n))} {L : Array (Array ℕ)}
    (hL : LettersIn G L) {w : List ℕ} (h : fourOK n L w = true) :
    ∃ g ∈ G, g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by
  simp only [fourOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq, wordsOK_iff] at h
  obtain ⟨⟨hw, h4⟩, x0, hx0, h2⟩ := h
  obtain ⟨g, hg, hgw⟩ := evalW_spec hL w (hw w (by simp))
  have hgg : ∀ x : Fin n, evalW L (w ++ w) x.val = ((g * g) x).val := evalW_append_spec hgw hgw
  have hg4 : ∀ x : Fin n, evalW L (w ++ w ++ (w ++ w)) x.val = ((g * g * (g * g)) x).val :=
    evalW_append_spec hgg hgg
  refine ⟨g, hg, ?_, ?_⟩
  · refine Equiv.ext fun x => Fin.ext ?_
    have := h4 x.val x.2
    rw [hg4 x] at this
    have e : g ^ 4 = g * g * (g * g) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [e]
    simpa using this
  · intro h1
    apply h2
    have := hgg ⟨x0, hx0⟩
    rw [← sq, h1] at this
    simpa using this

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

end
