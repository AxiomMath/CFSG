module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2C
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSPrime

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

@[expose] def cInvC (smul : ℕ → ℕ → ℕ) (I : List ℕ) (x : ℕ) : ℕ :=
  (I.filter fun c => smul c x == smul x c).length

@[expose] def kDataOK (smul : ℕ → ℕ → ℕ) (N : ℕ) (I : List ℕ) (tab : Array ℕ) (gens : List ℕ)
    (L : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  let ws := L.map Prod.fst
  L.head? == some (0, 0, 0, 0) && ws.Nodup &&
    (gens.all fun g => decide (g < N)) &&
    ((List.range L.length).all fun i =>
      let e := L.getD i (0, 0, 0, 0)
      decide (e.1 < N) &&
        (i == 0 || (decide (e.2.2.1 < i) && decide (e.2.2.2 < gens.length) &&
          e.1 == smul (ws.getD e.2.2.1 0) (gens.getD e.2.2.2 0))) &&
        (gens.all fun g => ws.contains (smul e.1 g)) &&
        (e.1 == 0 || (decide (e.2.1 < N) && tab[e.2.1]! == e.1 &&
          cInvC smul I e.1 != cInvC smul I e.2.1)))

section Spec

variable {H : Type*} [Group H] [Finite H] {N : ℕ} {smul : ℕ → ℕ → ℕ} (Φ : CodeIso H N smul)
  (h0 : smul 0 0 = 0) {tab : Array ℕ} {gens : List ℕ} {L : List (ℕ × ℕ × ℕ × ℕ)}

@[expose] noncomputable def kSub (gens : List ℕ) : Subgroup H :=
  closure {x | ∃ g ∈ gens, x = Φ.g g}

include h0 in
theorem kData_spec (hk : kDataOK smul N (kInv smul N) tab gens L = true) :
    Nat.card (kSub Φ gens) = L.length ∧
      ∀ x ∈ kSub Φ gens, x ≠ 1 → ∃ c, c < N ∧ tab[c]! = Φ.f x ∧
        cInvC smul (kInv smul N) (Φ.f x) ≠ cInvC smul (kInv smul N) c := by
  classical
  unfold kDataOK at hk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at hk
  obtain ⟨⟨⟨hhead, hnd⟩, hgl⟩, hent⟩ := hk
  set ws := L.map Prod.fst
  have hlen : ws.length = L.length := List.length_map _
  have hws : ∀ i < L.length, ws.getD i 0 = (L.getD i (0, 0, 0, 0)).1 := fun i hi => by
    simp only [ws, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some]
  set Y : Set H := {x | Φ.f x ∈ ws}
  have hY1 : (1 : H) ∈ Y := by
    have h := Φ.f_one h0
    show Φ.f 1 ∈ ws
    rw [h]
    cases L with
    | nil => simp at hhead
    | cons e L => simp only [List.head?_cons, Option.some.injEq] at hhead; simp [ws, hhead]
  have hYgen : ∀ y ∈ Y, ∀ g ∈ gens, y * Φ.g g ∈ Y := by
    intro y hy g hg
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hy
    rw [hlen] at hi
    have := (hent i hi).1.2 g hg
    show Φ.f (y * Φ.g g) ∈ ws
    rw [Φ.map_mul, Φ.f_g (hgl g hg)]
    have e1 : (L.getD i (0, 0, 0, 0)).1 = Φ.f y := by
      rw [← hws i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [hlen]),
        Option.getD_some, hiw]
    rwa [e1] at this
  have hYK : ∀ z ∈ kSub Φ gens, ∀ y ∈ Y, y * z ∈ Y := by
    intro z hz
    induction hz using closure_induction with
    | mem z hz =>
      obtain ⟨g, hg, rfl⟩ := hz
      exact fun y hy => hYgen y hy g hg
    | one => intro y hy; rwa [mul_one]
    | mul a b _ _ ha hb => intro y hy; rw [← mul_assoc]; exact hb _ (ha y hy)
    | inv a _ ha =>
      intro y hy
      have hfin : Y.Finite := Set.toFinite _
      have hinj : Set.InjOn (fun x => x * a) Y := fun p _ q _ h => mul_right_cancel h
      have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo hfin (fun x hx => ha x hx)).1 hinj
      obtain ⟨x, hx, hxa⟩ := hbij.surjOn hy
      have : y * a⁻¹ = x := by rw [← hxa]; group
      rw [this]; exact hx
  have hLK : ∀ i < L.length, Φ.g (ws.getD i 0) ∈ kSub Φ gens := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases (hent i hi).1.1.2 with h | ⟨⟨hp, hkl⟩, hwp⟩
      · subst h
        rw [hws 0 hi]
        cases L with
        | nil => simp at hi
        | cons e L =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          simp only [List.getD_cons_zero, hhead]
          have : Φ.g 0 = 1 := by rw [← Φ.f_one h0, Φ.g_f]
          rw [this]; exact one_mem _
      · rw [hws i hi, hwp]
        have hpl : (L.getD i (0, 0, 0, 0)).2.2.1 < L.length := lt_trans hp hi
        have hpw := ih _ hp hpl
        have hgk : gens.getD (L.getD i (0, 0, 0, 0)).2.2.2 0 ∈ gens := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl, Option.getD_some]
          exact List.getElem_mem hkl
        have hwlt : ws.getD (L.getD i (0, 0, 0, 0)).2.2.1 0 < N := by
          rw [hws _ hpl]; exact (hent _ hpl).1.1.1
        have hglt := hgl _ hgk
        rw [show smul (ws.getD (L.getD i (0, 0, 0, 0)).2.2.1 0)
            (gens.getD (L.getD i (0, 0, 0, 0)).2.2.2 0) =
            Φ.f (Φ.g (ws.getD (L.getD i (0, 0, 0, 0)).2.2.1 0) *
              Φ.g (gens.getD (L.getD i (0, 0, 0, 0)).2.2.2 0)) by
          rw [Φ.map_mul, Φ.f_g hwlt, Φ.f_g hglt], Φ.g_f]
        exact mul_mem hpw (subset_closure ⟨_, hgk, rfl⟩)
  have hKY : ∀ x, x ∈ kSub Φ gens ↔ Φ.f x ∈ ws := by
    intro x
    constructor
    · intro hx
      have := hYK x hx 1 hY1
      rwa [one_mul] at this
    · intro hx
      obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hx
      rw [hlen] at hi
      have := hLK i hi
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [hlen]),
        Option.getD_some, hiw, Φ.g_f] at this
  refine ⟨?_, fun x hx hx1 => ?_⟩
  ·
    rw [← hlen, ← List.toFinset_card_of_nodup hnd]
    rw [Nat.card_congr (Equiv.ofBijective (fun x : kSub Φ gens =>
      (⟨Φ.f x, List.mem_toFinset.2 ((hKY x).1 x.2)⟩ : ws.toFinset)) ⟨fun a b hab => ?_, fun w => ?_⟩)]
    · exact Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    · exact Subtype.ext (Φ.inj (congrArg Subtype.val hab))
    · have hw := List.mem_toFinset.1 w.2
      obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
      rw [hlen] at hi
      have hwlt : (w : ℕ) < N := by
        rw [← hiw, ← List.getD_eq_getElem _ 0 (by rwa [hlen]), hws i hi]
        exact (hent i hi).1.1.1
      refine ⟨⟨Φ.g w, (hKY _).2 (by rw [Φ.f_g hwlt]; exact hw)⟩, Subtype.ext ?_⟩
      exact Φ.f_g hwlt
  · obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem ((hKY x).1 hx)
    rw [hlen] at hi
    have e1 : (L.getD i (0, 0, 0, 0)).1 = Φ.f x := by
      rw [← hws i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [hlen]),
        Option.getD_some, hiw]
    have hne : (L.getD i (0, 0, 0, 0)).1 ≠ 0 := by
      rw [e1]
      intro h
      apply hx1
      rw [← Φ.g_f x, h, ← Φ.f_one h0, Φ.g_f]
    rcases (hent i hi).2 with h | ⟨⟨hc, htab⟩, hcnt⟩
    · exact absurd h hne
    · exact ⟨_, hc, by rw [htab, e1], by rw [← e1]; exact hcnt⟩

end Spec

theorem cInvC_eq {G : Type*} [Group G] {S : Subgroup G} {N : ℕ} {smul : ℕ → ℕ → ℕ}
    (Φ : CodeIso S N smul) (h0 : smul 0 0 = 0) (x : S) :
    cInvC smul (kInv smul N) (Φ.f x) = cInv S x := by
  unfold cInvC cInv
  rw [Φ.length_kInv_filter h0]
  refine Nat.card_congr
    { toFun := fun h => ⟨h.1, h.1.2, ?_, ?_, ?_⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_, ?_, ?_⟩
      left_inv := fun h => rfl
      right_inv := fun y => rfl }
  · exact congrArg Subtype.val h.2.1
  · intro h1; exact h.2.2.1 (Subtype.ext h1)
  · have h3 := h.2.2.2
    simp only [beq_iff_eq, ← Φ.map_mul, Φ.f_eq_iff] at h3
    exact congrArg Subtype.val h3
  · exact Subtype.ext y.2.2.1
  · intro h1; exact y.2.2.2.1 (congrArg Subtype.val h1)
  · simp only [beq_iff_eq, ← Φ.map_mul, Φ.f_eq_iff]
    exact Subtype.ext y.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
