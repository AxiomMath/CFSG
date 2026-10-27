
module

public import Certificates.Data.Kernel.GH74Tab.B
public import CFSG.Certificates.Kernel.GH74Tab.E1Sound

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def claimBP {n : ℕ} [NeZero n] (t : Tab n) (L : List Tbl) (a : Tbl) (u : Fin 64) :
    Bool :=
  let X0 := t.reach a t.x0i
  let V0 := t.reach a (t.mulT t.x0i (a.get t.x0i))
  (List.finRange 64).all (fun i => imp (t.isInv i) (X0.get i || V0.get i)) &&
  (List.finRange 64).any fun s =>
    t.mulT (t.mulT s (a.get s)) u == t.one && L.any fun ψ => t.certB a X0 V0 s ψ

theorem claimB_eq {n : ℕ} [NeZero n] (t : Tab n) : t.claimB = t.claimG (claimBP t t.autsOf) :=
  rfl

theorem mem_autsOf_of_aut {n : ℕ} [NeZero n] {t : Tab n} {ψ : Tbl} (hv : t.Valid)
    (h : t.IsAutT ψ) : ψ ∈ t.autsOf := by
  have hf : (![ψ.get (t.gens.get 0), ψ.get (t.gens.get 1), ψ.get (t.gens.get 2),
      ψ.get (t.gens.get 3)] : Fin 4 → Fin 64) = fun k => ψ.get (t.gens.get k) := by
    funext k
    fin_cases k <;> rfl
  have e : t.ofImages ![ψ.get (t.gens.get 0), ψ.get (t.gens.get 1), ψ.get (t.gens.get 2),
      ψ.get (t.gens.get 3)] = ψ := by
    rw [hf]
    exact (h.eq_ofImages hv).symm
  simp only [Tab.autsOf, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_finRange,
    true_and]
  refine ⟨_, ?_, _, ?_, _, ?_, _, ⟨?_, ?_⟩, e⟩
  · simp only [Tab.ok0, h.cls3_eq, beq_self_eq_true]
  · simp only [Tab.ok1, h.cls3_eq, h.pairOK, beq_self_eq_true, Bool.and_self]
  · simp only [Tab.ok2, h.cls3_eq, h.pairOK, beq_self_eq_true, Bool.and_self]
  · simp only [Tab.ok3, h.cls3_eq, h.pairOK, beq_self_eq_true, Bool.and_self]
  · rw [e]
    exact (Tab.isAutB_iff t ψ).2 h

theorem bit_foldl_shl_f (f : Nat → Nat) (l : List Nat) (acc k : Nat) :
    bit (l.foldl (fun m i => m ||| 1 <<< f i) acc) k =
      (bit acc k || l.any fun i => decide (k = f i)) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih => rw [List.foldl_cons, ih, bit_or, bit_shl1, List.any_cons, Bool.or_assoc]

section Sound

variable {D : Dat} {n : ℕ} [NeZero n]

theorem isAutT_of_autFK (ht : transOK D n = true) (hd : dataOK D = true) {ψ : Nat}
    (h : autFK D ψ = true) : (mkTab n).IsAutT (tblOf ψ) := by
  have hd1 := (dataOK_spec D hd).1
  simp only [autFK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hsurj : Function.Surjective (tblOf ψ).get := by
    intro k
    have hk : bit (r64.foldl (fun m i => m ||| 1 <<< g6 ψ i) 0) k.val = true := by
      rw [h3, bit_eq, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true k.2
    rw [bit_foldl_shl_f] at hk
    simp only [bit_eq, Nat.zero_testBit, Bool.false_or, List.any_eq_true, decide_eq_true_eq, r64,
      List.mem_range] at hk
    obtain ⟨i, hi, hik⟩ := hk
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [tblOf_get_eq]
    apply Fin.ext
    rw [val_f64_g6]
    exact hik.symm
  refine ⟨?_, fun i j => ?_, Finite.injective_iff_surjective.2 hsurj⟩
  · rw [one_eq D ht, tblOf_get_eq, val_f64 hd1, h1]
  · simp only [mulT_eq D ht, tblOf_get_eq, val_f64_mul, val_f64_g6]
    rw [h2 i.val (mem_r64 i.2) j.val (mem_r64 j.2)]

variable {A N4 N8 : Nat}

theorem transB_spec (h : transB n A N4 N8 = true) (k : Fin 64) :
    a0perm n * emb n ((mkTab n).el.get k) * (a0perm n)⁻¹ =
        emb n ((mkTab n).el.get (f64 (g6 A k))) ∧
      ((mkTab n).nm.get k == 4) = bit N4 k.val ∧ ((mkTab n).nm.get k == 8) = bit N8 k.val := by
  simp only [transB, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k
  exact ⟨h1, h2, h3⟩

theorem astar_eq (hv : (mkTab n).Valid) (h : transB n A N4 N8 = true) (k : Fin 64) :
    (mkTab n).astar.get k = f64 (g6 A k.val) :=
  hv.el_inj _ _ (emb_injective n ((hv.astar_spec k).symm.trans (transB_spec h k).1))

theorem nm4_iff (h : transB n A N4 N8 = true) (k : Fin 64) :
    (mkTab n).nm.get k = 4 ↔ bit N4 k.val = true := by
  rw [← (transB_spec h k).2.1, beq_iff_eq]

theorem nm8_iff (h : transB n A N4 N8 = true) (k : Fin 64) :
    (mkTab n).nm.get k = 8 ↔ bit N8 k.val = true := by
  rw [← (transB_spec h k).2.2, beq_iff_eq]

variable (ht : transOK D n = true) (hd : dataOK D = true) (hv : (mkTab n).Valid)
  (htb : transB n A N4 N8 = true)
include ht hd hv htb

theorem bK_sound {Ψ : List Nat} (hΨ : ∀ ψ ∈ Ψ, autFK D ψ = true) {p w : Nat × Nat}
    (h : bK D A N4 N8 Ψ p w = true) :
    claimBP (mkTab n) (mkTab n).autsOf (tblOf p.1) (f64 p.2) = true := by
  obtain ⟨a, u⟩ := p
  obtain ⟨s, k⟩ := w
  have hx0 := (dataOK_spec D hd).2.1
  simp only [bK, certK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hu, hcov⟩, hs⟩, hk⟩, hsu⟩, ⟨hψx, hconj⟩, hnm⟩ := h
  have hψ : Ψ.getD k 0 ∈ Ψ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hX : ∀ j : Fin 64, ((mkTab n).reach (tblOf a) (mkTab n).x0i).get j =
      bit (reachK D a 12 (1 <<< D.x0)) j.val := reachX ht hd a
  have hV : ∀ j : Fin 64, ((mkTab n).reach (tblOf a)
      ((mkTab n).mulT (mkTab n).x0i ((tblOf a).get (mkTab n).x0i))).get j =
      bit (reachK D a 12 (1 <<< mul D D.x0 (g6 a D.x0))) j.val := reachV ht hd a
  unfold claimBP
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true,
    List.any_eq_true, true_and, beq_iff_eq, Bool.or_eq_true]
  refine ⟨fun i hi => ?_, f64 s, ?_,
    tblOf (Ψ.getD k 0), mem_autsOf_of_aut hv (isAutT_of_autFK ht hd (hΨ _ hψ)), ?_⟩
  · rw [isInv_eq ht hd] at hi
    rw [hX, hV]
    rcases hcov i.val (mem_r64 i.2) with (h1 | h1) | h1
    · rw [hi] at h1
      exact absurd h1 (by decide)
    · exact Or.inl h1
    · exact Or.inr h1
  · rw [one_eq D ht]
    simp only [mulT_eq D ht, tblOf_get_eq, val_f64 hs, val_f64 hu, val_f64_g6, val_f64_mul]
    rw [hsu]
  · unfold Tab.certB
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies,
      imp_eq_true]
    refine ⟨⟨?_, fun i => ?_⟩, fun i hi => ⟨fun hxi => ?_, fun hvi => ?_⟩⟩
    · rw [x0i_eq D ht, tblOf_get_eq, val_f64 hx0, hψx]
    · rw [astar_eq hv htb]
      simp only [mulT_eq D ht, inv_eq D ht, tblOf_get_eq, val_f64 hs, val_f64_g6, val_f64_mul]
      rw [hconj i.val (mem_r64 i.2)]
    · rw [isInv_eq ht hd] at hi
      rw [hX] at hxi
      rw [nm4_iff htb, tblOf_get_eq, val_f64_g6]
      rcases hnm i.val (mem_r64 i.2) with h1 | ⟨h1, -⟩
      · rw [hi] at h1
        exact absurd h1 (by decide)
      · rcases h1 with h1 | h1
        · rw [hxi] at h1
          exact absurd h1 (by decide)
        · exact h1
    · rw [isInv_eq ht hd] at hi
      rw [hV] at hvi
      rw [nm8_iff htb, tblOf_get_eq, val_f64_g6]
      rcases hnm i.val (mem_r64 i.2) with h1 | ⟨-, h1⟩
      · rw [hi] at h1
        exact absurd h1 (by decide)
      · rcases h1 with h1 | h1
        · rw [hvi] at h1
          exact absurd h1 (by decide)
        · exact h1

theorem bOK_sound {Ψ : List Nat} {L W : List (Nat × Nat)} (hb : bOK D A N4 N8 Ψ L W = true)
    {p : Nat × Nat} (hp : p ∈ L) :
    claimBP (mkTab n) (mkTab n).autsOf (tblOf p.1) (f64 p.2) = true := by
  simp only [bOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨hΨ, hlen⟩, hLW⟩ := hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hz : i < (L.zip W).length := by
    rw [List.length_zip, ← hlen, Nat.min_self]
    exact hi
  have hw := hLW _ (List.getElem_mem hz)
  rw [List.getElem_zip] at hw
  exact bK_sound ht hd hv htb hΨ hw

end Sound

end CFSG.KC.GH74Tab

end
