module

public import CFSG.Certificates.Kernel.ListBridge.PackSound
public import Certificates.Data.Kernel.ListBridgeTree
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge CFSG.Sporadic.Schreier

variable {n w : Nat}

theorem roundL_mono (gens : List (Equiv.Perm (Fin n))) {r s : Nat} (h : r ≤ s) {x : Equiv.Perm (Fin n)}
    (hx : x ∈ roundL gens r) : x ∈ roundL gens s := by
  induction h with
  | refl => exact hx
  | step _ ih =>
    rw [roundL_succ, mem_stepL]
    exact Or.inl ih

theorem prod_mem_roundL (gens : List (Equiv.Perm (Fin n))) :
    ∀ l : List (Equiv.Perm (Fin n)), (∀ s ∈ l, s ∈ gens) → l.prod ∈ roundL gens l.length := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simpa [roundL]
  | append_singleton l s ih =>
    intro hl
    rw [List.prod_append, List.prod_singleton, List.length_append, List.length_singleton,
      roundL_succ, mem_stepL]
    exact Or.inr ⟨l.prod, ih fun t ht => hl t (List.mem_append_left _ ht), s,
      hl s (List.mem_append_right _ (List.mem_singleton_self s)), rfl⟩

theorem depthK_words {ng N fuel : Nat} {G T E S D : Nat → Nat} {gens : List (Equiv.Perm (Fin n))}
    (hk : bfsK n w ng G N T E S = true) (hl : gens.length = ng)
    (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1)) (hd : depthK n w ng G T N fuel D = true) :
    ∀ i < N, ∃ l : List (Equiv.Perm (Fin n)), (∀ s ∈ l, s ∈ gens) ∧ l.length ≤ fuel ∧
      PRep n w (T i) l.prod := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  have hn32 : n < 2 ^ 32 := by omega
  obtain ⟨-, hT0, -, -⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  unfold depthK at hd
  obtain ⟨hd0, hall⟩ := (bAnd_iff _ _).1 hd
  have hd0' : rDep (D 0) = 0 := Nat.eq_of_beq_eq_true hd0
  have step : ∀ i < N, i ≠ 0 → rPar (D i) < N ∧ rGen (D i) < ng ∧ rDep (D i) ≤ fuel ∧
      rDep (D i) = rDep (D (rPar (D i))) + 1 ∧
      T i = pcomp n w (mask w) (G (rGen (D i))) (T (rPar (D i))) := by
    intro i hi h0
    have h := allN_spec hall i hi
    have hb : Nat.beq i 0 = false := by
      cases h' : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') h0
    rw [hb] at h
    have h' : strictB (D i) (fun r =>
        bAnd(Nat.blt (rPar r) N, bAnd(Nat.blt (rGen r) ng,
          bAnd(Nat.blt (rDep r) (Nat.succ fuel),
            bAnd(Nat.beq (rDep r) (Nat.succ (rDep (D (rPar r)))),
              Nat.beq (T i) (pcomp n w (mask w) (G (rGen r)) (T (rPar r)))))))) = true := h
    rw [Orb.strictB_eq] at h'
    obtain ⟨h1, h'⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h2, h'⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h3, h'⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h'
    exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.lt_succ_iff.mp (Nat.blt_eq.mp h3),
      Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩
  have key : ∀ m, ∀ i < N, rDep (D i) = m → ∃ l : List (Equiv.Perm (Fin n)),
      (∀ s ∈ l, s ∈ gens) ∧ l.length ≤ m ∧ PRep n w (T i) l.prod := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi hm
      by_cases h0 : i = 0
      · subst h0
        refine ⟨[], by simp, by simp, ?_⟩
        rw [List.prod_nil, hT0]
        exact prep_pidn hn hw
      · obtain ⟨hp, hg, -, hdep, hT⟩ := step i hi h0
        obtain ⟨l, hls, hll, hlr⟩ := ih _ (by omega) _ hp rfl
        refine ⟨gens.getD (rGen (D i)) 1 :: l, fun s hs => ?_, by simp; omega, ?_⟩
        · rcases List.mem_cons.1 hs with rfl | hs
          · exact getD_mem (hl ▸ hg)
          · exact hls s hs
        · rw [List.prod_cons, hT]
          exact prep_pcomp hn32 (hG _ hg) hlr
  intro i hi
  obtain ⟨l, hls, hll, hlr⟩ := key _ i hi rfl
  refine ⟨l, hls, ?_, hlr⟩
  by_cases h0 : i = 0
  · subst h0
    omega
  · have := (step i hi h0).2.2.1
    omega

theorem mem_permClosureList_of_K {ng N fuel : Nat} {G T E S D : Nat → Nat}
    {gens : List (Equiv.Perm (Fin n))} (hk : bfsK n w ng G N T E S = true)
    (hl : gens.length = ng) (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1))
    (hd : depthK n w ng G T N fuel D = true) (x : Equiv.Perm (Fin n)) :
    x ∈ permClosureList gens fuel ↔ x ∈ Subgroup.closure {s | s ∈ gens} := by
  rw [permClosureList_eq]
  refine ⟨fun h => roundL_subset gens fuel x h, fun hx => ?_⟩
  obtain ⟨i, hi, hr⟩ := ((enum_closure hk hl hG).1 x).1 hx
  obtain ⟨l, hls, hll, hlr⟩ := depthK_words hk hl hG hd i hi
  rw [prep_unique hr hlr]
  exact roundL_mono gens hll (prod_mem_roundL gens l hls)

theorem indexTwoCheck_of_K {gK gN KL : List (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {ngK NK ngN NN fuel R : Nat} {GK TK EK SK GN TN EN SN DN : Nat → Nat}
    (hKL : ∀ g, g ∈ KL ↔ g ∈ Subgroup.closure {s | s ∈ gK}) (hKn : KL.Nodup)
    (hkK : bfsK n w ngK GK NK TK EK SK = true) (hlK : gK.length = ngK)
    (hGK : ∀ j < ngK, PRep n w (GK j) (gK.getD j 1))
    (hkN : bfsK n w ngN GN NN TN EN SN = true) (hlN : gN.length = ngN)
    (hGN : ∀ j < ngN, PRep n w (GN j) (gN.getD j 1))
    (hd : depthK n w ngN GN TN NN fuel DN = true)
    (hNK : ∀ u ∈ gN, u ∈ Subgroup.closure {s | s ∈ gK})
    (hcard : Nat.beq NK (2 * NN) = true) (hR : PRep n w R r)
    (hRc : canonK n w (mask w) (n * w) R = true) (hout : CFSG.KLie.CT.notB (inK NN TN R) = true) :
    indexTwoCheck r KL (permClosureList gN fuel) = true := by
  have hN := mem_permClosureList_of_K hkN hlN hGN hd
  refine indexTwoCheck_of _ _ hKL hN hKn (permClosureList_nodup gN fuel)
    ((Subgroup.closure_le _).2 fun u hu => hNK u hu) ?_ ?_
  · rw [(enum_closure hkK hlK hGK).2, (enum_closure hkN hlN hGN).2]
    exact Nat.eq_of_beq_eq_true hcard
  · intro hr
    obtain ⟨i, hi, hTi⟩ := ((enum_closure hkN hlN hGN).1 r).1 hr
    have e := eq_of_prep (bfsK_canon hkN i hi) hRc hTi hR
    have hin : inK NN TN R = true := by
      unfold inK
      rw [anyN_eq, List.any_eq_true]
      exact ⟨i, List.mem_range.2 hi, by rw [e]; exact Nat.beq_refl R⟩
    rw [hin] at hout
    exact absurd hout (by decide)

end CFSG.ClassicalInvolution.ListBridge

end
