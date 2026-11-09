module

public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import CFSG.Certificates.Kernel.SporSch.ChainKConj
public import CFSG.Sporadic.Schreier.PairChain

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.Mathieu
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

@[expose] noncomputable def invBaseK (w m k G T : Nat) : Bool :=
  bAnd(Bool.not (allN k fun b => Nat.beq (pg w m G (pg w m T b)) b),
    allN k fun b => strictB (pg w m G (pg w m T b)) fun y => Nat.beq (pg w m G (pg w m T y)) b)

@[expose] noncomputable def enumBaseK (n w m nw k : Nat) (LR TR : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun i g s => strictN (LR i) (fun R =>
      foldUp (rcnt R) (fun j s => nIf(invBaseK w m k g (TR (Nat.add (roff n nw R) j)),
        Nat.succ s, s)) s))
    (fun _ ih i g s => strictN (LR i) (fun R =>
      foldUp (rcnt R) (fun j s => strictN (pcomp n w m g (TR (Nat.add (roff n nw R) j)))
        (fun h => ih (Nat.succ i) h s)) s))

@[expose] noncomputable def cntInvBK (n w m nw k : Nat) (LR TR : Nat → Nat) (k₀ : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun R =>
    enumBaseK n w m nw k LR TR (Nat.sub k (nat_lit 2)) (nat_lit 1) (TR (Nat.add (roff n nw R) k₀))
      (nat_lit 0))

variable {n w : Nat}

@[expose] def baseInvQ (k : Nat) (x : Equiv.Perm (Fin n)) : Bool :=
  decide ((∃ b : Fin n, (b : Nat) < k ∧ x b ≠ b) ∧ ∀ b : Fin n, (b : Nat) < k → x (x b) = b)

theorem invBaseK_eq {k G T : Nat} {g t : Equiv.Perm (Fin n)} (hk : k ≤ n) (hG : PRep n w G g)
    (hT : PRep n w T t) : invBaseK w (mask w) k G T = baseInvQ k (g * t) := by
  have e : ∀ b (hb : b < n), pg w (mask w) G (pg w (mask w) T b) = ((g * t) ⟨b, hb⟩ : Nat) := by
    intro b hb
    have h1 := hT ⟨b, hb⟩
    simp only at h1
    rw [h1, hG, Equiv.Perm.mul_apply]
  unfold invBaseK baseInvQ
  rw [bAnd_eq, Bool.eq_iff_iff, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_iff]
  refine and_congr ?_ ?_
  · rw [← Bool.not_eq_true, allN_iff]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      exact h fun b hb => by
        rw [e b (by omega)]
        exact Nat.beq_eq_true_eq _ _ ▸ (congrArg Fin.val (hc ⟨b, by omega⟩ hb))
    · rintro ⟨b, hb, hne⟩ h
      have := Nat.eq_of_beq_eq_true (h b hb)
      rw [e b b.2] at this
      exact hne (Fin.ext this)
  · rw [allN_iff]
    constructor
    · intro h b hb
      have := h b hb
      rw [Orb.strictB_eq, e b b.2] at this
      have := Nat.eq_of_beq_eq_true this
      rw [e _ ((g * t) b).2] at this
      exact Fin.ext this
    · intro h b hb
      rw [Orb.strictB_eq, e b (by omega), e _ ((g * t) ⟨b, by omega⟩).2]
      exact Nat.beq_eq_true_eq _ _ ▸ (congrArg Fin.val (h ⟨b, by omega⟩ hb))

theorem baseInvQ_eq {H : Subgroup (Equiv.Perm (Fin n))} {k : Nat}
    (hF : BaseFaithful H (List.range k)) {x : Equiv.Perm (Fin n)} (hx : x ∈ H) :
    baseInvQ k x = decide (orderOf x = 2) := by
  have h1 : x ≠ 1 ↔ ∃ b : Fin n, (b : Nat) < k ∧ x b ≠ b := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      exact h (hF x hx fun b hb => hc b (List.mem_range.1 hb))
    · rintro ⟨b, -, hb⟩ rfl
      exact hb rfl
  have h2 : x ^ 2 = 1 ↔ ∀ b : Fin n, (b : Nat) < k → x (x b) = b := by
    constructor
    · intro h b _
      rw [← Equiv.Perm.mul_apply, ← sq, h, Equiv.Perm.one_apply]
    · intro h
      exact hF (x ^ 2) (H.pow_mem hx 2) fun b hb => by
        rw [sq, Equiv.Perm.mul_apply]
        exact h b (List.mem_range.1 hb)
  have h3 : orderOf x = 2 ↔ x ≠ 1 ∧ x ^ 2 = 1 := by
    constructor
    · intro h
      refine ⟨fun e => ?_, h ▸ pow_orderOf_eq_one x⟩
      rw [e, orderOf_one] at h
      exact absurd h (by norm_num)
    · rintro ⟨hne, hsq⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime hsq hne
  unfold baseInvQ
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, h3, h1, h2]

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem enumBaseK_zero (n w m nw k : Nat) (LR TR : Nat → Nat) (i g s : Nat) :
    enumBaseK n w m nw k LR TR 0 i g s = (List.range (rcnt (LR i))).foldl
      (fun s j => if invBaseK w m k g (TR (roff n nw (LR i) + j)) = true then s + 1 else s) s := by
  have e : enumBaseK n w m nw k LR TR 0 i g s = strictN (LR i) (fun R =>
      foldUp (rcnt R) (fun j s => nIf(invBaseK w m k g (TR (Nat.add (roff n nw R) j)),
        Nat.succ s, s)) s) := rfl
  rw [e, Orb.strictN_eq, foldUp_eq]
  congr 1
  funext s j
  rw [Orb.nIf_eq]
  rfl

theorem enumBaseK_succ (n w m nw k : Nat) (LR TR : Nat → Nat) (d i g s : Nat) :
    enumBaseK n w m nw k LR TR (d + 1) i g s = (List.range (rcnt (LR i))).foldl
      (fun s j => enumBaseK n w m nw k LR TR d (i + 1) (pcomp n w m g (TR (roff n nw (LR i) + j)))
        s) s := by
  have e : enumBaseK n w m nw k LR TR (d + 1) i g s = strictN (LR i) (fun R =>
      foldUp (rcnt R) (fun j s => strictN (pcomp n w m g (TR (Nat.add (roff n nw R) j)))
        (fun h => enumBaseK n w m nw k LR TR d (Nat.succ i) h s)) s) := rfl
  rw [e, Orb.strictN_eq, foldUp_eq]
  congr 1
  funext s j
  rw [Orb.strictN_eq]
  rfl

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem enumBaseK_spec {kb : Nat} (hkb : kb ≤ n) :
    ∀ d i, i + d + 1 ≤ k → ∀ G g s, PRep n w G g → G >>> (n * w) = 0 →
      enumBaseK n w (mask w) (n * w) kb LR TR d i G s = s +
        ((products ((List.range (d + 1)).map fun t => trL n w LR TR (i + t))).map
          (g * ·)).countP (baseInvQ kb)
  | 0, i, hd, G, g, s, hG, _ => by
    rw [enumBaseK_zero, range_map_succ, countP_products_cons, trL, List.map_map]
    refine foldl_eq_add _ (fun j hj s => ?_) s
    obtain ⟨h1, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hj)
    rw [invBaseK_eq hkb hG h1]
    simp only [List.range_zero, List.map_nil, products, List.map_cons, mul_one,
      List.countP_singleton, Function.comp_apply]
    split <;> simp_all
  | d + 1, i, hd, G, g, s, hG, sG => by
    have hn := chainK_h32 hQ
    have hw := PF.w_pos hQ.2.1
    rw [enumBaseK_succ, range_map_succ, countP_products_cons, trL, List.map_map]
    refine foldl_eq_add _ (fun j hj s => ?_) s
    obtain ⟨h1, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hj)
    rw [enumBaseK_spec hkb d (i + 1) (by omega) _ (g * trP n w LR TR i j) s
      (prep_pcomp hn hG h1) (PF.pcomp_shr _ _ hn hw)]
    rfl

theorem chainK_invCount (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hbv : bv.toList.map Fin.val = List.range k) (hk : 2 ≤ k) {CS : List Nat}
    (hCS : CS.length = rcnt (LR 0))
    (hc : ∀ k₀ < rcnt (LR 0), cntInvBK n w (mask w) (n * w) k LR TR k₀ = CS.getD k₀ 0) :
    (cosetOrderTables (certificate hn gens words bv hbs) 1 2).length = CS.sum := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  set Q := certificate hn gens words bv hbs
  have hV : ValidSchreier Q := chainK_valid hQ hn hbs
  have hF : BaseFaithful Q.originalSubgroup (List.range k) := by
    have := baseFaithful_of_valid hV
    have hb : Q.base.toList.map Fin.val = List.range k := hbv
    rwa [hb] at this
  have hkn : k ≤ n := by
    have := congrArg List.length hbv
    simp only [List.length_map, Vector.length_toList, List.length_range] at this
    have := bv.toList.nodup_iff_injective_get.1 hbs
    simpa using Fintype.card_le_of_injective _ this
  rw [length_cosetOrderTables_one hn32 Q (by norm_num)]
  have e1 : (enumeration Q).countP (fun h => decide (orderOf h = 2)) =
      ((enumeration Q).map (1 * ·)).countP (baseInvQ k) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro x hx
    rw [Function.comp_apply, one_mul,
      baseInvQ_eq hF ((mem_enumeration_iff Q hV x).1 hx)]
  rw [e1, countP_coset1 hQ hn hbs (by omega)]
  refine sum_range_getD hCS fun k₀ hk₀ => ?_
  rw [← hc k₀ hk₀]
  obtain ⟨h1, s1⟩ := tr_facts hQ (by omega) hk₀
  have e2 : cntInvBK n w (mask w) (n * w) k LR TR k₀ =
      enumBaseK n w (mask w) (n * w) k LR TR (k - 2) 1 (TR (roff n (n * w) (LR 0) + k₀)) 0 := by
    unfold cntInvBK
    rw [Orb.strictN_eq]
    rfl
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have e3 : d + 2 - 1 = d + 1 := rfl
  rw [e2, Nat.add_sub_cancel, e3, enumBaseK_spec hQ hkn d 1 (by omega) _ _ 0 h1 s1, Nat.zero_add]
  simp only [one_mul]

end Chain

end CFSG.KS.SporSch.MOC
