module

import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.GroupTheory.OrderOfElement
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import Certificates.Data.Kernel.Spor.GraphSep

public section

namespace CFSG.KS.GraphSep

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2

theorem shl_one_eq (x : Nat) : Nat.shiftLeft (nat_lit 1) x = 2 ^ x := Nat.one_shiftLeft x

theorem testBit_orFold (f : Nat → Nat) (k v : Nat) :
    ((List.range k).foldl (fun s i => Nat.lor s (Nat.shiftLeft (nat_lit 1) (f i)))
      (nat_lit 0)).testBit v = true ↔ ∃ i < k, f i = v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, shl_one_eq]
    change (_ ||| 2 ^ f k).testBit v = true ↔ _
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, ih, decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, e⟩ | e)
      · exact ⟨i, by omega, e⟩
      · exact ⟨k, by omega, e⟩
    · rintro ⟨i, hi, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact Or.inl ⟨i, h, e⟩
      · exact Or.inr e

theorem testBit_andFold (g : Nat → Nat) (c init y : Nat) :
    ((List.range c).foldl (fun s i => Nat.land s (g i)) init).testBit y = true ↔
      init.testBit y = true ∧ ∀ i < c, (g i).testBit y = true := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (_ &&& g c).testBit y = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 c (by omega)⟩

theorem testBit_mask (n i : Nat) : (mask n).testBit i = decide (i < n) := by
  rw [Orb.mask_eq', Nat.testBit_two_pow_sub_one]

theorem land_one_shr (z x : Nat) :
    Nat.land (Nat.shiftRight z x) (nat_lit 1) = if z.testBit x then 1 else 0 := by
  change (z >>> x) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ x) with h | h <;> simp [h]

theorem listK_nbr {n w d v : Nat} {NB AL : Nat → Nat} (h : listK n w (mask w) d NB AL v = true) :
    ∀ u, (NB v).testBit u = true → u < n ∧ ∃ i < d, pg w (mask w) (AL v) i = u := by
  intro u hu
  simp only [listK, Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [Nat.eq_of_beq_eq_true h2, Orb.foldUp_eq, testBit_orFold] at hu
  obtain ⟨i, hi, e⟩ := hu
  exact ⟨e ▸ Nat.blt_eq.mp (h1 i hi), i, hi, e⟩

@[expose] def edgeGrp (n : Nat) (NB : Nat → Nat) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ v u : Fin n, (NB (g v)).testBit (g u) = (NB v).testBit u}
  mul_mem' := fun {a b} ha hb v u => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha (b v) (b u), hb v u]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha v u => by
    have e : ∀ x : Fin n, a (a⁻¹ x) = x := fun x => by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have := ha (a⁻¹ v) (a⁻¹ u)
    rw [e, e] at this
    exact this.symm

theorem mem_edgeGrp_of {n : Nat} {NB : Nat → Nat} {σ : Equiv.Perm (Fin n)}
    (h : ∀ v u : Fin n, (NB v).testBit u = true → (NB (σ v)).testBit (σ u) = true) :
    σ ∈ edgeGrp n NB := by
  have hpow : ∀ m : Nat, ∀ v u : Fin n, (NB v).testBit u = true →
      (NB ((σ ^ m) v)).testBit ((σ ^ m) u) = true := by
    intro m
    induction m with
    | zero =>
      intro v u h'
      simpa using h'
    | succ m ih =>
      intro v u h'
      rw [pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      exact ih _ _ (h _ _ h')
  intro v u
  refine Bool.eq_iff_iff.2 ⟨fun h' => ?_, h v u⟩
  have e : σ ^ (orderOf σ - 1) * σ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]
  have e1 : ∀ x : Fin n, (σ ^ (orderOf σ - 1)) (σ x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, e, Equiv.Perm.one_apply]
  have := hpow (orderOf σ - 1) _ _ h'
  rwa [e1, e1] at this

theorem perm_fwd {n w d s : Nat} {NB AL : Nat → Nat}
    (hL : ∀ v < n, listK n w (mask w) d NB AL v = true)
    (hI : ∀ v < n, invK w (mask w) d NB AL s v = true) :
    ∀ v u : Fin n, (NB v).testBit u = true →
      (NB (permOfArr n (unpack n w s) v)).testBit (permOfArr n (unpack n w s) u) = true := by
  intro v u h
  by_cases hc : (∀ i < n, (unpack n w s)[i]! < n) ∧
      ∀ i < n, ∀ j < n, (unpack n w s)[i]! = (unpack n w s)[j]! → i = j
  · have hap : ∀ x : Fin n, (permOfArr n (unpack n w s) x : Nat) = pg w (mask w) s x := by
      intro x
      have e : (permOfArr n (unpack n w s) x : Nat) = (unpack n w s)[x.val]! := by
        rw [permOfArr, dite_eq_left hc]
        rfl
      rw [e, unpack, getElem!_ofFn_nat _ x.2]
    obtain ⟨_, i, hi, e⟩ := listK_nbr (hL v v.2) u h
    have hv := hI v v.2
    simp only [invK, Orb.strictB_eq, Orb.allN_iff, Orb.hasBit_eq] at hv
    have := hv i hi
    rw [e] at this
    rw [hap, hap]
    exact this
  · rw [permOfArr, dite_eq_right hc]
    exact h

theorem wSet_bit {n w m e x y : Nat} {NB : Nat → Nat} {ORD : Nat} (hy : y < n)
    (he : Nat.land e (nat_lit 1) =
      nbBit w m NB ORD (Nat.shiftRight e (nat_lit 1)) x)
    (hb : (NB (pg w m ORD (Nat.shiftRight e (nat_lit 1)))).testBit y =
      (NB (pg w m ORD (Nat.shiftRight e (nat_lit 1)))).testBit x) :
    (wSet n w m NB ORD e).testBit y = true := by
  unfold nbBit at he
  rw [land_one_shr] at he
  unfold wSet
  rw [Orb.strictN_eq, Orb.nIf_eq]
  split
  · rename_i h1
    rw [hb]
    have h1' := Nat.eq_of_beq_eq_true h1
    rw [h1'] at he
    split at he
    · assumption
    · exact absurd he (by decide)
  · rename_i h1
    change (mask n ^^^ _).testBit y = true
    rw [Nat.testBit_xor, testBit_mask, decide_eq_true hy, hb]
    cases hbx : (NB (pg w m ORD (Nat.shiftRight e (nat_lit 1)))).testBit x
    · rfl
    · simp only [hbx, ↓reduceIte] at he
      rw [he] at h1
      exact absurd rfl h1

theorem fix_of_refK {n w k : Nat} {NB WT : Nat → Nat} {ORD : Nat} {G : Equiv.Perm (Fin n)}
    (hG : G ∈ edgeGrp n NB) (hlt : ∀ p ≤ k, pg w (mask w) ORD p < n)
    (hfix : ∀ p < k, ∀ h : pg w (mask w) ORD p < n,
      G ⟨pg w (mask w) ORD p, h⟩ = ⟨pg w (mask w) ORD p, h⟩)
    (hR : refK n w (mask w) NB WT ORD k = true) (hx : pg w (mask w) ORD k < n) :
    G ⟨pg w (mask w) ORD k, hx⟩ = ⟨pg w (mask w) ORD k, hx⟩ := by
  set x := pg w (mask w) ORD k with hxd
  by_cases hrep : ∃ i < k, pg w (mask w) ORD i = x
  · obtain ⟨i, hi, e⟩ := hrep
    have h' := hfix i hi (hlt i hi.le)
    have hz : (⟨pg w (mask w) ORD i, hlt i hi.le⟩ : Fin n) = ⟨x, hx⟩ := Fin.ext e
    rw [hz] at h'
    exact h'
  · apply Fin.ext
    set y := G ⟨x, hx⟩ with hyd
    simp only [refK, Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff] at hR
    obtain ⟨hW, hF⟩ := hR
    rw [← hxd] at hW hF
    rw [Orb.foldUp_eq] at hF
    have hFe := Nat.eq_of_beq_eq_true hF
    have hnf : (fixedK w (mask w) ORD k).testBit y.val = false := by
      unfold fixedK
      rw [Orb.foldUp_eq, Bool.eq_false_iff]
      intro hf
      obtain ⟨i, hi, e⟩ := (testBit_orFold _ k y.val).1 hf
      have hfi := hfix i hi (hlt i hi.le)
      have hG' : G ⟨pg w (mask w) ORD i, hlt i hi.le⟩ = G ⟨x, hx⟩ := by
        rw [hfi]
        exact Fin.ext e
      exact hrep ⟨i, hi, congrArg Fin.val (G.injective hG')⟩
    have hinit : (Nat.xor (mask n) (fixedK w (mask w) ORD k)).testBit y.val = true := by
      change (mask n ^^^ _).testBit y.val = true
      rw [Nat.testBit_xor, testBit_mask, decide_eq_true y.2, hnf]
      rfl
    have hwit : ∀ i < Nat.land (WT k) (nat_lit 255),
        (wSet n w (mask w) NB ORD (wEnt w (WT k) i)).testBit y.val = true := by
      intro i hi
      obtain ⟨hp, he⟩ := hW i hi
      have hp' := Nat.blt_eq.mp hp
      set p := Nat.shiftRight (wEnt w (WT k) i) (nat_lit 1) with hpd
      have ha := hlt p hp'.le
      refine wSet_bit y.2 (Nat.eq_of_beq_eq_true he) ?_
      have h1 := hG ⟨pg w (mask w) ORD p, ha⟩ ⟨x, hx⟩
      rw [hfix p hp' ha] at h1
      exact h1
    have hbit := (testBit_andFold (fun i => wSet n w (mask w) NB ORD (wEnt w (WT k) i))
      (Nat.land (WT k) (nat_lit 255)) (Nat.xor (mask n) (fixedK w (mask w) ORD k)) y.val).2
      ⟨hinit, hwit⟩
    beta_reduce at hbit
    rw [hFe, shl_one_eq, Nat.testBit_two_pow] at hbit
    exact (of_decide_eq_true hbit).symm

theorem graphSep_sound {n w kS nb BP d ORD : Nat} {PS NB AL WT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} (hb : Binds n w PS kS nb BP S base)
    (hL : ∀ v < n, listK n w (mask w) d NB AL v = true)
    (hI : ∀ j < kS, ∀ v < n, invK w (mask w) d NB AL (PS j) v = true)
    (hO : ordK n w (mask w) nb BP ORD = true)
    (hR : ∀ k < n, nb ≤ k → refK n w (mask w) NB WT ORD k = true) : Sep n S base := by
  have hSs : S.size = kS := hb.2.2.2.1
  have hS := hb.2.2.2.2.1
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbase := hb.2.2.2.2.2.2
  intro G hG hfixB
  have hGE : G ∈ edgeGrp n NB := by
    refine (Subgroup.closure_le _).2 ?_ hG
    rintro _ ⟨j, hj, rfl⟩
    rw [hS j (hSs ▸ hj)]
    exact mem_edgeGrp_of (perm_fwd hL (hI j (hSs ▸ hj)))
  simp only [ordK, Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff] at hO
  obtain ⟨hnb, hOB, hcov⟩ := hO
  have hnb' := Nat.ble_eq.mp hnb
  rw [Orb.foldUp_eq] at hcov
  have hcov' := Nat.eq_of_beq_eq_true hcov
  have hmem : ∀ z, z < n ↔ ∃ k < n, pg w (mask w) ORD k = z := by
    intro z
    rw [← testBit_orFold (pg w (mask w) ORD) n z, hcov', testBit_mask, decide_eq_true_iff]
  have hlt : ∀ k < n, pg w (mask w) ORD k < n := fun k hk => (hmem _).2 ⟨k, hk, rfl⟩
  have key : ∀ k < n, ∀ h : pg w (mask w) ORD k < n,
      G ⟨pg w (mask w) ORD k, h⟩ = ⟨pg w (mask w) ORD k, h⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk h
      by_cases hkb : k < nb
      · have e : pg w (mask w) ORD k = base[k]! := by
          rw [Nat.eq_of_beq_eq_true (hOB k hkb), hbase k hkb]
        revert h
        rw [e]
        intro h
        exact hfixB k (by omega) h
      · exact fix_of_refK hGE (fun p hp => hlt p (by omega))
          (fun p hp h' => ih p hp (by omega) h') (hR k hk (by omega)) h
  refine Equiv.ext fun z => ?_
  obtain ⟨k, hk, e⟩ := (hmem z.val).1 z.2
  have := key k hk (hlt k hk)
  have hz : (⟨pg w (mask w) ORD k, hlt k hk⟩ : Fin n) = z := Fin.ext e
  rw [hz] at this
  exact this

end CFSG.KS.GraphSep

end
