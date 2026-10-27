module

public import Certificates.Data.Kernel.SporSch.OddPt
public import CFSG.Certificates.Kernel.SporSch.ChainKCount
import CFSG.Sporadic.Recognition.LyonsAmalgamInv
import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.KS.SporSch.OddPt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem strictLN_eq (y : Nat) (k : Nat → List Nat) : strictLN y k = k y := by cases y <;> rfl

theorem bindL_eq (l : List Nat) (k : List Nat → Bool) : bindL l k = k l := by cases l <;> rfl

theorem tsK_succ (n nw : Nat) (LR T : Nat → Nat) (d j : Nat) (acc : List Nat) :
    tsK n nw LR T (d + 1) j acc =
      tsK n nw LR T d (j / rcnt (LR d)) (T (roff n nw (LR d) + j % rcnt (LR d)) :: acc) := by
  unfold tsK
  simp only [strictLN_eq]
  rfl

theorem itF_eq_pow {n : Nat} {f : Nat → Nat} {g : Equiv.Perm (Fin n)}
    (hf : ∀ q : Fin n, f q = g q) : ∀ (e : Nat) (q : Fin n), itF f e q = (g ^ e) q
  | 0, q => rfl
  | e + 1, q => by
    change strictN (itF f e q) f = _
    rw [strictN_eq, itF_eq_pow hf e q, pow_succ', Equiv.Perm.mul_apply, ← hf]

theorem pow_ne_one_of_movesK {n : Nat} {f : Nat → Nat} {g : Equiv.Perm (Fin n)}
    (hf : ∀ q : Fin n, f q = g q) {mo L p : Nat} (hp : p < n) (h : movesK f mo L p = true) :
    g ^ mo ≠ 1 := by
  unfold movesK at h
  rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : itF f L p = ((g ^ L) ⟨p, hp⟩).val := itF_eq_pow hf L ⟨p, hp⟩
  have e2 : itF f (Nat.mod mo L) p = ((g ^ (mo % L)) ⟨p, hp⟩).val := itF_eq_pow hf (mo % L) ⟨p, hp⟩
  intro hmo
  have hL : (g ^ L) ⟨p, hp⟩ = ⟨p, hp⟩ := Fin.ext (by rw [← e1]; exact Nat.eq_of_beq_eq_true h1)
  have hLm : ∀ a, (g ^ (L * a)) ⟨p, hp⟩ = ⟨p, hp⟩ := by
    intro a
    induction a with
    | zero => rfl
    | succ a ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hL, ih]
  have h3 : (g ^ (mo % L)) ⟨p, hp⟩ = ⟨p, hp⟩ := by
    have e := congrArg (fun x : Equiv.Perm (Fin n) => x ⟨p, hp⟩) hmo
    simp only [Equiv.Perm.one_apply] at e
    rw [← Nat.mod_add_div mo L, pow_add, Equiv.Perm.mul_apply, hLm] at e
    exact e
  have h3' : ((g ^ (mo % L)) ⟨p, hp⟩).val = p := congrArg Fin.val h3
  rw [e2, h3', Nat.beq_refl] at h2
  exact Bool.noConfusion h2

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

@[expose] def ApR (n w : Nat) (xs : List Nat) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ q : Fin n, apR w (mask w) xs q = g q

@[expose] def ApL (n w : Nat) (xs : List Nat) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ q : Fin n, apL w (mask w) xs q = g q

theorem apR_nil : ApR n w [] 1 := fun _ => rfl

theorem apL_nil : ApL n w [] 1 := fun _ => rfl

theorem apR_cons {t : Nat} {xs : List Nat} {g h : Equiv.Perm (Fin n)} (ht : PRep n w t g)
    (hx : ApR n w xs h) : ApR n w (t :: xs) (g * h) := fun q => by
  change strictN (apR w (mask w) xs q) (fun y => pg w (mask w) t y) = _
  rw [strictN_eq, hx q, ht (h q)]
  rfl

theorem apL_cons {t : Nat} {xs : List Nat} {g h : Equiv.Perm (Fin n)} (ht : PRep n w t g)
    (hx : ApL n w xs h) : ApL n w (t :: xs) (h * g) := fun q => by
  change strictN (pg w (mask w) t q) (fun y => apL w (mask w) xs y) = _
  rw [strictN_eq, ht q, hx (g q)]
  rfl

theorem elemRP_mul (LR TR : Nat → Nat) : ∀ (d j : Nat) (acc : Equiv.Perm (Fin n)),
    elemRP n w LR TR d j acc = elemRP n w LR TR d j 1 * acc
  | 0, _, _ => (one_mul _).symm
  | d + 1, j, acc => by
    rw [elemRP, elemRP, elemRP_mul LR TR d _ (_ * acc), elemRP_mul LR TR d _ (_ * 1), mul_one,
      mul_assoc]

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem apR_tsK : ∀ d ≤ k, ∀ (j : Nat) (acc : List Nat) (a : Equiv.Perm (Fin n)), ApR n w acc a →
    ApR n w (tsK n (n * w) LR TR d j acc) (elemRP n w LR TR d j a)
  | 0, _, _, _, _, h => h
  | d + 1, hd, j, acc, a, h => by
    rw [tsK_succ, elemRP]
    exact apR_tsK d (by omega) _ _ _ (apR_cons ((chainK_agree hQ (by omega)).2 _
      (Nat.mod_lt j (rcnt_pos hQ (by omega)))).1 h)

theorem apL_tsK : ∀ d ≤ k, ∀ (j : Nat) (acc : List Nat) (a : Equiv.Perm (Fin n)), ApL n w acc a →
    ApL n w (tsK n (n * w) LR TRI d j acc) (a * (elemRP n w LR TR d j 1)⁻¹)
  | 0, _, _, acc, a, h => by
    change ApL n w acc (a * (1 : Equiv.Perm (Fin n))⁻¹)
    simpa using h
  | d + 1, hd, j, acc, a, h => by
    rw [tsK_succ, elemRP, elemRP_mul LR TR d _ (_ * 1), mul_one, mul_inv_rev, ← mul_assoc]
    exact apL_tsK d (by omega) _ _ _ (apL_cons ((chainK_agree hQ (by omega)).2 _
      (Nat.mod_lt j (rcnt_pos hQ (by omega)))).2 h)

end Chain

theorem chainK_oddPt (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {mo L NB : Nat} {W : Nat → Nat}
    (hL : ordK LR k ≤ NB * L)
    (h : ∀ s < NB, oddPK n w (mask w) (n * w) (pidn n w) LR TR TRI k mo W (s * L) L = true) :
    oddWitnessOK n mo (allTables (certificate hn gens words bv hbs)) = true := by
  set Q := certificate hn gens words bv hbs
  set N := ordK LR k
  have h32 := chainK_h32 hQ
  have hA := forall₂_allTables_elem hQ hn hbs
  have hlen := hA.length_eq
  rw [oddWitnessOK, List.all_eq_true]
  intro X hX
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hX
  have hiN : i < N := by
    rw [hlen] at hi
    simpa using hi
  set j := N - 1 - i with hjdef
  have hj : j < N := by omega
  have hRi : Rep n (allTables Q)[i] (elemP n w LR TR k j) := by
    have := hA.get hi (by simpa [← hlen] using hi)
    simp only [List.get_eq_getElem, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range] at this
    convert this using 2
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.mul_zero] at hL
      omega
    · exact h0
  have hs : j / L < NB := (Nat.div_lt_iff_lt_mul hLpos).2 (by omega)
  have hb := h (j / L) hs
  unfold oddPK at hb
  rw [allBlk_eq, List.all_eq_true] at hb
  have hone := hb (j % L) (List.mem_range.2 (Nat.mod_lt j hLpos))
  rw [Nat.div_add_mod' j L] at hone
  have hxR := apR_tsK hQ k le_rfl j [] 1 apR_nil
  unfold oddPtOne at hone
  simp only [Orb.strictB_eq, bIf_eq, bindL_eq] at hone
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  split_ifs at hone with ht0 hp ht1 ht2
  ·
    left; left; left
    have e : elemP n w LR TR k j = 1 := by
      have hk := prep_elemK hQ j
      rw [Nat.eq_of_beq_eq_true hone] at hk
      exact MOC.prep_unique hk (prep_pidn (chainK_n24 hQ) hQ.2.1)
    exact (CFSG.Sporadic.SmallOddCore.tblEq_idT_iff h32 hRi).2 e
  ·
    left; left; right
    have hne := pow_ne_one_of_movesK hxR (Nat.blt_eq.mp hp) hone
    have hpw := powFixW_iff perm_faithful (List.Forall₂.cons hRi List.Forall₂.nil) mo
    simp only [List.prod_cons, List.prod_nil, mul_one] at hpw
    cases e : powFixW n [(allTables Q)[i]] mo
    · rfl
    · exact absurd (hpw.1 e) hne
  ·
    left; right
    have hmv := hone
    have hp' := Nat.blt_eq.mp hp
    set hI := Nat.div (W j) 67108864
    set x := elemP n w LR TR k j
    set y := elemP n w LR TR k hI
    have hhR := apR_tsK hQ k le_rfl hI [] 1 apR_nil
    have hhL := apL_tsK hQ k le_rfl hI [] 1 apL_nil
    rw [one_mul] at hhL
    have hf : ∀ q : Fin n, apR w (mask w) (tsK n (n * w) LR TR k j [])
        (apR w (mask w) (tsK n (n * w) LR TR k hI [])
          (apR w (mask w) (tsK n (n * w) LR TR k j [])
            (apL w (mask w) (tsK n (n * w) LR TRI k hI []) q))) = ([x, y, x, y⁻¹].prod) q := by
      intro q
      rw [hhL q, hxR, hhR, hxR]
      simp [x, y, elemP]
    have hne := pow_ne_one_of_movesK hf hp' hmv
    have hyQ : y ∈ ((List.range N).map (elemP n w LR TR k)).reverse := by
      rw [List.mem_reverse, mem_elemP_iff hQ hn hbs]
      exact elemP_mem hQ hn hbs hI
    obtain ⟨H, hH, hHR⟩ := exists_mem_of_forall₂_left hA y hyQ
    have hinv := invOK_invT_of_rep h32 hHR
    have hHi := Rep.inv_of_invOK hHR hinv
    rw [List.any_eq_true]
    refine ⟨H, hH, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hinv, ?_⟩
    have hpw := powFixW_iff perm_faithful (List.Forall₂.cons hRi (List.Forall₂.cons hHR
      (List.Forall₂.cons hRi (List.Forall₂.cons hHi List.Forall₂.nil)))) mo
    cases e : powFixW n [(allTables Q)[i], H, (allTables Q)[i], invT n H] mo
    · rfl
    · exact absurd (hpw.1 e) hne

end CFSG.KS.SporSch.OddPt

end
