module

public import CFSG.Certificates.Kernel.He7222.StackSound
public import CFSG.Sporadic.Schreier.PairWords
import CFSG.Certificates.Kernel.Misc.WordPtsGroup

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.Sporadic.Schreier

variable {n w : ℕ}

theorem evK_append (w m : ℕ) : ∀ (l l' : List ℕ) (q : ℕ),
    evK w m (l ++ l') q = evK w m l (evK w m l' q)
  | [], _, _ => rfl
  | a :: l, l', q => by
    have e1 : evK w m (a :: l ++ l') q = pg w m a (evK w m (l ++ l') q) := rfl
    have e2 : evK w m (a :: l) (evK w m l' q) = pg w m a (evK w m l (evK w m l' q)) := rfl
    rw [e1, e2, evK_append w m l l' q]

theorem foldl_eq_evK (w m : ℕ) : ∀ (ts : List ℕ) (q : ℕ),
    ts.foldl (fun q t => pg w m t q) q = evK w m ts.reverse q
  | [], _ => rfl
  | t :: ts, q => by
    rw [List.foldl_cons, foldl_eq_evK w m ts, List.reverse_cons, evK_append]
    rfl

theorem eq_of_keyF {H : Subgroup (Equiv.Perm (Fin n))} (hH : BaseFaithful H [0, 1, 2, 3, 4])
    (hnw : n ≤ 2 ^ w) {f f' : ℕ → ℕ} {g h : Equiv.Perm (Fin n)} (hg : g ∈ H) (hh : h ∈ H)
    (hf : ∀ p : Fin n, (p : ℕ) < 5 → f p = g p) (hf' : ∀ p : Fin n, (p : ℕ) < 5 → f' p = h p)
    (h5 : 5 ≤ n) (he : keyF w f 5 = keyF w f' 5) : g = h := by
  have hb : ∀ k < 5, f k < 2 ^ w := fun k hk => by
    rw [show k = ((⟨k, by omega⟩ : Fin n) : ℕ) from rfl, hf ⟨k, by omega⟩ hk]
    exact lt_of_lt_of_le (g _).2 hnw
  have hb' : ∀ k < 5, f' k < 2 ^ w := fun k hk => by
    rw [show k = ((⟨k, by omega⟩ : Fin n) : ℕ) from rfl, hf' ⟨k, by omega⟩ hk]
    exact lt_of_lt_of_le (h _).2 hnw
  have hk := keyF_inj hb hb' he
  refine CFSG.KC.WordPts.eq_of_pts hH hg hh fun p hp => ?_
  have hp5 : (p : ℕ) < 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  exact Fin.ext (by rw [← hf p hp5, ← hf' p hp5]; exact hk p hp5)

theorem keyF_const_zero (w : ℕ) : ∀ nf, keyF w (fun _ => 0) nf = 0
  | 0 => rfl
  | nf + 1 => by
    have e : keyF w (fun _ => 0) (nf + 1) = Nat.lor (keyF w (fun _ => 0) nf)
      (Nat.shiftLeft 0 (Nat.mul w nf)) := rfl
    rw [e, keyF_const_zero w nf]
    change (0 ||| 0 <<< (w * nf)) = 0
    simp

theorem keyF_ne_zero (hnw : n ≤ 2 ^ w) (h5 : 5 ≤ n) {f : ℕ → ℕ} {g : Equiv.Perm (Fin n)}
    (hf : ∀ p : Fin n, (p : ℕ) < 5 → f p = g p) : keyF w f 5 ≠ 0 := by
  intro h0
  have hb : ∀ k < 5, f k < 2 ^ w := fun k hk => by
    rw [show k = ((⟨k, by omega⟩ : Fin n) : ℕ) from rfl, hf ⟨k, by omega⟩ hk]
    exact lt_of_lt_of_le (g _).2 hnw
  have hk := keyF_inj (g := fun _ => 0) hb (fun _ _ => Nat.two_pow_pos w)
    (by rw [h0, keyF_const_zero])
  have e0 := hk 0 (by norm_num)
  have e1 := hk 1 (by norm_num)
  rw [show (0 : ℕ) = ((⟨0, by omega⟩ : Fin n) : ℕ) from rfl, hf ⟨0, by omega⟩ (by norm_num)] at e0
  rw [show (1 : ℕ) = ((⟨1, by omega⟩ : Fin n) : ℕ) from rfl, hf ⟨1, by omega⟩ (by norm_num)] at e1
  have : g ⟨0, by omega⟩ = g ⟨1, by omega⟩ := Fin.ext (by rw [e0, e1])
  have := congrArg Fin.val (g.injective this)
  simp at this

end CFSG.KC.HeChain

end
