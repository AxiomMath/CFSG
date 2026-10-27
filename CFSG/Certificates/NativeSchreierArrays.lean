module

public import CFSG.Certificates.NativeValidSchreier

public noncomputable section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n : ℕ}

@[expose] def RawSchreierDatum.ofArrays (n : ℕ) (hn : 1 ≤ n) (S : Array (Array ℕ)) (k : ℕ)
    (hk : k ≤ S.size) (base : List (Fin n)) (hb : base.Nodup) (W : Array (List ℤ)) :
    RawSchreierDatum n where
  degree_pos := hn
  originalCount := k
  strongCount := S.size
  baseCount := base.length
  originalCount_le := hk
  original := Vector.ofFn fun i : Fin k => permOfArr n S[(i : ℕ)]!
  strong := Vector.ofFn fun j : Fin S.size => permOfArr n S[(j : ℕ)]!
  base := ⟨base.toArray, by simp⟩
  base_distinct := by simpa using hb
  derivation j _ := toLetters j.val W[(j : ℕ)]!

section

variable {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size} {base : List (Fin n)}
  {hb : base.Nodup} {W : Array (List ℤ)}

theorem RawSchreierDatum.ofArrays_originalCount :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalCount = k := rfl

theorem RawSchreierDatum.ofArrays_strongCount :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).strongCount = S.size := rfl

theorem RawSchreierDatum.ofArrays_original_get
    (i : Fin (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalCount) :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).original.get i =
      permOfArr n S[(i : ℕ)]! := by
  simp [RawSchreierDatum.ofArrays, Vector.get]
  rfl

theorem RawSchreierDatum.ofArrays_strong_get
    (j : Fin (RawSchreierDatum.ofArrays n hn S k hk base hb W).strongCount) :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).strong.get j =
      permOfArr n S[(j : ℕ)]! := by
  have hj : (j : ℕ) < S.size := j.2
  simp [RawSchreierDatum.ofArrays, Vector.get]
  rw [getElem!_pos S (j : ℕ) hj]
  rfl

theorem RawSchreierDatum.ofArrays_base_toList :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).base.toList = base := by
  change (⟨base.toArray, _⟩ : Vector (Fin n) base.length).toList = base
  simp

theorem chainArrays_ofArrays (hinv : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true) :
    ChainArrays (RawSchreierDatum.ofArrays n hn S k hk base hb W) (S.extract 0 k) S
      (base.map Fin.val).toArray W where
  orig_size := by
    change (S.extract 0 k).size = k
    simp [Nat.min_eq_left hk]
  strong_size := rfl
  base_size := by
    change (base.map Fin.val).toArray.size = base.length
    simp
  orig i := by
    have hi : (i : ℕ) < k := i.2
    rw [RawSchreierDatum.ofArrays_original_get]
    have hext : (S.extract 0 k)[(i : ℕ)]! = S[(i : ℕ)]! := by
      rw [getElem!_pos _ _ (by simp [Nat.min_eq_left hk]; exact hi),
        getElem!_pos _ _ (by omega), Array.getElem_extract]
      simp
    rw [hext]
    exact (rep_permOfArr (hinv i (by omega))).1
  strong j := by
    rw [RawSchreierDatum.ofArrays_strong_get]
    exact (rep_permOfArr (hinv j j.2)).1
  base_val i := by
    have hi : (i : ℕ) < base.length := i.2
    change (((⟨base.toArray, _⟩ : Vector (Fin n) base.length).get i : Fin n) : ℕ) = _
    rw [getElem!_pos _ _ (by simpa using hi)]
    simp [Vector.get]
    rfl
  deriv _ _ := rfl

end

end CFSG.Certificates
