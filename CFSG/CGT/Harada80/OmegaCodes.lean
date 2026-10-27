module

public import CFSG.Quasithin.SteinbergCBI16Gen
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.CGT.Harada80

open CFSG.Quasithin.SteinbergCB.G2Two

@[expose] def codeIdx (m : ℕ) : Fin m ⊕ Fin m ⊕ Fin 2 ≃ Fin (m + (m + 2)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

@[expose] def vec (m x : ℕ) : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2 := toV (m + (m + 2)) x ∘ codeIdx m

@[expose] def code {m : ℕ} (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) : ℕ := ofV (v ∘ (codeIdx m).symm)

@[expose] def polarCode (m x y : ℕ) : ZMod 2 :=
  CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m x + vec m y) -
    CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m x) -
      CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m y)

@[expose] def reflCode (m u x : ℕ) : ℕ := code (vec m x + polarCode m x u • vec m u)

@[expose] def reflChain (m : ℕ) (cs : List ℕ) (x : ℕ) : ℕ := cs.foldr (reflCode m) x

@[expose] def wordCols {k : ℕ} (d : ℕ) (cols : List (List ℕ)) : List (Fin k) → List ℕ
  | [] => (List.range d).map (2 ^ ·)
  | i :: w => mComp (cols.getD i []) (wordCols d cols w)

theorem vec_code {m : ℕ} (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) : vec m (code v) = v := by
  funext a
  simp only [vec, code, Function.comp_apply, toV_ofV, Equiv.symm_apply_apply]

theorem code_lt {m : ℕ} (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) : code v < 2 ^ (m + (m + 2)) :=
  ofV_lt _

theorem vec_xor (m x y : ℕ) : vec m (x ^^^ y) = vec m x + vec m y := by
  funext a
  simp only [vec, Function.comp_apply, toV_xor, Pi.add_apply]

theorem vec_zero (m : ℕ) : vec m 0 = 0 := by
  funext a
  simp only [vec, Function.comp_apply, toV_zero, Pi.zero_apply]

theorem vec_inj {m x y : ℕ} (hx : x < 2 ^ (m + (m + 2))) (hy : y < 2 ^ (m + (m + 2)))
    (h : vec m x = vec m y) : x = y := by
  apply toV_inj hx hy
  funext a
  have := congrFun h ((codeIdx m).symm a)
  simpa only [vec, Function.comp_apply, Equiv.apply_symm_apply] using this

theorem vec_reflCode (m u x : ℕ) :
    vec m (reflCode m u x) = vec m x + polarCode m x u • vec m u := by
  unfold reflCode
  exact vec_code _

theorem reflCode_lt (m u x : ℕ) : reflCode m u x < 2 ^ (m + (m + 2)) :=
  code_lt _

theorem mApp_range_pow {d x : ℕ} (hx : x < 2 ^ d) : mApp ((List.range d).map (2 ^ ·)) x = x := by
  have step : ∀ (M : List ℕ) (y : ℕ), mApp (M.map (fun c => c <<< 1)) y = mApp M y <<< 1 := by
    intro M
    induction M with
    | nil => intro y; simp [mApp]
    | cons c cs ih =>
      intro y
      simp only [List.map_cons, mApp]
      rw [ih (y / 2), Nat.shiftLeft_xor_distrib]
      by_cases hy : y % 2 = 1
      · simp only [hy, if_true]
      · simp only [hy, if_false, Nat.zero_xor]
        rw [Nat.shiftLeft_eq]
        norm_num
  induction d generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    simp [mApp]
  | succ d ih =>
    have hx' : x / 2 < 2 ^ d := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      simpa [Nat.pow_succ, Nat.mul_comm] using hx
    have hlow : (if x % 2 = 1 then 1 else 0) ^^^ ((x / 2) <<< 1) = x := by
      have hxmod : x = 2 * (x / 2) + x % 2 := by
        have := Nat.div_add_mod x 2
        omega
      have hshift : (x / 2) <<< 1 = 2 * (x / 2) := by
        rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
      rw [hshift]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · rw [if_neg (by omega), Nat.zero_xor]
        omega
      · rw [if_pos h, Nat.xor_comm, Nat.xor_one_of_even (even_two_mul (x / 2))]
        omega
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    change mApp (2 ^ 0 :: List.map (fun j => 2 ^ (j + 1)) (List.range d)) x = x
    have htail : (List.range d).map (fun j => 2 ^ (j + 1)) =
        ((List.range d).map (fun j => 2 ^ j)).map (fun c => c <<< 1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      change 2 ^ (j + 1) = 2 ^ j <<< 1
      rw [Nat.pow_succ, Nat.shiftLeft_eq, Nat.pow_one]
    rw [htail]
    simp only [Nat.pow_zero, mApp]
    rw [step, ih hx']
    exact hlow

theorem wordCols_lt {k d : ℕ} {cols : List (List ℕ)}
    (hcols : ∀ i : Fin k, ∀ c ∈ cols.getD i [], c < 2 ^ d) (w : List (Fin k)) :
    ∀ c ∈ wordCols d cols w, c < 2 ^ d := by
  induction w with
  | nil =>
    intro c hc
    simp only [wordCols, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    exact Nat.pow_lt_pow_right (by norm_num) hj
  | cons i w ih =>
    intro c hc
    simp only [wordCols, mComp, List.mem_map] at hc
    obtain ⟨n, _, rfl⟩ := hc
    exact CFSG.Quasithin.SteinbergCB.I16.mApp_lt_pow _ (hcols i) n

theorem mApp_wordCols_cons {k d : ℕ} (cols : List (List ℕ)) (i : Fin k) (w : List (Fin k)) (x : ℕ) :
    mApp (wordCols d cols (i :: w)) x = mApp (cols.getD i []) (mApp (wordCols d cols w) x) := by
  simp only [wordCols]
  exact mApp_mComp _ _ _

end CFSG.CGT.Harada80
