module

public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

@[expose] noncomputable def letC {A : Type} [Group A] (ga gb : A) (c : Nat) : A :=
  if Nat.beq c 0 then ga else if Nat.beq c 1 then gb else if Nat.beq c 2 then ga⁻¹ else gb⁻¹

@[expose] noncomputable def wC {A : Type} [Group A] (ga gb : A) (W : Nat) : Nat → A
  | 0 => 1
  | k + 1 => wC ga gb W k * letC ga gb (wl W k)

theorem lt_letC {a b ai bi : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w a ga)
    (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) (c q : Nat)
    (hq : q < n) :
    CFSG.KC.Enum.lt w (mask w) a b ai bi c q = (letC ga gb c ⟨q, hq⟩ : Nat) := by
  unfold CFSG.KC.Enum.lt letC
  simp only [PK.nIf_eq]
  by_cases h0 : Nat.beq c 0 = true
  · rw [if_pos h0, if_pos h0]
    exact ha ⟨q, hq⟩
  by_cases h1 : Nat.beq c 1 = true
  · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1]
    exact hb ⟨q, hq⟩
  by_cases h2 : Nat.beq c 2 = true
  · rw [if_neg h0, if_neg h1, if_pos h2, if_neg h0, if_neg h1, if_pos h2]
    exact hai ⟨q, hq⟩
  · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h0, if_neg h1, if_neg h2]
    exact hbi ⟨q, hq⟩

theorem foldN_letC {a b ai bi W : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w a ga)
    (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) :
    ∀ k q (hq : q < n), foldN k (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) q =
      (wC ga gb W k ⟨q, hq⟩ : Nat) := by
  intro k
  induction k with
  | zero => exact fun q hq => by rw [PK.foldN_eq]; rfl
  | succ k ih =>
    intro q hq
    have e : ∀ (f : Nat → Nat → Nat) (s : Nat), foldN (k + 1) f s = foldN k f (f k s) :=
      fun f s => by
        rw [PK.foldN_eq, PK.foldN_eq, List.range_succ, List.foldr_append, List.foldr_cons,
          List.foldr_nil]
    rw [e, lt_letC ha hai hb hbi _ q hq, ih _ (letC ga gb (wl W k) ⟨q, hq⟩).2]
    rfl

theorem wpt_eq_foldN (a b ai bi W : Nat) :
    ∀ len q, wpt w (mask w) a b ai bi W len q =
      foldN len (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) q := by
  intro len
  induction len with
  | zero => intro q; rw [PK.foldN_eq]; rfl
  | succ k ih =>
    intro q
    have e : ∀ (f : Nat → Nat → Nat) (s : Nat), foldN (k + 1) f s = foldN k f (f k s) :=
      fun f s => by
        rw [PK.foldN_eq, PK.foldN_eq, List.range_succ, List.foldr_append, List.foldr_cons,
          List.foldr_nil]
    rw [e, ← ih]
    change strictN _ _ = _
    rw [PF.strictN_eqP]
    rfl

theorem wpt_prep_code {a b ai bi W len : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w a ga)
    (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) (q : Nat)
    (hq : q < n) : wpt w (mask w) a b ai bi W len q = (wC ga gb W len ⟨q, hq⟩ : Nat) := by
  rw [wpt_eq_foldN]
  exact foldN_letC ha hai hb hbi len q hq

theorem wperm_prep_code {a b ai bi W len : Nat} {ga gb : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n ≤ 2 ^ w) (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb)
    (hbi : PRep n w bi gb⁻¹) :
    PRep n w (wperm n w (mask w) a b ai bi W len) (wC ga gb W len) := by
  have hf := foldN_letC (W := W) ha hai hb hbi len
  intro x
  set F : Nat → Nat := fun p =>
    foldN len (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) p
  have hF : ∀ y < n, F y < 2 ^ w := fun y hy => by
    change foldN len _ y < 2 ^ w
    rw [hf y hy]
    exact Nat.lt_of_lt_of_le (wC ga gb W len ⟨y, hy⟩).2 hw
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w F hF (clog n) 0
  have e : wperm n w (mask w) a b ai bi W len = pmkT n w F (clog n) 0 := by
    unfold wperm pmk
    rw [PF.strictN_eqP]
  have hx : (x : Nat) < 2 ^ clog n := Nat.lt_of_lt_of_le x.2 hc
  rw [e, PF.pg_of_fld h (by simp only [hx, ↓reduceIte, Nat.zero_add, x.2]; exact hF x x.2)]
  simp only [hx, ↓reduceIte, Nat.zero_add, x.2]
  exact hf x x.2

theorem wC_mem {A : Type} [Group A] (ga gb : A) (W : Nat) :
    ∀ len, wC ga gb W len ∈ Subgroup.closure ({ga, gb} : Set A) := by
  intro len
  induction len with
  | zero => exact Subgroup.one_mem _
  | succ k ih =>
    refine Subgroup.mul_mem _ ih ?_
    have hga : ga ∈ Subgroup.closure ({ga, gb} : Set A) := Subgroup.subset_closure (Set.mem_insert _ _)
    have hgb : gb ∈ Subgroup.closure ({ga, gb} : Set A) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    unfold letC
    split_ifs
    · exact hga
    · exact hgb
    · exact Subgroup.inv_mem _ hga
    · exact Subgroup.inv_mem _ hgb

end CFSG.KC.EnumSound

end
