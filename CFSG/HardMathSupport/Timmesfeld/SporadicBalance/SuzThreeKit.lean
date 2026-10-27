module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeKit

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Certificates.ChainArrays

variable {n : ℕ}

@[expose] def fltOK : Option (Array ℕ) → ℕ → Bool
  | none, _ => true
  | some f, q => f[q]! == q

@[expose] def fsearch (n : ℕ) (L : Array Level) (base : Array ℕ)
    (rels : Array (Option (ℕ × Array ℕ))) (flt : Array (Option (Array ℕ)))
    (pred : Array ℕ → Bool) : ℕ → ℕ → Array ℕ → Array ℕ → List (Array ℕ)
  | 0, _, acc, _ => if pred acc then [acc] else []
  | fuel + 1, i, acc, accI =>
    match rels.getD i none with
    | some (j, y) =>
      if (L[i]!).pos[accI[y[acc[base[j]!]!]!]!]! < (L[i]!).pts.size then
        fsearch n L base rels flt pred fuel (i + 1)
          (compA n acc (L[i]!).tr[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]!)
          (compA n (L[i]!).trInv[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]! accI)
      else []
    | none =>
      (List.range (L[i]!).pts.size).flatMap fun k =>
        if fltOK (flt.getD i none) acc[((L[i]!).tr[k]!)[base[i]!]!]! then
          fsearch n L base rels flt pred fuel (i + 1) (compA n acc (L[i]!).tr[k]!)
            (compA n (L[i]!).trInv[k]! accI)
        else []

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem fsearch_spec {rels : Array (Option (ℕ × Array ℕ))} {flt : Array (Option (Array ℕ))}
    {pred : Array ℕ → Bool} {c : Equiv.Perm (Fin n)}
    (hrel : ∀ l (hl : l < Q.baseCount) j y, rels.getD l none = some (j, y) →
      ∃ hj : j < l, ∃ Y : Equiv.Perm (Fin n), Rep n y Y ∧
        c (Q.base.get ⟨l, hl⟩) = Y (c (Q.base.get ⟨j, by omega⟩)))
    (hflt : ∀ l (hl : l < Q.baseCount) f, flt.getD l none = some f →
      ∃ F : Equiv.Perm (Fin n), Rep n f F ∧ F (c (Q.base.get ⟨l, hl⟩)) = c (Q.base.get ⟨l, hl⟩))
    (hpred : ∀ a, Rep n a c → pred a = true) :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc accI : Array ℕ) (A : Equiv.Perm (Fin n)),
      Rep n acc A → Rep n accI A⁻¹ → A⁻¹ * c ∈ Q.levelSubgroup i →
      ∃ e ∈ fsearch n (rawLevels n S base) base rels flt pred fuel i acc accI, Rep n e c := by
  have hbase : ∀ m (hm : m < Q.baseCount), ((Q.base.get ⟨m, hm⟩ : Fin n) : ℕ) = base[m]! :=
    fun m hm => hA.base_val ⟨m, hm⟩
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc accI A hacc _ hh
    rw [Nat.add_zero] at hi
    subst hi
    rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot, inv_mul_eq_one] at hh
    subst hh
    have hp := hpred acc hacc
    refine ⟨acc, ?_, hacc⟩
    simp [fsearch, hp]
  | succ fuel ih =>
    intro i hi acc accI A hacc haccI hh
    have hib : i < Q.baseCount := by omega
    set h := A⁻¹ * c with hhdef
    obtain ⟨hk, hk'⟩ := Co2T.levT_pos_inv_mul_mem hA hF hQ hib hh
    set k := (lev n S base i).pos[((h (Q.base.get ⟨i, hib⟩) : Fin n) : ℕ)]! with hkdef
    have hrepT : Rep n ((rawLevels n S base)[i]!).tr[k]! (levT n S base i k) :=
      hA.rep_levT hF hib hk
    have hrepTI : Rep n ((rawLevels n S base)[i]!).trInv[k]! (levT n S base i k)⁻¹ :=
      hA.rep_levTInv hF hib hk
    have hacc' : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc hrepT
    have haccI' : Rep n (compA n ((rawLevels n S base)[i]!).trInv[k]! accI)
        (A * levT n S base i k)⁻¹ := by
      rw [mul_inv_rev]
      exact rep_compA hrepTI haccI
    have hh' : (A * levT n S base i k)⁻¹ * c ∈ Q.levelSubgroup (i + 1) := by
      rw [mul_inv_rev, mul_assoc]
      exact hk'
    obtain ⟨e, he, hre⟩ := ih (i + 1) (by omega) _ _ _ hacc' haccI' hh'
    refine ⟨e, ?_, hre⟩
    cases hr : rels.getD i none with
    | none =>
      have hfixi : ((A * levT n S base i k)⁻¹ * c) (Q.base.get ⟨i, hib⟩) =
          Q.base.get ⟨i, hib⟩ :=
        Q.levelSubgroup_fixes_base_index (i + 1) _ hh' ⟨i, hib⟩ (Nat.lt_succ_self i)
      have hci : c (Q.base.get ⟨i, hib⟩) = (A * levT n S base i k) (Q.base.get ⟨i, hib⟩) := by
        have : c = (A * levT n S base i k) * ((A * levT n S base i k)⁻¹ * c) := by group
        conv_lhs => rw [this]
        rw [Equiv.Perm.mul_apply, hfixi]
      have hq : acc[(((rawLevels n S base)[i]!).tr[k]!)[base[i]!]!]! =
          ((c (Q.base.get ⟨i, hib⟩) : Fin n) : ℕ) := by
        rw [← hbase i hib, hrepT, hacc, hci, Equiv.Perm.mul_apply]
      have hok : fltOK (flt.getD i none) acc[(((rawLevels n S base)[i]!).tr[k]!)[base[i]!]!]! =
          true := by
        cases hf : flt.getD i none with
        | none => rfl
        | some f =>
          obtain ⟨F, hFr, hFc⟩ := hflt i hib f hf
          rw [hq]
          simp only [fltOK, beq_iff_eq]
          rw [hFr, hFc]
      simp only [fsearch, hr, List.mem_flatMap, List.mem_range]
      refine ⟨k, hk, ?_⟩
      rw [ite_eq_left hok]
      exact he
    | some jy =>
      obtain ⟨j, y⟩ := jy
      obtain ⟨hj, Y, hY, hcY⟩ := hrel i hib j y hr
      have hfixj : h (Q.base.get ⟨j, by omega⟩) = Q.base.get ⟨j, by omega⟩ :=
        Q.levelSubgroup_fixes_base_index i h hh ⟨j, by omega⟩ hj
      have hcj : c (Q.base.get ⟨j, by omega⟩) = A (Q.base.get ⟨j, by omega⟩) := by
        have : c = A * h := by rw [hhdef]; group
        rw [this, Equiv.Perm.mul_apply, hfixj]
      have hq : accI[y[acc[base[j]!]!]!]! = ((h (Q.base.get ⟨i, hib⟩) : Fin n) : ℕ) := by
        rw [← hbase j (by omega), hacc, ← hcj, hY, ← hcY, haccI, hhdef, Equiv.Perm.mul_apply]
      have hpos : ((rawLevels n S base)[i]!).pos[accI[y[acc[base[j]!]!]!]!]! = k := by
        rw [hq]
        rfl
      simp only [fsearch, hr]
      rw [hpos, ite_eq_left (by exact hk)]
      exact he

theorem exists_mem_fsearch {rels : Array (Option (ℕ × Array ℕ))} {flt : Array (Option (Array ℕ))}
    {pred : Array ℕ → Bool} {c : Equiv.Perm (Fin n)} (hc : c ∈ Q.originalSubgroup)
    (hrel : ∀ l (hl : l < Q.baseCount) j y, rels.getD l none = some (j, y) →
      ∃ hj : j < l, ∃ Y : Equiv.Perm (Fin n), Rep n y Y ∧
        c (Q.base.get ⟨l, hl⟩) = Y (c (Q.base.get ⟨j, by omega⟩)))
    (hflt : ∀ l (hl : l < Q.baseCount) f, flt.getD l none = some f →
      ∃ F : Equiv.Perm (Fin n), Rep n f F ∧ F (c (Q.base.get ⟨l, hl⟩)) = c (Q.base.get ⟨l, hl⟩))
    (hpred : ∀ a, Rep n a c → pred a = true) :
    ∃ e ∈ fsearch n (rawLevels n S base) base rels flt pred base.size 0 (idA n) (idA n),
      Rep n e c := by
  rw [hA.base_size]
  refine fsearch_spec hA hF hQ hrel hflt hpred Q.baseCount 0 (by omega) (idA n) (idA n) 1 rep_idA
    (by rw [inv_one]; exact rep_idA) ?_
  rw [inv_one, one_mul, Q.levelSubgroup_zero_eq_original hQ]
  exact hc

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
