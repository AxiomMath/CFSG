module

public import CFSG.Certificates.Kernel.S5Ext.Sound
public import CFSG.CGT.PushingUpLit.J42.S5ExtRefl

public section

namespace CFSG.KD.S5Ext

open CFSG.CGT.PushingUpLit.SolK

theorem extraMulFin_val (i j : Fin 32) : (extraMulFin i j).val = pm i.val j.val := by
  change extraMul i.val j.val % 32 = pm i.val j.val
  exact Nat.mod_eq_of_lt (pm_lt i j)

@[expose] def toF (f : Nat → Nat) (x : Fin 32) : Fin 32 := ⟨f x.val % 32, Nat.mod_lt _ (by decide)⟩

theorem toF_val {f : Nat → Nat} (hf : IsAutN f) (x : Fin 32) : (toF f x).val = f x.val :=
  Nat.mod_eq_of_lt (hf.1 _ x.isLt)

theorem toF_hom {f : Nat → Nat} (hf : IsAutN f) (i j : Fin 32) :
    toF f (extraMulFin i j) = extraMulFin (toF f i) (toF f j) := by
  apply Fin.ext
  rw [extraMulFin_val, toF_val hf, toF_val hf, toF_val hf, extraMulFin_val]
  exact hf.2.1 _ _ i.isLt j.isLt

theorem toF_injective {f : Nat → Nat} (hf : IsAutN f) : Function.Injective (toF f) := by
  intro x y h
  have h' := congrArg Fin.val h
  rw [toF_val hf, toF_val hf] at h'
  exact Fin.ext (hf.2.2 _ _ x.isLt y.isLt h')

theorem pmul_zero_zero : S5Ext.pmul 0 0 = 0 := by decide

theorem hom_zero {f : Fin 32 → Fin 32} (hf : ∀ i j, f (extraMulFin i j) = extraMulFin (f i) (f j)) :
    f 0 = 0 := by
  apply S5Ext.pmul_self_eq
  rw [S5Ext.pmul_eq, ← hf, ← S5Ext.pmul_eq, pmul_zero_zero]

theorem toF_eq_of_key {f g : Nat → Nat} {k : Nat} (hf : IsAutN f) (hg : IsAutN g)
    (hfk : HasKey f k) (hgk : HasKey g k) : toF f = toF g := by
  have hf' := toF_hom hf
  have hg' := toF_hom hg
  refine S5Ext.hom_ext_gens _ _ (fun i j => hf' i j) (fun i j => hg' i j) (hom_zero hf')
    (hom_zero hg') ?_ ?_ ?_ ?_
  · exact Fin.ext ((toF_val hf 1).trans (hfk.1.trans (hgk.1.symm.trans (toF_val hg 1).symm)))
  · exact Fin.ext ((toF_val hf 2).trans (hfk.2.1.trans (hgk.2.1.symm.trans (toF_val hg 2).symm)))
  · exact Fin.ext ((toF_val hf 8).trans
      (hfk.2.2.1.trans (hgk.2.2.1.symm.trans (toF_val hg 8).symm)))
  · exact Fin.ext ((toF_val hf 16).trans
      (hfk.2.2.2.trans (hgk.2.2.2.symm.trans (toF_val hg 16).symm)))

theorem and31 (x : Nat) : x &&& 31 = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5

theorem key_eq_of_fields {k k' : Nat} (hk : k < 2 ^ 20) (hk' : k' < 2 ^ 20)
    (h1 : k >>> 15 = k' >>> 15) (h2 : (k >>> 10) &&& 31 = (k' >>> 10) &&& 31)
    (h3 : (k >>> 5) &&& 31 = (k' >>> 5) &&& 31) (h4 : k &&& 31 = k' &&& 31) : k = k' := by
  rw [and31, and31] at h2 h3 h4
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow] at h1 h2 h3 h4 hk hk'
  omega

theorem keyN_fields {a b c d : Nat} (ha : a < 32) (hb : b < 32) (hc : c < 32) (hd : d < 32) :
    keyN a b c d >>> 15 = a ∧ (keyN a b c d >>> 10) &&& 31 = b ∧ (keyN a b c d >>> 5) &&& 31 = c ∧
      keyN a b c d &&& 31 = d := by
  simp only [and31, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  unfold keyN
  omega

end CFSG.KD.S5Ext
