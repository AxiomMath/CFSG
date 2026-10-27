module

public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.Asch54

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier.Co3
  CFSG.KS.Raw

theorem co3_sep
    {S : Array (Array Nat)} {base : Array Nat}
    (hS : ∀ j < S.size, permOfArr 276 S[j]! ∈ co3P)
    (hb : ∀ i < co3ChainBaseArr.size, ∃ t < base.size, base[t]! = co3ChainBaseArr[i]!) :
    Sep 276 S base := by
  intro G hG hfix
  have hGP : G ∈ co3P := by
    refine (Subgroup.closure_le _).2 ?_ hG
    rintro _ ⟨j, hj, rfl⟩
    exact hS j hj
  refine co3Chain.eq_one_of_fixes_base co3Chain_valid.1 hGP fun i => ?_
  have hv : ((co3Chain.base.get i : Fin 276) : ℕ) = co3ChainBaseArr[(i : ℕ)]! :=
    co3ChainArrays.base_val i
  have hi : (i : ℕ) < co3ChainBaseArr.size := lt_of_lt_of_eq i.2 rfl
  obtain ⟨t, ht, hbt⟩ := hb i hi
  have hlt : base[t]! < 276 := hbt ▸ hv ▸ (co3Chain.base.get i).2
  have e : co3Chain.base.get i = ⟨base[t]!, hlt⟩ := Fin.ext (hv.trans hbt.symm)
  rw [e]
  exact hfix t ht hlt

end CFSG.KS.Asch54

end
