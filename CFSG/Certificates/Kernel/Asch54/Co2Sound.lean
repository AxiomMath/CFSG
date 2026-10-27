module

public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.Asch54

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert
  CFSG.KS.Raw

theorem co2_fix {base : Array Nat}
    (hb : ∀ i < co2BaseArr.size, ∃ t < base.size, base[t]! = co2BaseArr[i]!)
    {G : Equiv.Perm (Fin 2300)} (hG : G ∈ co2P)
    (hfix : ∀ t < base.size, ∀ h : base[t]! < 2300, G ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) :
    G = 1 := by
  rw [← co2Q_originalSubgroup] at hG
  refine co2Q.eq_one_of_fixes_base co2Q_valid.1 hG fun i => ?_
  have hv : ((co2Q.base.get i : Fin 2300) : ℕ) = co2BaseArr[(i : ℕ)]! :=
    co2Q_chainArrays.base_val i
  have hi : (i : ℕ) < co2BaseArr.size := lt_of_lt_of_eq i.2 rfl
  obtain ⟨t, ht, hbt⟩ := hb i hi
  have hlt : base[t]! < 2300 := hbt ▸ hv ▸ (co2Q.base.get i).2
  have e : co2Q.base.get i = ⟨base[t]!, hlt⟩ := Fin.ext (hv.trans hbt.symm)
  rw [e]
  exact hfix t ht hlt

theorem co2_sep
    {S : Array (Array Nat)} {base : Array Nat}
    (hS : ∀ j < S.size, permOfArr 2300 S[j]! ∈ co2P)
    (hb : ∀ i < co2BaseArr.size, ∃ t < base.size, base[t]! = co2BaseArr[i]!) :
    Sep 2300 S base := by
  intro G hG hfix
  have hGP : G ∈ co2P := by
    refine (Subgroup.closure_le _).2 ?_ hG
    rintro _ ⟨j, hj, rfl⟩
    exact hS j hj
  exact co2_fix hb hGP hfix

end CFSG.KS.Asch54

end
