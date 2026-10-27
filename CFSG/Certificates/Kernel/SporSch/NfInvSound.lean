module

public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
import CFSG.Certificates.Kernel.SporSch.TabChainLv

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier

variable {n : Nat}

theorem nfInv4_sound {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs : List Nat}
    (hT : TabChain n w kS 4 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs) {F : Nat}
    (hF : nfValidK 4 LR F = true) :
    RepF n (fun x =>
      strictN (trInvPtT w kS NR NL LT PT (nat_lit 0) fld(F, nat_lit 0, nat_lit 65535) x)
      (fun y => strictN (trInvPtT w kS NR NL LT PT (nat_lit 1) fld(F, nat_lit 16, nat_lit 65535) y)
      (fun z => strictN (trInvPtT w kS NR NL LT PT (nat_lit 2) fld(F, nat_lit 32, nat_lit 65535) z)
      (fun v => trInvPtT w kS NR NL LT PT (nat_lit 3) fld(F, nat_lit 48, nat_lit 65535) v))))
      (nfElt n S base (nfArr 4 F))⁻¹ := by
  obtain ⟨hb, hp, ho, hN, htab, -⟩ := hT
  have hv : ∀ t < 4, F / 2 ^ (16 * t) % 65536 < rcnt (LR t) := fun t ht' => by
    have := allN_spec hF t ht'
    rw [Tab.fld16] at this
    exact Nat.blt_eq.mp this
  have hI : ∀ i < 4, ∀ z (hz : z < n), trInvPtT w kS NR NL LT PT i (F / 2 ^ (16 * i) % 65536) z =
      ((levT n S base i (F / 2 ^ (16 * i) % 65536))⁻¹ ⟨z, hz⟩ : Nat) := fun i hi z hz => by
    rw [Tab.trInvPtT_eq hb hp ho hN htab hi (hv i hi) ⟨z, hz⟩,
      ← Tab.trT_eq_levT hb hp ho hN hi (hv i hi)]
  have hE : nfElt n S base (nfArr 4 F) = levT n S base 0 (F / 2 ^ (16 * 0) % 65536) *
      (levT n S base 1 (F / 2 ^ (16 * 1) % 65536) * (levT n S base 2 (F / 2 ^ (16 * 2) % 65536) *
        levT n S base 3 (F / 2 ^ (16 * 3) % 65536))) := by
    simp only [nfElt, nfArr, Array.size_ofFn, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc]
    rw [getElem!_ofFn_nat _ (by norm_num), getElem!_ofFn_nat _ (by norm_num),
      getElem!_ofFn_nat _ (by norm_num), getElem!_ofFn_nat _ (by norm_num)]
    rfl
  have f0 : fld(F, nat_lit 0, nat_lit 65535) = F / 2 ^ (16 * 0) % 65536 := Tab.fld16 F 0
  have f1 : fld(F, nat_lit 16, nat_lit 65535) = F / 2 ^ (16 * 1) % 65536 := Tab.fld16 F 16
  have f2 : fld(F, nat_lit 32, nat_lit 65535) = F / 2 ^ (16 * 2) % 65536 := Tab.fld16 F 32
  have f3 : fld(F, nat_lit 48, nat_lit 65535) = F / 2 ^ (16 * 3) % 65536 := Tab.fld16 F 48
  intro x hx
  simp only [strictN_val]
  rw [f0, f1, f2, f3, hE, hI 0 (by norm_num) x hx]
  set a := (levT n S base 0 (F / 2 ^ (16 * 0) % 65536))⁻¹ ⟨x, hx⟩
  rw [hI 1 (by norm_num) _ a.2]
  set b := (levT n S base 1 (F / 2 ^ (16 * 1) % 65536))⁻¹ ⟨(a : Nat), a.2⟩
  rw [hI 2 (by norm_num) _ b.2]
  set c := (levT n S base 2 (F / 2 ^ (16 * 2) % 65536))⁻¹ ⟨(b : Nat), b.2⟩
  rw [hI 3 (by norm_num) _ c.2]
  simp only [mul_inv_rev, Equiv.Perm.mul_apply, a, b, c, Fin.eta]

end CFSG.KS.SporSch

end
