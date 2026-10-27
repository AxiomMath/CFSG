
module

public import CFSG.Certificates.Kernel.M24L2.CtxSound
public import Certificates.Data.Kernel.M24L2.L2

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R

theorem ttC_lt {k : Nat} (hk : k < 16) : ttC k < 2 ^ 20 := by
  unfold ttC
  change k + 541200 < 2 ^ 20
  omega

theorem ctx_tt_tabC {k : Nat} (hk : k < 16) : (mkCtx ()).tt[k]! = tabC (ttC k) := ctx_tt' hk

theorem isTt_tabC {c : Nat} (hc : c < 2 ^ 20) : (mkCtx ()).isTt (tabC c) = isTtK c := by
  unfold Ctx8.isTt isTtK
  rw [codeOf_tabC hc, ctx_tt_tabC (Nat.mod_lt c (by norm_num)),
    beq_tabC hc (ttC_lt (Nat.mod_lt c (by norm_num)))]

theorem idT_beq {c : Nat} (hc : c < 2 ^ 20) : (tabC c == idT 16) = Nat.beq c idC := by
  rw [idT_tabC, beq_tabC hc (by decide)]

theorem relCheck_eq : relCheck = relCheckK := by
  unfold relCheck relCheckK
  congr 1
  funext r
  rw [wTab_tabC, idT_beq (cwK_lt r)]

theorem range16 {k : Nat} (hk : k ∈ List.range 16) : k < 16 := List.mem_range.1 hk

theorem xor_lt16' {k l : Nat} (hk : k < 16) (hl : l < 16) : k ^^^ l < 16 :=
  Nat.xor_lt_two_pow (n := 4) hk hl

theorem tCheck_eq : tCheck (mkCtx ()) = tCheckK := by
  unfold tCheck tCheckK
  have e1 : ((List.range 16).all fun k => (List.range 16).all fun l =>
      compT 16 (mkCtx ()).tt[k]! (mkCtx ()).tt[l]! == (mkCtx ()).tt[k ^^^ l]!) =
      (List.range 16).all fun k => (List.range 16).all fun l =>
        Nat.beq (mulC (ttC k) (ttC l)) (ttC (k ^^^ l)) := by
    refine all_mem_congr fun k hk => all_mem_congr fun l hl => ?_
    rw [ctx_tt_tabC (range16 hk), ctx_tt_tabC (range16 hl),
      ctx_tt_tabC (xor_lt16' (range16 hk) (range16 hl)), compT_tabC,
      beq_tabC (mulC_lt _ _) (ttC_lt (xor_lt16' (range16 hk) (range16 hl)))]
  have e2 : ((List.range 16).all fun k => (List.range 16).all fun l =>
      !((mkCtx ()).tt[k]! == (mkCtx ()).tt[l]!) || k == l) =
      (List.range 16).all fun k => (List.range 16).all fun l =>
        !(Nat.beq (ttC k) (ttC l)) || k == l := by
    refine all_mem_congr fun k hk => all_mem_congr fun l hl => ?_
    rw [ctx_tt_tabC (range16 hk), ctx_tt_tabC (range16 hl),
      beq_tabC (ttC_lt (range16 hk)) (ttC_lt (range16 hl))]
  have e3 : ((List.range 16).all fun k => codeOf (mkCtx ()).tt[k]! % 16 == k) =
      (List.range 16).all fun k => ttC k % 16 == k := by
    refine all_mem_congr fun k hk => ?_
    rw [ctx_tt_tabC (range16 hk), codeOf_tabC (ttC_lt (range16 hk))]
  rw [e1, e2, e3]

theorem tNormCheck_eq : tNormCheck (mkCtx ()) = tNormCheckK := by
  unfold tNormCheck tNormCheckK
  refine all_mem_congr fun j _ => all_mem_congr fun b _ =>
    all_mem_congr fun k hk => any_mem_congr fun l hl => ?_
  rw [letTab_tabC, ctx_tt_tabC (range16 hk), ctx_tt_tabC (range16 hl), compT_tabC, compT_tabC,
    beq_tabC (mulC_lt _ _) (mulC_lt _ _)]

theorem b0T_eq : b0T = tabC b0C := wTab_tabC _

theorem b1T_eq : b1T = tabC b1C := wTab_tabC _

theorem b01T_eq : b01T = tabC b01C := by
  unfold b01T b01C
  rw [b0T_eq, b1T_eq, compT_tabC]

theorem b0C_lt : b0C < 2 ^ 20 := cwK_lt _

theorem b1C_lt : b1C < 2 ^ 20 := cwK_lt _

theorem b01C_lt : b01C < 2 ^ 20 := mulC_lt _ _

theorem commT_tabC' (a b : Nat) : commT (tabC a) (tabC b) = commK a b := by
  unfold commT commK
  rw [compT_tabC, compT_tabC, beq_tabC (mulC_lt _ _) (mulC_lt _ _)]

theorem bCheck_eq : bCheck (mkCtx ()) = bCheckK := by
  unfold bCheck bCheckK
  rw [b01T_eq, b0T_eq, b1T_eq, compT_tabC, compT_tabC, idT_beq (mulC_lt _ _),
    idT_beq (mulC_lt _ _), commT_tabC', idT_beq b0C_lt, idT_beq b1C_lt, beq_tabC b0C_lt b1C_lt,
    idT_beq b01C_lt, beq_tabC b01C_lt b0C_lt, beq_tabC b01C_lt b1C_lt, isTt_tabC b0C_lt]

end CFSG.KC.M24L2
