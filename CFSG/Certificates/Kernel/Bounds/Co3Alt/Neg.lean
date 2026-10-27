module

public import CFSG.Certificates.Kernel.Bounds.Co3Alt.Route
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Co3Alt.Neg

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec true false b

theorem rels_T2_alpha : notB (KB.relsOk CFSG.KBData.Co3Alt_T2v.R (nat_lit 18) (nat_lit 1694364715909633) rels) = true := by quickRfl

theorem rels_T2_drop : notB (KB.relsOk CFSG.KBData.Co3Alt_T2v.R (nat_lit 18) (nat_lit 1694364598469121) [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)], [(4, true), (4, true)], [(5, true), (5, true)], [(6, true), (6, true)], [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)], [(0, true), (4, true), (0, true), (4, true)], [(1, true), (3, true), (1, true), (3, true)], [(2, true), (4, true), (2, true), (4, true)], [(3, true), (6, true), (3, true), (6, true)], [(4, true), (6, true), (4, true), (6, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)], [(5, true), (0, true), (6, true), (0, true), (6, true), (0, true), (6, true)], [(6, true), (1, true), (5, true), (1, true), (5, true), (1, true), (5, true)], [(2, true), (5, true), (6, true), (2, true), (5, true), (6, true), (2, true), (5, true), (6, true)], [(4, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true)], [(4, true), (0, true), (2, true), (6, true), (0, true), (2, true), (6, true), (0, true), (2, true), (6, true), (0, true), (2, true), (6, true)], [(1, true), (2, true), (5, true), (2, true), (5, true), (1, true), (2, true), (5, true), (2, true), (5, true), (1, true), (2, true), (5, true), (2, true), (5, true)]]) = true := by quickRfl

theorem subs_T2_big : notB (KB.subsOk CFSG.KBData.Co3Alt_T2v.S (nat_lit 6) (nat_lit 1694364598469121) [[(0, true)], [(2, true)], [(4, true)], [(5, true)], [(6, true)], [(1, true)]]) = true := by quickRfl

theorem subs_T2_small : notB (KB.subsOk CFSG.KBData.Co3Alt_T2v.S (nat_lit 5) (nat_lit 1694364598469121) [[(0, true)], [(2, true)], [(4, true)], [(5, true)]]) = true := by quickRfl

theorem subs_T2_swap : notB (KB.subsOk CFSG.KBData.Co3Alt_T2v.S (nat_lit 5) (nat_lit 1694364598469121) [[(0, true)], [(2, true)], [(4, true)], [(5, true)], [(1, true)]]) = true := by quickRfl

theorem rels_T3_alpha : notB (KB.relsOk CFSG.KBData.Co3Alt_T3v.R (nat_lit 12) (nat_lit 1411785815098881) rels) = true := by quickRfl

theorem rels_T3_drop : notB (KB.relsOk CFSG.KBData.Co3Alt_T3v.R (nat_lit 12) (nat_lit 1411785815097345) [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)], [(4, true), (4, true)], [(5, true), (5, true)], [(6, true), (6, true)], [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)], [(0, true), (4, true), (0, true), (4, true)], [(1, true), (3, true), (1, true), (3, true)], [(2, true), (4, true), (2, true), (4, true)], [(3, true), (6, true), (3, true), (6, true)], [(4, true), (6, true), (4, true), (6, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)], [(5, true), (0, true), (6, true), (0, true), (6, true), (0, true), (6, true)], [(6, true), (1, true), (5, true), (1, true), (5, true), (1, true), (5, true)], [(2, true), (5, true), (6, true), (2, true), (5, true), (6, true), (2, true), (5, true), (6, true)], [(4, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true)], [(1, true), (2, true), (5, true), (2, true), (5, true), (1, true), (2, true), (5, true), (2, true), (5, true), (1, true), (2, true), (5, true), (2, true), (5, true)], [(4, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true)]]) = true := by quickRfl

theorem subs_T3_big : notB (KB.subsOk CFSG.KBData.Co3Alt_T3v.S (nat_lit 1) (nat_lit 1411785815097345) [[(0, true)]]) = true := by quickRfl

theorem order_twice : notB (Nat.beq (Nat.mul (Nat.mul (nat_lit 170775) (nat_lit 7560)) (nat_lit 768)) (nat_lit 495766656000)) = true := by quickRfl

end CFSG.KBRoute.Co3Alt.Neg

end
