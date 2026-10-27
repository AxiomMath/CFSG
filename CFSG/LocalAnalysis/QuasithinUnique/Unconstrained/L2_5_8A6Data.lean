module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.QuasithinUnique.Unc25A6

open CFSG.QuasithinUnique.A6Facts.Core

@[expose] def invsD : List (List Nat) := dLit.filter fun c => c != cid && cmul c c == cid

@[expose] def Fl (t s : List Nat) : List (List Nat) := [cid, t, s, cmul t s]

@[expose] def normsB (c : List Nat) (F : List (List Nat)) : Bool :=
  F.all fun f => F.any fun u => cmul c f == cmul u c

theorem d_nodup : dLit.Nodup := by decide +kernel

theorem d_length : dLit.length = 8 := by decide +kernel

theorem d_dihedral_check : dLit.any (fun ρ => dLit.any fun σ =>
    cmul σ σ == cid && cpow ρ 4 == cid && cpow ρ 2 != cid && cmul (cmul σ ρ) σ == cpow ρ 3 &&
      dLit.all fun x => (List.range 4).any fun i => (List.range 2).any fun j =>
        cmul (cpow ρ i) (cpow σ j) == x) = true := by
  decide +kernel

theorem d_norm_check : pslLit.all (fun g => !(normsB g dLit) || dLit.contains g) = true := by
  decide +kernel

theorem d_cent_check : pslLit.all (fun g => invsD.all fun t => invsD.all fun s =>
    !(cmul g t == cmul t g) || !(cmul g s == cmul s g) || t == s || !(cmul t s == cmul s t) ||
      g == cid || g == t || g == s || g == cmul t s) = true := by
  decide +kernel

theorem d_three_check : invsD.all (fun t => invsD.all fun s =>
    t == s || !(cmul t s == cmul s t) || pslLit.any fun w =>
      cpow w 3 == cid && w != cid && (Fl t s).any (fun u => cmul w t == cmul u w) &&
        (Fl t s).any (fun u => cmul w s == cmul u w)) = true := by
  decide +kernel

theorem aut_sq_check : autL.all (fun c => pslLit.contains (cmul c c)) = true := by
  decide +kernel

theorem d_fix_check : autL.all (fun c => invsD.all fun t => invsD.all fun s =>
    !(cmul c t == cmul t c) || !(cmul c s == cmul s c) || t == s || !(cmul t s == cmul s t) ||
      normsB c dLit) = true := by
  decide +kernel

@[expose] def t1C : List Nat := [9, 1, 2, 6, 5, 4, 3, 8, 7, 0]

@[expose] def s1C : List Nat := [6, 2, 1, 9, 4, 5, 0, 8, 7, 3]

theorem f1_valid : (invsD.contains t1C && invsD.contains s1C && t1C != s1C &&
    cmul t1C s1C == cmul s1C t1C) = true := by
  decide +kernel

theorem f1_dnorm : dLit.all (fun d => normsB d (Fl t1C s1C)) = true := by decide +kernel

theorem f1_ne_d : pslLit.any (fun w => normsB w (Fl t1C s1C) && !dLit.contains w) = true := by
  decide +kernel

theorem f1_ne_top : pslLit.any (fun g => !normsB g (Fl t1C s1C)) = true := by decide +kernel

theorem dyn_check : autL.all (fun a => !(dLit.all fun d => cmul a d == cmul d a) ||
    pslLit.contains a || autL.all fun b => !(normsB b dLit) || normsB b (Fl t1C s1C) ||
      !(cmul a b == cmul b a)) = true := by
  decide +kernel

end CFSG.QuasithinUnique.Unc25A6
