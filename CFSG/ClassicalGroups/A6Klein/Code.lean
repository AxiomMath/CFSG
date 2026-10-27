module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel

public section

namespace CFSG.ClassicalGroups.A6Klein

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.A6Facts.Core

@[expose] def cinv (c : List ℕ) : List ℕ := (List.range 10).map fun j => c.idxOf j

@[expose] def inV (A B v : List ℕ) : Bool := v == cid || v == A || v == B || v == cmul A B

@[expose] def kleinC (A B : List ℕ) : Bool :=
  A != cid && B != cid && A != B && cmul A A == cid && cmul B B == cid && cmul A B == cmul B A

@[expose] def nrmInv (A B n : List ℕ) : Bool :=
  inV A B (cmul (cmul n A) n) && inV A B (cmul (cmul n B) n)

@[expose] def invU (T S σ : List ℕ) : Bool :=
  let U := [cid, T, S, cmul T S]
  U.contains (cmul (cmul σ T) σ) && U.contains (cmul (cmul σ S) σ)

@[expose] def pslPairs : List (List ℕ × List ℕ) := pslLit.map fun c => (c, cinv c)

@[expose] def cjp (p : List ℕ × List ℕ) (v : List ℕ) : List ℕ := cmul (cmul p.1 v) p.2

@[expose] def goodSc (A B Sc : List ℕ) : Bool :=
  Sc != cid && cmul Sc Sc == cid && cmul A Sc == cmul Sc A && !(inV A B Sc)

@[expose] def condIV (A B Sc : List ℕ) : Bool :=
  pslPairs.all (fun G => !(nrmInv A B (cmul (cmul G.2 A) G.1)) ||
    (invU A Sc (cjp G A) && invU A Sc (cjp G B)))

@[expose] def condS (A Sc : List ℕ) : Bool :=
  pslPairs.any (fun N => !([cid, A, Sc, cmul A Sc].contains (cjp N A) &&
    [cid, A, Sc, cmul A Sc].contains (cjp N Sc)))

@[expose] def condX (A B : List ℕ) : Bool :=
  pslPairs.any (fun X => nrmInv A B (cmul (cmul X.2 A) X.1) &&
    [A, B, cmul A B].any fun v => [A, B, cmul A B].any fun w =>
      cmul (cmul (cmul v (cjp X w)) (cmul v (cjp X w))) (cmul v (cjp X w)) == cid &&
        cmul v (cjp X w) != cid)

@[expose] def checkKlein (A B : List ℕ) : Bool :=
  (pslLit.any fun Sc => goodSc A B Sc && condIV A B Sc && condS A Sc) && condX A B

@[expose] def a0 : List ℕ := (pslLit.find? (fun A => A != cid && cmul A A == cid)).getD cid

theorem cinv_mem : pslLit.all (fun C => pslLit.contains (cinv C)) = true := by decide +kernel

theorem cmul_cinv : pslLit.all (fun C => cmul C (cinv C) == cid) = true := by decide +kernel

theorem inv_conj : pslLit.all (fun A => !(A != cid && cmul A A == cid) ||
    pslPairs.any fun G => cjp G A == a0) = true := by decide +kernel

theorem kleinClosed_std : pslLit.all (fun B => !kleinC a0 B ||
    pslLit.all fun C => !(cmul C C == cid && cmul C a0 == cmul a0 C && cmul C B == cmul B C) ||
      inV a0 B C) = true := by decide +kernel

theorem checkAll : pslLit.all (fun B => !kleinC a0 B || checkKlein a0 B) = true := by
  decide +kernel

abbrev K0 : Type := ↥A6Models.psl29

@[expose] def kap (g : K0) : List ℕ := code (g : P10)

theorem kap_mul (g h : K0) : kap (g * h) = cmul (kap g) (kap h) := by
  unfold kap
  rw [Subgroup.coe_mul, code_mul]

theorem kap_one : kap (1 : K0) = cid := by
  unfold kap
  rw [Subgroup.coe_one, code_one]

theorem kap_injective : Function.Injective kap := by
  intro g h hgh
  exact Subtype.ext (code_injective hgh)

theorem kap_mem (g : K0) : kap g ∈ pslLit := (mem_psl29_iff _).mp g.2

theorem exists_kap {C : List ℕ} (hC : C ∈ pslLit) : ∃ g : K0, kap g = C := by
  obtain ⟨x, hx, hxC⟩ := exists_psl29_of_code hC
  exact ⟨⟨x, hx⟩, hxC⟩

theorem kap_inv (g : K0) : kap g⁻¹ = cinv (kap g) := by
  have h1 : cinv (kap g) ∈ pslLit := by
    have := List.all_eq_true.mp cinv_mem (kap g) (kap_mem g)
    exact List.contains_iff_mem.mp this
  obtain ⟨y, hy⟩ := exists_kap h1
  have h2 : cmul (kap g) (cinv (kap g)) = cid := by
    have := List.all_eq_true.mp cmul_cinv (kap g) (kap_mem g)
    exact beq_iff_eq.mp this
  have h3 : g * y = 1 := by
    apply kap_injective
    rw [kap_mul, hy, h2, kap_one]
  have : y = g⁻¹ := eq_inv_of_mul_eq_one_right h3
  rw [← this, hy]

end CFSG.ClassicalGroups.A6Klein
