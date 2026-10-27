module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open Equiv CFSG.QuasithinUnique.Unc25G2

namespace M11Insp

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

@[expose] def genT (i : ℕ) : Perm (Fin 11) := if i = 0 then pA else if i = 1 then pB else 1

theorem genT_eq : genT = CFSG.Sporadic.Bridge.M11.gen := by
  funext i
  by_cases h0 : i = 0
  · subst h0
    simp [genT, pA_eq]
  · by_cases h1 : i = 1
    · subst h1
      simp [genT, pB_eq]
    · simp [genT, CFSG.Sporadic.Bridge.M11.gen, h0, h1]

@[expose] def dec (l : List ℕ) : List (ℕ × Bool) := l.map fun n => (n / 2, n % 2 == 0)

@[expose] def ev (x : ℕ → Perm (Fin 11)) (l : List ℕ) : Perm (Fin 11) :=
  CFSG.Sporadic.Bridge.wordProd x (dec l)

@[expose] def code (g : Perm (Fin 11)) : List ℕ := (List.finRange 11).map fun i => (g i).val

theorem code_injective : Function.Injective code := by
  intro g h hgh
  have h1 := List.map_inj_left.1 hgh
  ext a
  exact h1 a (List.mem_finRange a)

@[expose] def cPerm (j : ℕ) : Perm (Fin 11) :=
  CFSG.Sporadic.Schreier.tab (ev genT (cWordsCode.getD j []))

@[expose] def alph (y : Perm (Fin 11)) (i : ℕ) : Perm (Fin 11) := if i < 4 then cPerm i else y

@[expose] def certOK (e : List ℕ × List ℕ × List ℕ) : Bool :=
  let y := CFSG.Sporadic.Schreier.tab (ev genT e.2.1)
  (code (y * pA * y⁻¹) == e.1) && (code (ev (alph y) e.2.2) == code pB)

@[expose] def covered (g : Perm (Fin 11)) : Bool :=
  decide (g * g ≠ 1) || decide (g = 1) || (code g == code pA) || tblCode.any fun e => e.1 == code g

theorem cert_check : tblCode.all certOK = true := by
  decide +kernel

theorem comm_check : (List.range 4).all (fun j => decide (cPerm j * pA = pA * cPerm j)) = true := by
  decide +kernel

theorem covered_check :
    (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses0).all (fun t₀ =>
      (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses1).all fun t₁ =>
        (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses2).all fun t₂ =>
          (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses3).all fun t₃ =>
            covered (t₀ * (t₁ * (t₂ * t₃)))) = true := by
  decide +kernel

end M11Insp

end CFSG.QuasithinUnique.Vol2Native.L239
