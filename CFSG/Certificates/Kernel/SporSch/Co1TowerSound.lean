module

public import Certificates.Data.Kernel.SporSch.Co1Tower
import CFSG.Certificates.Kernel.SporSch.Co1TowerLib
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw CFSG.KS.SporSch.M24

theorem tower_sound {M : Nat → Nat} {K : Nat} {base sizes : List Nat} {gens : List (List Nat)}
    (hn : ∀ i < base.length, 0 < sizes.getD i 0 ∧ sizes.getD i 0 < 131072)
    (hl : ∀ i < base.length, ∃ (T E S C : Nat → Nat) (NS L : Nat),
      levelHd K (gens.getD i []) (base.getD i 0) T = true ∧ C 0 = 1 ∧
        C NS = sizes.getD i 0 ∧ sizes.getD i 0 ≤ NS * L ∧
        (∀ s < NS, levelSl M (gens.getD i []) (sizes.getD i 0) T E (s * L) L (C s) (C (s + 1)) =
          true) ∧
        (∀ s < NS, permSl S T (sizes.getD i 0) (s * L) L = true) ∧
        fixesK M (gens.getD i []) base i = true) :
    vTowerOK (Array.ofFn (n := K) fun j => transposeRows 24 (unpack 24 24 (M j.val))) base gens
      sizes = true :=
  TowerLib.tower_ok hn hl

@[expose] def nonlinP (A : Rows) (z v3 c1 c2 : Nat) (vs : List Nat) (O OX : VOrbit) : Bool :=
  vs.foldl (· ^^^ ·) 0 == v3 &&
    vs.all (fun w => decide (w < 2 ^ 24) && decide (act A w < 2 ^ 24) &&
      inEnum OX 98280 w && !inEnum O 4600 w && !inEnum O 4600 (act A w)) &&
    inEnum O 4600 (z ^^^ v3) &&
    decide (act A (z ^^^ v3) < 2 ^ 24) &&
    vs.foldl (fun s w => s ^^^ act A w) 0 == c1 &&
    (if inEnum O 4600 (act A (z ^^^ v3)) then z ^^^ act A (z ^^^ v3) else act A (z ^^^ v3)) == c2

private theorem strictN_eqV (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_eqV (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_eqV (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem bIf_eqV (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem nIf_eqV (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem foldXor_eq (g : Nat → Nat) : ∀ (vs : List Nat) (s : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun w _ ih s => CFSG.KC.Enum.strictN (Nat.xor s (g w)) ih) vs s = vs.foldl (fun s w => s ^^^ g w) s
  | [], _ => rfl
  | w :: vs, s => by
    change CFSG.KC.Enum.strictN (Nat.xor s (g w)) (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun w _ ih s => CFSG.KC.Enum.strictN (Nat.xor s (g w)) ih) vs) = _
    rw [strictN_eqV, foldXor_eq g vs]
    rfl

theorem nonlinK_sound {A : Nat} {T S TX SX : Nat → Nat} {z v3 c1 c2 : Nat} {vs : List Nat}
    {O OX : VOrbit}
    (hO : ∀ u, ((List.range 4600).any fun i => O.pts[i]! == u) = memK T S 4600 u)
    (hOX : ∀ u, ((List.range 98280).any fun i => OX.pts[i]! == u) = memK TX SX 98280 u)
    (h : nonlinK A T S TX SX z v3 c1 c2 vs = true) :
    nonlinP (unpack 24 24 A) z v3 c1 c2 vs O OX = true := by
  have hact : ∀ w, act (unpack 24 24 A) w = actK A w := M24.ActL.act_unpack A
  have hlt : ∀ w, actK A w < 2 ^ 24 := fun w => by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [M24.ActL.actK_eq_foldr, M24.ActL.testBit_foldr_or]
    have : ¬ i < 24 := by omega
    simp [this]
  have hin : ∀ u, inEnum O 4600 u = memK T S 4600 u := hO
  have hinX : ∀ u, inEnum OX 98280 u = memK TX SX 98280 u := hOX
  unfold nonlinK at h
  simp only [bAnd_eqV, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [foldXor_eq (fun w => w)] at h1
  rw [foldXor_eq (fun w => actK A w)] at h4
  rw [strictB_eqV, nIf_eqV] at h5
  have hall : ∀ w ∈ vs, w < 2 ^ 24 ∧ memK TX SX 98280 w = true ∧ memK T S 4600 w = false ∧
      memK T S 4600 (actK A w) = false := by
    clear h1 h3 h4 h5
    induction vs with
    | nil =>
      intro w hw
      exact absurd hw List.not_mem_nil
    | cons v vs ih =>
      simp only [Bool.and_eq_true] at h2
      obtain ⟨a, b, c, d, e⟩ := h2
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · rw [bIf_eqV] at c d
        refine ⟨by simpa [Nat.blt_eq] using a, b, ?_, ?_⟩
        · cases hm : memK T S 4600 w <;> simp_all
        · cases hm : memK T S 4600 (actK A w) <;> simp_all
      · exact ih e w hw
  unfold nonlinP
  simp only [hact, hin, hinX, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨Nat.eq_of_beq_eq_true h1, fun w hw => ?_⟩, h3⟩, hlt _⟩, Nat.eq_of_beq_eq_true h4⟩, ?_⟩
  · obtain ⟨a, b, c, d⟩ := hall w hw
    exact ⟨⟨⟨⟨a, hlt w⟩, b⟩, c⟩, d⟩
  · have := Nat.eq_of_beq_eq_true h5
    split_ifs with hm <;> simp_all

end CFSG.KS.SporSch.VOrb

end
