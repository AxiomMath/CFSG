module

public import CFSG.Certificates.Kernel.RouteP.MonoPerm
public import CFSG.Certificates.Kernel.RouteP.Slp
public import Certificates.Data.Kernel.RouteP.Lines
public import Mathlib.Data.Int.Star

public section

namespace CFSG.KS.RouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] noncomputable def ρT (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : ℤ) : Perm Pt :=
  if 0 < z then (gT NW KA KB (z.toNat - 1))⁻¹ else gT NW KA KB ((-z).toNat - 1)

theorem ρT_apply {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : ℤ} (hz0 : z ≠ 0) (hz : LOK NW KA KB z)
    (y : Pt) : (ρT NW KA KB z y).val = eL NW KA KB z y.val := by
  unfold ρT
  cases z with
  | ofNat m =>
    rcases m with _ | j
    · exact absurd rfl hz0
    · rw [if_pos (by simp)]
      have e : (Int.ofNat (j + 1)).toNat - 1 = j := by simp
      rw [e]
      exact gT_inv_apply hz y
  | negSucc n =>
    rw [if_neg (by omega)]
    have e : (-Int.negSucc n).toNat - 1 = n := by omega
    rw [e]
    exact gT_apply hz y

theorem ρT_pos (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (j : Nat) :
    ρT NW KA KB ((j + 1 : Nat) : ℤ) = (gT NW KA KB j)⁻¹ := by
  unfold ρT
  rw [if_pos (by omega)]
  congr 2

theorem ρT_neg (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (j : Nat) :
    ρT NW KA KB (-((j + 1 : Nat) : ℤ)) = gT NW KA KB j := by
  unfold ρT
  rw [if_neg (by omega)]
  congr 1

theorem wordG_replicate {G : Type*} [Group G] (ρ : ℤ → G) (n : Nat) (z : ℤ) :
    wordG ρ (List.replicate n z) = ρ z ^ n := by
  induction n with
  | zero => simp [wordG]
  | succ n ih =>
    rw [List.replicate_succ, show wordG ρ (z :: List.replicate n z) = ρ z * wordG ρ (List.replicate n z) by
      simp [wordG], ih, pow_succ']

theorem wordG_flatMap {G : Type*} [Group G] {α : Type*} (ρ : ℤ → G) (f : α → List ℤ) :
    ∀ L : List α, wordG ρ (L.flatMap f) = (L.map fun a => wordG ρ (f a)).prod
  | [] => by simp [wordG]
  | a :: L => by
    rw [List.flatMap_cons, List.map_cons, List.prod_cons, ← wordG_flatMap ρ f L]
    simp [wordG, List.map_append, List.prod_append]

theorem wordG_lineW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (o : Nat) {l : List ℤ}
    (hl : ∀ p ∈ pairsOf l, 1 ≤ p.1) :
    wordG (ρT NW KA KB) (lineW o l) = (lineProd (fun r => gT NW KA KB (r + o)) l)⁻¹ := by
  unfold lineW lineProd
  rw [wordG_flatMap, List.prod_inv_reverse, List.map_reverse, List.map_map]
  congr 2
  apply List.map_congr_left
  intro p hp
  have hp1 := hl p hp
  have e : p.1 + o = (p.1 - 1 + o) + 1 := by omega
  simp only [Function.comp]
  by_cases hs : p.2 < 0
  · rw [if_pos hs, e, wordG_replicate, ρT_neg]
    have hp2 : p.2 = -(p.2.natAbs : ℤ) := by omega
    conv_rhs => rw [hp2]
    rw [zpow_neg, inv_inv, zpow_natCast]
  · rw [if_neg hs, e, wordG_replicate, ρT_pos, inv_pow]
    have hp2 : p.2 = (p.2.natAbs : ℤ) := by omega
    conv_rhs => rw [hp2]
    rw [zpow_natCast]

theorem line_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {o j : Nat} {l : List ℤ}
    (hj : LOK NW KA KB (Int.ofNat (j + 1))) (hw : WOK NW KA KB (lineW o l)) (hl : ∀ p ∈ pairsOf l, 1 ≤ p.1)
    (hck : ∀ k < 19, CFSG.KC.RouteP.wordOK NW (lineW o l) j k = true)
    (hkk : wordKOK NW KA KB (lineW o l) j = true) :
    gT NW KA KB j = lineProd (fun r => gT NW KA KB (r + o)) l := by
  have hz : ∀ z ∈ lineW o l, z ≠ 0 := by
    intro z hz
    unfold lineW at hz
    obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    have hp1 := hl p (List.mem_reverse.1 hp)
    have := (List.mem_replicate.1 hz).2
    split_ifs at this <;> omega
  have hI : (gT NW KA KB j)⁻¹ = wordG (ρT NW KA KB) (lineW o l) := by
    apply Equiv.ext
    intro y
    apply Fin.ext
    rw [gT_inv_apply hj, wordG_apply (ρT NW KA KB) id (lineW o l)
      (fun z hz' y' => ρT_apply (hz z hz') (hw z hz') y'), List.map_id]
    exact word_spec hj.1 hj.2 hw hck hkk _ y.isLt
  rw [wordG_lineW NW KA KB o hl] at hI
  exact inv_injective hI

theorem lineProd_congr {G : Type*} [Group G] {π π' : ℕ → G} {l : List ℤ}
    (h : ∀ p ∈ pairsOf l, π (p.1 - 1) = π' (p.1 - 1)) : lineProd π l = lineProd π' l := by
  unfold lineProd
  congr 1
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem prog_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {g o : Nat} {ls : Array (List ℤ)}
    {t : Nat → Nat} (hls : LinesOK g ls) {regs : ℕ → Perm Pt} (hregs : ∀ r < g, regs r = gT NW KA KB (r + o))
    (ht : ∀ ℓ < ls.size, LOK NW KA KB (Int.ofNat (t ℓ + 1)))
    (hw : ∀ ℓ < ls.size, WOK NW KA KB (lineW o ls[ℓ]!))
    (hck : ∀ ℓ < ls.size, ∀ k < 19, CFSG.KC.RouteP.wordOK NW (lineW o ls[ℓ]!) (t ℓ) k = true)
    (hkk : ∀ ℓ < ls.size, wordKOK NW KA KB (lineW o ls[ℓ]!) (t ℓ) = true)
    (hfac : ∀ ℓ < ls.size, ∀ p ∈ pairsOf ls[ℓ]!, g < p.1 → t (p.1 - 1 - g) = p.1 - 1 + o) :
    ∀ ℓ < ls.size, runSLPG (compileSLP g ls) regs (g + ℓ) = gT NW KA KB (t ℓ) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro hℓ
    have hl1 : ∀ p ∈ pairsOf ls[ℓ]!, 1 ≤ p.1 := fun p hp => (hls ℓ hℓ p hp).1
    rw [runSLPG_compileSLP_line g ls hls regs hℓ, line_spec (ht ℓ hℓ) (hw ℓ hℓ) hl1 (hck ℓ hℓ) (hkk ℓ hℓ)]
    refine lineProd_congr fun p hp => ?_
    obtain ⟨h1, h2⟩ := hls ℓ hℓ p hp
    by_cases hg : p.1 ≤ g
    · rw [runSLPG_compileSLP_lt g ls hls regs (by omega), hregs _ (by omega)]
    · have e : p.1 - 1 = g + (p.1 - 1 - g) := by omega
      rw [e, ih (p.1 - 1 - g) (by omega) (by omega), hfac ℓ hℓ p hp (by omega), ← e]

end CFSG.KS.RouteP

end
