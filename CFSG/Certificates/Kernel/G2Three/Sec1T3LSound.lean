module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3D8Sound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop

theorem listRecAnd_iff {α : Type} (f : α → Bool) : ∀ l : List α,
    List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(f c, ih)) l = true ↔
      ∀ c ∈ l, f c = true
  | [] => by simp
  | c :: l => by
    change bAnd(f c, List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(f c, ih)) l) =
      true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, listRecAnd_iff f l, List.forall_mem_cons]

theorem listHead_of (F : ℕ → Bool) : ∀ c : List ℕ,
    List.rec (motive := fun _ => Bool) false (fun x _ _ => F x) c = true →
      c ≠ [] ∧ F (hdL c) = true
  | [], h => (Bool.false_ne_true h).elim
  | x :: _, h => ⟨List.cons_ne_nil _ _, h⟩

theorem hdL_mem : ∀ {c : List ℕ}, c ≠ [] → hdL c ∈ c
  | [], h => (h rfl).elim
  | _ :: _, _ => List.mem_cons_self

theorem unionL_bit (k : ℕ) : ∀ cl : List (List ℕ),
    (unionL cl).testBit k = true ↔ ∃ c ∈ cl, (lstM c).testBit k = true
  | [] => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | c :: cl => by
    change (lstM c ||| unionL cl).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, unionL_bit k cl]
    simp

theorem unionM_bit (k : ℕ) : ∀ ms : List ℕ,
    (unionM ms).testBit k = true ↔ ∃ m ∈ ms, m.testBit k = true
  | [] => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | m :: ms => by
    change (m ||| unionM ms).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, unionM_bit k ms]
    simp

theorem lstMs_eq : ∀ cl : List (List ℕ), lstMs cl = cl.map lstM
  | [] => rfl
  | c :: cl => by
    change lstM c :: lstMs cl = _
    rw [lstMs_eq cl, List.map_cons]

theorem clsMs_eq (P C V T : ℕ) : ∀ rs : List ℕ, clsMs P C V T rs = rs.map (clsE P C V T)
  | [] => rfl
  | r :: rs => by
    change clsE P C V T r :: clsMs P C V T rs = _
    rw [clsMs_eq P C V T rs, List.map_cons]

theorem distB_spec : ∀ {ms : List ℕ}, distB ms = true → ms.Pairwise (· ≠ ·)
  | [], _ => List.Pairwise.nil
  | m :: ms, h => by
    change bAnd(List.rec (motive := fun _ => Bool) true (fun m' _ ih2 =>
      bAnd(Bool.not' (Nat.beq m m'), ih2)) ms, distB ms) = true at h
    rw [bAnd_eq, Bool.and_eq_true, listRecAnd_iff] at h
    refine List.Pairwise.cons (fun m' hm' he => ?_) (distB_spec h.2)
    have := h.1 m' hm'
    rw [not'_eq, he, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem testBit_imgR_lt {r H k : ℕ} (h : (imgR r H).testBit k = true) : k < 128 := by
  rw [← hasB_eq, imgR_bit] at h
  obtain ⟨i, -, -, rfl⟩ := h
  exact atR_lt _ _

theorem testBit_clsE_lt {P C V X y k : ℕ} (h : (clsE P C V X y).testBit k = true) : k < 128 := by
  have e : clsE P C V X y = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P i) (rowT C (atR V i)) y)), acc))
      128 := by
    simp only [clsE, strictN_eq]
  rw [e, recMask_bit] at h
  obtain ⟨i, -, -, rfl⟩ := h
  exact atR_lt _ _

theorem testBit_lstM_lt {l : List ℕ} (hl : ∀ x ∈ l, x < 128) {k : ℕ}
    (h : (lstM l).testBit k = true) : k < 128 :=
  hl k ((lstM_bit k l).1 h)

variable {G : Type} [Group G] {elt : ℕ → G}

theorem eq_of_mset_eq (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {m₁ m₂ : ℕ}
    (h₁ : ∀ k, m₁.testBit k = true → k < 128) (h₂ : ∀ k, m₂.testBit k = true → k < 128)
    (h : mset elt m₁ = mset elt m₂) : m₁ = m₂ := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 128
  · have e := congrArg (elt k ∈ ·) h
    simp only [mem_mset_iff hinj hk, hasB_eq, eq_iff_iff] at e
    exact Bool.eq_iff_iff.2 e
  · cases hb1 : m₁.testBit k
    · cases hb2 : m₂.testBit k
      · rfl
      · exact absurd (h₂ k hb2) hk
    · exact absurd (h₁ k hb1) hk

section Tables

variable {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

theorem listsOK_sound {T I : ℕ} {cl : List (List ℕ)} (h : listsOK P C V T I cl = true) :
    (∀ c ∈ cl, c ≠ [] ∧ hdL c < 128 ∧ elt (hdL c) ∈ mset elt I ∧
      mset elt (lstM c) = {g | ∃ x ∈ mset elt T, x * elt (hdL c) * x⁻¹ = g}) ∧
    (∀ y ∈ mset elt I, ∃ c ∈ cl, y ∈ mset elt (lstM c)) ∧ (cl.map lstM).Pairwise (· ≠ ·) := by
  unfold listsOK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, listRecAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => ?_, ?_, lstMs_eq cl ▸ distB_spec h3⟩
  · obtain ⟨hne, hF⟩ := listHead_of _ c (h1 c hc)
    rw [bAnd_eq, Bool.and_eq_true] at hF
    have hlt : hdL c < 128 := by
      have := hF.1
      rw [hasB_eq] at this
      by_contra hk
      have e := Nat.eq_of_beq_eq_true hF.2
      have hb : (lstM c).testBit (hdL c) = true := (lstM_bit _ c).2 (hdL_mem hne)
      rw [e] at hb
      exact hk (testBit_clsE_lt hb)
    refine ⟨hne, hlt, (mem_mset_iff hR.inj hlt).2 hF.1, ?_⟩
    rw [Nat.eq_of_beq_eq_true hF.2, clsE_mset hR T hlt]
  · rintro _ ⟨i, hi, hb, rfl⟩
    rw [← Nat.eq_of_beq_eq_true h2, hasB_eq] at hb
    change (I &&& unionL cl).testBit i = true at hb
    rw [Nat.testBit_and, Bool.and_eq_true, unionL_bit] at hb
    obtain ⟨c, hc, hb⟩ := hb.2
    exact ⟨c, hc, i, hi, by rw [hasB_eq]; exact hb, rfl⟩

theorem repsOK_sound {T I : ℕ} {rs : List ℕ} (hrs : ∀ r ∈ rs, r < 128)
    (h : repsOK P C V T I rs = true) :
    (∀ r ∈ rs, elt r ∈ mset elt I) ∧
    (∀ y ∈ mset elt I, ∃ r ∈ rs, ∃ x ∈ mset elt T, x * elt r * x⁻¹ = y) ∧
    (rs.map (clsE P C V T)).Pairwise (· ≠ ·) := by
  unfold repsOK at h
  rw [bAnd_eq, Bool.and_eq_true, listRecAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  dsimp only at h2
  rw [bAnd_eq, Bool.and_eq_true, clsMs_eq] at h2
  refine ⟨fun r hr => (mem_mset_iff hR.inj (hrs r hr)).2 (h1 r hr), ?_, distB_spec h2.2⟩
  rintro _ ⟨i, hi, hb, rfl⟩
  rw [← Nat.eq_of_beq_eq_true h2.1, hasB_eq] at hb
  change (I &&& unionM (rs.map (clsE P C V T))).testBit i = true at hb
  rw [Nat.testBit_and, Bool.and_eq_true, unionM_bit] at hb
  obtain ⟨m, hm, hb⟩ := hb.2
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hm
  have : elt i ∈ mset elt (clsE P C V T r) := ⟨i, hi, by rw [hasB_eq]; exact hb, rfl⟩
  rw [clsE_mset hR T (hrs r hr)] at this
  obtain ⟨x, hx, he⟩ := this
  exact ⟨r, hr, x, hx, he⟩

theorem z2d8K_sound {X c g1 g2 R : ℕ} (hc : c < 128) (hg1 : g1 < 128) (hg2 : g2 < 128)
    (h : z2d8K P C Q X c g1 g2 R = true) :
    mset elt (closK C [g1, g2] R) =
      (Subgroup.closure {x | ∃ g ∈ [g1, g2], elt g = x} : Set G) ∧
    elt c ≠ 1 ∧ elt c * elt c = 1 ∧
    mset elt X = mset elt (closK C [g1, g2] R) ∪ (elt c * ·) '' mset elt (closK C [g1, g2] R) ∧
    elt c ∉ mset elt (closK C [g1, g2] R) ∧
    (∀ d ∈ mset elt (closK C [g1, g2] R), d * elt c = elt c * d) ∧
    ∃ φ : DihedralGroup 4 →* G, Function.Injective φ ∧
      Set.range φ = mset elt (closK C [g1, g2] R) := by
  unfold z2d8K at h
  rw [bAnd_eq, Bool.and_eq_true, strictB_eq, strictB_eq] at h
  obtain ⟨hcl, h⟩ := h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, not'_eq, Bool.not_eq_true'] at h
  obtain ⟨h0, hq, hX, hn, hcen, hd8⟩ := h
  have hgs : ∀ g ∈ [g1, g2], g < 128 := by simp [hg1, hg2]
  set D := closK C [g1, g2] R
  refine ⟨closK_closure hR hgs hcl, fun he => ?_, ?_, ?_, fun hm => ?_, fun d hd => ?_,
    d8K_sound hR hg1 hd8⟩
  · rw [← hR.one] at he
    have := hR.inj _ hc _ (by decide) he
    omega
  · rw [← hR.sq hc, hq, hR.one]
  · rw [← hX, mset_lor, mset_imgR_left hR hc]
  · rw [mem_mset_iff hR.inj hc, hn] at hm
    exact absurd hm (by decide)
  · rw [← hcen, cenE_mset hR D hc] at hd
    exact hd.2

end Tables

end CFSG.KC.G2Three.Sec1T3
