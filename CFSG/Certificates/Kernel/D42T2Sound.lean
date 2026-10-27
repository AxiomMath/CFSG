module

public import Certificates.Data.Kernel.D42T2
public import CFSG.Certificates.Kernel.B433Alt.ChainCount
public import CFSG.Certificates.Kernel.LyBase.Stab
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.CommBaseSound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.Walter.JRFacts

public section

namespace CFSG.KC.D42T2

open CFSG.KC.Enum CFSG.KC.CommBase Equiv MulAction CFSG.Sporadic.Schreier

theorem orbOK_sound {n : Nat} {f : Nat → Nat → Nat} {k b : Nat} {P Q L : List Nat}
    (h : orbOK n f k b P Q L = true) (K : Subgroup (Perm (Fin n))) (g : Nat → Perm (Fin n))
    (hg : ∀ l < k, g l ∈ K) (hf : ∀ l < k, ∀ q : Fin n, f l q = g l q) (hb : b < n) :
    P.length ≤ (orbit K (⟨b, hb⟩ : Fin n)).ncard := by
  unfold orbOK at h
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨-, h0, hlt, hnd, hst⟩ := h
  have h0' : P.getD 0 n = b := Nat.eq_of_beq_eq_true h0
  have hlt' : ∀ p ∈ P, p < n := fun p hp => Nat.blt_eq.mp (allL_iff.1 hlt p hp)
  have hhead : P.head? = some b := by
    cases P with
    | nil => simp at h0'; omega
    | cons a P => simpa using h0'
  have hstep : ∀ i (hi : i < P.length), 0 < i → ∃ j < i, ∃ hj : j < P.length,
      ∃ c ∈ Subgroup.closure (K : Set (Perm (Fin n))),
        (c ⟨P[j], hlt' _ (List.getElem_mem hj)⟩ : ℕ) = P[i] := by
    intro i hi hpos
    have e := CFSG.KS.allN_spec hst i hi
    rw [bIf_eqC] at e
    have hi0 : Nat.beq i 0 = false := by
      cases i with
      | zero => omega
      | succ i => rfl
    rw [hi0] at e
    simp only [Bool.false_eq_true, ↓reduceIte, CFSG.KS.bAnd_iff] at e
    obtain ⟨e1, e2, e3⟩ := e
    have hj := Nat.blt_eq.mp e1
    have hl := Nat.blt_eq.mp e2
    have hjP : Q.getD i 0 < P.length := hj.trans hi
    refine ⟨Q.getD i 0, hj, hjP, g (L.getD i 0), Subgroup.subset_closure (hg _ hl), ?_⟩
    have e3' := Nat.eq_of_beq_eq_true e3
    rw [List.getD_eq_getElem _ _ hjP, List.getD_eq_getElem _ _ hi] at e3'
    rw [← e3', hf _ hl ⟨P[Q.getD i 0], hlt' _ (List.getElem_mem hjP)⟩]
  have := CFSG.KC.B433Alt.length_le_ncard_orbit (K : Set (Perm (Fin n))) b hb P hlt' hhead hstep
    (CFSG.Decide.nodup_of_bitsetNodup_nat hnd)
  rwa [Subgroup.closure_eq] at this

theorem mul_card_centralizerIn_le {n : Nat} (Ω : Subgroup (Perm (Fin n))) (t : Perm (Fin n))
    (p x y : Fin n) (hx : t p = x) (hy : t x = y) {m₀ m₁ m₂ c a : ℕ}
    (h₀ : m₀ ≤ (orbit Ω p).ncard)
    (h₁ : m₁ ≤ (orbit ↥(Ω ⊓ stabilizer (Perm (Fin n)) p) x).ncard)
    (h₂ : m₂ ≤ (orbit ↥(Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x) y).ncard)
    (hc : c ≤ (conjClass (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x ⊓
      stabilizer (Perm (Fin n)) y) t).ncard)
    (ha : (orbit ↥(centralizerIn Ω t) p).ncard ≤ a) :
    m₀ * m₁ * m₂ * c * Nat.card (centralizerIn Ω t) ≤ a * Nat.card Ω := by
  have e₀ := CFSG.KC.LyBase.ncard_orbit_mul_card_inf Ω p
  have e₁ := CFSG.KC.LyBase.ncard_orbit_mul_card_inf (Ω ⊓ stabilizer (Perm (Fin n)) p) x
  have e₂ := CFSG.KC.LyBase.ncard_orbit_mul_card_inf
    (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x) y
  have eC := CFSG.KC.LyBase.ncard_orbit_mul_card_inf (centralizerIn Ω t) p
  have ecl := ncard_conjClass_mul_card (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓
    stabilizer (Perm (Fin n)) x ⊓ stabilizer (Perm (Fin n)) y) t
  have hle : centralizerIn Ω t ⊓ stabilizer (Perm (Fin n)) p ≤
      centralizerIn (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x ⊓
        stabilizer (Perm (Fin n)) y) t := by
    intro g hg
    obtain ⟨hgC, hgp⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgΩ, hgt⟩ := mem_centralizerIn.1 hgC
    have hgp' : g p = p := by
      have := mem_stabilizer_iff.1 hgp
      rwa [Perm.smul_def] at this
    have hgx : g x = x := by
      rw [← hx, ← Perm.mul_apply, hgt, Perm.mul_apply, hgp']
    have hgy : g y = y := by
      rw [← hy, ← Perm.mul_apply, hgt, Perm.mul_apply, hgx]
    have hsx : g ∈ stabilizer (Perm (Fin n)) x :=
      mem_stabilizer_iff.2 (by rw [Perm.smul_def]; exact hgx)
    have hsy : g ∈ stabilizer (Perm (Fin n)) y :=
      mem_stabilizer_iff.2 (by rw [Perm.smul_def]; exact hgy)
    exact mem_centralizerIn.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
      ⟨hgΩ, hgp⟩, hsx⟩, hsy⟩, hgt⟩
  have hcard := Subgroup.card_le_of_le hle
  have hC : Nat.card (centralizerIn Ω t) ≤ a * Nat.card (centralizerIn
      (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x ⊓
        stabilizer (Perm (Fin n)) y) t) := by
    rw [← eC]
    exact Nat.mul_le_mul ha hcard
  have hH : c * Nat.card (centralizerIn (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓
      stabilizer (Perm (Fin n)) x ⊓ stabilizer (Perm (Fin n)) y) t) ≤
      Nat.card ↥(Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x ⊓
        stabilizer (Perm (Fin n)) y) := by
    rw [← ecl]
    exact Nat.mul_le_mul_right _ hc
  have hΩ : m₀ * m₁ * m₂ * Nat.card ↥(Ω ⊓ stabilizer (Perm (Fin n)) p ⊓
      stabilizer (Perm (Fin n)) x ⊓ stabilizer (Perm (Fin n)) y) ≤ Nat.card Ω := by
    rw [← e₀, ← e₁, ← e₂]
    calc m₀ * m₁ * m₂ * _ ≤ (orbit Ω p).ncard *
          (orbit ↥(Ω ⊓ stabilizer (Perm (Fin n)) p) x).ncard *
          (orbit ↥(Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x) y).ncard * _ := by
          gcongr
      _ = _ := by ring
  calc m₀ * m₁ * m₂ * c * Nat.card (centralizerIn Ω t)
      ≤ m₀ * m₁ * m₂ * c * (a * Nat.card (centralizerIn
        (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x ⊓
          stabilizer (Perm (Fin n)) y) t)) := Nat.mul_le_mul_left _ hC
    _ = a * (m₀ * m₁ * m₂ * (c * Nat.card (centralizerIn
        (Ω ⊓ stabilizer (Perm (Fin n)) p ⊓ stabilizer (Perm (Fin n)) x ⊓
          stabilizer (Perm (Fin n)) y) t))) := by ring
    _ ≤ a * (m₀ * m₁ * m₂ * Nat.card ↥(Ω ⊓ stabilizer (Perm (Fin n)) p ⊓
        stabilizer (Perm (Fin n)) x ⊓ stabilizer (Perm (Fin n)) y)) := by gcongr
    _ ≤ a * Nat.card Ω := Nat.mul_le_mul_left _ hΩ

end CFSG.KC.D42T2

end
