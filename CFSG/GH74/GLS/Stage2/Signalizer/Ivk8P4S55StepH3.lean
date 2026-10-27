module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

namespace Hyp89

variable {p : ℕ} {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ}

theorem bAutN_nontrivial (hf : Hyp89 p ρ K a) : bAutN K a hf.norm ≠ 1 := by
  have hperf : Group.IsPerfect ↥K := hf.quasi.1
  intro h1
  rw [bAutN_eq_yAct] at h1
  have hc : a ∈ centralizer (K : Set Γ) := (YCfg.yAct_eq_one_iff K ⟨a, hf.norm⟩).mp h1
  apply hf.acts
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hcom : Commute a x := (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  exact (hcom.zpow_left n).eq

theorem orderOf_bAutN (hf : Hyp89 p ρ K a) : orderOf (bAutN K a hf.norm) = p := by
  have := Fact.mk hf.prime
  have hpow : (⟨a, hf.norm⟩ : ↥(normalizer (K : Set Γ))) ^ p = 1 :=
    Subtype.ext (by simpa using hf.pow_prime)
  have hbp : bAutN K a hf.norm ^ p = 1 := by
    rw [bAutN_eq_yAct, ← map_pow, hpow, map_one]
  exact orderOf_eq_prime hbp hf.bAutN_nontrivial

theorem bAutN_fixed_of_rgroup [Finite Γ] [Module.Finite (ZMod p) V] (hf : Hyp89 p ρ K a)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) (E : Subgroup (↥K ⧸ center ↥K))
    (hE : IsPGroup r ↥E) (hinv : ∀ x ∈ E, bAutN K a hf.norm x ∈ E) :
    ∀ x ∈ E, bAutN K a hf.norm x = x := by
  intro x hx
  by_contra hne
  exact hf.false_of_hhobsAt (r := r) (fun h => absurd h hr2)
    ⟨hr, hrp, E, hE, fun h => absurd h hr2, hinv, x, hx, hne⟩

theorem eq_bot_of_crossE1 [Finite Γ] [Module.Finite (ZMod p) V] (hE1 : CrossE1)
    (hf : Hyp89 p ρ K a) {r : ℕ} (hr : OddChev r (↥K ⧸ center ↥K)) (hrp : r ≠ p)
    (E : Subgroup (↥K ⧸ center ↥K)) (hE : IsPGroup r ↥E)
    (hinv : ∀ x ∈ E, bAutN K a hf.norm x ∈ E) : E = ⊥ := by
  have hrpr : r.Prime := hr.1
  have hr2 : r ≠ 2 := hr.2.1
  have hndvd : ¬ r ∣ orderOf (bAutN K a hf.norm) := by
    rw [hf.orderOf_bAutN]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hrpr hf.prime).mp h)
  exact hE1 r _ hr _ hf.bAutN_nontrivial hndvd
    (fun E' hE' hinv' => hf.bAutN_fixed_of_rgroup hrpr hr2 hrp E' hE' hinv') E hE hinv

theorem false_of_hhobs_noR [Finite Γ] [Module.Finite (ZMod p) V] (hf : Hyp89 p ρ K a) {s : ℕ}
    (h : HHObsAt p s (↥K ⧸ center ↥K) (bAutN K a hf.norm))
    (hN : s = 2 → NoR 2 (↥K ⧸ center ↥K)) : False :=
  hf.false_of_hhobsAt (fun hs2 => hN hs2 ↥K hf.quasi ⟨MulEquiv.refl _⟩) h

end Hyp89

theorem Ord3Types.cases (h : Ord3Types) {r : ℕ} {Y : Type} [Group Y] [Finite Y] (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hY : FL3d r Y ∨ FU3d r Y ∨ FSp4d r Y ∨ FG2d r Y ∨ FD4d r Y ∨ FL4d r Y ∨ FU4d r Y ∨
      FReed r Y)
    (b : MulAut Y) (hb : orderOf b = 3) :
    (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
      ∃ s : ℕ, HHObsAt 3 s Y b ∧ (s = 2 → NoR 2 Y) := by
  rcases hY with hT | hT | hT | hT | hT | hT | hT | hT
  · exact h.l3 r Y hr hr2 hr3 hT b hb
  · exact h.u3 r Y hr hr2 hr3 hT b hb
  · exact h.sp4 r Y hr hr2 hr3 hT b hb
  · exact h.g2 r Y hr hr2 hr3 hT b hb
  · exact h.d4 r Y hr hr2 hr3 hT b hb
  · exact h.l4 r Y hr hr2 hr3 hT b hb
  · exact h.u4 r Y hr hr2 hr3 hT b hb
  · exact absurd hT.1 hr3

theorem stepH3_of (hE1 : CrossE1) (hO : Ord3Types) : StepH3 := by
  intro p Γ _ _ V _ _ _ ρ K a hf _ hp3 r hr hrp
  subst hp3
  obtain ⟨hrpr, hr2, hT⟩ := hr
  have hY : OddChev r (↥K ⧸ center ↥K) := ⟨hrpr, hr2, Or.inr hT⟩
  rcases hO.cases hrpr hr2 hrp hT _ hf.orderOf_bAutN with ⟨E, hE, hEp, hEi⟩ | ⟨s, hs, hN⟩
  · exact hE (hf.eq_bot_of_crossE1 hE1 hY hrp E hEp hEi)
  · exact hf.false_of_hhobs_noR hs hN

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
