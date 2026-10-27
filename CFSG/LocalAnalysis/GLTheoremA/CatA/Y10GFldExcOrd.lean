module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.LocalAnalysis.GLTheoremA

theorem dvd_of_chevField_order {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime)
    (H : Subgroup (LargeEvenChevGL A K)) (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, chevAct A K σ h ∈ H)
    {f : MulAut (LargeEvenCenterQuot H)} (hf : f ∈ LargeEvenChevFieldImage A K H)
    (hord : orderOf f = p) : p ∣ n := by
  obtain ⟨σ, hσ⟩ := hf
  let rel : (K ≃+* K) → H → H → Prop := fun a h h' =>
    ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
      LargeEvenEntrywise A K a (map_zero a) ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K))
  have hrel : ∀ (a : K ≃+* K) (h h' : H), rel a h h' ↔ (h' : LargeEvenChevGL A K) = chevAct A K a h := by
    intro a h h'
    show _ ↔ _
    rw [Units.ext_iff, chevAct_val]
  let act : (K ≃+* K) → LargeEvenChevGL A K → LargeEvenChevGL A K := fun a g => chevAct A K a g
  have hactmul : ∀ a b (x : LargeEvenChevGL A K), act (a * b) x = act a (act b x) :=
    fun a b x => chevAct_mul A K a b x
  have hstab : ∀ a (h : H), act a (h : LargeEvenChevGL A K) ∈ H := fun a h => hH a h h.2
  have hpow : ∀ k : ℕ, LargeEvenGraphAut (LargeEvenCenterMk H) (rel (σ ^ k)) (f ^ k) := by
    intro k
    induction k with
    | zero =>
      intro h h' hh'
      rw [pow_zero] at hh' ⊢
      have e : (h' : LargeEvenChevGL A K) = h := by
        have := (hrel 1 h h').1 hh'
        rw [this, chevAct_one]
      rw [MulAut.one_apply, Subtype.ext e]
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact FP.graph_mul H (LargeEvenCenterMk H) act hactmul hstab rel hrel ih hσ
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) (p := 2) (n := n) Nat.prime_two hn hK
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hdn : orderOf σ ∣ n := by
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hσd : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
  have hf1 : f ^ orderOf σ = 1 := by
    have h1 := hpow (orderOf σ)
    rw [hσd] at h1
    have h2 : LargeEvenGraphAut (LargeEvenCenterMk H) (rel 1) 1 := by
      intro h h' hh'
      have e : (h' : LargeEvenChevGL A K) = h := by
        have := (hrel 1 h h').1 hh'
        rw [this, chevAct_one]
      rw [MulAut.one_apply, Subtype.ext e]
    exact FP.graph_unique H (LargeEvenCenterMk H) (QuotientGroup.mk_surjective) act hstab rel hrel
      h1 h2
  have hpd : p ∣ orderOf σ := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hf1
  exact hpd.trans hdn

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
