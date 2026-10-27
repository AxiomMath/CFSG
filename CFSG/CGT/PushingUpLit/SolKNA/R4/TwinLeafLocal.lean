module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafTwin

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

@[expose] def IsTwoPrimeTwo {Y : Type} [Group Y] (K : Subgroup Y) : Prop :=
  ∃ O : Subgroup Y, O ≤ K ∧ (O.subgroupOf K).Normal ∧ Odd (Nat.card O) ∧
    ∀ g ∈ K, ∃ k : ℕ, g ^ 2 ^ k ∈ O

theorem isTwoPrimeTwo_conjSub {Y : Type} [Group Y] {K : Subgroup Y} (g : Y)
    (h : IsTwoPrimeTwo K) : IsTwoPrimeTwo (conjSub g K) := by
  obtain ⟨O, hOK, hOn, hodd, hq⟩ := h
  refine ⟨conjSub g O, conjSub_mono hOK, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff (conjSub_mono hOK)]
    intro h' k hh' hk
    rw [mem_conjSub_iff] at hh' hk ⊢
    have := (Subgroup.normal_subgroupOf_iff hOK).mp hOn (g⁻¹ * h' * g) (g⁻¹ * k * g) hh' hk
    simpa [mul_assoc] using this
  · rw [show Nat.card ↥(conjSub g O) = Nat.card ↥O from
      (Nat.card_congr (Subgroup.equivMapOfInjective O (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm]
    exact hodd
  · intro x hx
    rw [mem_conjSub_iff] at hx
    obtain ⟨k, hk⟩ := hq _ hx
    refine ⟨k, ?_⟩
    rw [mem_conjSub_iff]
    have e : (g⁻¹ * x * g) ^ 2 ^ k = g⁻¹ * x ^ 2 ^ k * g := by
      simpa using (conj_pow (a := g⁻¹) (b := x) (i := 2 ^ k))
    rw [e] at hk
    exact hk

theorem conj_mem_oddCoreOf' {Y : Type} [Group Y] {H : Subgroup Y} {k y : Y} (hk : k ∈ H)
    (hy : y ∈ oddCoreOf H) : k * y * k⁻¹ ∈ oddCoreOf H := by
  obtain ⟨o, ho, rfl⟩ := hy
  exact ⟨⟨k, hk⟩ * o * ⟨k, hk⟩⁻¹,
    (inferInstance : (classicalInvolutionOddCore ↥H).Normal).conj_mem o ho ⟨k, hk⟩, rfl⟩

@[expose] def LocalNoQ16Q16 (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (F : Type) [Group F], P F → ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal],
    Nonempty (↥N ≃* F) → Subgroup.centralizer (N : Set Y) = ⊥ →
    ∀ t : Y, orderOf t = 2 → ∀ K K' : Subgroup Y,
      CFSG.Open.IsSubnormal K (Subgroup.centralizer ({t} : Set Y)) →
      CFSG.Open.IsSubnormal K' (Subgroup.centralizer ({t} : Set Y)) →
      IsTwoPrimeTwo K → IsTwoPrimeTwo K' →
      ∀ x ∈ K, ∀ y ∈ K, ∀ x' ∈ K', ∀ y' ∈ K', ¬ Q16Q16 x y x' y'

theorem LocalNoQ16Q16.of_noQ16Q16Aut {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → NoQ16Q16 (MulAut F)) : LocalNoQ16Q16 P := by
  intro F _ hF Y _ _ N _ hN hC t _ K K' _ _ _ _ x _ y _ x' _ y' _ hq
  obtain ⟨f, hf⟩ := embedsAut_mulAut F Y N hN hC
  exact h F hF (f x) (f y) (f x') (f y') (hq.map f hf)

theorem isTwoPrimeTwo_core {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) : IsTwoPrimeTwo (tightCore R) := by
  refine ⟨tightCore R ⊓ oddCoreOf R, inf_le_left, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h' k hh' hk
    exact ⟨(tightCore R).mul_mem ((tightCore R).mul_mem hk hh'.1) ((tightCore R).inv_mem hk),
      conj_mem_oddCoreOf' (tightCore_le R hk) hh'.2⟩
  · exact Odd.of_dvd_nat (card_oddCoreOf_odd R) (Subgroup.card_dvd_of_le inf_le_right)
  · intro g hg
    have hgR : g ∈ R := tightCore_le R hg
    obtain ⟨k, hk⟩ := h.core.datum.twoGroup (QuotientGroup.mk (⟨g, hgR⟩ : ↥R))
    refine ⟨k, (tightCore R).pow_mem hg _, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact ⟨⟨g, hgR⟩ ^ 2 ^ k, hk, by simp⟩

theorem twinLeafR_of_local {r n : ℕ} (hr : 4 ≤ r) {P : ∀ (F : Type) [Group F], Prop}
    (h : LocalNoQ16Q16 P) : TwinLeafR r n P := by
  intro Y _ _ R S t hP _ hPF
  haveI := genFittingFStar_normal Y
  haveI := hP.core.simple
  obtain ⟨K', x, y, x', y', -, ⟨g, hg⟩, -, hsub', hx, hy, hx', hy', hq⟩ :=
    exists_q16Q16_of_perp hr hP
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hP.core.datum
  have hsub : CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen hP.core.hyp (CoreAssembly.mem_conjClass_self _) hz
  have h22' : IsTwoPrimeTwo K' := by
    rw [← show conjSub g (tightCore R) = K' from hg]
    exact isTwoPrimeTwo_conjSub g (isTwoPrimeTwo_core hP)
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab) t hP.core.datum.order _ K' hsub hsub'
    (isTwoPrimeTwo_core hP) h22' x hx y hy x' hx' y' hy' hq

theorem twinLeafR_of_noQ16Q16Aut {r n : ℕ} (hr : 4 ≤ r) {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → NoQ16Q16 (MulAut F)) : TwinLeafR r n P :=
  twinLeafR_of_local hr (LocalNoQ16Q16.of_noQ16Q16Aut h)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
