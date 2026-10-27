module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.LayerLemma
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Helpers
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Small0

variable {G : Type} [Group G]

theorem Fs_eq_sup (N : Subgroup G) : Fs N = Fm N ⊔ Em N := by
  rw [Fs_def, Fm_def, Em_def, ← Subgroup.map_sup]
  rfl

theorem Em_le_Fs (N : Subgroup G) : Em N ≤ Fs N := by
  rw [Fs_eq_sup]
  exact le_sup_right

theorem Fm_le_Fs (N : Subgroup G) : Fm N ≤ Fs N := by
  rw [Fs_eq_sup]
  exact le_sup_left

theorem commutator_le_inf_of_normalizing {X Y L K : Subgroup G} (hX : X ≤ normalizer (K : Set G))
    (hY : Y ≤ normalizer (L : Set G)) (hYK : Y ≤ K) (hXL : X ≤ L) : ⁅X, Y⁆ ≤ L ⊓ K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · have h1 : y * x⁻¹ * y⁻¹ ∈ L := (mem_normalizer_iff.mp (hY hy) x⁻¹).mp (L.inv_mem (hXL hx))
    have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact L.mul_mem (hXL hx) h1
  · have h1 : x * y * x⁻¹ ∈ K := (mem_normalizer_iff.mp (hX hx) y).mp (hYK hy)
    have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact K.mul_mem h1 (K.inv_mem (hYK hy))

end Small0

section Small

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_pGroup_coprime {X : Subgroup G} {r : ℕ} (hr : r.Prime) (h1 : IsPGroup r ↥X)
    (h2 : Nat.Coprime r (Nat.card ↥X)) : X = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h1
  rw [hn] at h2
  have hn0 : n = 0 := by
    by_contra hn0
    have : r ∣ r ^ n := dvd_pow_self r hn0
    exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one (h2 ▸ Nat.dvd_gcd (dvd_refl r) this))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

theorem eq_bot_of_pGroup_pGroup {X : Subgroup G} {r q : ℕ} (hr : r.Prime) (hq : q.Prime) (hne : r ≠ q)
    (h1 : IsPGroup r ↥X) (h2 : IsPGroup q ↥X) : X = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h2
  refine eq_bot_of_pGroup_coprime hr h1 ?_
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr hq).mpr hne)

theorem coprime_card_of_pGroups {X Y : Subgroup G} {r q : ℕ} (hr : r.Prime) (hq : q.Prime) (hne : r ≠ q)
    (h1 : IsPGroup r ↥X) (h2 : IsPGroup q ↥Y) : Nat.Coprime (Nat.card ↥X) (Nat.card ↥Y) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h1
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp h2
  rw [hn, hm]
  exact Nat.Coprime.pow n m ((Nat.coprime_primes hr hq).mpr hne)

end Small

section Prop62b

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M N A B : Subgroup G} {p r : ℕ}

theorem A_centralizes_Fm (hH : Hyp62 z M N A B r) (hF : Fm N ≤ M) {q : ℕ} (hq : q.Prime)
    (hne : r ≠ q) (hqP : IsPGroup q ↥(Fm N)) : A ≤ centralizer (Fm N : Set G) := by
  have hcomm : ⁅Fm N, A⁆ ≤ Fm N ⊓ Op r M :=
    commutator_le_inf_of_normalizing (le_trans hF (le_normalizer_Op r M))
      (hH.A_le.trans (le_normalizer_Fm N)) hH.A_le_Or le_rfl
  have hcop : Nat.Coprime (Nat.card ↥(Fm N)) (Nat.card ↥(Op r M)) :=
    (coprime_card_of_pGroups hH.prime hq hne (isPGroup_Op r hH.prime M) hqP).symm
  have hbot : Fm N ⊓ Op r M = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [hbot, le_bot_iff] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hcomm)

theorem B_centralizes_Fm (hH : Hyp62 z M N A B r) (hF : Fm N ≤ M) (hrP : IsPGroup r ↥(Fm N)) :
    B ≤ centralizer (Fm N : Set G) := by
  have hcomm : ⁅Fm N, B⁆ ≤ Fm N ⊓ Ep r M :=
    commutator_le_inf_of_normalizing (le_trans hF (le_normalizer_Ep r M))
      (hH.B_le.trans (le_normalizer_Fm N)) hH.B_le_E le_rfl
  have hcop : Nat.Coprime (Nat.card ↥(Fm N)) (Nat.card ↥(Ep r M)) := by
    have : Fact r.Prime := ⟨hH.prime⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hrP
    have h1 : Nat.card ↥(Ep r M) = Nat.card ↥(pPrimeCore r ↥(Fm M)) :=
      Subgroup.card_map_of_injective (Fm M).subtype_injective
    rw [hn, h1]
    exact Nat.Coprime.pow_left n (pPrimeCore_coprime_card (p := r) (G := ↥(Fm M)))
  have hbot : Fm N ⊓ Ep r M = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [hbot, le_bot_iff] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hcomm)

theorem mem_Fm_of_centralizes {N : Subgroup G} {x : G} (hx : x ∈ N) (h1 : x ∈ centralizer (Fm N : Set G))
    (h2 : x ∈ centralizer (Em N : Set G)) : x ∈ Fm N := by
  refine mem_Fm_of_centralizes_Fs hx ?_
  rw [Fs_eq_sup, sup_le_iff]
  constructor
  · intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h1 y hy)
  · intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h2 y hy)

theorem twoPrimes_Fm_of_hyp62 (hH : Hyp62 z M N A B r) (hF : Fm N ≤ M) (hFs : Fs N ≤ M) :
    TwoPrimes (Fm N) := by
  by_contra hnt
  obtain ⟨q, hq, hqP⟩ := isPrimePowerGrp_of_not_twoPrimes hnt
  have hAF : A ≤ Fm M := hH.A_le_Or.trans (Op_le_Fm r hH.prime M)
  have hBF : B ≤ Fm M := hH.B_le_E.trans (Subgroup.map_subtype_le _)
  have hEM : Em N ≤ M := (Em_le_Fs N).trans hFs
  have hAcE : A ≤ centralizer (Em N : Set G) := centralizes_Em hH.A_le hAF hEM
  have hBcE : B ≤ centralizer (Em N : Set G) := centralizes_Em hH.B_le hBF hEM
  by_cases hqr : q = r
  ·
    subst hqr
    have : Fact q.Prime := ⟨hq⟩
    have hBc : B ≤ centralizer (Fm N : Set G) := B_centralizes_Fm hH hF hqP
    have hBF' : B ≤ Fm N := fun b hb => mem_Fm_of_centralizes (hH.B_le hb) (hBc hb) (hBcE hb)
    have hBp : IsPGroup q ↥B := hqP.to_le hBF'
    have hcop : Nat.Coprime q (Nat.card ↥B) := by
      have h1 : Nat.card ↥B ∣ Nat.card ↥(Ep q M) := Subgroup.card_dvd_of_le hH.B_le_E
      have h2 : Nat.Coprime q (Nat.card ↥(Ep q M)) := by
        have : Nat.card ↥(Ep q M) = Nat.card ↥(pPrimeCore q ↥(Fm M)) :=
          Subgroup.card_map_of_injective (Fm M).subtype_injective
        rw [this]
        exact pPrimeCore_coprime_card (p := q) (G := ↥(Fm M))
      exact h2.coprime_dvd_right h1
    exact hH.B_mem.2.1 (eq_bot_of_pGroup_coprime hq hBp hcop)
  ·
    have hAc : A ≤ centralizer (Fm N : Set G) := A_centralizes_Fm hH hF hq (Ne.symm hqr) hqP
    have hAF' : A ≤ Fm N := fun a ha => mem_Fm_of_centralizes (hH.A_le ha) (hAc ha) (hAcE ha)
    have hAq : IsPGroup q ↥A := hqP.to_le hAF'
    have hAr : IsPGroup r ↥A := (isPGroup_Op r hH.prime M).to_le hH.A_le_Or
    exact hH.A_mem.2.1 (eq_bot_of_pGroup_pGroup hH.prime hq (Ne.symm hqr) hAr hAq)


theorem prop6_2_of (h63 : Lemma6_3) (h64 : Lemma6_4) (h13 : Bender13) : Prop6_2 := by
  intro G _ _ z k S M p hC N A B r hH
  have hF := h63 G z k S M p hC N A B r hH
  have hFs := h64 G z k S M p hC N A B r hH
  have hNM : Links N M := ⟨⊥, bot_le, inf_le_left.trans hFs⟩
  refine ⟨⟨hFs, hNM⟩, twoPrimes_Fm_of_hyp62 hH hF hFs, ?_⟩
  intro hMN
  rcases h13 G hC.ctx.std.kps M N hC.coatom hH.maximal hMN hNM with h | ⟨q, hq, hqM, -⟩
  · exact h
  · exfalso
    rw [hC.Fs_eq hC.mem] at hqM
    exact not_isPGroup_of_twoPrimes hC.twoPrimes hq hqM

end Prop62b

end CFSG.GH74.GLS.Stage2.Bender.Thm1
