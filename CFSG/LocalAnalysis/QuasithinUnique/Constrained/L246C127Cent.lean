module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_two_of_forall {D : Subgroup G}
    (h : ∀ x ∈ D, ∀ r : ℕ, r.Prime → orderOf x = r → r = 2) : IsPGroup 2 D := by
  by_contra hD
  have hnpow : ¬ ∃ n : ℕ, Nat.card D = 2 ^ n := fun ⟨n, hn⟩ => hD (IsPGroup.of_card hn)
  have hex : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card D ∧ r ≠ 2 := by
    by_contra hne
    push Not at hne
    refine hnpow ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdd
    exact hne d hd hdd
  obtain ⟨r, hr, hrd, hr2⟩ := hex
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) r hrd
  exact hr2 (h x.1 x.2 r hr (by rw [Subgroup.orderOf_coe]; exact hx))

omit [Finite G] in
theorem eq_two_of_orderOf_eq_prime {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q)
    {r : ℕ} (hr : r.Prime) (hxr : orderOf x = r) : r = 2 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQ ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hxr
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hxr
    exact hr.one_lt.ne' hxr.symm
  have h2 : 2 ∣ r := by rw [← hxr]; exact dvd_pow_self 2 hk1
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h2).symm

theorem inf_centralizer_le_pCoreOf {X L V : Subgroup G} (hX : CharTwo X) (hLX : L ≤ X)
    (hVX : X ≤ Subgroup.normalizer (V : Set G))
    (hLQ : ∀ y ∈ L, ∀ q ∈ pCoreOf 2 X, ⁅y, q⁆ ∈ V) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hD2 : IsPGroup 2 (L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    refine isPGroup_two_of_forall fun x hx r hr hxr => ?_
    by_contra hr2
    have : Fact r.Prime := ⟨hr⟩
    set A : Subgroup G := Subgroup.zpowers x with hA
    have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [hA, Nat.card_zpowers, hxr, pow_one])
    have hAL : A ≤ L := Subgroup.zpowers_le.2 hx.1
    have hAN : A ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := hAL.trans (hLX.trans hXQ)
    have hcop : Nat.Coprime r (Nat.card (pCoreOf 2 X)) := by
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent r hr A
      (pCoreOf 2 X) hAp hAN hcop
    have hQV : ⁅pCoreOf 2 X, A⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro q hq a ha
      have h1 := hLQ a (hAL ha) q hq
      have : ⁅q, a⁆ = ⁅a, q⁆⁻¹ := (commutatorElement_inv a q).symm
      rw [this]
      exact V.inv_mem h1
    have hAC : A ≤ Subgroup.centralizer (V : Set G) :=
      (Subgroup.zpowers_le.2 hx.2)
    have hVA : ⁅V, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAC
    have h2 : ⁅⁅pCoreOf 2 X, A⁆, A⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono hQV le_rfl).trans hVA.le)
    have h3 : ⁅pCoreOf 2 X, A⁆ = ⊥ := by rw [← hidem]; exact h2
    have hxQ : x ∈ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      have : A ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h3
      exact this (Subgroup.mem_zpowers x)
    have hxQ' : x ∈ pCoreOf 2 X := hX ⟨hLX hx.1, hxQ⟩
    exact hr2 (eq_two_of_orderOf_eq_prime hQ2 hxQ' hr hxr)
  have hLC : L ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    B2F.le_normalizer_centralizer (hLX.trans hVX)
  have hLD : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer hLC
  exact C1.le_pCoreOf_of_normalized inf_le_left hLD hD2

@[expose] def cQV (X Q V : Subgroup G) (hV : X ≤ Subgroup.normalizer (V : Set G))
    (hQ : X ≤ Subgroup.normalizer (Q : Set G)) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ V}
  one_mem' := ⟨X.one_mem, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxq⟩ ⟨hy, hyq⟩
    refine ⟨X.mul_mem hx hy, fun q hq => ?_⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 (hV hx) _).1 (hyq q hq)
    have h3 := hxq q hq
    have e : ⁅x * y, q⁆ = (x * ⁅y, q⁆ * x⁻¹) * ⁅x, q⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem h2 h3
  inv_mem' := by
    rintro x ⟨hx, hxq⟩
    refine ⟨X.inv_mem hx, fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (hQ (X.inv_mem hx)) q).1 hq
      simpa using this
    have h1 := hxq (x⁻¹ * q * x) hq'
    have e : ⁅x⁻¹, q⁆ = ⁅x, x⁻¹ * q * x⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.inv_mem h1

section cQV

variable {X Q V : Subgroup G} (hV : X ≤ Subgroup.normalizer (V : Set G))
  (hQ : X ≤ Subgroup.normalizer (Q : Set G))

omit [Finite G] in
theorem mem_cQV {x : G} : x ∈ cQV X Q V hV hQ ↔ x ∈ X ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ V := Iff.rfl

omit [Finite G] in
theorem cQV_le : cQV X Q V hV hQ ≤ X := fun _ hx => hx.1

omit [Finite G] in
theorem conj_mem_cQV {g x : G} (hg : g ∈ X) (hx : x ∈ cQV X Q V hV hQ) :
    g * x * g⁻¹ ∈ cQV X Q V hV hQ := by
  obtain ⟨hxX, hxq⟩ := hx
  refine ⟨X.mul_mem (X.mul_mem hg hxX) (X.inv_mem hg), fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (hQ (X.inv_mem hg)) q).1 hq
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.1 (hV hg) _).1 (hxq _ hq')
  have e : ⁅g * x * g⁻¹, q⁆ = g * ⁅x, g⁻¹ * q * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h1

omit [Finite G] in
theorem conjClosure_le_cQV {K L₀ : Subgroup G} (hK : K ≤ cQV X Q V hV hQ) (hL₀ : L₀ ≤ X) :
    conjClosure K L₀ ≤ cQV X Q V hV hQ :=
  conjClosure_le fun _ hh _ hz => conj_mem_cQV hV hQ (hL₀ hh) (hK hz)

end cQV

end L246C127

end CFSG.QuasithinUnique
