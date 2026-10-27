module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalGroup
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Ext
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecDiag
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem commutator_mem_oddCoreOf_of_ne {N A A' : Subgroup X} (hA : IsPCompIn 2 N A)
    (hA' : IsPCompIn 2 N A') (hne : A ≠ A') {a a' : X} (ha : a ∈ A) (ha' : a' ∈ A') :
    ⁅a, a'⁆ ∈ oddCoreOf N := by
  have hne' : A.subgroupOf N ≠ A'.subgroupOf N := fun h => hne (by
    have := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hA.1, Subgroup.map_subgroupOf_eq_of_le hA'.1] at this)
  have h1 := ComponentClassification.Sp4Rec.commute_map_of_ne (X := ↥N) hA.2 hA'.2 hne'
    (k := ⟨a, hA.1 ha⟩) (l := ⟨a', hA'.1 ha'⟩) ha ha'
  have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥N))
      ⁅(⟨a, hA.1 ha⟩ : ↥N), ⟨a', hA'.1 ha'⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h1
  have h3 := (QuotientGroup.eq_one_iff _).1 h2
  have hmem : ⁅a, a'⁆ ∈ N := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hA.1 ha) (hA'.1 ha')) (inv_mem (hA.1 ha)))
      (inv_mem (hA'.1 ha'))
  exact mem_oddCoreOf_iff.2 ⟨hmem, h3⟩

theorem oddCoreOf_le_of_isPCompIn {N A : Subgroup X} (hA : IsPCompIn 2 N A) :
    oddCoreOf A ≤ oddCoreOf N := by
  obtain ⟨K, -, hsub, -, -⟩ := hA.2
  have hker := ComponentClassification.Sp4Rec.ker_mk_comp_subtype hsub
  intro x hx
  obtain ⟨hxA, hP⟩ := mem_oddCoreOf_iff.1 hx
  let e : ↥(A.subgroupOf N) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hA.1
  have hmap := pPrimeCore_map_iso 2 e
  rw [← hmap] at hP
  obtain ⟨κ, hκ, hκx⟩ := Subgroup.mem_map.1 hP
  have hκN : κ.1 ∈ pPrimeCore 2 ↥N := by
    have : κ ∈ ((QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (A.subgroupOf N).subtype).ker := by
      rw [hker]; exact hκ
    exact (QuotientGroup.eq_one_iff _).1 this
  have hxN : x ∈ N := hA.1 hxA
  refine mem_oddCoreOf_iff.2 ⟨hxN, ?_⟩
  have : (⟨x, hxN⟩ : ↥N) = κ.1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hκx
    exact this.symm
  rw [this]
  exact hκN

omit [Finite X] in
theorem Sec5Comp.map_conj {n : ℕ} {N A : Subgroup X} (hA : Sec5Comp X n N A) {c : X}
    (hc : c ∈ normalizer (N : Set X)) :
    Sec5Comp X n N (A.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨⟨u, hu⟩, hcov⟩ := hA
  have h1 := hu.map_mulEquiv (MulAut.conj c)
  rw [map_conj_eq_of_mem_normalizer hc] at h1
  refine ⟨⟨_, h1⟩, ?_⟩
  let ψ : ↥A ≃* ↥(A.map (MulAut.conj c).toMonoidHom) :=
    Subgroup.equivMapOfInjective A _ (MulAut.conj c).injective
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
  exact isDoubleCoverOfAlt_congr' f hcov

theorem exists_sylow_inf_component {N A : Subgroup X} (hA : IsPCompIn 2 N A) (S : Sylow 2 ↥N) :
    ∃ P : Sylow 2 ↥A, (P : Subgroup ↥A).map A.subtype =
      (S : Subgroup ↥N).map N.subtype ⊓ A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, -, hsub, -, -⟩ := hA.2
  obtain ⟨P₁, hP₁⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_subnormal S hsub
  let e : ↥(A.subgroupOf N) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hA.1
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  refine ⟨Sylow.mapSurjective he P₁, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : A.subtype.comp e.toMonoidHom = N.subtype.comp (A.subgroupOf N).subtype := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map, hP₁, Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hA.1]

omit [Finite X] in
theorem Sec5Comp.isPCompIn {n : ℕ} {N A : Subgroup X} (hA : Sec5Comp X n N A) :
    IsPCompIn 2 N A := by
  obtain ⟨⟨u, hu⟩, -⟩ := hA
  exact hu.2.2.1

theorem inf_oddCoreOf_le {N A : Subgroup X} (hAN : A ≤ N) : A ⊓ oddCoreOf N ≤ oddCoreOf A := by
  have hodd : Odd (Nat.card ↥(A ⊓ oddCoreOf N)) :=
    Odd.of_dvd_nat (odd_card_oddCoreOf N) (Subgroup.card_dvd_of_le inf_le_right)
  refine le_oddCoreOf_of_normalized inf_le_left ?_ hodd
  intro a ha
  exact mem_normalizer_inf (Subgroup.le_normalizer ha) (le_normalizer_oddCoreOf N (hAN ha))

theorem not_sylow_le_center {K : Type} [Group K] [Finite K] {n : ℕ} (hn : 8 ≤ n)
    (hK : IsDoubleCoverOfAlt K n) (P : Sylow 2 K) : ¬ (P : Subgroup K) ≤ center K := by
  intro hle
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card K = n.factorial :=
    natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hK
  have h1 : Nat.card (P : Subgroup K) ∣ Nat.card (center K) := Subgroup.card_dvd_of_le hle
  rw [hK.2.1, Sylow.card_eq_multiplicity, hcard] at h1
  have h7 : 2 ^ 7 ∣ n.factorial :=
    (show 2 ^ 7 ∣ Nat.factorial 8 by decide).trans (Nat.factorial_dvd_factorial hn)
  have h8 : 7 ≤ n.factorial.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.factorial_ne_zero n)).1 h7
  have h9 : 2 ^ 7 ∣ 2 := (pow_dvd_pow 2 h8).trans h1
  omega

theorem Sec5Comp.comm_of_centralizes_sylow {n : ℕ} (hn : 8 ≤ n) {N A : Subgroup X}
    (hA : Sec5Comp X n N A) (S : Sylow 2 ↥N) {c : X} (hcN : c ∈ N) (hc2 : c * c = 1)
    (hc : ∀ y ∈ (S : Subgroup ↥N).map N.subtype ⊓ A, c * y = y * c) :
    ∀ a ∈ A, ⁅a, c⁆ ∈ oddCoreOf A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp := hA.isPCompIn
  have hAN : A ≤ N := hAp.1
  obtain ⟨P, hP⟩ := exists_sylow_inf_component hAp S
  have hPmem : ∀ y : ↥A, y ∈ (P : Subgroup ↥A) →
      (y : X) ∈ (S : Subgroup ↥N).map N.subtype ⊓ A := fun y hy => by
    rw [← hP]
    exact Subgroup.mem_map_of_mem _ hy
  have hdc := hA.2
  let M₀ : AhatModel X n A := ⟨↥A ⧸ pPrimeCore 2 ↥A, MulEquiv.refl _,
    AhatData.CoverSetup.ofCover hdc⟩
  let ξ : ↥A →* M₀.K := M₀.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥A))
  have hξ : Function.Surjective ξ := fun k => by
    obtain ⟨a, ha⟩ := M₀.surj_mk k
    exact ⟨a, ha⟩
  have hξapp : ∀ a : ↥A, ξ a = M₀.e (QuotientGroup.mk a) := fun a => rfl
  let Pb : Sylow 2 M₀.K := Sylow.mapSurjective hξ P
  have hPb : ∀ p ∈ (Pb : Subgroup M₀.K), ∃ y ∈ (P : Subgroup ↥A), ξ y = p := fun p hp => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hp
    exact ⟨y, hy, rfl⟩
  have hnormA : A.map (MulAut.conj c).toMonoidHom = A := by
    by_contra hne
    have hA' := hA.map_conj (Subgroup.le_normalizer hcN)
    have hAp' := hA'.isPCompIn
    have hcen : (Pb : Subgroup M₀.K) ≤ center M₀.K := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := hPb p hp
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨a, rfl⟩ := hξ k
      have hy1 := hPmem y hy
      have hyc := hc y hy1
      have hyA' : (y : X) ∈ A.map (MulAut.conj c).toMonoidHom :=
        ⟨y, y.2, by
          show c * (y : X) * c⁻¹ = y
          rw [hyc]; group⟩
      have hcomm := commutator_mem_oddCoreOf_of_ne hAp hAp' (fun h => hne h.symm) a.2 hyA'
      have hmem : ⁅(a : X), (y : X)⁆ ∈ oddCoreOf A := by
        refine inf_oddCoreOf_le hAN ⟨?_, hcomm⟩
        simp only [commutatorElement_def]
        exact A.mul_mem (A.mul_mem (A.mul_mem a.2 y.2) (A.inv_mem a.2)) (A.inv_mem y.2)
      obtain ⟨_, hmemP⟩ := mem_oddCoreOf_iff.1 hmem
      have : ξ (a * y) = ξ (y * a) := by
        have h1 : a * y = ⁅a, y⁆ * (y * a) := by
          simp only [commutatorElement_def]; group
        rw [h1, map_mul]
        have h2 : (⁅a, y⁆ : ↥A) ∈ pPrimeCore 2 ↥A := hmemP
        have : ξ ⁅a, y⁆ = 1 := by
          rw [hξapp, (QuotientGroup.eq_one_iff _).2 h2, map_one]
        rw [this, one_mul]
      rw [map_mul, map_mul] at this
      exact this
    exact not_sylow_le_center hn hdc Pb hcen
  have hcA : c ∈ normalizer (A : Set X) := mem_normalizer_of_map_conj_eq hnormA
  let σ : Perm (Fin n) := M₀.perm c hcA
  have hσ2 : σ * σ = 1 := by
    have h1 := M₀.perm_mul hn hcA hcA
    have h2 : (⟨c, hcA⟩ : ↥(normalizer (A : Set X))) * ⟨c, hcA⟩ = 1 := Subtype.ext hc2
    have h3 := congrArg (M₀.permHom hn) h2
    rw [map_mul, map_one] at h3
    exact h3
  by_cases hσ1 : σ = 1
  · exact (M₀.perm_eq_one_iff hn hcA).1 hσ1
  · exfalso
    have hind : M₀.C.Induces (M₀.autOf c hcA) σ := M₀.induces_perm hn c hcA
    have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact hσ2
    have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
    have hsum := Equiv.Perm.sum_cycleType σ
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hk : σ.support.card = 2 * σ.cycleType.card := by omega
    have hk1 : 1 ≤ σ.cycleType.card := by
      by_contra hcon
      have h0 : σ.support.card = 0 := by omega
      exact hσ1 (Equiv.Perm.card_support_eq_zero.1 h0)
    have hfix : (Pb : Subgroup M₀.K) ≤ AhatData.fixSub (M₀.autOf c hcA) := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := hPb p hp
      have hyc := hc y (hPmem y hy)
      rw [AhatData.mem_fixSub, hξapp, M₀.autOf_mk]
      congr 2
      apply Subtype.ext
      show c * (y : X) * c⁻¹ = y
      rw [hyc]; group
    exact hind.not_sylow_le_fixSub hn hσ2 hk hk1 Pb hfix

theorem comm_mem_oddCoreOf_of_centralizes_sylow {n : ℕ} (hn : 8 ≤ n) {N : Subgroup X}
    (S : Sylow 2 ↥N) {c : X} (hcN : c ∈ N) (hc2 : c * c = 1)
    (hc : ∀ y ∈ (S : Subgroup ↥N).map N.subtype ⊓ K0 X n N, c * y = y * c) :
    ∀ k ∈ K0 X n N, ⁅k, c⁆ ∈ pPrimeCoreOf 2 (K0 X n N) := by
  have hDN : K0 X n N ≤ N := K0_le n N
  have hND : N ≤ normalizer (K0 X n N : Set X) := Sec5Data.le_normalizer_K0 X n N
  have hOD : oddCoreOf (K0 X n N) = K0 X n N ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  let W : Subgroup X :=
    { carrier := {k | k ∈ K0 X n N ∧ ⁅k, c⁆ ∈ oddCoreOf (K0 X n N)}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        refine mul_mem ?_ ha'
        exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ ha) _).1 hb'
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have h1 : ⁅a⁻¹, c⁆ = a⁻¹ * ⁅a, c⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [h1]
        have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ (inv_mem ha)) _).1
          (inv_mem ha')
        simpa using this }
  have hA : ∀ A, Sec5Comp X n N A → A ≤ W := by
    intro A hA a ha
    have hAp := hA.isPCompIn
    have hAD : A ≤ K0 X n N := le_sSup hA
    have hcA := hA.comm_of_centralizes_sylow hn S hcN hc2 (fun y hy => hc y ⟨hy.1, hAD hy.2⟩) a ha
    have hcomm1 : ⁅a, c⁆ ∈ oddCoreOf N := oddCoreOf_le_of_isPCompIn hAp hcA
    have hcomm2 : ⁅a, c⁆ ∈ K0 X n N := by
      have e : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem (hAD ha) (conj_mem_K0 n (Subgroup.le_normalizer hcN) (inv_mem (hAD ha)))
    exact ⟨hAD ha, by rw [hOD]; exact ⟨hcomm2, hcomm1⟩⟩
  have hDW : K0 X n N ≤ W := by
    rw [K0_eq_sSup_sec5Comp]
    exact sSup_le fun A hA' => hA A hA'
  intro k hk
  exact (hDW hk).2

end CFSG.OddStandard.Solomon75
