module

public import CFSG.HardMathSupport.Solomon.Coordinator.W3Core
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsUni
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisRed
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo Matrix
  Subgroup
open scoped commutatorElement

section Model

variable {p : ℕ} {S : Type*} [Group S] [Finite S] {K : Type*} [Field K] {M : Type*} [Group M]

open CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP in
theorem isWeaklyLocallyBalancedAbs_of_model (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (ι : M →* GL (Fin p) K) (hι : Function.Injective ι) (ρ : M →* MulAut S)
    (hker : ∀ g : M, ρ g = 1 → ∃ c : Kˣ, ι g = GeneralLinearGroup.scalar (Fin p) c)
    (hscalar : ∀ (g : M) (c : Kˣ), ι g = GeneralLinearGroup.scalar (Fin p) c → ρ g = 1)
    (hplane : ∀ A B : M, A * B = B * A → ρ A ^ p = 1 → ρ B ^ p = 1 → ρ A ≠ 1 →
      ρ B ∉ zpowers (ρ A) → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
        closure {ρ A, ρ B} ≤ normalizer (H : Set (MulAut S)) →
          localDeltaIn p H (closure {ρ A, ρ B}) = ⊥)
    (houter : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → ¬ D ≤ ρ.range →
      ∀ H : Subgroup (MulAut S), innerAut S ≤ H → localDeltaIn p H D = ⊥)
    (hcomm : ∀ α β : MulAut S, α * β * α⁻¹ * β⁻¹ ∈ ρ.range) :
    IsWeaklyLocallyBalancedAbs p 2 S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  intro A hA D hD H hH hAH
  obtain ⟨hDA, hDe, hDc⟩ := hD
  by_cases hDr : D ≤ ρ.range
  swap
  · rw [houter D hDe hDr H hH]
    exact commutator_bot_left _
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ := exists_gen_pair hp hDe hDc
  obtain ⟨A0, rfl⟩ := MonoidHom.mem_range.1 (hDr hx)
  obtain ⟨B0, rfl⟩ := MonoidHom.mem_range.1 (hDr hy)
  have hxy : ρ A0 * ρ B0 = ρ B0 * ρ A0 :=
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  obtain ⟨z, hz⟩ := hker (A0 * B0 * A0⁻¹ * B0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]; group)
  simp only [map_mul, map_inv] at hz
  by_cases hz1 : z = 1
  · have hAB : A0 * B0 = B0 * A0 := by
      apply hι
      rw [hz1, map_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz
      rw [map_mul, map_mul]
      exact hz
    rw [← hgen, hplane A0 B0 hAB (hDe.2 _ hx) (hDe.2 _ hy) hx1 hyx H hH (hgen ▸ hDA.trans hAH)]
    exact commutator_bot_left _
  have hpow : ∀ X : M, ρ X ^ p = 1 →
      ∃ a0 : Kˣ, ι X ^ p = GeneralLinearGroup.scalar (Fin p) a0 := by
    intro X hX
    obtain ⟨a0, ha0⟩ := hker (X ^ p) (by rw [map_pow, hX])
    exact ⟨a0, by rw [← map_pow]; exact ha0⟩
  obtain ⟨a0, ha0⟩ := hpow A0 (hDe.2 _ hx)
  obtain ⟨b0, hb0⟩ := hpow B0 (hDe.2 _ hy)
  have hzp : z ^ p = 1 := by
    have := pow_eq_one_of_conj ha0 (rel_BA hz)
    rwa [inv_pow, inv_eq_one] at this
  have hω : IsPrimitiveRoot z p := by
    have := orderOf_eq_prime hzp hz1
    rw [← this]
    exact IsPrimitiveRoot.orderOf z
  have hy1 : ρ B0 ≠ 1 := fun e => hyx (e ▸ one_mem _)
  have hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a := fun a ha d hd =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨d, hDA hd⟩)
  rw [eq_bot_iff, commutator_le]
  intro g hg a ha
  rw [mem_bot]
  have hcΔ : ⁅g, a⁆ ∈ localDeltaIn p H D := by
    rw [commutatorElement_def]
    have h1 : a * g⁻¹ * a⁻¹ ∈ localDeltaIn p H D :=
      w3_conj_mem_localDeltaIn hp (hAH ha) (hAD a ha) (inv_mem hg)
    simpa [mul_assoc] using mul_mem hg h1
  obtain ⟨C0, hC⟩ := MonoidHom.mem_range.1 (hcomm g a)
  rw [← commutatorElement_def] at hC
  have hCA : ρ C0 * ρ A0 = ρ A0 * ρ C0 := by
    rw [hC]; exact w3_commute_of_mem_localDeltaIn hx hx1 hcΔ
  have hCB : ρ C0 * ρ B0 = ρ B0 * ρ C0 := by
    rw [hC]; exact w3_commute_of_mem_localDeltaIn hy hy1 hcΔ
  obtain ⟨α, hα⟩ := hker (C0 * A0 * C0⁻¹ * A0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hCA]; group)
  obtain ⟨β, hβ⟩ := hker (C0 * B0 * C0⁻¹ * B0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hCB]; group)
  simp only [map_mul, map_inv] at hα hβ
  have hCA' := rel_AB hα
  have hCB' := rel_AB hβ
  obtain ⟨i, j, m, hm⟩ := heisenberg_normalizer_p hω hz hpK (pow_eq_one_of_conj ha0 hCA')
    (pow_eq_one_of_conj hb0 hCB') hCA' hCB'
  have hm0 : ρ ((A0 ^ i * B0 ^ j)⁻¹ * C0) = 1 := by
    refine hscalar _ m ?_
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, hm, inv_mul_cancel_left]
  have hcD : ⁅g, a⁆ ∈ D := by
    have hC0 : C0 = (A0 ^ i * B0 ^ j) * ((A0 ^ i * B0 ^ j)⁻¹ * C0) := by group
    rw [← hC, hC0, map_mul, hm0, mul_one, map_mul, map_pow, map_pow]
    exact mul_mem (pow_mem hx i) (pow_mem hy j)
  have hcop := w3_coprime_orderOf_of_mem_localDeltaIn hp hx hx1 hcΔ
  have hdvd : orderOf ⁅g, a⁆ ∣ p := orderOf_dvd_of_pow_eq_one (hDe.2 _ hcD)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

end Model

section Linear

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem weakBalance_projectiveSL (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) :
    IsWeaklyLocallyBalancedAbs p 2 (projectiveSL p F) := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hpF' : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    have hc : 1 ≤ Nat.card F := Nat.card_pos
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  refine isWeaklyLocallyBalancedAbs_of_model hp
    (CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpF') (MonoidHom.id _)
    (fun _ _ h => h) (conjAut p F) (fun g hg => ?_) (fun g c hg => ?_) ?_ ?_ ?_
  · obtain ⟨c, hc⟩ := Heis.eq_scalar_of_conjAut_eq_one hn hg
    exact ⟨c, hc.symm⟩
  · rw [MonoidHom.id_apply] at hg
    rw [hg]
    exact conjAut_scalar_eq_one c
  · intro A B hAB hAp hBp hA1 hBA H hH hnorm
    exact diagAbelianPlaneBalance_holds p F hn p hp hp2 hpF dvd_rfl A B hAB hAp hBp hA1 hBA H hH
      hnorm
  · intro D hD hDl H hH
    exact localDeltaIn_eq_bot_of_not_le_linearAutGroup hn hp hp2 hpF hD
      (fun h => hDl fun x hx => MonoidHom.mem_range.2 (mem_linearAutGroup_iff.1 (h hx))) hH
  · intro α β
    exact MonoidHom.mem_range.2 (mem_linearAutGroup_iff.1
      (OuterDerived.commutator_mem_linearAutGroup hn α β))

end Linear

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {n p : ℕ}

theorem primeFormConjHom_eq_one_of_scalar (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {X : primeFormUnitary h (idGram K n)} {m : Kˣ}
    (hX : (X : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) m) :
    primeFormConjHom h (idGram K n) X = 1 := by
  have : NeZero n := ⟨by omega⟩
  refine (primeFormConjHom_eq_one_iff_of_ne hn hne X).2 ⟨m, ?_, hX⟩
  have hb := bar_mul_self_of_scalar_mem h (hX ▸ X.2)
  refine (pow_succ_eq_one_iff_norm h m).mpr ?_
  rw [UnitaryFieldData.norm, mul_comm]
  exact hb

theorem primeFormUnitary_exists_comm_scalar (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {X Y : primeFormUnitary h (idGram K n)}
    (hXY : primeFormConjHom h (idGram K n) X * primeFormConjHom h (idGram K n) Y =
      primeFormConjHom h (idGram K n) Y * primeFormConjHom h (idGram K n) X) :
    ∃ z : Kˣ, (X : GL (Fin n) K) * Y = GeneralLinearGroup.scalar (Fin n) z * (Y * X) := by
  have h1 : primeFormConjHom h (idGram K n) (X * Y * X⁻¹ * Y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hXY]
    group
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).1 h1
  refine ⟨c, ?_⟩
  rw [← hc]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

include h in
theorem three_lt_of_dvd_add_one (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    (hpq : p ∣ ℓ ^ f + 1) : 3 < ℓ ^ f := by
  have h2 : 2 ≤ ℓ ^ f :=
    le_trans h.prime.two_le (Nat.le_self_pow (by have := h.one_le; omega) ℓ)
  by_contra hlt
  rcases (by omega : ℓ ^ f = 2 ∨ ℓ ^ f = 3) with hq | hq
  · rw [hq] at hpq
    exact hne ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpq, hq⟩
  · rw [hq, show (3 + 1 : ℕ) = 2 ^ 2 by norm_num] at hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpq))

theorem not_three_pow_div_eq_two (hne : ¬(p = 3 ∧ ℓ ^ f = 2)) (h8 : ¬(p = 3 ∧ ℓ ^ f = 8))
    {D : Subgroup (MulAut (primeFormP h (idGram K p)))} (hDe : IsElemAbelian p D)
    (hDl : ¬ D ≤ primeFormD h (idGram K p)) : ¬(p = 3 ∧ ℓ ^ (f / p) = 2) := by
  rintro ⟨rfl, h2⟩
  have := h.finite
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, hxl⟩ := Set.not_subset.1 hDl
  set φ := primeFormFieldFactor h isPrimeFormGram_one le_rfl hne x with hφ
  have hφ1 : φ ≠ 1 := by
    intro e
    apply hxl
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one le_rfl hne]
    exact e
  have hφ3 : φ ^ 3 = 1 := by rw [hφ, ← map_pow, hDe.2 x hx, map_one]
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hcard := (card_ringAut_and_isCyclic h.prime K h.card).1
  have hdvd : 3 ∣ 2 * f := by
    rw [← hord, ← hcard]
    exact orderOf_dvd_natCard φ
  have h3f : 3 ∣ f := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hdvd
  have hk : f / 3 ≠ 0 := by
    intro hk
    rw [hk, pow_zero] at h2
    norm_num at h2
  have hl : ℓ = 2 := by
    have hd : ℓ ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self ℓ hk
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact absurd h1 h.prime.one_lt.ne'
    · exact h1
  subst hl
  have hk1 : f / 3 = 1 := by
    have : (2 : ℕ) ^ (f / 3) = 2 ^ 1 := by rw [h2, pow_one]
    exact Nat.pow_right_injective le_rfl this
  have hf : f = 3 := by
    obtain ⟨c, rfl⟩ := h3f
    omega
  subst hf
  exact h8 ⟨rfl, by norm_num⟩

theorem weakBalance_primeFormP (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    (h8 : ¬(p = 3 ∧ ℓ ^ f = 8)) (hpq : p ∣ ℓ ^ f + 1) :
    IsWeaklyLocallyBalancedAbs p 2 (primeFormP h (idGram K p)) := by
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primeFormP h (idGram K p)) := finite_primeFormP
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hpℓ : ¬ p ∣ ℓ := by
    intro hd
    have h1 : p ∣ ℓ ^ f := hd.trans (dvd_pow_self ℓ (by have := h.one_le; omega))
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpq))
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp ?_
    rw [h.card]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow hd)
  have hq3 := three_lt_of_dvd_add_one h hp hp2 hne hpq
  refine isWeaklyLocallyBalancedAbs_of_model hp hpK (primeFormUnitary h (idGram K p)).subtype
    (Subgroup.subtype_injective _) (primeFormConjHom h (idGram K p)) (fun g hg => ?_)
    (fun g c hg => primeFormConjHom_eq_one_of_scalar h hn hne hg) ?_ ?_ ?_
  · obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne g).1 hg
    exact ⟨c, hc⟩
  · intro A B hAB hAp hBp hA1 hBA H hH _
    exact localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq hAB hAp hBp hA1 hBA hH
  · intro D hD hDl H hH
    exact localDeltaIn_eq_bot_of_not_le_primeFormD h hn hne hp hp2 hpq
      (not_three_pow_div_eq_two h hne h8 hD hDl) hD hDl hH
  · intro α β
    have := commutator_mem_primeFormD_of_ne (h := h) hn hne α β
    rwa [commutatorElement_def] at this

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator
