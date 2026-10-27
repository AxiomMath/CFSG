module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

variable {G : Type*} [Group G] [Finite G] {X Q : Type*} [Group X] [Group Q] [Finite Q]
  [IsCyclic Q]

theorem exists_normal_index_two_of_graphField {M : Subgroup G} (ρ : M →* MulAut X)
    (hker : Odd (Nat.card ρ.ker)) (hInn : ∀ g : X, ∃ m : M, ρ m = MulAut.conj g)
    (Φ : MulAut X →* Q) (hΦInn : ∀ g : X, Φ (MulAut.conj g) = 1)
    (s : Q →* MulAut X) (hs : ∀ c, Φ (s c) = c)
    (γ : MulAut X) (hγ2 : γ * γ = 1) (hΦγ : Φ γ = 1) (hγs : ∀ c, γ * s c = s c * γ)
    (hNF : ∀ α : MulAut X, ∃ g : X, ∃ c : Q,
      α = MulAut.conj g * s c ∨ α = MulAut.conj g * γ * s c)
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2) (hts : ρ ⟨t, htM⟩ ∈ s.range)
    (hΦt : Φ (ρ ⟨t, htM⟩) ≠ 1) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup Q := IsCyclic.commGroup
  set α := ρ ⟨t, htM⟩ with hαdef
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hα2 : α ^ 2 = 1 := EPilot.action_sq_eq_one ρ htM ht2
  obtain ⟨ι, hι⟩ := hts
  have hΦα : Φ α = ι := by rw [← hι, hs]
  have hι1 : ι ≠ 1 := by rw [← hΦα]; exact hΦt
  have hι2 : ι ^ 2 = 1 := by rw [← hΦα, ← map_pow, hα2, map_one]
  set R := (Φ.comp ρ).range with hR
  have hιR : ι ∈ R := ⟨⟨t, htM⟩, by rw [MonoidHom.comp_apply, ← hαdef, hΦα]⟩
  have hιp : IsPGroup 2 (zpowers (⟨ι, hιR⟩ : R)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, pow_one]
    exact orderOf_eq_prime hι2 hι1
  obtain ⟨P', hP'⟩ := hιp.exists_le_sylow
  have hιP' : (⟨ι, hιR⟩ : R) ∈ (P' : Subgroup R) := hP' (mem_zpowers _)
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := (P' : Subgroup R))
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 P'.isPGroup'
  have hc₀o : orderOf c₀ = 2 ^ a := (orderOf_eq_card_of_forall_mem_zpowers hc₀).trans ha
  set c : Q := ((c₀ : R) : Q) with hcdef
  have hco : orderOf c = 2 ^ a := by
    rw [hcdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc₀o]
  have hRidx : ¬ 2 ^ (a + 1) ∣ Nat.card R := by
    intro hdvd
    rw [← (P' : Subgroup R).card_mul_index, ha, pow_succ] at hdvd
    exact P'.not_dvd_index (Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd)
  have ha1 : 1 ≤ a := by
    by_contra h0
    obtain rfl : a = 0 := by omega
    have hcard1 : Nat.card (P' : Subgroup R) = 1 := by rw [ha, pow_zero]
    have hsub : Subsingleton (P' : Subgroup R) := (Nat.card_eq_one_iff_unique.1 hcard1).1
    have h1 : (⟨_, hιP'⟩ : (P' : Subgroup R)) = 1 := Subsingleton.elim _ _
    exact hι1 (congrArg (fun z : (P' : Subgroup R) => ((z : R) : Q)) h1)
  set H : Subgroup M := (Φ.comp ρ).ker with hH
  have hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ H) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (Φ.comp ρ)).toEquiv]
    exact hRidx
  have hordQ : ∀ m : M, orderOf (QuotientGroup.mk' H m) = orderOf (Φ (ρ m)) := by
    intro m
    rw [← orderOf_injective _ (QuotientGroup.kerLift_injective (Φ.comp ρ))]
    change orderOf (QuotientGroup.kerLift (Φ.comp ρ) (m : M ⧸ (Φ.comp ρ).ker)) = _
    rw [QuotientGroup.kerLift_mk, MonoidHom.comp_apply]
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    obtain rfl : a = 1 := by omega
    have hxQ : orderOf (QuotientGroup.mk' H ⟨t, htM⟩) = 2 ^ 1 := by
      rw [hordQ, ← hαdef, hΦα, pow_one]
      exact orderOf_eq_prime hι2 hι1
    exact EPilot.exists_normal_index_two_of_unique_of_quotientSub H huniq htM le_rfl
      (by rw [ht, pow_one]) hxQ hQ (n := 1) (by rw [pow_one])
  obtain ⟨m, hm⟩ : c ∈ R := (c₀ : R).2
  have hzA : ∃ z ∈ ρ.range, Φ z = c ∧ z ^ 2 ^ (a - 1) = s (c ^ 2 ^ (a - 1)) ∧
      z ^ 2 ^ a = 1 := by
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by rw [← pow_succ]; congr 1; omega
    have hsca : s c ^ 2 ^ a = 1 := by rw [← map_pow, ← hco, pow_orderOf_eq_one, map_one]
    have hγpow : γ ^ 2 ^ (a - 1) = 1 := by
      obtain ⟨b, hb⟩ : ∃ b, a - 1 = b + 1 := ⟨a - 2, by omega⟩
      rw [hb, pow_succ', pow_mul, sq, hγ2, one_pow]
    obtain ⟨g, c', hgc | hgc⟩ := hNF (ρ m)
    · have hc' : c' = c := by
        have h1 := congrArg Φ hgc
        rw [map_mul, hΦInn, one_mul, hs] at h1
        rw [← h1]
        exact hm
      rw [hc'] at hgc
      obtain ⟨m', hm'⟩ := hInn g
      refine ⟨s c, ⟨m'⁻¹ * m, ?_⟩, hs c, (map_pow s c _).symm, hsca⟩
      rw [map_mul, map_inv, hm', hgc, inv_mul_cancel_left]
    · have hc' : c' = c := by
        have h1 := congrArg Φ hgc
        rw [map_mul, map_mul, hΦInn, hΦγ, one_mul, one_mul, hs] at h1
        rw [← h1]
        exact hm
      rw [hc'] at hgc
      obtain ⟨m', hm'⟩ := hInn g
      have hcomm : Commute γ (s c) := hγs c
      refine ⟨γ * s c, ⟨m'⁻¹ * m, ?_⟩, by rw [map_mul, hΦγ, hs, one_mul], ?_, ?_⟩
      · rw [map_mul, map_inv, hm', hgc, mul_assoc, inv_mul_cancel_left]
      · rw [hcomm.mul_pow, hγpow, one_mul, map_pow]
      · rw [hcomm.mul_pow, ← h2a, pow_mul, hγpow, one_pow, one_mul, h2a, hsca]
  obtain ⟨z, hzA, hΦz, hzpow, hz1⟩ := hzA
  have hcpow : c ^ 2 ^ (a - 1) = ι := by
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by rw [← pow_succ]; congr 1; omega
    refine EPilot.eq_of_sq_eq_one_of_ne_one_of_isCyclic ?_ hι2 ?_ hι1
    · rw [← pow_mul, h2a, ← hco, pow_orderOf_eq_one]
    · intro h1
      have := orderOf_le_of_pow_eq_one (by positivity) h1
      rw [hco] at this
      have : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  have hzo : orderOf z = 2 ^ a := by
    have hΦo : orderOf (Φ z) ∣ orderOf z := orderOf_map_dvd Φ z
    rw [hΦz, hco] at hΦo
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hz1) hΦo
  obtain ⟨x, hxρ, hxo⟩ := LinearPilot.exists_orderOf_eq_of_odd_ker ρ hker hzA hzo
  have hxQ : orderOf (QuotientGroup.mk' H ⟨(x : G), x.2⟩) = 2 ^ a := by
    rw [hordQ, Subtype.coe_eta, hxρ, hΦz, hco]
  have hxpowM : (x : G) ^ 2 ^ (a - 1) ∈ M := pow_mem x.2 _
  have hρx : ρ ⟨(x : G) ^ 2 ^ (a - 1), hxpowM⟩ = α := by
    have h1 : (⟨(x : G) ^ 2 ^ (a - 1), hxpowM⟩ : M) = x ^ 2 ^ (a - 1) := Subtype.ext (by simp)
    rw [h1, map_pow, hxρ, hzpow, hcpow, hι]
  have hxsq : ((x : G) ^ 2 ^ (a - 1)) ^ 2 = 1 := by
    rw [← pow_mul, show 2 ^ (a - 1) * 2 = 2 ^ a by rw [← pow_succ]; congr 1; omega,
      ← hxo, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  have hconj : IsConj t ((x : G) ^ 2 ^ (a - 1)) :=
    EPilot.isConj_of_action_eq ρ hker htM hxpowM ht2 hxsq hρx.symm
  exact EPilot.exists_normal_index_two_of_unique_of_quotientSub H huniq x.2 ha1
    (by rw [Subgroup.orderOf_coe, hxo]) hxQ hQ hconj

end CFSG.SeitzReduction.OmegaPilot
