module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PrimePowMod
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

@[expose] def RankOK (p : ℕ) {M : Type*} [Group M] (C : Subgroup M) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ p → ∀ V : Subgroup M, V ≤ C → IsElemAbelian q V → V ≠ ⊥ →
    Nat.card V % p ≠ 1

theorem rankOK_of_primePowOK {M : Type*} [Group M] [Finite M] {p : ℕ} {C : Subgroup M}
    (h : PrimePowOK p (Nat.card C)) : RankOK p C := by
  intro q hq hqp V hV hVel hVne
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.1 hVel.isPGroup
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      apply hVne
      apply Subgroup.eq_bot_of_card_eq
      rw [hs, h0, pow_zero]
    · exact h0
  rw [hs]
  exact h q s hq hqp hs0 (hs ▸ Subgroup.card_dvd_of_le hV)

theorem inf_centralizer_conj_eq {M : Type*} [Group M] (B : Subgroup M) {g : M} (hg : g ∈ B)
    (y' : M) :
    B ⊓ Subgroup.centralizer ({g * y' * g⁻¹} : Set M) =
      (B ⊓ Subgroup.centralizer ({y'} : Set M)).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨hxB, hxC⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · exact B.mul_mem (B.mul_mem (B.inv_mem hg) hxB) hg
    · have hxC' : x * (g * y' * g⁻¹) = (g * y' * g⁻¹) * x :=
        Subgroup.mem_centralizer_singleton_iff.1 hxC
      show g⁻¹ * x * g ∈ Subgroup.centralizer ({y'} : Set M)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * y' = g⁻¹ * (x * (g * y' * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y' * g⁻¹) * x) * g := by rw [hxC']
        _ = y' * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hyB, hyC⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply] using B.mul_mem (B.mul_mem hg hyB) (B.inv_mem hg)
    · have hyC' : y * y' = y' * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
      show (MulAut.conj g).toMonoidHom y ∈ Subgroup.centralizer ({g * y' * g⁻¹} : Set M)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * y * g⁻¹ * (g * y' * g⁻¹) = g * (y * y') * g⁻¹ := by group
        _ = g * (y' * y) * g⁻¹ := by rw [hyC']
        _ = g * y' * g⁻¹ * (g * y * g⁻¹) := by group

theorem rankOK_map_conj {M : Type*} [Group M] {p : ℕ} {C : Subgroup M} (h : RankOK p C) (g : M) :
    RankOK p (C.map (MulAut.conj g).toMonoidHom) := by
  intro q hq hqp V hV hVel hVne
  set V' : Subgroup M := V.map (MulAut.conj g⁻¹).toMonoidHom with hV'
  have hV'C : V' ≤ C := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := hV hv
    have : (MulAut.conj g⁻¹).toMonoidHom v = c := by
      rw [← hcv]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hc
  have hcard : Nat.card V' = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hne : V' ≠ ⊥ := fun hbot => hVne
    ((Subgroup.map_eq_bot_iff_of_injective V (MulAut.conj g⁻¹).injective).1 hbot)
  have := h q hq hqp V' hV'C (hVel.map _) hne
  rwa [hcard] at this

theorem rankOK_inf_centralizer_conj {M : Type*} [Group M] {p : ℕ} (B : Subgroup M) {g : M}
    (hg : g ∈ B) {y' : M} (h : RankOK p (B ⊓ Subgroup.centralizer ({y'} : Set M))) :
    RankOK p (B ⊓ Subgroup.centralizer ({g * y' * g⁻¹} : Set M)) := by
  rw [inf_centralizer_conj_eq B hg y']
  exact rankOK_map_conj h g

theorem rankOK_inf_centralizer_of_conj {M : Type*} [Group M] {p : ℕ} (B : Subgroup M) {g : M}
    (hg : g ∈ B) {y z : M} (hyz : g * y * g⁻¹ = z)
    (h : RankOK p (B ⊓ Subgroup.centralizer ({z} : Set M))) :
    RankOK p (B ⊓ Subgroup.centralizer ({y} : Set M)) := by
  have h1 : g⁻¹ * z * (g⁻¹)⁻¹ = y := by rw [← hyz]; group
  have := rankOK_inf_centralizer_conj B (B.inv_mem hg) (y' := z) h
  rwa [h1] at this

theorem rankOK_of_two_witness {M : Type*} [Group M] [Finite M] {p : ℕ} {C : Subgroup M} {n : ℕ}
    (hn : Nat.card C = n)
    (hcheck : ∀ q k : ℕ, q.Prime → q ≠ p → 0 < k → q ^ k ∣ n → q ^ k % p = 1 →
      q = 2 ∧ ¬ 2 ^ (k + 1) ∣ n)
    (hw : ∃ c ∈ C, orderOf c = 4) : RankOK p C := by
  intro q hq hqp V hVC hVel hVne hmod
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.1 hVel.isPGroup
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      apply hVne
      apply Subgroup.eq_bot_of_card_eq
      rw [hs, h0, pow_zero]
    · exact h0
  have hdvd : q ^ s ∣ n := hn ▸ hs ▸ Subgroup.card_dvd_of_le hVC
  obtain ⟨hq2, hnd⟩ := hcheck q s hq hqp hs0 hdvd (hs ▸ hmod)
  subst hq2
  have hn0 : n ≠ 0 := hn ▸ Nat.card_pos.ne'
  have hfac : (Nat.card C).factorization 2 = s := by
    rw [hn]
    have h1 : s ≤ n.factorization 2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).1 hdvd
    have h2 : ¬ s + 1 ≤ n.factorization 2 := fun h =>
      hnd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).2 h)
    omega
  have hVcard : Nat.card (V.subgroupOf C) = 2 ^ s := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, hs]
  let SV : Sylow 2 ↥C := Sylow.ofCard (V.subgroupOf C) (by rw [hVcard, hfac])
  have hSV : (SV : Subgroup ↥C) = V.subgroupOf C := rfl
  obtain ⟨c, hcC, hc4⟩ := hw
  have hc4' : orderOf (⟨c, hcC⟩ : ↥C) = 4 := by rw [Subgroup.orderOf_mk, hc4]
  have hpg : IsPGroup 2 (Subgroup.zpowers (⟨c, hcC⟩ : ↥C)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hc4']; norm_num)
  obtain ⟨S', hS'⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C SV S'
  have hcS' : (⟨c, hcC⟩ : ↥C) ∈ (S' : Subgroup ↥C) := hS' (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, hSV] at hcS'
  obtain ⟨v, hv, hvc⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hcS'
  have hv2 : v ^ 2 = 1 := by
    have := hVel.2 (v : M) (Subgroup.mem_subgroupOf.1 hv)
    exact Subtype.ext this
  have hc2 : (⟨c, hcC⟩ : ↥C) ^ 2 = 1 := by
    rw [← hvc]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    rw [conj_pow, hv2, mul_one, mul_inv_cancel]
  have : orderOf (⟨c, hcC⟩ : ↥C) ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
  rw [hc4'] at this
  omega

end CFSG.HardMathSupport.Dickson.I271
