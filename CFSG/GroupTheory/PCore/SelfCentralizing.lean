module

public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG

open CFSG.Open

theorem gLAPPrimeCoreOf_inf_eq_bot_of_normal_simple {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {N X : Subgroup G} (hNX : N ≤ X)
    (hNn : (N.subgroupOf X).Normal) (hN : IsSimpleGroup ↥N) (hpN : p ∣ Nat.card N) :
    GLAPPrimeCoreOf p X ⊓ N = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O := GLAPPrimeCoreOf p X
  have hOX : O ≤ X := Subgroup.map_subtype_le _
  have hOn : (O.subgroupOf X).Normal :=
    gLAPPrimeCoreOf_normal p X
  have hONn : ((O ⊓ N).subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact Subgroup.mem_inf.2
      ⟨(Subgroup.normal_subgroupOf_iff hOX).1 hOn h k (Subgroup.mem_inf.1 hh).1
          (hNX hk),
       (Subgroup.normal_subgroupOf_iff hNX).1 hNn h k (Subgroup.mem_inf.1 hh).2 (hNX hk)⟩
  haveI := hONn
  have hcop : Nat.Coprime p (Nat.card ↥(O ⊓ N)) := by
    have hcopO : Nat.Coprime p (Nat.card O) := by
      rw [show O = GLAPPrimeCoreOf p X from rfl, GLAPPrimeCoreOf, GLAPPrimeCore]
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact pPrimeCore_coprime_card (p := p) (G := ↥X)
    exact hcopO.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  rcases hN.eq_bot_or_eq_top_of_normal ((O ⊓ N).subgroupOf N) with h | h
  · refine (Subgroup.eq_bot_iff_forall _).2 ?_
    intro x hx
    have hxN : x ∈ N := (Subgroup.mem_inf.1 hx).2
    have hmem : (⟨x, hxN⟩ : ↥N) ∈ (O ⊓ N).subgroupOf N := Subgroup.mem_subgroupOf.2 hx
    rw [h] at hmem
    simpa using hmem
  · exfalso
    have hNO : N ≤ O := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥N) ∈ (O ⊓ N).subgroupOf N := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).1
    exact (hp.coprime_iff_not_dvd.1 hcop) (hpN.trans (Subgroup.card_dvd_of_le (le_inf hNO le_rfl)))

theorem gLAPPrimeCoreOf_eq_bot_of_normal_simple_of_pow_mem {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {T X : Subgroup G} (hTX : T ≤ X) (hTn : (T.subgroupOf X).Normal)
    (hT : IsSimpleGroup ↥T) (hpT : p ∣ Nat.card T) (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ (p ^ k) ∈ T) :
    GLAPPrimeCoreOf p X = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hOT : GLAPPrimeCoreOf p X ⊓ T = ⊥ :=
    gLAPPrimeCoreOf_inf_eq_bot_of_normal_simple hp hTX hTn hT hpT
  rw [eq_bot_iff]
  intro x hx
  have hxX : x ∈ X := Subgroup.map_subtype_le (pPrimeCore p ↥X) hx
  obtain ⟨k, hk⟩ := hpow x hxX
  have hxkO : x ^ (p ^ k) ∈ GLAPPrimeCoreOf p X := (GLAPPrimeCoreOf p X).pow_mem hx (p ^ k)
  have hxk : x ^ (p ^ k) = 1 := by
    have hmem : x ^ (p ^ k) ∈ GLAPPrimeCoreOf p X ⊓ T := Subgroup.mem_inf.2 ⟨hxkO, hk⟩
    rwa [hOT, Subgroup.mem_bot] at hmem
  have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hcopO : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X)) := by
    rw [GLAPPrimeCoreOf, GLAPPrimeCore, Subgroup.card_map_of_injective X.subtype_injective]
    exact pPrimeCore_coprime_card (p := p) (G := ↥X)
  have hcop : Nat.Coprime (orderOf x) (p ^ k) :=
    (hcopO.coprime_dvd_right (Subgroup.orderOf_dvd_natCard (GLAPPrimeCoreOf p X) hx)).symm.pow_right k
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd))

theorem gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card {Y : Type*} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (hY : IsSimpleGroup Y) (hdvd : p ∣ Nat.card Y) :
    GLAPPrimeCore p Y = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p Y)) := pPrimeCore_coprime_card
  rcases hY.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p Y) with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact hp.coprime_iff_not_dvd.1 hcop hdvd

end CFSG
