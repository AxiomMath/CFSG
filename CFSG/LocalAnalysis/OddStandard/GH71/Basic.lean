module

public import CFSG.GH74.GLS.Balance.Step3Basic
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem le_pPrimeCore_of_normal_odd {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ pPrimeCore 2 X :=
  le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩

theorem le_pPrimeCoreOf_of_odd {H W : Subgroup G} (hWH : W ≤ H) (hodd : Odd (Nat.card W))
    (hn : H ≤ normalizer (W : Set G)) : W ≤ pPrimeCoreOf 2 H := by
  have hnorm : (W.subgroupOf H).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (hn g.2) n).mp hn'
    exact h1
  have hcard : Nat.card (W.subgroupOf H) = Nat.card W :=
    Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv
  have hle := le_pPrimeCore_of_normal_odd hnorm (hcard ▸ hodd)
  intro w hw
  exact ⟨⟨w, hWH hw⟩, hle (show (⟨w, hWH hw⟩ : ↥H) ∈ W.subgroupOf H from hw), rfl⟩

theorem pPrimeCoreOf_le' (H : Subgroup G) : pPrimeCoreOf 2 H ≤ H :=
  TwoThin.pPrimeCoreOf_le H

theorem le_normalizer_pPrimeCoreOf' (H : Subgroup G) :
    H ≤ normalizer (pPrimeCoreOf 2 H : Set G) :=
  Balance.le_normalizer_pPrimeCoreOf H

theorem odd_card_pPrimeCoreOf' [Finite G] (H : Subgroup G) : Odd (Nat.card (pPrimeCoreOf 2 H)) :=
  Balance.odd_card_pPrimeCoreOf H

theorem odd_card_of_le [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (hB : Odd (Nat.card B)) :
    Odd (Nat.card A) :=
  Odd.of_dvd_nat hB (card_dvd_of_le hAB)

theorem pPrimeCoreOf_inf_le [Finite G] {H K : Subgroup G} (hKH : K ≤ H) :
    pPrimeCoreOf 2 H ⊓ K ≤ pPrimeCoreOf 2 K := by
  refine le_pPrimeCoreOf_of_odd inf_le_right
    (odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' H)) ?_
  intro k hk
  exact inf_normalizer_le_normalizer_inf ⟨le_normalizer_pPrimeCoreOf' H (hKH hk), le_normalizer hk⟩

theorem not_two_dvd_of_odd {n : ℕ} (h : Odd n) : ¬ 2 ∣ n := fun h2 =>
  (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

theorem mem_map_conj {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem fusionIsSylowIn_map_conj {p : ℕ} {P N : Subgroup G} (hP : Open.fusionIsSylowIn p P N)
    {g : G} (hg : g ∈ normalizer (N : Set G)) :
    Open.fusionIsSylowIn p (P.map (MulAut.conj g).toMonoidHom) N := by
  obtain ⟨hPN, hPp, hmax⟩ := hP
  have hg' : g⁻¹ ∈ normalizer (N : Set G) := inv_mem hg
  refine ⟨?_, hPp.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp (hPN hy)
  · intro Q hQN hQp hPQ
    have h1 : Q.map (MulAut.conj g⁻¹).toMonoidHom = P := by
      refine (hmax _ ?_ (hQp.map _) ?_).symm.symm
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hg' y).mp (hQN hy)
      · intro x hx
        refine ⟨g * x * g⁻¹, hPQ ⟨x, hx, rfl⟩, ?_⟩
        simp [mul_assoc]
    rw [← h1, map_map]
    have : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) = MonoidHom.id G := by
      ext x; simp [mul_assoc]
    rw [this, map_id]

theorem exists_conj_sylow [Finite G] {p : ℕ} (hp : p.Prime) {Y P P' : Subgroup G}
    (hP : Open.fusionIsSylowIn p P Y) (hP' : Open.fusionIsSylowIn p P' Y) :
    ∃ c ∈ Y, P' = P.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨r, hr1, hr⟩ := Nat.exists_infinite_primes (Nat.card Y + 1)
  have hrY : ¬ r ∣ Nat.card Y := fun h =>
    absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  have h2 : IsPGroup r ↥(⊥ : Subgroup G) := IsPGroup.of_bot
  obtain ⟨c, hc, hEq⟩ := Goldschmidt.G310.exists_conj_of_invariant_sylows hr hp h2
    hrY (by simp) hP hP' (by simp) (by simp)
  exact ⟨c, (mem_inf.mp hc).1, hEq⟩

theorem exists_conj_sylow_of_odd [Finite G] {p : ℕ} (hp : p.Prime) {N P P' : Subgroup G}
    (hN : Odd (Nat.card N)) (hP : Open.fusionIsSylowIn p P N) (hP' : Open.fusionIsSylowIn p P' N) :
    ∃ c ∈ N, P' = P.map (MulAut.conj c).toMonoidHom := by
  have h2 : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_bot
  obtain ⟨c, hc, hEq⟩ := Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_two hp h2
    (not_two_dvd_of_odd hN) (by simp) hP hP' (by simp) (by simp)
  exact ⟨c, (mem_inf.mp hc).1, hEq⟩

end CFSG.OddStandard.GH71
