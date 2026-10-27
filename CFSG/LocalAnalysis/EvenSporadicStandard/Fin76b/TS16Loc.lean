module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Rung
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Extremal

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def ExtremalParity : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q : Subgroup G) (z : G) (c : ℕ),
    Q ≤ M → IsPGroup 2 Q → ¬ 2 ∣ (Q.subgroupOf M).index → z ∈ Q → z * z = 1 →
    (∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ M ⊓ centralizer ({z} : Set G) ∧ Nat.card R = c) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ M ⊓ centralizer ({z} : Set G) → Nat.card R ≤ c) →
    Odd (Nat.card (extremalClasses M Q z c))

@[expose] def Fin76bOuterS16Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G) (Q : Sylow 2 G)
    (x : G) (B : Subgroup G) (β : G), OuterS16Hyp G L z t T E Q x B β →
    ∃ (M Q' P : Subgroup G), Q' ≤ M ∧ IsPGroup 2 Q' ∧ ¬ 2 ∣ (Q'.subgroupOf M).index ∧ z ∈ Q' ∧
      P ≤ Q' ∧ P.relIndex Q' = 2 ∧ z ∉ P ∧
      (∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ M ⊓ centralizer ({z} : Set G) ∧ Nat.card R = 512) ∧
      (∀ y ∈ Q', (∃ g : G, y = g * z * g⁻¹) →
        Nat.card ↥(Q' ⊓ centralizer ({y} : Set G)) = 512 → ∃ m ∈ M, y = m * z * m⁻¹) ∧
      ∀ η ∈ P, η * η = 1 → η ≠ 1 →
        ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ centralizer ({η} : Set G) ∧ 512 < Nat.card R

theorem fin76bOuterS16Cent_of_loc (hPar : ExtremalParity) (hLoc : Fin76bOuterS16Loc) :
    Fin76bOuterS16Cent := by
  intro G _ _ L z t T E Q x B β h
  obtain ⟨M, Q', P, hQM, hQ2, hidx, hzQ, hPQ, hPidx, hzP, hR, hext, hcent⟩ :=
    hLoc G L z t T E Q x B β h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ∀ (g : G) (R : Subgroup G), IsPGroup 2 R →
      R ≤ centralizer ({g * z * g⁻¹} : Set G) → Nat.card R ≤ 512 := by
    intro g R hR hRc
    have h1 := h.outerE.cfg.card_le_of_two_subgroup_cent_conj hR hRc
    rw [h.cardT] at h1
    exact h1
  have hcmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M ⊓ centralizer ({z} : Set G) →
      Nat.card R ≤ 512 := by
    intro R hR hRc
    refine hc 1 R hR ?_
    rw [one_mul, inv_one, mul_one]
    exact fun r hr => (hRc hr).2
  have hodd := hPar G M Q' z 512 hQM hQ2 hidx hzQ h.outerE.cfg.z_sq hR hcmax
  have hSyl : ¬ 2 ∣ Q'.index := not_dvd_index_of_odd_extremalClasses hQ2 hc hext hodd
  exact ⟨hQ2.toSylow hSyl, P, by simpa using hzQ, by simpa using hPQ, by simpa using hPidx, hzP,
    hcent⟩

end CFSG.EvenSporadicStandard.Fin76b
