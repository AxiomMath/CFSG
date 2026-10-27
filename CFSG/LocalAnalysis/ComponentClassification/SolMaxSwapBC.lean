module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem exists_typed_pump (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hs : Setting t J n e E D M) (hn : 13 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N₁ : Subgroup X} (hP : PumpData M e₀ r N₁) :
    ∃ N : Subgroup X, N ≤ centralizer ({r} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))) ∧
      fixA M e₀ r ≤ N ⊔ conjBy N e₀ ∧ (N = N₁ ∨ N = conjBy N₁ e₀) ∧
      ∃ (m : ℕ) (_ : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m)), n - 4 ≤ m ∧ m ≤ n ∧
        (m = n - 4 ∨ (conjBy N e₀ = N ∧
          IsPComponent 2 ((fixA M e₀ r).subgroupOf (N ⊓ centralizer ({e₀} : Set X))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({r} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top S.kProper (centralizer_ne_top_of_ne_one S.nonab hd.r1)
  have hkodd : Odd (n - 4) := by
    obtain ⟨a, ha⟩ := S.pair.2.1
    exact ⟨a - 2, by omega⟩
  obtain ⟨N, hNC, hNpc, hAN, hlayer, htype⟩ :=
    pump_type_in hPump hK he₀r he₀o hArle hArpc hkodd (by omega) χr
  have hNN₁ := eq_or_eq_of_pumpData he₀r he₀2 hP hNC hNpc hAN
  refine ⟨N, hNC, hNpc, hAN, hNN₁, ?_⟩
  have hT : zpowers r ≠ ⊥ := fun h => hd.r1 (zpowers_eq_bot.mp h)
  have hCr : centralizer ((zpowers r : Subgroup X) : Set X) = centralizer ({r} : Set X) :=
    centralizer_zpowers_eq' r
  have hNC' : N ≤ centralizer ((zpowers r : Subgroup X) : Set X) := by rw [hCr]; exact hNC
  have hNpc' : IsPComponent 2 (N.subgroupOf (centralizer ((zpowers r : Subgroup X) : Set X))) := by
    rw [hCr]
    exact hNpc
  have hZ : ∀ m : ℕ, Odd m → 9 ≤ m → (↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin m)) →
      ∃ θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m), m ≤ n := by
    intro m hmo hm9 eN
    have hZ := hN1 X S.nonab S.kProper S.unbal S.notU (zpowers r) m N hT
      (isPGroup_zpowers_of_mul_self hd.r2) hmo hm9 hNC' hNpc' ⟨eN⟩
    let θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eN
    exact ⟨θN, S.pair.2.2.2.1 r N m ⟨hr2, hNC, hNpc, ⟨θN⟩⟩ hmo⟩
  rcases htype with ⟨hfix, ⟨m, hmo, hkm, ⟨eN⟩⟩ | ⟨h7, -⟩⟩ | ⟨-, ⟨eN⟩⟩
  · obtain ⟨θN, hmn⟩ := hZ m hmo (by omega) eN
    refine ⟨m, θN, hkm, hmn, Or.inr ⟨hfix, ?_⟩⟩
    have h1 := hlayer
    rwa [hfix, sup_idem] at h1
  · omega
  · obtain ⟨θN, -⟩ := hZ (n - 4) hkodd (by omega) eN
    exact ⟨n - 4, θN, le_rfl, by omega, Or.inl rfl⟩

theorem pumpSide_of_inputs (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) : PumpSide := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd he₀H N₁ hP
  classical
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein hs.sig.klein).2 e₀ hd.e₀E
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  obtain ⟨N, hNC, hNpc, hAN, hNN₁, m, θN, hm, hmn, hcase⟩ :=
    exists_typed_pump hPump hN1 hs hn hd χr hArle hArpc hP
  have hY : N ⊔ conjBy N e₀ = N₁ ⊔ conjBy N₁ e₀ := by
    rcases hNN₁ with h | h
    · rw [h]
    · rw [h, conjBy_conjBy_of_mul_self N₁ he₀2, sup_comm]
  intro f hf
  obtain ⟨a, ha, h1, h2⟩ :=
    pumpSide_of_type hs (by omega) hd he₀H χr hArle hArpc hNC hNpc hAN θN hm hmn hcase f hf
  exact ⟨a, ha, by rw [← hY]; exact h1, h2⟩

end SwapP2

end CFSG.ComponentClassification.SolMax
