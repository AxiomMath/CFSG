module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporOneLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporBase
import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Open

namespace MonsterRows

theorem prime_eq_of_sq_dvd_monsterOrder {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ monsterOrder) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  have hN : monsterOrder ≠ 0 := by norm_num [monsterOrder]
  have hmem : p ∈ monsterOrder.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, hN⟩
  clear hN
  norm_num [monsterOrder, Nat.primeFactors, Nat.primeFactorsList] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact absurd rfl hp2
    | (exfalso; norm_num [monsterOrder] at h; done)
    | simp

theorem pow_four_dvd_monsterOrder {p : ℕ} (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    p ^ 4 ∣ monsterOrder := by
  rcases hp with rfl | rfl | rfl <;> norm_num [monsterOrder]

theorem card_eq_monsterOrder {K : Type} [Group K]
    (hMcard : Nat.card MonsterY443Derived = monsterOrder)
    (e : K ≃* NativeSporadic.Carrier .M) : Nat.card K = monsterOrder :=
  (Nat.card_congr e.toEquiv).trans
    ((Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard)

end MonsterRows

theorem glbCore_one_eq_top_of_betaData {K : Type} [Group K] [Finite K]
    (h : SporadicBetaData K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h4 : p ^ 4 ∣ Nat.card K)
    (T : Sylow p K) : GLBCore p 1 (T : Subgroup K) = ⊤ := by
  rcases h.2 p hp hp2 with h3 | ⟨h4', -⟩ | hfus
  · exact absurd ((pow_dvd_pow p (by norm_num : 3 ≤ 4)).trans h4) h3
  · exact absurd h4 h4'
  · exact glbCore_one_eq_top_of_fusionGenerationOf hp hfus T

theorem oneLieIdentSporAt_M_of_betaData (hβM : MonsterBetaData)
    (hbr : Nonempty (NativeSporadic.Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group)) :
    OneLieIdentSporAt .M := by
  intro K _ _ hs hnab ⟨e⟩ p
  obtain ⟨f⟩ := hbr
  exact oneLieIdentAtP_of_betaData hs hnab (hβM K hnab ⟨e.trans f.symm⟩) p

theorem smallIdentSporAt_M_of_betaData (hβM : MonsterBetaData)
    (hbr : Nonempty (NativeSporadic.Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group))
    (hMcard : Nat.card MonsterY443Derived = monsterOrder)
    (h11 : SporGammaOneAt .M 11) (h13 : SporGammaOneAt .M 13) : SmallIdentSporAt .M := by
  intro K _ _ hs hnab ⟨e⟩ p hp hp2 T hT hΓ _
  obtain ⟨f⟩ := hbr
  have e' : K ≃* NativeSporadic.Carrier .M := e.trans f.symm
  have hKcard : Nat.card K = monsterOrder := MonsterRows.card_eq_monsterOrder hMcard e'
  exfalso
  by_cases hsq : p ^ 2 ∣ monsterOrder
  · have key : (p = 3 ∨ p = 5 ∨ p = 7) → GLBCore p 1 (T : Subgroup K) = ⊤ := fun h357 =>
      glbCore_one_eq_top_of_betaData (hβM K hnab ⟨e'⟩) hp hp2
        (hKcard ▸ MonsterRows.pow_four_dvd_monsterOrder h357) T
    rcases MonsterRows.prime_eq_of_sq_dvd_monsterOrder hp hp2 hsq with h3 | h5 | h7 | h11' | h13'
    · exact hΓ (key (Or.inl h3))
    · exact hΓ (key (Or.inr (Or.inl h5)))
    · exact hΓ (key (Or.inr (Or.inr h7)))
    · subst h11'
      exact hΓ (h11 K ⟨e⟩ T)
    · subst h13'
      exact hΓ (h13 K ⟨e⟩ T)
  · exact hT (isCyclic_sylow_of_not_sq_dvd hp T (by rwa [hKcard]))

end CFSG.AGLEmbedding
