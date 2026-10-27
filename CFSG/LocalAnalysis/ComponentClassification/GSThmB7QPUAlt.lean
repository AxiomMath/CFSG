module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAltJ
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAltJordan
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAltOrd
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv Equiv.Perm

namespace QPUAlt

theorem false_of_alternating {M : Type} [Group M] [Finite M] (hZ : IsPGroup 2 (center M))
    {n : ℕ} (e : M ⧸ center M ≃* alternatingGroup (Fin n)) {p' f' : ℕ} (hp' : p'.Prime)
    (hp'2 : p' ≠ 2) (hf' : 1 ≤ f') {L : Subgroup M}
    (hLie : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f') {t : M} (ht : t * t = 1)
    {J J₀ : Subgroup M} (hJt : J ≤ centralizer ({t} : Set M))
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M)))) (hJ₀L : J₀ ≤ L)
    (hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) : False := by
  have hcl : Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f' := by
    rcases hLie with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hcl
    all_goals exact absurd h0 (by norm_num)
  have hs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) :=
    ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 p' f' hcl
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hcl
  have hcard : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) * 2 =
      (p' ^ f') ^ 4 * (((p' ^ f') ^ 2 - 1) * ((p' ^ f') ^ 4 - 1)) := by
    rw [Nat.card_congr eK.toEquiv, ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero
      (ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp' hp'2 hK) (by norm_num), hK,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  obtain ⟨ν, hν, hker⟩ := exists_hom_of_mulEquiv e
  obtain ⟨hdeg, hO, h3⟩ := isPComponent_centralizer_of_central hZ ν hν hker ht hJt hJc
  have hJL : J ≤ L := by
    rw [← hJ₀, hO, Subgroup.map_bot, sup_bot_eq]
    exact hJ₀L
  let ψ : L →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp (ν.comp L.subtype)
  obtain ⟨m, -, hm⟩ := two_mul_card_eq_factorial ψ hs
    {x : Fin n | ((ν t : alternatingGroup (Fin n)) : Perm (Fin n)) x = x} hdeg
    fun a ha b hb c hc hab hac hbc => by
      obtain ⟨j, hj, hjσ⟩ := h3 a b c ha hb hc hab hac hbc
      exact ⟨⟨j, hJL hj⟩, hjσ⟩
  exact factorial_ne_two_mul_card_psp4 hp' hp'2 hf' (m := m) (by rw [← hm, ← hcard, mul_comm])

end QPUAlt

theorem cfQPUJAlt_holds : CFQPUJAlt := by
  rintro M _ _ p' f' p f hc ⟨n, -, ⟨e⟩⟩
  obtain ⟨-, hZ, hp', hp'2, hf', -, -, -, -, -, -, -, E, L, t, J, J₀, -, -, -, -, hLie, -, ht, -,
    hJt, hJc, -, hJ₀L, -, hJ₀⟩ := hc
  exact QPUAlt.false_of_alternating hZ e hp' hp'2 hf' hLie ht hJt hJc hJ₀L hJ₀

end CFSG.ComponentClassification.GSThmB
