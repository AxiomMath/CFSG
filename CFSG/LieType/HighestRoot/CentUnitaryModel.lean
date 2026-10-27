module

public import CFSG.LieType.HighestRoot.CentUnitary
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU

public section

namespace CFSG.LieType.HighestRoot

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary.SUExtras
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem centralizerCondition_of_isLongRootSU2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {n : ℕ} {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) : CentralizerCondition (fixedSubfield K p f) L := by
  obtain ⟨g, rfl, -⟩ := h
  exact centralizerCondition_map (MulAut.conj g) (centralizerCondition_rootSU2 hK hp hn)

theorem exists_longRoot_unitary (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    ∃ (k : Fin (n / 2)) (γ : Fin (n / 2) → ℤ),
      γ ∈ (CFSG.LieType.Universal.Unitary.rootDatum hK n).roots ∧
      (∀ δ ∈ (CFSG.LieType.Universal.Unitary.rootDatum hK n).roots,
        rootForm (CFSG.LieType.Universal.Unitary.rootDatum hK n) δ δ ≤
          rootForm (CFSG.LieType.Universal.Unitary.rootDatum hK n) γ γ) ∧
      toStd n γ = 2 • weight n (lowIdx k) ∧
      toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k)) := by
  have hm : 0 < n / 2 := by omega
  set k : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩ with hkdef
  have hk : ¬ k.val + 1 < n / 2 := by simp [hkdef]; omega
  have hk' : k.val + 1 = n / 2 := by simp [hkdef]; omega
  refine ⟨k, ?_⟩
  by_cases he : Even n
  · have hc : cartan n = CFSG.LieType.Universal.Symplectic.cartanC (n / 2) := by simp [cartan, he]
    have hd : divisible n = ∅ := by simp [divisible, he]
    refine ⟨Pi.single k 1, Or.inl ⟨1, k, by rw [map_one, Module.End.one_apply]; exact rfl⟩, ?_,
      toStd_last_even hk he,
      toStd_neg_last_even hk he⟩
    intro δ hδ
    have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongest_single_cartanC
      (m := n / 2) hm hc (isFiniteType_cartan n) hk'
    have hδ' : δ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartan n) ∅ := by
      rw [← hd]
      exact hδ
    exact hlong.2 δ hδ'
  · have hc : cartan n = (CFSG.LieType.Universal.Symplectic.cartanC (n / 2))ᵀ := by
      simp [cartan, he]
    have hd : divisible n = {k : Fin (n / 2) | k.val + 1 = n / 2} := by simp [divisible, he]
    have hkd : k ∈ divisible n := by
      rw [hd]
      exact hk'
    refine ⟨2 • Pi.single k 1,
      Or.inr ⟨1, k, hkd, by rw [map_one, Module.End.one_apply]; exact rfl⟩, ?_, ?_, ?_⟩
    · intro δ hδ
      have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongest_two_nsmul_single_BC
        (m := n / 2) hm hc (isFiniteType_cartan n) hk'
      rw [← hd] at hlong
      exact hlong.2 δ hδ
    · rw [toStd_nsmul_two, toStd_last_odd hk he]
    · rw [← smul_neg, toStd_nsmul_two, toStd_neg_last_odd hk he]

theorem highestRootCZ_unitary (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = p ^ f) :
    HighestRootCZ (CFSG.LieType.Universal.Unitary.rootDatum hK n) F' := by
  obtain ⟨k, γ, hγ, hl, hγs, hγs'⟩ := exists_longRoot_unitary hK hn
  refine ⟨γ, hγ, hl, ?_⟩
  obtain ⟨P, hP⟩ := exists_wittMatrix hK n
  obtain ⟨i, hi⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isLongRootSU2_map_rankOne hK hp hn
    hγs hγs' P hP
  have hcc := centralizerCondition_map (conjEquiv P hP).symm
    (centralizerCondition_of_isLongRootSU2 hK hp hi)
  rw [Subgroup.map_map] at hcc
  have e : ((conjEquiv P hP).symm.toMonoidHom.comp (conjEquiv P hP).toMonoidHom) =
      MonoidHom.id _ := by
    ext x
    simp
  rw [e, Subgroup.map_id] at hcc
  have : Fintype (fixedSubfield K p f) := Fintype.ofFinite _
  have : Fintype F' := Fintype.ofFinite _
  refine centralizerCondition_of_ringEquiv (FiniteField.ringEquivOfCardEq ?_) hcc
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_fixedSubfield hK, hF']

end CFSG.LieType.HighestRoot
