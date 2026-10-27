module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisAutChain
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Blueprint CFSG.RankThree.PartOne.OutStructure
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

theorem outPCyc_of_not_dvd_outer {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer X)) : OutPCyc p X := by
  intro E hE
  refine ⟨1, E.one_mem, fun x hx => ?_⟩
  have hxinn : x ∈ Inn X := by
    obtain ⟨k, hk⟩ := hE ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
    let φ : MulAut X →* Outer X :=
      QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
    have h1 : orderOf (φ x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
    have h2 : orderOf (φ x) ∣ Nat.card (Outer X) := orderOf_dvd_natCard _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact (QuotientGroup.eq_one_iff x).1 hj
    · exact absurd ((dvd_pow_self p hjpos.ne').trans (hj ▸ h2)) h
  exact Subgroup.mem_sup_right hxinn

theorem heis_not_dvd_lieOrderDivisor {p : ℕ} (hp5 : 5 ≤ p) {t : StatedLieTag} (hL : t ≠ .PSL)
    (hU : t ≠ .PSU) (n q : ℕ) : ¬ p ∣ lieOrderDivisor t n q := by
  intro hdvd
  have hle : lieOrderDivisor t n q ≤ 4 := by
    cases t <;> simp only [lieOrderDivisor] <;>
      first
      | exact absurd rfl hL
      | exact absurd rfl hU
      | omega
      | exact (Nat.gcd_le_left _ (by norm_num)).trans (by norm_num)
  have hpos : 0 < lieOrderDivisor t n q := by
    cases t <;> simp only [lieOrderDivisor] <;>
      first
      | exact absurd rfl hL
      | exact absurd rfl hU
      | omega
      | exact Nat.gcd_pos_of_pos_left _ (by norm_num)
  have := Nat.le_of_dvd hpos hdvd
  omega

theorem heis_out_chain
    {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {t : StatedLieTag}
    {n f : ℕ} (hmodel : LieModel K t n 2 f) (hndL : t = .PSL → ¬ p ∣ Nat.gcd n (2 ^ f - 1))
    (hndU : t = .PSU → ¬ p ∣ Nat.gcd n (2 ^ f + 1)) :
    OutPChain p K ∨ ¬ p ∣ Nat.card (Outer K) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSL_two hp hcl).toChain
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSL_ge_three hp hp2 (by omega) hcl (hndL rfl)).toChain
    · exact Or.inl (outPNice_PSU hp hcl (hndU rfl)).toChain
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSp_two hp hcl).toChain
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSp_ge_three hp (by omega) hcl).toChain
    · obtain ⟨⟨-, -, -, hp2'⟩, -⟩ := id hcl
      exact absurd rfl hp2'
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      by_cases hn : n = 4
      · subst hn
        exact Or.inl (outPChain_POmegaPlus_four hp (by omega) hcl)
      · exact Or.inl (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hcl).toChain
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      exact Or.inl (outPNice_POmegaMinus hp hp2 hn4 hcl).toChain
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (outPNice_G2 hp hch).toChain
    · exact Or.inl (outPNice_F4 hp hch).toChain
    · exact Or.inl (outPNice_E6 hp hp3 hp2 hch).toChain
    · exact Or.inl (outPNice_E7 hp hch).toChain
    · exact Or.inl (outPNice_E8 hp hch).toChain
    · exact Or.inl (outPNice_twistedE6 hp hp3 hch).toChain
    · exact Or.inl (outPNice_trialityD4 hp hch).toChain
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨⟨-, -, -, h23, -⟩, -⟩ := id hree
      omega
    · exact Or.inl (outPNice_twistedF4 hp hree).toChain
    · refine Or.inr fun hdvd => ?_
      obtain ⟨k, hk⟩ := (Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 f hree).1.exists_card_eq
      rw [hk] at hdvd
      have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
      omega
  · subst ht
    exact Or.inl (outPNice_Suzuki hp hsz).toChain

theorem heis_out_data
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {t : StatedLieTag}
    {n f : ℕ} (hmodel : LieModel X t n 2 f) (ht : t ≠ .Tits)
    (hndL : t = .PSL → ¬ p ∣ Nat.gcd n (2 ^ f - 1))
    (hndU : t = .PSU → ¬ p ∣ Nat.gcd n (2 ^ f + 1)) :
    OutPCyc p X ∧ ((∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) → ∃ f₀ : ℕ, f = p * f₀) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  refine ⟨?_, ?_⟩
  · rcases heis_out_chain hp hp5 hmodel hndL hndU with h | h
    · exact outPCyc_of_outPChain h
    · exact outPCyc_of_not_dvd_outer hp h
  · rintro ⟨α, hαin, hαp⟩
    have hadm : StatedLieAdmissible t n 2 f := LieModel.admissible hmodel
    have hdiv : ¬ p ∣ lieOrderDivisor t n (2 ^ f) := by
      by_cases hL : t = .PSL
      · subst hL
        have := hndL rfl
        simpa [lieOrderDivisor] using this
      · by_cases hU : t = .PSU
        · subst hU
          have := hndU rfl
          simpa [lieOrderDivisor] using this
        · exact heis_not_dvd_lieOrderDivisor hp5 hL hU n _
    obtain ⟨f₀, hf₀, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds X t
      n 2 f hadm hmodel ht p hp hp2 hdiv (fun h => hp3 h.2.2) (fun h => hp3 h.2) α hαp hαin
    exact ⟨f₀, hf₀⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
