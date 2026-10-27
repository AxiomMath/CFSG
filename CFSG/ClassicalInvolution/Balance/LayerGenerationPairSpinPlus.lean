module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame
public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimple
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTransfer
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
open scoped MatrixGroups


section Plus

variable {n : ℕ} {K : Type} [Field K]

open CFSG.LieType.CurtisTits in
theorem map_rankOne_plus (hn : 3 ≤ n) (k : Fin n) :
    (rankOne (plusDatum n K hn).rootGroup k).map (spinAction (quadPlus n K)) =
      ((plusFrame n K hn).toFrame (rootIdxD_ne n (by omega) k) true (rootSignD n k)).La.range := by
  have h1 : rankOne (plusDatum n K hn).rootGroup k = (rankOneD K hn k).range :=
    PlusCT.rankOne_plusRootGroup hn k
  rw [h1]
  exact map_longSL2_range (plusFrame n K hn) (rootIdxD_ne n (by omega) k) true (rootSignD n k)

open CFSG.LieType.CurtisTits in
theorem exists_frame_of_mem_fund_plus (hn : 3 ≤ n)
    (hsingle : Generic.FundamentalSingleClass .POmegaPlus (plusDatum n K hn))
    (hlong : ∀ k : Fin n, Generic.IsLongestRoot (plusDatum n K hn) (Pi.single k 1))
    {R : Subgroup (spinGroup (quadPlus n K))}
    (hR : R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum n K hn)) :
    ∃ fr : Frame (quadPlus n K), R.map (spinAction (quadPlus n K)) = fr.La.range := by
  let k₀ : Fin n := ⟨0, by omega⟩
  have hR₀ : rankOne (plusDatum n K hn).rootGroup k₀ ∈
      Generic.fundamentalSubgroups .POmegaPlus (plusDatum n K hn) := by
    refine ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀), ?_⟩
    ext y
    simp [rankOne]
  obtain ⟨g, rfl⟩ := hsingle _ hR₀ R hR
  have hθ : spinAction (quadPlus n K) g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ g)
  refine ⟨((plusFrame n K hn).toFrame (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀)).map hθ,
    ?_⟩
  rw [conjSub, map_conj_map, map_rankOne_plus hn k₀]
  exact (La_range_eq_map_conj fun A => Frame.map_La _ hθ A).symm

open CFSG.LieType.CurtisTits in
theorem commutingGeneration_plus [Finite K] (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n) (hn : 4 ≤ n)
    (hsingle : Generic.FundamentalSingleClass .POmegaPlus (plusDatum n K hn3))
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum n K hn3), ⁅R, R⁆ = R)
    (hlong : ∀ k : Fin n, Generic.IsLongestRoot (plusDatum n K hn3) (Pi.single k 1))
    (hgen : ∀ x : spinGroup (quadPlus n K),
      ⨆ k : Fin n, rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) = ⊤) :
    CommutingGeneration (Generic.fundamentalSubgroups .POmegaPlus (plusDatum n K hn3)) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ : (quadPlus n K).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus n K)
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hker : (spinAction (quadPlus n K)).ker ≤ Subgroup.center (spinGroup (quadPlus n K)) :=
    ker_spinAction_le_center _
  have hmemF : ∀ (x : spinGroup (quadPlus n K)) (k : Fin n),
      rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) ∈
        Generic.fundamentalSubgroups .POmegaPlus (plusDatum n K hn3) := fun x k =>
    ⟨x, Pi.single k 1, Or.inl (hlong k), rfl⟩
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  have key : ∀ x : spinGroup (quadPlus n K),
      (∀ k : Fin n, rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) ≤
          Subgroup.centralizer ({c₁} : Set _) ∨
        rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) ≤
          Subgroup.centralizer ({c₂} : Set _) ∨
        rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) ≤
          Subgroup.centralizer ({c₁ * c₂} : Set _)) →
      (⊤ : Subgroup (spinGroup (quadPlus n K))) ≤
        ⨆ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum n K hn3),
          ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set _) ∨
            R ≤ Subgroup.centralizer ({c₂} : Set _) ∨
            R ≤ Subgroup.centralizer ({c₁ * c₂} : Set _)), R := by
    intro x hx
    rw [← hgen x]
    exact iSup_le fun k => le_iSup₂_of_le _ (hmemF x k) (le_iSup_of_le (hx k) le_rfl)
  have hcentral : ∀ c : spinGroup (quadPlus n K), c ∈ Subgroup.center (spinGroup (quadPlus n K)) →
      ∀ R : Subgroup (spinGroup (quadPlus n K)), R ≤ Subgroup.centralizer ({c} : Set _) :=
    fun c hc R y _ => Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc y)
  by_cases hθ₁ : spinAction (quadPlus n K) c₁ = 1
  · exact key 1 fun k => Or.inl (hcentral c₁ (hker hθ₁) _)
  by_cases hθ₂ : spinAction (quadPlus n K) c₂ = 1
  · exact key 1 fun k => Or.inr (Or.inl (hcentral c₂ (hker hθ₂) _))
  by_cases hθ₁₂ : spinAction (quadPlus n K) (c₁ * c₂) = 1
  · exact key 1 fun k => Or.inr (Or.inr (hcentral _ (hker hθ₁₂) _))
  obtain ⟨fr₁, hfr₁⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR₁
  obtain ⟨fr₂, hfr₂⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR₂
  have hi₁ : spinAction (quadPlus n K) c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction (quadPlus n K) c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  have hne : fr₂.La (-1) ≠ fr₁.La (-1) := fun h => hθ₁₂ (by
    rw [map_mul, hi₁, hi₂, h, ← map_mul, neg_mul_neg, one_mul, map_one])
  have hc : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
    rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hx₂₁ c₁ hc₁]
  have hcent : ∀ A : SL(2, K), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
    intro A
    obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction (quadPlus n K)) := hfr₁ ▸ ⟨A, rfl⟩
    rw [← hi₂, ← hrA, ← map_mul, ← map_mul, hx₂₁ r hr]
  have horth : ∀ X Y, polar (quadPlus n K) (fr₁.incl X) (fr₂.incl Y) = 0 :=
    ((Frame.orth_or_eq h2 hc hcent).resolve_right hne)
  let a₀ : Fin n := ⟨0, by omega⟩
  let a₁ : Fin n := ⟨1, by omega⟩
  let a₂ : Fin n := ⟨2, by omega⟩
  let a₃ : Fin n := ⟨3, by omega⟩
  have h01 : a₀ ≠ a₁ := fun h => by simpa [a₀, a₁] using congrArg Fin.val h
  have h23 : a₂ ≠ a₃ := fun h => by simpa [a₂, a₃] using congrArg Fin.val h
  have h02 : a₀ ≠ a₂ := fun h => by simpa [a₀, a₂] using congrArg Fin.val h
  have h03 : a₀ ≠ a₃ := fun h => by simpa [a₀, a₃] using congrArg Fin.val h
  have h12 : a₁ ≠ a₂ := fun h => by simpa [a₁, a₂] using congrArg Fin.val h
  have h13 : a₁ ≠ a₃ := fun h => by simpa [a₁, a₃] using congrArg Fin.val h
  obtain ⟨x, hx₁, hx₂⟩ := exists_spin_conj_orth_pair hodd hQ
    ((plusFrame n K hn3).toFrame h01 true true) ((plusFrame n K hn3).toFrame h23 true true) fr₁ fr₂
    (polar_incl_toFrame_of_disjoint (plusFrame n K hn3) h01 h23 h02 h03 h12 h13 true true true true)
    horth
  set θx : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) := spinAction (quadPlus n K) x with hθx
  have hconj : ∀ (T L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)), T * L = L * T →
      (θx * T * θx⁻¹) * (θx * L * θx⁻¹) = (θx * L * θx⁻¹) * (θx * T * θx⁻¹) := by
    intro T L h
    calc (θx * T * θx⁻¹) * (θx * L * θx⁻¹) = θx * (T * L) * θx⁻¹ := by group
      _ = θx * (L * T) * θx⁻¹ := by rw [h]
      _ = (θx * L * θx⁻¹) * (θx * T * θx⁻¹) := by group
  refine key x fun k => ?_
  have hR := hperf _ (hmemF x k)
  have himg : (rankOneRoot (plusDatum n K hn3) x (Pi.single k 1)).map (spinAction (quadPlus n K)) =
      ((plusFrame n K hn3).toFrame (rootIdxD_ne n (by omega) k) true (rootSignD n k)).La.range.map
        (MulAut.conj θx).toMonoidHom := by
    show ((rankOne (plusDatum n K hn3).rootGroup k).map (MulAut.conj x).toMonoidHom).map _ = _
    rw [map_conj_map, map_rankOne_plus hn3 k]
  have hcen : ∀ c : spinGroup (quadPlus n K),
      (∀ A : SL(2, K), spinAction (quadPlus n K) c *
        (θx * ((plusFrame n K hn3).toFrame (rootIdxD_ne n (by omega) k) true (rootSignD n k)).La A *
          θx⁻¹) =
        (θx * ((plusFrame n K hn3).toFrame (rootIdxD_ne n (by omega) k) true (rootSignD n k)).La A *
          θx⁻¹) * spinAction (quadPlus n K) c) →
      rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) ≤ Subgroup.centralizer ({c} : Set _) := by
    intro c hc
    have hmem : c ∈ Subgroup.centralizer
        ((rankOneRoot (plusDatum n K hn3) x (Pi.single k 1) : Subgroup _) : Set _) := by
      refine Models.Transfer.mem_centralizer_of_map (θ := spinAction (quadPlus n K)) hker hR ?_
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : t ∈ ((plusFrame n K hn3).toFrame (rootIdxD_ne n (by omega) k) true
          (rootSignD n k)).La.range.map (MulAut.conj θx).toMonoidHom := himg ▸ ht
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ht'
      exact (hc A).symm
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hmem y hy)
  rcases exists_comm_toFrame_of_pairs (plusFrame n K hn3) h01 h23 (rootIdxD_ne n (by omega) k)
    true (rootSignD n k) with hT | hT | hT
  · refine Or.inl (hcen c₁ fun A => ?_)
    rw [hi₁, ← hx₁]
    exact hconj _ _ (hT A)
  · refine Or.inr (Or.inl (hcen c₂ fun A => ?_))
    rw [hi₂, ← hx₂]
    exact hconj _ _ (hT A)
  · refine Or.inr (Or.inr (hcen (c₁ * c₂) fun A => ?_))
    have : spinAction (quadPlus n K) (c₁ * c₂) =
        θx * ((plusFrame n K hn3).toFrame h01 true true).La (-1) *
          ((plusFrame n K hn3).toFrame h23 true true).La (-1) * θx⁻¹ := by
      rw [map_mul, hi₁, hi₂, ← hx₁, ← hx₂]
      group
    rw [this]
    have h3 := hconj _ _ (hT A)
    simpa [mul_assoc] using h3

end Plus

section Main

variable {p e : ℕ} [Fact p.Prime]

theorem commutingFundamentalGeneration_pOmegaPlus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    CommutingFundamentalGeneration p .POmegaPlus n e := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, -⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaPlus n p e Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus n p e Fact.out =
      ModelFacts.modelUniv .POmegaPlus n p e Fact.out).trans (modelUniv_POmegaPlus hn3)
  have hsingle : Generic.FundamentalSingleClass .POmegaPlus
      (Generic.modelUniv .POmegaPlus n p e Fact.out).D :=
    fundamentalSingleClass .POmegaPlus n p e Fact.out trivial hadm (by decide) (by decide)
  have hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus n p e Fact.out).D, ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
      (fundPerfect_core .POmegaPlus n p e hp2 trivial hadm (by omega) R hR)
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaPlus n p e Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .POmegaPlus n p e Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus n p e Fact.out trivial hadm k trivial
  have hgen : ∀ g : (Generic.modelUniv .POmegaPlus n p e Fact.out).K,
      ⨆ i : Fin (Generic.modelUniv .POmegaPlus n p e Fact.out).D.rank,
        rankOneRoot (Generic.modelUniv .POmegaPlus n p e Fact.out).D g (Pi.single i 1) = ⊤ :=
    iSup_rankOneRoot_simple_eq_top .POmegaPlus n p e Fact.out trivial hadm
  show CommutingGeneration (Generic.fundamentalSubgroups .POmegaPlus
    (Generic.modelUniv .POmegaPlus n p e Fact.out).D)
  generalize Generic.modelUniv .POmegaPlus n p e Fact.out = M at hM hsingle hperf hlong hgen ⊢
  subst hM
  exact commutingGeneration_plus hodd hn3 hn4 hsingle hperf hlong hgen

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
