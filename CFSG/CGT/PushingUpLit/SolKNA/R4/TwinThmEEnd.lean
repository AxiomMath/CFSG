module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEEndU3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14BenderSz
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESteps

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Bender


@[expose] def E178Bender (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        IsSimpleGroup ↥(Subgroup.normalClosure ({z} : Set G)) →
        (∃ x ∈ Subgroup.normalClosure ({z} : Set G), ∃ y ∈ Subgroup.normalClosure ({z} : Set G),
          x * y ≠ y * x) →
        Subgroup.centralizer ((Subgroup.normalClosure ({z} : Set G) : Subgroup G) : Set G) = ⊥ →
        BenderSuzuki.IsBenderGroup ↥(Subgroup.normalClosure ({z} : Set G)) →
        BenderSuzuki.IsStronglyEmbeddedOrder (H.subgroupOf (Subgroup.normalClosure ({z} : Set G))) →
        False

theorem e178Bender_of {r : ℕ} (hr : 3 ≤ r) : E178Bender r := by
  intro G _ _ Ω K S R W H c z hz hSyl hFs hnab hFc hB hSE
  obtain ⟨P, -, ⟨eP⟩⟩ := c.stand.quat K c.stand.mem
  obtain ⟨Q, -, hQ⟩ := EndGame.exists_subgroup_q8 hr eP
  rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact TwinThmE.BenderSz.benderNoQ8' G (Subgroup.normalClosure ({z} : Set G)) hFc
      (Or.inl ⟨n, hn, ⟨e⟩⟩) Q hQ
  · exact TwinThmE.BenderSz.benderNoQ8' G (Subgroup.normalClosure ({z} : Set G)) hFc
      (Or.inr ⟨n, hn, ⟨e⟩⟩) Q hQ
  · exact e178U3_of_twin hr G Ω K S R W H c z hz hSyl hFs hnab hFc ⟨n, ⟨e⟩⟩ hSE

end Bender

section End


theorem e18_endC_of_e178Bender {r : ℕ} (h : E178Bender r) : E18_endC r := by
  intro G _ _ Ω K S R W H c hF z hz hSyl h1 h2S
  obtain ⟨F, hFn, hFs, hFnab, hFc⟩ := hF
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h2 := CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_mul_of_isSylow2In hz2 hSyl h2S
  obtain ⟨hFeq, hB, hSE⟩ := CFSG.StronglyEmbedded.UniqueCoset.lemma_3_9 c.proper hz2 h1 h2 hFs
    hFnab hFc
  subst hFeq
  exact h G Ω K S R W H c z hz hSyl hFs hFnab hFc hB hSE

theorem e18_endC_of {r : ℕ} (hr : 3 ≤ r) : E18_endC r :=
  e18_endC_of_e178Bender (e178Bender_of hr)

end End

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
