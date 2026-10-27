module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoO
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.ReductionFixed
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbedding.TrialityTwo

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem ordD_four_two : CFSG.Open.ordD 4 (2 ^ 1) = 174182400 := by decide

theorem transport_hypotheses {X P : Type} [Group X] [Group P] (e : X ≃* P) (α : MulAut X)
    (hα : α ∉ inner X) (h3 : α ^ 3 = 1)
    (hfree : ∀ Q : Subgroup X, ⁅Q, Q⁆ = Q → (∀ y ∈ Q, α y = y) → Q = ⊥) :
    MulAut.congr e α ∉ inner P ∧ MulAut.congr e α ^ 3 = 1 ∧
      ∀ L : Subgroup P, ⁅L, L⁆ = L → (∀ y ∈ L, MulAut.congr e α y = y) → L = ⊥ := by
  refine ⟨fun hin => hα ?_, by rw [← map_pow, h3, map_one], fun L hL hfix => ?_⟩
  · rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hin
    obtain ⟨β, hβ, hβα⟩ := hin
    rwa [(MulAut.congr e).injective hβα] at hβ
  · have h := hfree (L.map e.symm.toMonoidHom) (by rw [← Subgroup.map_commutator, hL]) (by
      rintro _ ⟨z, hz, rfl⟩
      have hz' := hfix z hz
      change e (α (e.symm z)) = z at hz'
      change α (e.symm z) = e.symm z
      calc α (e.symm z) = e.symm (e (α (e.symm z))) := (e.symm_apply_apply _).symm
        _ = e.symm z := by rw [hz'])
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h

theorem kFactThreeCentTrialityTwo_of_model
    (H : ∀ (T : Type) [Group T], StatedClassicalModel T .POmegaPlus 4 2 1 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 1 →
      ∀ (_ : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
        (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))),
        α ∉ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K))) → α ^ 3 = 1 →
        (∀ L : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K))), ⁅L, L⁆ = L →
          (∀ y ∈ L, α y = y) → L = ⊥) →
        ∀ x, α x = x → (orderOf x = 5 ∨ orderOf x = 7) → False) :
    KFactThreeCentTrialityTwo := by
  intro d hd α hα h3 hfree x hx n hn hxn
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp2, hf⟩ : q.p = 2 ∧ q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq
    exact (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp2
    (MulEquiv.refl _)
  rw [hp2, hf] at h
  obtain ⟨hZ, -⟩ := center_eq_bot_and_innerKey_of_model_pomegaPlus_two h
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl
  rw [hZ, Subgroup.mem_bot] at hx hxn ⊢
  have hαx : α x = x := (inv_mul_eq_one.mp hx).symm
  by_contra hx1
  obtain ⟨p, k, hp, hp5, hpk⟩ := exists_pow_orderOf_prime_of_coprime_six hn hxn hx1
  have hαy : α (x ^ k) = x ^ k := by rw [map_pow, hαx]
  have hp57 : p = 5 ∨ p = 7 := by
    refine prime_eq_five_or_seven_of_dvd hp hp5 ?_
    rw [← hpk, ← ordD_four_two, ← hcard]
    exact orderOf_dvd_natCard _
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hα', h3', hfree'⟩ := transport_hypotheses e α hα h3 hfree
  refine H _ h K hK e (MulAut.congr e α) hα' h3' hfree' (e (x ^ k)) ?_ ?_
  · change e (α (e.symm (e (x ^ k)))) = e (x ^ k)
    rw [MulEquiv.symm_apply_apply, hαy]
  · rw [MulEquiv.orderOf_eq, hpk]
    exact hp57

end CFSG.AGLEmbedding.TrialityTwo
