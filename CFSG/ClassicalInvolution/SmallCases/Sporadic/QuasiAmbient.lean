module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.CentralizerOrbit
public import CFSG.ClassicalInvolution.SmallCases.Exclusion

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.Schreier (centralizerIn)

variable {M : Type*} [Group M]

theorem isQuasisimple_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple G' :=
  h.of_mulEquiv e.symm

theorem NoNonsolvableClassicalAt.of_ambient_quasisimple (H : Subgroup M) [Finite H] (t : H)
    (K : Subgroup M) (hK : centralizerIn H (t : M) = K) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 2)
    (hcard : Nat.card K = 40320 ∨ Nat.card K = 39916800) : NoNonsolvableClassicalAt t := by
  have hKH : K ≤ H := by
    rw [← hK]
    exact inf_le_left
  have hCK : Subgroup.centralizer {t} = K.subgroupOf H := by
    have h1 := centralizer_mk_eq (H := H) (x := (t : M)) t.2
    rw [Subtype.coe_eta] at h1
    rw [h1, ← hK]
    ext g
    simp only [Subgroup.mem_subgroupOf, centralizerIn, Subgroup.mem_inf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  let e : ↥(Subgroup.centralizer {t}) ≃* ↥K :=
    (MulEquiv.subgroupCongr hCK).trans (Subgroup.subgroupOfEquivOfLe hKH)
  have hqC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer {t}) :=
    isQuasisimple_of_mulEquiv e.symm hq
  have hZC : Nat.card (Subgroup.center ↥(Subgroup.centralizer {t})) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZ
  have hcardC : Nat.card (Subgroup.centralizer {t}) = Nat.card K := Nat.card_congr e.toEquiv
  refine NoNonsolvableClassicalAt.of_isQuasisimple_centralizer hqC ?_
  rcases hcard with h | h
  · exact not_classicalInvolutionWitness_of_card_eq_40320 _ hqC hZC (by rw [hcardC, h])
  · exact not_classicalInvolutionWitness_of_card_eq_39916800 _ hqC hZC (by rw [hcardC, h])

end CFSG.ClassicalInvolution
