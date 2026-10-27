module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsWords

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem exists_conj_of_involution_S (s t : S)
    (hs2 : s * s = 1) (ht2 : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    ∃ σ : S, σ⁻¹ * s * σ = t := by
  classical
  set O : Set S := MulAction.orbit (ConjAct S) s with hO
  set I : Set S := {y | y * y = 1 ∧ y ≠ 1} with hI
  have hOI : O ⊆ I := by
    rintro _ ⟨c, rfl⟩
    simp only [hI, Set.mem_ofPred_eq, ConjAct.smul_def]
    constructor
    · rw [show ConjAct.ofConjAct c * s * (ConjAct.ofConjAct c)⁻¹ *
        (ConjAct.ofConjAct c * s * (ConjAct.ofConjAct c)⁻¹) =
        ConjAct.ofConjAct c * (s * s) * (ConjAct.ofConjAct c)⁻¹ by group, hs2]
      group
    · intro h
      apply hs1
      calc s = (ConjAct.ofConjAct c)⁻¹ * (ConjAct.ofConjAct c * s * (ConjAct.ofConjAct c)⁻¹) *
          ConjAct.ofConjAct c := by group
        _ = 1 := by rw [h]; group
  have hs2' : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hOcard : O.ncard = 315 := by
    have h1 := (MulAction.stabilizer (ConjAct S) s).card_mul_index
    rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
      card_centralizer_involution_S s hs2',
      show Nat.card (ConjAct S) = Nat.card S from Nat.card_congr ConjAct.ofConjAct.toEquiv,
      card_S, ← hO] at h1
    omega
  have hIcard : I.ncard ≤ 315 := by
    rw [← conjClass₁.2]
    have hinj : Set.InjOn (fun y : S => (⟨y, S_le_R y.2⟩ : R)) I := by
      intro y _ y' _ h
      have h' := congrArg (fun r : R => (r : Equiv.Perm (Fin 42))) h
      exact Subtype.ext h'
    have hmaps : Set.MapsTo (fun y : S => (⟨y, S_le_R y.2⟩ : R)) I
        (ConjClasses.mk r₁R).carrier := by
      intro y hy
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      refine isConj_r₁_of_inner (x := ⟨y, S_le_R y.2⟩) y.2 ?_ ?_
      · intro h
        have h' := congrArg (fun r : R => (r : Equiv.Perm (Fin 42))) h
        exact hy.2 (Subtype.ext h')
      · have h' := congrArg (fun r : S => (r : Equiv.Perm (Fin 42))) hy.1
        exact Subtype.ext h'
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
  have hOI' : O = I := Set.eq_of_subset_of_ncard_le hOI (by omega) (Set.toFinite _)
  have htO : t ∈ O := by rw [hOI']; exact ⟨ht2, ht1⟩
  obtain ⟨c, hc⟩ := htO
  refine ⟨(ConjAct.ofConjAct c)⁻¹, ?_⟩
  rw [← hc]
  simp only [ConjAct.smul_def, inv_inv]

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_jq_mem_center {J : Subgroup G}
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {u w : G} (huJ : u ∈ J) (hwJ : w ∈ J)
    (huu : u * u = 1) (hww : w * w = 1) (huZ : u ∉ zStarIn J) (hwZ : w ∉ zStarIn J) :
    ∃ j : J, (jq J ⟨w, hwJ⟩)⁻¹ * jq J (j⁻¹ * ⟨u, huJ⟩ * j) ∈ center (Jhat J) := by
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  have hsq : ∀ {v : G} (hv : v ∈ J), v * v = 1 → q (jq J ⟨v, hv⟩) * q (jq J ⟨v, hv⟩) = 1 :=
    fun hv hvv => by
      rw [← map_mul, ← map_mul, show (⟨_, hv⟩ : J) * ⟨_, hv⟩ = 1 from Subtype.ext hvv, map_one,
        map_one]
  have hne : ∀ {v : G} (hv : v ∈ J), v ∉ zStarIn J → q (jq J ⟨v, hv⟩) ≠ 1 := fun hv hvZ h => by
    apply hvZ
    rw [mem_zStarIn_iff hv, ← hqker]
    exact h
  obtain ⟨σ, hσ⟩ := exists_conj_of_involution_S ⟨_, hqS (jq J ⟨u, huJ⟩)⟩ ⟨_, hqS (jq J ⟨w, hwJ⟩)⟩
    (Subtype.ext (hsq huJ huu)) (Subtype.ext (hsq hwJ hww))
    (fun h => hne huJ huZ (congrArg Subtype.val h)) (fun h => hne hwJ hwZ (congrArg Subtype.val h))
  obtain ⟨e, he⟩ := hqsurj σ σ.2
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) e
  refine ⟨j, ?_⟩
  have hσ' := congrArg Subtype.val hσ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hσ'
  change q (jq J j) = σ at he
  have hj : q (jq J (j⁻¹ * ⟨u, huJ⟩ * j)) = q (jq J ⟨w, hwJ⟩) := by
    simp only [map_mul, map_inv, he]
    exact hσ'
  rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hj, inv_mul_cancel]

end CFSG.ComponentClassification.GrSLit.GrS4
