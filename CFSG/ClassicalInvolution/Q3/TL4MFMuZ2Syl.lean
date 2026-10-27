module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDType2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3T6

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

theorem exists_sylow_le_centralizer (hd : TightDatum R S z) (he : TightEdgeless R) :
    ∃ T : Sylow 2 X, (S : Subgroup R).map R.subtype ≤ (T : Subgroup X) ∧
      (T : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
  classical
  set S0 : Subgroup X := (S : Subgroup R).map R.subtype with hS0
  have d : OddByQuat R S0 z :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  have hS0N : S0 ≤ Subgroup.normalizer (S0 : Set X) := Subgroup.le_normalizer
  obtain ⟨T, hT, -⟩ := exists_isSylow2Of_ge d.S_two hS0N
  have hTG : IsSylow2Of T ⊤ := by
    by_contra hnot
    exact hd.not_dEdgeless_of_not_sylow hT hnot he
  let T' : Sylow 2 X :=
    { toSubgroup := T
      isPGroup' := hTG.2.1
      is_maximal' := fun {Q} hQ hle => hTG.2.2 Q le_top hQ hle }
  have hST : S0 ≤ T := by
    have hsup : IsPGroup 2 ↥(T ⊔ S0) := hT.2.1.to_sup_of_normal_right' d.S_two hT.1
    have heq := hT.2.2 (T ⊔ S0) (sup_le hT.1 hS0N) hsup le_sup_left
    rw [← heq]
    exact le_sup_right
  have hTt : T ≤ Subgroup.centralizer ({z} : Set X) := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (S0 : Set X) := hT.1 hx
    have hxt : x * z * x⁻¹ ∈ S0 := (Subgroup.mem_normalizer_iff.mp hxN z).mp d.t_mem
    have hord : orderOf (x * z * x⁻¹) = 2 := by
      have := (MulAut.conj x).orderOf_eq z
      rwa [MulAut.conj_apply, hd.order] at this
    have h2 : x * z * x⁻¹ = z := d.unique _ hxt hord
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h2]
  exact ⟨T', hST, hTt⟩

theorem allTypeTwo_of_muZ2Member (hd : TightDatum R S z) (he : TightEdgeless R)
    (hmu : TL4.MuZ2Member R) : AllTypeTwo (tightCore R) z := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hd.hypOmegaGen T
  have hW : (⨆ U ∈ η, U) ∈ WSet (CoreAssembly.conjClass (tightCore R)) :=
    ⟨η, ⟨T, hη, hinv⟩, rfl⟩
  have hst := SD.omegaStarNbr_eq_empty_of_muIsoZ2 muS3OfShape3 hd.partIHypG hW he (hmu _ hW)
  exact SD.allTypeTwo_of_omegaStarNbr_eq_empty hd.hypOmegaGen he hst hd.isUniqueInvolution_core

omit [Finite X] in
theorem eight_dvd_card (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) :
    8 ∣ Nat.card X := by
  obtain ⟨e⟩ := hq
  have h8 : Nat.card (S : Subgroup R) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h1 := Subgroup.card_subgroup_dvd_card (S : Subgroup R)
  rw [h8] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card R)

omit [Finite X] in
theorem nonabelian_fstar [hs : IsSimpleGroup ↥(genFittingFStar X)]
    (hidx : (genFittingFStar X).index ∣ 6) (h8 : 8 ∣ Nat.card X) :
    ∃ a b : genFittingFStar X, a * b ≠ b * a := by
  by_contra hcomm
  simp only [not_exists, ne_eq, not_not] at hcomm
  have : IsMulCommutative ↥(genFittingFStar X) := ⟨⟨fun a b => hcomm a b⟩⟩
  have hp : (Nat.card ↥(genFittingFStar X)).Prime := Group.is_simple_iff_prime_card.mp hs
  have hmul := (genFittingFStar X).card_mul_index
  have h6 : 8 ∣ Nat.card ↥(genFittingFStar X) * 6 :=
    h8.trans (hmul ▸ Nat.mul_dvd_mul_left _ hidx)
  have h4 : 4 ∣ Nat.card ↥(genFittingFStar X) * 3 := by omega
  have h4' : 4 ∣ Nat.card ↥(genFittingFStar X) :=
    (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h4)
  rcases hp.eq_one_or_self_of_dvd 4 h4' with h1 | h1
  · omega
  · exact absurd (h1 ▸ hp) (by decide)

end CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2
