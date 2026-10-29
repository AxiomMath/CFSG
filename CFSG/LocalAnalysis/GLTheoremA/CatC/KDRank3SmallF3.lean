module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallL3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF3

open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open TauCeti
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)

theorem smallF3_of_card_dvd_six {S : Type} [Group S] (h : Nat.card (Outer S) ∣ 6) :
    SmallF3 S := by
  haveI : Finite (Outer S) := Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0] at h; norm_num at h)
  intro P hP
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hd : Nat.card P ∣ 6 := (Subgroup.card_subgroup_dvd_card P).trans h
  rw [hm] at hd
  have hm1 : m ≤ 1 := by
    by_contra hc
    push Not at hc
    have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 hc).trans hd
    norm_num at h4
  interval_cases m
  · have h1 : Nat.card P = 1 := by simpa using hm
    haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (by simpa using hm)

theorem smallF3_of_isCyclic {S : Type} [Group S] (h : IsCyclic (Outer S)) : SmallF3 S := by
  intro P _
  haveI := h
  exact inferInstance

theorem isCyclic_outer_of_equiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsCyclic (Outer T)) : IsCyclic (Outer S) :=
  (MulEquiv.isCyclic (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e)).2 h

theorem card_outer_A2 {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.A 2 q).Valid)
    (hq : q.card = 27) (e : S ≃* (ValidLieTypeIndex.Group ⟨LieTypeIndex.A 2 q, hv⟩)) :
    Nat.card (Outer S) ∣ 6 := by
  have hpow : q.p ^ q.exponent = 3 ^ 3 := by
    rw [← PrimePower.card_def, hq]; norm_num
  have hp3 : q.p = 3 := KDRank3SmallL3.prime_eq_three_of_card_eq_27 q hq
  have hf3 : q.exponent = 3 := by
    rw [hp3] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e2 : S ≃* projectiveSL 3 (GaloisField q.p q.exponent) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 (GaloisField q.p q.exponent))
  have hk : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hdvd := higher_linear_outer_order_divides_field_gcd_bound (n := 3) q.prime_p
    q.exponent_pos (by norm_num) hk
  have h6 : 2 * q.exponent * Nat.gcd 3 (q.p ^ q.exponent - 1) = 6 := by
    rw [hf3, hp3]; norm_num
  rw [h6] at hdvd
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e2).toEquiv]
  exact hdvd

theorem card_outer_statedSU_param {S : Type} [Group S] (c fe : ℕ) [Fact c.Prime] (hc : c = 3)
    (hfe : fe = 3) (E : S ≃* StatedProj (StatedSU 3 (c ^ fe) (GaloisField c (2 * fe)))) :
    Nat.card (Outer S) = 6 := by
  subst hc hfe
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 3
      (GaloisField 3 (2 * 3)) :=
    ⟨Nat.prime_three, by norm_num, by rw [GaloisField.card 3 (2 * 3) (by norm_num)]⟩
  have e1 : S ≃* unitaryPSU h 3 := E.trans (unitaryPSUEquiv h (by norm_num)).symm
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    unitary_full_diagonal_outer_order h (n := 3) (by norm_num) (by norm_num)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e1).toEquiv, hcard]
  norm_num

theorem card_outer_twistedA2 {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 27)
    (e : S ≃* (ValidLieTypeIndex.Group ⟨LieTypeIndex.twistedA 2 q, hv⟩)) :
    Nat.card (Outer S) = 6 := by
  have hpow : q.p ^ q.exponent = 3 ^ 3 := by
    rw [← PrimePower.card_def, hq]; norm_num
  have hp3 : q.p = 3 := KDRank3SmallL3.prime_eq_three_of_card_eq_27 q hq
  have hf3 : q.exponent = 3 := by
    rw [hp3] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hc : ValidLieTypeIndex.characteristic ⟨LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    simp [ValidLieTypeIndex.characteristic, hp3]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    simp [ValidLieTypeIndex.fieldExponent, hf3]
  exact card_outer_statedSU_param _ _ hc hfe
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv))

section Ree


theorem isCyclic_outer_reeG2 {S : Type} [Group S] (hv : (LieTypeIndex.reeG2 1).Valid)
    (e : S ≃* (ValidLieTypeIndex.Group ⟨LieTypeIndex.reeG2 1, hv⟩)) : IsCyclic (Outer S) := by
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge 1 hv (GaloisField 3 3) (by rw [hK])
  have hmodel : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 3 :=
    ⟨⟨Nat.prime_three, by norm_num, rfl, rfl, by decide, le_rfl⟩, 1, by norm_num,
      GaloisField 3 3, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩
  obtain ⟨eG⟩ := (CFSG.LieType.Ree.small_Ree_model_Schreier S 3 3 hmodel).2.2.2.2 1
    (GaloisField 3 3) (by norm_num) hK ⟨e.trans b.symm⟩
  have hcyc := (CFSG.ComponentClassification.LiteratureLocal.SmallRee.outer_reeGamma_cyclic
    (a := 1) (K := GaloisField 3 3) (by norm_num) (by rw [hK])).1
  exact isCyclic_outer_of_equiv eG hcyc

theorem smallF3_all :
    ∀ (S : Type) [Group S] [Finite S] (d : ValidLieTypeIndex),
      Nonempty (S ≃* (CFSGIndex.lie d).Group) → CFSG.LocalAnalysis.GLTheoremA.IsRank3Small d.1 →
        SmallF3 S := by
  intro S _ _ d hd hsmall
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact hsmall.elim
    · exact hsmall.elim
    · exact smallF3_of_card_dvd_six (card_outer_A2 q hv hsmall hd.some)
    · exact hsmall.elim
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · exact hsmall.elim
    · exact hsmall.elim
    · exact smallF3_of_card_dvd_six
        (by rw [card_outer_twistedA2 q hv hsmall hd.some])
    · exact hsmall.elim
  | reeG2 m =>
    have hm : m = 1 := hsmall
    subst hm
    exact smallF3_of_isCyclic (isCyclic_outer_reeG2 hv hd.some)
  | _ => exact hsmall.elim

end Ree

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF3
