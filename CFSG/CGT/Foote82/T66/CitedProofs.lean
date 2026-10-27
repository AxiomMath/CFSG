module

public import CFSG.CGT.Foote82.T66.Cited
import CFSG.LocalAnalysis.OddStandard.GlueAlt
import CFSG.GH74.Uniqueness.SU.SU13TA1Invol
import CFSG.ClassicalInvolution.LBalance.Glauberman
import CFSG.CGT.Foote82.OddCover
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU4
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.CGT.Foote82

open Equiv Equiv.Perm

namespace CitedProofsAux

theorem exists_two_two_mem_altOn {m : ℕ} {F : Set (Fin m)} (hF : 4 ≤ F.ncard) :
    ∃ g ∈ altOn F, g.cycleType = {2, 2} ∧ g ^ 2 = 1 := by
  have hcard : 4 ≤ Nat.card F := by rwa [Nat.card_coe_set_eq]
  let e : Fin 4 ↪ F := (Fin.castLEEmb hcard).trans (Finite.equivFin F).symm.toEmbedding
  let p : Fin 4 → Fin m := fun i => (e i : Fin m)
  have hp : Function.Injective p := Subtype.val_injective.comp e.injective
  have hpF : ∀ i, p i ∈ F := fun i => (e i).2
  have hct : (swap (p 0) (p 1) * swap (p 2) (p 3)).cycleType = {2, 2} :=
    cycleType_swap_mul_swap_of_nodup ((show [(0 : Fin 4), 1, 2, 3].Nodup by decide).map hp)
  refine ⟨swap (p 0) (p 1) * swap (p 2) (p 3), Subgroup.mem_inf.2 ⟨?_, ?_⟩, hct, ?_⟩
  · rw [Perm.mem_alternatingGroup, map_mul, sign_swap (hp.ne (by decide)),
      sign_swap (hp.ne (by decide))]
    decide
  · rw [mem_fixingSubgroup_iff]
    intro x hx
    have hx' : ∀ i, x ≠ p i := fun i h => hx (h ▸ hpF i)
    rw [Perm.smul_def, Perm.mul_apply, swap_apply_of_ne_of_ne (hx' 2) (hx' 3),
      swap_apply_of_ne_of_ne (hx' 0) (hx' 1)]
  · rw [Perm.pow_prime_eq_one_iff, hct]
    simp

private def a6a : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide⟩

private def a6b : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, by
    rw [Perm.mem_alternatingGroup, map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide⟩

private theorem a6_four :
    a6a * a6a = 1 ∧ a6b * a6b = 1 ∧ a6a * a6b = a6b * a6a ∧ a6a ≠ 1 ∧ a6b ≠ 1 ∧ a6b ≠ a6a ∧
      a6a * a6b ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem center_omegaMinusTwo_two :
    Subgroup.center ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) = ⊥ := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨hs, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : IsSimpleGroup ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2)) with h | h
  · exact h
  · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x) hna

end CitedProofsAux

open CitedProofsAux in
theorem schurAltLift_holds : SchurAltLift := by
  intro E _ _ m hm π hrange hperf hker _ L F hF hLF hinj
  by_contra hne
  have hmem : ∀ x, π x ∈ alternatingGroup (Fin m) := fun x => hrange ▸ ⟨x, rfl⟩
  let η : E →* alternatingGroup (Fin m) := π.codRestrict _ hmem
  have hηx : ∀ x, ((η x : alternatingGroup (Fin m)) : Perm (Fin m)) = π x := fun _ => rfl
  have hηker : η.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hηx, OneMemClass.coe_eq_one]
  have hηsurj : Function.Surjective η := by
    rintro ⟨g, hg⟩
    rw [← hrange] at hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨x, rfl⟩
  haveI : Group.IsPerfect E := ⟨hperf⟩
  have hle : Nat.card η.ker ≤ 2 :=
    CFSG.OddStandard.GlueAlt.card_ker_le_two_of_alt hm η hηsurj (hηker ▸ hker)
  have hlt : 1 < Nat.card η.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 (hηker ▸ hne)
  have hcov : CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover η :=
    ⟨hηsurj, hηker ▸ hker, by omega, inferInstance⟩
  obtain ⟨g, hgF, hg, hg2⟩ := exists_two_two_mem_altOn hF
  rw [← hLF] at hgF
  obtain ⟨x, hxL, hx⟩ := hgF
  have h4 : orderOf x = 4 :=
    hcov.orderOf_eq_four_of_cycleType_two_two (by omega) (by rw [hηx, hx]; exact hg)
  have hx2 : x ^ 2 = 1 := hinj _ (L.pow_mem hxL 2) (by rw [map_pow, hx, hg2])
  have hdvd := orderOf_dvd_of_pow_eq_one hx2
  rw [h4] at hdvd
  norm_num at hdvd

open CFSG.ClassicalInvolution in
theorem glaubermanF_holds : GlaubermanF := by
  intro X _ _ _ hX _ heven S K hK hfix
  have hcore : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [pPrimeCore_two_eq_oddCore X, CFSG.oddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hKle : K ≤ sylowFixingAut (S : Subgroup X) := fun α hα =>
    mem_sylowFixingAut.2 (hfix α hα)
  haveI : Group.IsSolvable (sylowFixingAut (S : Subgroup X)) :=
    glaubermanSylowFixingSolvable X hcore S
  have hsolv : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKle)
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable K hsolv

section U42

open CFSG.RankThree.PartTwo CitedProofsAux in
theorem schurU42Lift_holds : SchurU42Lift := by
  intro E _ _ π hπ hperf hker _ L ⟨e⟩ hinj
  haveI : Group.IsPerfect E := ⟨hperf⟩
  by_contra hne
  have hdvd : Nat.card π.ker ∣ 2 :=
    (Subgroup.card_dvd_of_surjective
      (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective π hπ hker)).trans
      (dvd_of_eq card_hopfMultiplier_omegaMinusTwo)
  have hlt : 1 < Nat.card π.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hcard : Nat.card π.ker = 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hcen : Subgroup.center E = π.ker := by
    refine le_antisymm (fun z hz => ?_) hker
    rw [MonoidHom.mem_ker]
    have hz' : π z ∈ Subgroup.center ↥(omegaMinusTwo 2) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := hπ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    rwa [center_omegaMinusTwo_two, Subgroup.mem_bot] at hz'
  have hL : CFSG.Blueprint.LieModel (E ⧸ Subgroup.center E) .PSU 4 2 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcen.symm))
      blueprintLieModel_omegaMinusTwo
  obtain ⟨α⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_mulEquiv_statedSp_of_lieModel
    inferInstance (by rw [hcen, hcard]) hL
  have hφinj : Function.Injective (π.subgroupMap L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hinj x x.2 (congrArg Subtype.val hx))
  let φ : ↥L ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.ofBijective (π.subgroupMap L) ⟨hφinj, π.subgroupMap_surjective L⟩).trans e
  obtain ⟨ha2, hb2, hab, ha1, hb1, hba, hab1⟩ := a6_four
  have hnc : ∀ y : ↥L, y ≠ 1 → (y : E) ∉ Subgroup.center E := fun y hy1 hyc =>
    hy1 (Subtype.ext (hinj y y.2 (by rw [← MonoidHom.mem_ker, ← hcen]; exact hyc)))
  have hu1 : φ.symm a6a ≠ 1 := fun h => ha1 (by rw [← φ.apply_symm_apply a6a, h, map_one])
  have hv1 : φ.symm a6b ≠ 1 := fun h => hb1 (by rw [← φ.apply_symm_apply a6b, h, map_one])
  have huv1 : φ.symm a6a * φ.symm a6b ≠ 1 := fun h =>
    hab1 (by rw [← φ.apply_symm_apply a6a, ← φ.apply_symm_apply a6b, ← map_mul, h, map_one])
  have hvu : φ.symm a6b ≠ φ.symm a6a := fun h => hba (φ.symm.injective h)
  have hu2 : φ.symm a6a * φ.symm a6a = 1 := by rw [← map_mul, ha2, map_one]
  have hv2 : φ.symm a6b * φ.symm a6b = 1 := by rw [← map_mul, hb2, map_one]
  have huv : φ.symm a6a * φ.symm a6b = φ.symm a6b * φ.symm a6a := by
    rw [← map_mul, ← map_mul, hab]
  obtain ⟨A, hA⟩ := α.surjective (φ.symm a6a : E)
  obtain ⟨B, hB⟩ := α.surjective (φ.symm a6b : E)
  have hcenα : ∀ x : CFSG.Open.StatedSp 2 (ZMod 3),
      x ∈ Subgroup.center (CFSG.Open.StatedSp 2 (ZMod 3)) → α x ∈ Subgroup.center E := by
    intro x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g', rfl⟩ := α.surjective g
    rw [← map_mul, ← map_mul, hx g']
  have hneg : ∀ x : CFSG.Open.StatedSp 2 (ZMod 3), (x : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -1 →
      x ∈ Subgroup.center (CFSG.Open.StatedSp 2 (ZMod 3)) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_neg_one, neg_one_mul]
  have hAA : A * A = 1 := α.injective (by
    rw [map_mul, hA, map_one]
    exact congrArg Subtype.val hu2)
  have hBB : B * B = 1 := α.injective (by
    rw [map_mul, hB, map_one]
    exact congrArg Subtype.val hv2)
  have hAB : A * B = B * A := α.injective (by
    rw [map_mul, map_mul, hA, hB]
    exact congrArg Subtype.val huv)
  have hA2 : (A : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * A = 1 := by
    rw [← Subgroup.coe_mul, hAA, Subgroup.coe_one]
  have hB2 : (B : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * B = 1 := by
    rw [← Subgroup.coe_mul, hBB, Subgroup.coe_one]
  have hAB' : (A : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * B = B * A := by
    rw [← Subgroup.coe_mul, hAB, Subgroup.coe_mul]
  have hA1 : (A : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ≠ 1 := fun h =>
    hu1 (Subtype.ext (by rw [← hA, show A = 1 from Subtype.ext h, map_one]; rfl))
  have hAm : (A : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ≠ -1 := fun h =>
    hnc _ hu1 (hA ▸ hcenα A (hneg A h))
  rcases CFSG.RankThree.SubgroupLists.eq_of_commute_involution (by decide : (2 : ZMod 3) ≠ 0)
      A.2 B.2 hA2 hB2 hAB' hA1 hAm with h | h | h | h
  · exact hv1 (Subtype.ext (by rw [← hB, show B = 1 from Subtype.ext h, map_one]; rfl))
  · exact hnc _ hv1 (hB ▸ hcenα B (hneg B h))
  · exact hvu (Subtype.ext (by rw [← hB, ← hA, show B = A from Subtype.ext h]))
  · have hAB1 : ((A * B : CFSG.Open.StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -1 := by
      rw [Subgroup.coe_mul, h, mul_neg, hA2]
    have hc := hcenα _ (hneg _ hAB1)
    rw [map_mul, hA, hB] at hc
    exact hnc _ huv1 hc

end U42

end CFSG.CGT.Foote82
