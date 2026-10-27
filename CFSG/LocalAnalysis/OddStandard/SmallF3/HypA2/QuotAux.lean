module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem isTwoQuasisimple_of_surjective_aux {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (hX : HarrisLit.IsTwoQuasisimple X) (f : X →* Y) (hf : Function.Surjective f)
    (hY : pPrimeCore 2 Y ≠ ⊤) :
    HarrisLit.IsTwoQuasisimple Y ∧
      Nonempty (X ⧸ Open.fusionZStar X ≃* Y ⧸ Open.fusionZStar Y) := by
  have : Group.IsPerfect X := hX.1
  have hYp : Group.IsPerfect Y := Group.IsPerfect.ofSurjective hf
  obtain ⟨e⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' f hf hX.2 hY
  refine ⟨⟨hYp, ?_⟩, ⟨e⟩⟩
  obtain ⟨eX⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar X
  obtain ⟨eY⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar Y
  let e' : (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X) ≃*
      (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y) := (eX.trans e).trans eY.symm
  obtain ⟨-, hsX, a, b, hab⟩ := hX.2
  have : IsSimpleGroup ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) := hsX
  refine ⟨Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _), e'.symm.isSimpleGroup,
    e' a, e' b, fun h => hab ?_⟩
  apply e'.injective
  rw [map_mul, map_mul, h]

theorem central_quotient_two_quasisimple {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hker : f.ker ≤ center A) (hA : HarrisLit.IsTwoQuasisimple A) :
    HarrisLit.IsTwoQuasisimple B ∧
      Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) := by
  haveI : Finite B := Finite.of_surjective f hf
  haveI : Group.IsPerfect A := hA.1
  haveI : Nontrivial ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A)) :=
    hA.2.2.1.toNontrivial
  haveI : Nontrivial (A ⧸ pPrimeCore 2 A) :=
    (QuotientGroup.mk'_surjective (center (A ⧸ pPrimeCore 2 A))).nontrivial
  haveI : Nontrivial A := (QuotientGroup.mk'_surjective (pPrimeCore 2 A)).nontrivial
  have hperfB : Group.IsPerfect B := Group.IsPerfect.ofSurjective hf
  have hBnt : Nontrivial B := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hker_top : f.ker = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [MonoidHom.mem_ker]
      exact Subsingleton.elim (f a) 1
    have hAleZ : (⊤ : Subgroup A) ≤ center A := by rw [← hker_top]; exact hker
    haveI : IsMulCommutative A :=
      IsMulCommutative.of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (hAleZ (show a ∈ (⊤ : Subgroup A) from trivial)) b).symm
    exact false_of_nontrivial_of_subsingleton A
  have hY : pPrimeCore 2 B ≠ ⊤ := by
    intro htop
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial B := hBnt
    haveI : Group.IsPerfect B := hperfB
    have hodd : Odd (Nat.card B) := by
      have h1 := Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := B))
      rwa [htop, Subgroup.card_top] at h1
    have hsolv : Group.IsSolvable B := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.IsPerfect.not_isSolvable (G := B) hsolv
  exact isTwoQuasisimple_of_surjective_aux hA f hf hY

theorem pPrimeCore_eq_bot_of_isQuasisimple {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) : pPrimeCore 2 K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect K := hK.1
  haveI : Nontrivial (K ⧸ center K) := hK.2.1.toNontrivial
  haveI : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hOcenter : pPrimeCore 2 K ≤ center K := by
    let O : Subgroup K := pPrimeCore 2 K
    let Z : Subgroup K := center K
    let π : K →* K ⧸ Z := QuotientGroup.mk' Z
    let Obar : Subgroup (K ⧸ Z) := O.map π
    have hObarNormal : Obar.Normal :=
      (inferInstance : O.Normal).map π (QuotientGroup.mk'_surjective Z)
    have hsimple : IsSimpleGroup (K ⧸ Z) := hK.2.1
    rcases (haveI := hObarNormal; hsimple.eq_bot_or_eq_top_of_normal Obar) with hbot | htop
    · intro x hx
      have hxmap : π x ∈ Obar := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hbot] at hxmap
      exact (QuotientGroup.eq_one_iff (N := Z) x).mp (Subgroup.mem_bot.mp hxmap)
    · exfalso
      have hcom : Z ⊔ O = ⊤ := by
        calc Z ⊔ O = Subgroup.comap π Obar := (QuotientGroup.comap_map_mk' Z O).symm
          _ = Subgroup.comap π (⊤ : Subgroup (K ⧸ Z)) := by rw [htop]
          _ = ⊤ := by simp
      have hOZ : O ⊔ Z = ⊤ := by simpa [sup_comm] using hcom
      have hleO : _root_.commutator K ≤ O :=
        (inferInstance : O.Normal).commutator_le_of_self_sup_commutative_eq_top hOZ
          (by infer_instance)
      have hOeq : O = ⊤ := by
        rw [hK.1.commutator_eq_top] at hleO
        exact eq_top_iff.mpr hleO
      have hOodd : Odd (Nat.card O) :=
        Nat.coprime_two_left.mp
          (by simpa [O] using (CFSG.pPrimeCore_coprime_card (p := 2) (G := K)))
      have hcard : Nat.card O = Nat.card K := by
        rw [hOeq]
        exact Subgroup.card_top
      have hKodd : Odd (Nat.card K) := hcard ▸ hOodd
      have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
      exact Group.IsPerfect.not_isSolvable (G := K) hsolv
  have hO2 : IsPGroup 2 ↥(pPrimeCore 2 K) := hZ.to_le hOcenter
  have hOodd : Odd (Nat.card ↥(pPrimeCore 2 K)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := K))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(pPrimeCore 2 K))).mp hO2
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 h
    have hdvd : 2 ∣ Nat.card ↥(pPrimeCore 2 K) := by rw [hn]; exact h2
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hdvd)
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.mp hn

theorem isTwoQuasisimple_of_isQuasisimple {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) : HarrisLit.IsTwoQuasisimple K := by
  have hO : pPrimeCore 2 K = ⊥ := pPrimeCore_eq_bot_of_isQuasisimple hK hZ
  refine ⟨hK.1, ?_⟩
  exact CFSG.IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot) hK

end CFSG.OddStandard.SmallF3.HypA2
