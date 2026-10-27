module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Sub
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Triv
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Nrm

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall Tables112 TableL2)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinatePlusWitnessEquiv)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3_two_lt_pRank_mulAut {Q : Type} [Group Q] [Finite Q] (hcen : Subgroup.center Q = ⊥)
    {H : Subgroup Q} (hH : IsElemAbelian 3 H) (hcard : 3 ^ 3 ≤ Nat.card H) :
    2 < CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Q)) := by
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hH
  have hEel : IsElemAbelian 3 (H.map (MulAut.conj : Q →* MulAut Q)) := by
    refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact isElemAbelian_commute hH hx hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hH.2 x hx, map_one]
  have hEcard : Nat.card (H.map (MulAut.conj : Q →* MulAut Q)) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hk]
  have hk3 : 3 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hEel hEcard
  omega

theorem noTrialityCharThreeAt_aux (hGA : CFSG.Open.GriessAllModelsStatement) (T112 : Tables112)
    (TL2 : TableL2) (TT : Tables112Types) {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    (h6 : D3AbelianSix) (h4 : D3TwoLocalFour) (hC : D3TrialityCentRank)
    (hcore : D3TwoLocalTriality) : NoTrialityCharThreeAt G := by
  intro B x J hB hx hJ hBJ hD
  obtain ⟨q, hv, hq3, ⟨e₀⟩⟩ := hD
  have hq2 : q.p ≠ 2 := by rw [hq3]; norm_num
  have hqs : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hZ := center_pQuot_eq_bot_of_d4 hGA hqs hv hq2 e₀
  have hcen := center_pSimple_eq_bot_of_qs hqs
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv e₀
  obtain ⟨⟨hr, hf, -⟩, K, _, _, hK, ⟨es⟩⟩ := hm
  set e := coordinatePlusWitnessEquiv K es with he
  have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, hq3]
  refine ⟨K, inferInstance, inferInstance, q.p, q.exponent, e, q.prime_p, hq2, hf, hK, ?_⟩
  by_contra hnot
  set n := q.exponent with hn
  set N := Subgroup.normalizer (J : Set G) with hN
  set ψ : MulAut (PSimple 3 J) ≃* MulAut (D4Model K) := MulAut.congr e with hψ
  have hBel : IsElemAbelian 3 (actImage 3 J B) := isElemAbelian_actImage hB.1 hBJ
  set E' : Subgroup (MulAut (D4Model K)) := (actImage 3 J B).map ψ.toMonoidHom with hE'
  have hE'el : IsElemAbelian 3 E' := isElemAbelian_map_equiv ψ hBel
  have hE'card : Nat.card E' = Nat.card (actImage 3 J B) :=
    Subgroup.card_map_of_injective ψ.injective
  have hE'nE : ¬ E' ≤ D4Img K := fun h => hnot (fun a ha => h ⟨a, ha, rfl⟩)
  obtain ⟨hU1, hU2⟩ := d3_card_le_of_triality hK3 hC E' hE'el hE'nE
  obtain ⟨F, z, hFel, hFcard, hz2, hz1, hFz⟩ := h4 K n hK3
  have hL4 : 3 ^ (4 * n) ≤ Nat.card (actImage 3 J B) := by
    have h1 := card_mul_le_card_actImage hB hBJ hZ hcen (F.map e.symm.toMonoidHom) (e.symm z) ⊥
      bot_le (by simp) (isElemAbelian_map_equiv e.symm hFel)
      (by rw [← map_pow, hz2, map_one])
      (fun h => hz1 (by simpa using congrArg e h))
      (by
        rintro _ ⟨s, hs, rfl⟩
        change e.symm s * e.symm z = e.symm z * e.symm s
        rw [← map_mul, ← map_mul, hFz s hs])
      (fun a ha => by rw [Subgroup.mem_bot] at ha; rw [ha]; rfl)
      (fun a ha s _ => by rw [Subgroup.mem_bot] at ha; rw [ha]; rfl)
    rw [Subgroup.card_map_of_injective e.symm.injective, Subgroup.card_bot, mul_one] at h1
    exact hFcard.trans h1
  have hcenK : Subgroup.center (D4Model K) = ⊥ :=
    (d4Facts2 Nat.prime_three (by norm_num) hf hK3).2.2
  have hrk : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 J))) := by
    have hπ : Function.Bijective (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))) := by
      refine ⟨?_, QuotientGroup.mk'_surjective _⟩
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
    let eπ : PQuot 3 J ≃* PSimple 3 J := MulEquiv.ofBijective _ hπ
    rw [i112f_pRank_mulAut_of_mulEquiv (eπ.trans e)]
    refine d3_two_lt_pRank_mulAut hcenK hFel ?_
    calc 3 ^ 3 ≤ 3 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Nat.card F := hFcard
  obtain ⟨T, hT, hT2, hBT, hTN⟩ :=
    d3_exists_invariant_two_subgroup T112 TL2 TT hsimple hKP hB hx hJ hrk
  by_cases hT1 : ∀ t : ↥N, (t : G) ∈ T → actHom 3 J t = 1
  ·
    obtain ⟨A, hAel, hAcard⟩ := h6 K n hK3
    have hle := d3_card_le_card_actImage_of_trivial_two hB hBJ hZ hcen (A.map e.symm.toMonoidHom)
      (isElemAbelian_map_equiv e.symm hAel) hTN hT hT2 hBT hT1
    rw [Subgroup.card_map_of_injective e.symm.injective] at hle
    have h6n : 3 ^ (6 * n) ≤ Nat.card (actImage 3 J B) := hAcard.trans hle
    rw [← hE'card] at h6n
    by_cases h3 : 3 ∣ n
    · have h3n : 3 ≤ n := Nat.le_of_dvd (by omega) h3
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (h6n.trans hU1)
      omega
    · have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (h6n.trans (hU2 h3))
      omega
  ·
    push Not at hT1
    obtain ⟨t, htT, ht1⟩ := hT1
    set TN : Subgroup ↥N := T.subgroupOf N with hTN'
    set Th : Subgroup (MulAut (PSimple 3 J)) := TN.map (actHom 3 J) with hTh
    have hThne : Th ≠ ⊥ := fun h => ht1 (by
      have : actHom 3 J t ∈ Th := ⟨t, Subgroup.mem_subgroupOf.2 htT, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this)
    have hTN2 : IsPGroup 2 TN := by
      obtain ⟨j, hj⟩ := hT2.exists_card_eq
      exact IsPGroup.of_card (n := j) (by
        rw [hTN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv]
        exact hj)
    have hTh2 : IsPGroup 2 Th := hTN2.map _
    have hnorm : actImage 3 J B ≤ Subgroup.normalizer (Th : Set (MulAut (PSimple 3 J))) := by
      rw [Subgroup.le_normalizer_iff]
      rintro _ ⟨b, hb, rfl⟩ _ ⟨t', ht', rfl⟩
      refine ⟨b * t' * b⁻¹, ?_, by simp⟩
      have ht'T : ((t' : ↥N) : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
      have hbB : ((b : ↥N) : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
      have := (Subgroup.mem_normalizer_iff.1 (hBT hbB) (t' : G)).1 ht'T
      exact Subgroup.mem_subgroupOf.2 (by simpa using this)
    have hnorm' : E' ≤ Subgroup.normalizer ((Th.map ψ.toMonoidHom : Subgroup _) :
        Set (MulAut (D4Model K))) :=
      (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map _)
    refine hcore K n hK3 E' hE'el hE'nE (by rw [hE'card]; exact hL4) (Th.map ψ.toMonoidHom) ?_
      (hTh2.map _) hnorm'
    intro h
    exact hThne ((Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h)

end CFSG.LocalAnalysis.GLTheoremA
