module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGASeven
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieL2

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.GorensteinWalter

theorem small_arith {n i x : ℕ} (hn : n = 60 ∨ n = 168 ∨ n = 360) (hmul : i * x = n)
    (hx : 120 ≤ x) (hfac : n ∣ i.factorial) (hi : i ≠ 1) : False := by
  have hi3 : i ≤ 3 := by
    by_contra h
    push Not at h
    have : 4 * 120 ≤ i * x := Nat.mul_le_mul h hx
    omega
  interval_cases i
  · omega
  · exact hi rfl
  · rcases hn with rfl | rfl | rfl <;> exact absurd hfac (by decide)
  · rcases hn with rfl | rfl | rfl <;> exact absurd hfac (by decide)

theorem five_le_of_isOddPrimePower {q : ℕ} (hq : IsOddPrimePower q) (h3 : q ≠ 3) : 5 ≤ q := by
  obtain ⟨p, f, hp, hpodd, hf, rfl⟩ := hq
  have hp3 : 3 ≤ p := by
    rcases hpodd with ⟨j, hj⟩
    have := hp.two_le
    omega
  have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  obtain ⟨j, hj⟩ := hpodd.pow (n := f)
  omega

variable {G : Type} [Group G] [Finite G]

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem false_of_isPGroup (h : IsPGroup 2 (G ⧸ pPrimeCore 2 G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (normalizer (Q : Set G))
  have hSidx : ¬ 2 ∣ S.index := by
    have := (isSylowOf_iff.mp (hE.isSylowOf_top hS)).2.2
    rwa [relIndex_top_right] at this
  set Hb := (normalizer (Q : Set G)).map (QuotientGroup.mk' (pPrimeCore 2 G)) with hHb
  have h1 : Hb.index ∣ S.index :=
    (index_map_dvd _ (QuotientGroup.mk'_surjective _)).trans (index_dvd_of_le hS.le)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ Hb.index_dvd_card)
  rcases j with _ | j
  · exact hE.map_normalizer_ne_top (index_eq_one.mp (by rw [hj, pow_zero]))
  · exact hSidx ((hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1)

theorem false_of_psl2
    {K' : Type} [Field K'] [Finite K']
    (hK' : IsOddPrimePower (Nat.card K')) {L₀ : Subgroup (G ⧸ pPrimeCore 2 G)} [L₀.Normal]
    (hidx : Odd L₀.index) (e₀ : L₀ ≃* PSL2 K') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M⟩ := hE.nonempty_pslModel
  set O := pPrimeCore 2 G with hO
  set π := QuotientGroup.mk' O with hπ
  set H := normalizer (Q : Set G) with hH
  have hOodd : Odd (Nat.card O) := odd_card_pPrimeCore
  set Xb := (L₀.comap π ⊓ H).map π with hXb
  have hXL : Xb ≤ L₀ := map_le_iff_le_comap.mpr inf_le_left
  have hXH : Xb ≤ H.map π := map_mono inf_le_right
  have hLH : ¬ L₀ ≤ H.map π := fun h => hE.false_of_normal_le_map hidx h
  have h120 : 120 ≤ Nat.card Xb := by
    have hdvd := M.card_pgl_dvd hE hidx
    rw [Nat.card_congr (pGammaL2PGLRangeEquiv M.F).symm.toEquiv, pgl2_card_formula] at hdvd
    have hle := Nat.le_of_dvd Nat.card_pos hdvd
    have h5 := five_le_of_isOddPrimePower M.hF (by have := M.h3; omega)
    calc 120 = 5 * (5 ^ 2 - 1) := by norm_num
      _ ≤ Nat.card M.F * (Nat.card M.F ^ 2 - 1) :=
        Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1)
      _ ≤ _ := hle
  have hXcard : Nat.card Xb ≤ Nat.card L₀ := Subgroup.card_le_of_le hXL
  have hcardL : Nat.card L₀ = Nat.card K' * (Nat.card K' ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e₀.toEquiv, psl2_card_formula _ hK']
  by_cases hq3 : Nat.card K' = 3
  · rw [hq3] at hcardL
    norm_num at hcardL
    omega
  have h5 := five_le_of_isOddPrimePower hK' hq3
  have h4 : 4 ≤ Nat.card K' := by omega
  have hqodd : Odd (Nat.card K') := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := hK'
    rw [hq]
    exact hpodd.pow
  have : IsSimpleGroup (PSL2 K') := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hL₀s : IsSimpleGroup L₀ := e₀.isSimpleGroup
  obtain ⟨E, hEK, hE2, hE4⟩ := hE.main.four
  have hEp : IsPGroup 2 E := isPGroup_of_sq_eq_one hE2
  have hinj : Set.InjOn π E := fun u hu v hv h =>
    AschbacherToolkit.quotient_injective_on_of_isPGroup O hOodd hEp hu hv h
  set U := E.map π with hU
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, hE2 z hz, map_one]
  have hUfour : AschbacherKnownGroup.IsFourGroup U := by
    refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hU2⟩, by rw [card_map_of_injOn π hinj, hE4]⟩
    exact mul_comm_of_sq_eq_one hU2 a.2 b.2
  have hjoin : AschbacherKnownGroup.centralizerJoin U L₀ ≤ H.map π := by
    unfold AschbacherKnownGroup.centralizerJoin
    refine iSup_le fun u => iSup_le fun hu => iSup_le fun hu1 => ?_
    obtain ⟨z, hzE, rfl⟩ := hu
    have hz1 : z ≠ 1 := fun h => hu1 (by rw [h, map_one])
    have hzo : orderOf z = 2 := orderOf_eq_prime (hE2 z hzE) hz1
    refine inf_le_right.trans ?_
    rw [AschbacherToolkit.centralizer_quotient_odd O hOodd z hzo]
    exact map_mono (centralizer_le_of_involution hE.main.tight
      (twoPrimeLayerIn_le Q (hEK hzE)) hzo)
  have hgen : ¬ L₀ ≤ AschbacherKnownGroup.centralizerJoin U L₀ := fun h =>
    hLH (h.trans hjoin)
  have hq : CFSG.Open.IsQuasisimple L₀ :=
    RankTwoOddLie.isQuasisimple_of_mulEquiv e₀.symm (RankTwoOddLie.isQuasisimple_psl2 h4)
  have hZ : center L₀ = ⊥ := RankTwoOddLie.center_eq_bot_of_psl2 h4 e₀
  have hdP : AschbacherKnownGroup.HasDihedralSylowTwo (PSL2 K') :=
    RankTwoOddLie.hasDihedralSylowTwo_of_gw (psl2_odd_hasDihedralSylowTwo_model _ hK')
  set eZ : L₀ ⧸ center L₀ ≃* L₀ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with heZ
  have hd : AschbacherKnownGroup.HasDihedralSylowTwo (L₀ ⧸ center L₀) :=
    RankTwoOddLie.hasDihedralSylowTwo_of_mulEquiv' (eZ.trans e₀).symm hdP
  have hz : (Nat.card (center L₀)).factorization 2 ≤ 1 := by
    rw [hZ, Subgroup.card_bot, Nat.factorization_one]
    simp
  have hUN : U ≤ normalizer (L₀ : Set (G ⧸ O)) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hsmall := (AschbacherKnownGroup.FactsL2.dihedral_cover_generation_holds _ L₀ U hq hd hz
    hUN hUfour hgen).1
  have hcardQ : Nat.card (L₀ ⧸ center L₀) = Nat.card L₀ := Nat.card_congr eZ.toEquiv
  have hn : Nat.card L₀ = 60 ∨ Nat.card L₀ = 168 ∨ Nat.card L₀ = 360 := by
    rcases hsmall with ⟨⟨eA⟩⟩ | ⟨p', f', hq', hmodel⟩
    · exfalso
      have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      have h1 := Nat.card_congr eA.toEquiv
      rw [hcardQ, hcardL, h7] at h1
      exact RankTwoOddLie.card_psl2_ne_2520 h5 hqodd h1
    · have : Fact p'.Prime := ⟨hmodel.1.1⟩
      obtain ⟨e'⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2
        p' f' hmodel
      have hf' : f' ≠ 0 := by have := hmodel.1.2.1; omega
      have hp'odd : Odd p' := by
        refine (Fact.out : p'.Prime).odd_of_ne_two fun h2 => ?_
        subst h2
        have hev : Even (2 ^ f') := Nat.even_pow.mpr ⟨even_two, hf'⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
        rcases hq' with h1 | h1 | h1 <;> rw [h1] at hev <;> exact absurd hev (by decide)
      have hK'' : Nat.card (GaloisField p' f') = p' ^ f' := GaloisField.card p' f' hf'
      have hcard' : Nat.card (L₀ ⧸ center L₀) = p' ^ f' * ((p' ^ f') ^ 2 - 1) / 2 := by
        rw [Nat.card_congr e'.toEquiv, psl2_card_formula _
          ⟨p', f', Fact.out, hp'odd, by omega, hK''⟩, hK'']
      rw [hcardQ] at hcard'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      rcases hq' with h1 | h1 | h1 <;> rw [h1] at hcard' <;> norm_num at hcard' <;> omega
  set Xs := Xb.subgroupOf L₀ with hXs
  have hXs : Xs ≠ ⊤ := fun h => hLH ((subgroupOf_eq_top.mp h).trans hXH)
  have hfac := card_dvd_factorial_index_of_isSimpleGroup hL₀s hXs
  have hmul := Xs.index_mul_card
  have hXscard : Nat.card Xs = Nat.card Xb := by rw [card_subgroupOf, inf_eq_left.mpr hXL]
  rw [hXscard] at hmul
  exact small_arith hn hmul h120 hfac fun h => hXs (index_eq_one.mp h)

end EndSetting

namespace MainCounterexample

variable {Q : Subgroup G} (hM : MainCounterexample G Q) (hE : EndSetting Q)
include hM hE

theorem false_of_pgl2
    {K' : Type} [Field K'] [Finite K']
    (hK' : IsOddPrimePower (Nat.card K')) {L₀ : Subgroup (G ⧸ pPrimeCore 2 G)} [L₀.Normal]
    (hidx : Odd L₀.index) (e₀ : L₀ ≃* PGL2 K') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M⟩ := hE.nonempty_pslModel
  set O := pPrimeCore 2 G with hO
  set π := QuotientGroup.mk' O with hπ
  have hcardL : Nat.card L₀ = Nat.card K' * (Nat.card K' ^ 2 - 1) := by
    rw [Nat.card_congr e₀.toEquiv, pgl2_card_formula]
  by_cases hq3 : Nat.card K' = 3
  ·
    set Xb := (L₀.comap π ⊓ normalizer (Q : Set G)).map π with hXb
    have hXL : Xb ≤ L₀ := map_le_iff_le_comap.mpr inf_le_left
    have hdvd := M.card_pgl_dvd hE hidx
    rw [Nat.card_congr (pGammaL2PGLRangeEquiv M.F).symm.toEquiv, pgl2_card_formula] at hdvd
    have hle := (Nat.le_of_dvd Nat.card_pos hdvd).trans (Subgroup.card_le_of_le hXL)
    have h5 := five_le_of_isOddPrimePower M.hF (by have := M.h3; omega)
    have h120 : 5 * (5 ^ 2 - 1) ≤ Nat.card M.F * (Nat.card M.F ^ 2 - 1) :=
      Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1)
    rw [hcardL, hq3] at hle
    norm_num at h120 hle
    omega
  obtain ⟨L₁, hL₁n, hL₁L₀, ⟨e₁⟩⟩ := exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
    L₀ inferInstance K' hK' (by have := five_le_of_isOddPrimePower hK' hq3; omega) e₀
  have hcard₁ : Nat.card L₁ = Nat.card K' * (Nat.card K' ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e₁.toEquiv, psl2_card_formula _ hK']
  have hrel : L₁.relIndex L₀ = 2 := by
    have h := relIndex_mul_card L₁ L₀
    rw [inf_eq_left.mpr hL₁L₀, hcard₁, hcardL] at h
    have hqodd : Odd (Nat.card K') := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hK'
      rw [hq]
      exact hpodd.pow
    have h5 := five_le_of_isOddPrimePower hK' hq3
    have h2 : 2 ≤ Nat.card K' * (Nat.card K' ^ 2 - 1) :=
      le_trans (by norm_num) (Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1))
    have hpos : 0 < Nat.card K' * (Nat.card K' ^ 2 - 1) / 2 := by omega
    have heven : 2 * (Nat.card K' * (Nat.card K' ^ 2 - 1) / 2) =
        Nat.card K' * (Nat.card K' ^ 2 - 1) := by
      apply Nat.mul_div_cancel'
      exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd.pow odd_one)) _
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans heven.symm)
  have hidx₁ : (L₁.comap π).index = 2 * L₀.index := by
    rw [index_comap_of_surjective L₁ (QuotientGroup.mk'_surjective _),
      ← relIndex_mul_index hL₁L₀, hrel]
  have := hL₁n
  obtain ⟨M₂, hM₂n, hM₂idx, -⟩ := exists_normal_index_two_containing_of_index_eq_two_mul_odd
    (N := L₁.comap π) inferInstance (by rw [hidx₁]; exact dvd_mul_right 2 _) (by
      rw [hidx₁]
      obtain ⟨j, hj⟩ := hidx
      omega)
  exact hM.false_of_index_eq_two hE hM₂n hM₂idx

theorem false_of_endSetting :
    False := by
  rcases (gorensteinWalter : gorensteinWalterStatement) G (hM.hasDihedralSylowTwo hE) with
    ⟨-, h⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, K', hK', L₀, hL₀n, hL₀idx, hmodel⟩
  · exact hE.false_of_isPGroup h
  · exact hE.false_of_aSeven e
  · have := hL₀n
    rcases hmodel with ⟨⟨e₀⟩⟩ | ⟨⟨e₀⟩⟩
    · exact hE.false_of_psl2 hK' hL₀idx e₀
    · exact hM.false_of_pgl2 hE hK' hL₀idx e₀

end MainCounterexample

theorem stepEndgame :
    StepEndgame :=
  fun _ _ _ _ hM hS hC hodd => hM.false_of_endSetting ⟨hS, hC, hodd⟩

end CFSG.ComponentClassification.Asc75T4
