module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264tTD42Aux
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42Aut
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sTD42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti


section Main


theorem td42_three_false (hR : TD42OuterFix) {Y : Type} [Group Y] [Finite Y] {K B : Subgroup Y}
    (hK : KHyp 3 K B) (hc : catalogIs (↥K ⧸ Subgroup.center ↥K) fTD42)
    (hcB : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < 3 ^ 3) : False := by
  haveI : K.Normal := hK.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥K = ⊥ := center_bot_of_KHyp_td42 hK hc
  obtain ⟨hfinS, hsimp, hcardS, ⟨φS⟩, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I131.sdata_of_lieModel
      (CFSG.LocalAnalysis.GLTheoremA.CatB.blueprintLieModel_td4two hc)
  haveI := hsimp
  have hMAS : Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) = 3 * 211341312 := card_mulAut_fTD42 hc
  let eSK : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eK : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) := eSK.symm
  have hKcard : Nat.card ↥K = 211341312 := (Nat.card_congr eSK.toEquiv).symm.trans hcardS
  have hMAK : Nat.card (MulAut ↥K) = 3 * Nat.card ↥K := by
    rw [hKcard]
    exact ((Nat.card_congr (MulAut.congr eSK).toEquiv).symm.trans hMAS)
  have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := CFSG.LocalAnalysis.GLTheoremA.TD42.conj_injective hZ
  have hInnCard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K) = Nat.card ↥K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hK3 : ∀ E W : Subgroup ↥K, IsElemAbelian 3 E → Nat.card E = 9 → ¬ 3 ∣ Nat.card W →
      E ≤ Subgroup.normalizer (W : Set ↥K) → W = ⊥ := by
    intro E W hE hE9 hW hEW
    have φ : ↥K ≃* ↥CFSG.Quasithin.trialityGroup8 := eK.trans φS
    exact CFSG.RankThree.PartTwo.Sec4.Item434D42.d4_k3_of_equiv φ hKcard hE hE9 hW hEW
  let π : Y →* MulAut ↥K := MulAut.conjNormal
  have hπker : ∀ y : Y, π y = 1 ↔ y ∈ Subgroup.centralizer (K : Set Y) := fun y =>
    CFSG.LocalAnalysis.GLTheoremA.conjNormal_eq_one_iff y
  have hπK : ∀ k : Y, ∀ hk : k ∈ K, π k = MulAut.conj (⟨k, hk⟩ : ↥K) := by
    intro k hk
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  have hπinn : ∀ k : Y, k ∈ K → π k ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
    fun k hk => ⟨⟨k, hk⟩, (hπK k hk).symm⟩
  have hKM : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.inf_centralizer_eq_bot hZ
  have hBea : IsElemAbelian 3 B := hK.elem
  haveI : IsMulCommutative B := hBea.1
  have hBcomm : ∀ b1 ∈ B, ∀ b2 ∈ B, b1 * b2 = b2 * b1 := fun b1 h1 b2 h2 =>
    comm_mem_of_isMulCommutative B h1 h2
  have hBexp : ∀ b ∈ B, b ^ 3 = 1 := hBea.2
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := hK.twogrp
  have hB81 : 81 ≤ Nat.card B := by
    have h := hK.card
    norm_num at h
    exact h
  have hMnorm : ∀ m ∈ Subgroup.centralizer (K : Set Y), m ∈ Subgroup.normalizer (T : Set Y) := by
    intro m hm
    apply mem_normalizer_of_comm
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.1 hm) h (hTK hh)).symm
  let f : ↥B →* MulAut ↥K := π.comp B.subtype
  let A : Subgroup (MulAut ↥K) := f.range
  let C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y)
  have hA_mem : ∀ a, a ∈ A ↔ ∃ b : ↥B, π (b : Y) = a := fun a => MonoidHom.mem_range
  have hC_mem : ∀ y, y ∈ C ↔ y ∈ B ∧ y ∈ Subgroup.centralizer (K : Set Y) := fun y => Subgroup.mem_inf
  have hBC : Nat.card ↥B = Nat.card ↥C * Nat.card ↥A := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥B ⧸ f.ker) = Nat.card ↥A :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have hmap : f.ker.map B.subtype = C := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : π (x : Y) = 1 := hx
        exact (hC_mem _).2 ⟨x.2, (hπker _).1 hx'⟩
      · intro hy
        obtain ⟨hyB, hyM⟩ := (hC_mem y).1 hy
        exact ⟨⟨y, hyB⟩, (hπker y).2 hyM, rfl⟩
    have h3 : Nat.card f.ker = Nat.card ↥C := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective Subtype.val_injective).symm
    rw [h1, h2, h3, mul_comm]
  let E0 : Subgroup Y := K ⊓ A.comap π
  have hE0K : E0 ≤ K := inf_le_left
  have hE0N : E0 ≤ Subgroup.normalizer (T : Set Y) := by
    intro k hk
    obtain ⟨_, hkA⟩ := Subgroup.mem_inf.1 hk
    obtain ⟨b, hb⟩ := (hA_mem _).1 hkA
    have hm : (b : Y)⁻¹ * k ∈ Subgroup.centralizer (K : Set Y) := by
      rw [← hπker, map_mul, map_inv, hb, inv_mul_cancel]
    have hk' : k = (b : Y) * ((b : Y)⁻¹ * k) := by group
    rw [hk']
    exact Subgroup.mul_mem _ (hBT b.2) (hMnorm _ hm)
  have hAcomm : ∀ a1 ∈ A, ∀ a2 ∈ A, a1 * a2 = a2 * a1 := by
    intro a1 h1 a2 h2
    obtain ⟨b1, rfl⟩ := (hA_mem _).1 h1
    obtain ⟨b2, rfl⟩ := (hA_mem _).1 h2
    rw [← map_mul, ← map_mul, hBcomm _ b1.2 _ b2.2]
  have hAexp : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hA_mem _).1 ha
    rw [← map_pow, hBexp _ b.2, map_one]
  have hE0comm : ∀ x ∈ E0, ∀ y ∈ E0, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxK, hxA⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hyK, hyA⟩ := Subgroup.mem_inf.1 hy
    have hcomm := hAcomm _ hxA _ hyA
    have hzK : x * y * (y * x)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hxK hyK) (K.inv_mem (K.mul_mem hyK hxK))
    have hzM : x * y * (y * x)⁻¹ ∈ Subgroup.centralizer (K : Set Y) := by
      rw [← hπker, map_mul, map_mul, map_inv, map_mul, hcomm, mul_inv_cancel]
    have hz : x * y * (y * x)⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set Y) :=
      Subgroup.mem_inf.2 ⟨hzK, hzM⟩
    rw [hKM, Subgroup.mem_bot, mul_inv_eq_one] at hz
    exact hz
  have hE0exp : ∀ x ∈ E0, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨hxK, hxA⟩ := Subgroup.mem_inf.1 hx
    have h3K : x ^ 3 ∈ K := K.pow_mem hxK 3
    have h3M : x ^ 3 ∈ Subgroup.centralizer (K : Set Y) := by
      rw [← hπker, map_pow]
      exact hAexp _ hxA
    have h : x ^ 3 ∈ K ⊓ Subgroup.centralizer (K : Set Y) := Subgroup.mem_inf.2 ⟨h3K, h3M⟩
    rw [hKM, Subgroup.mem_bot] at h
    exact h
  have hE0ea : IsElemAbelian 3 E0 := ⟨isMulCommutative_of_forall E0 hE0comm, hE0exp⟩
  have hgE0 : Function.Injective (π.comp E0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    have hxM : (x : Y) ∈ Subgroup.centralizer (K : Set Y) := (hπker _).1 hx1
    have hxK : (x : Y) ∈ K := (Subgroup.mem_inf.1 x.2).1
    have h : (x : Y) ∈ K ⊓ Subgroup.centralizer (K : Set Y) := Subgroup.mem_inf.2 ⟨hxK, hxM⟩
    rw [hKM, Subgroup.mem_bot] at h
    exact Subtype.ext h
  have hE0le3 : Nat.card ↥E0 ≤ 3 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hE0ea)
    have hn2 : 2 ≤ n := by
      by_contra h2
      push Not at h2
      rw [hn] at hgt
      interval_cases n <;> norm_num at hgt
    let E0K : Subgroup ↥K := E0.subgroupOf K
    have hE0K' : Nat.card ↥E0K = Nat.card ↥E0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0K).toEquiv
    have hdvd : 3 ^ 2 ∣ Nat.card ↥E0K := by
      rw [hE0K', hn]
      exact pow_dvd_pow 3 hn2
    obtain ⟨H9, hH9⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    have hE0Kcomm : ∀ x ∈ E0K, ∀ y ∈ E0K, x * y = y * x := by
      intro x hx y hy
      apply Subtype.ext
      exact hE0comm x.1 (Subgroup.mem_subgroupOf.1 hx) y.1 (Subgroup.mem_subgroupOf.1 hy)
    have hE0Kexp : ∀ x ∈ E0K, x ^ 3 = 1 := by
      intro x hx
      apply Subtype.ext
      exact hE0exp x.1 (Subgroup.mem_subgroupOf.1 hx)
    let E9K : Subgroup ↥K := H9.map E0K.subtype
    have hE9card : Nat.card ↥E9K = 9 := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective, hH9]
      norm_num
    have hE9ea : IsElemAbelian 3 E9K :=
      isElemAbelian_map_of_forall E0K.subtype Subtype.val_injective
        (fun x _ y _ => Subtype.ext (hE0Kcomm x.1 x.2 y.1 y.2))
        (fun x _ => Subtype.ext (hE0Kexp x.1 x.2))
    let W : Subgroup ↥K := T.subgroupOf K
    have hW_card : Nat.card ↥W = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
    have hW3 : ¬ 3 ∣ Nat.card ↥W := by
      rw [hW_card]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
      rw [hk]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this
    have hEW : E9K ≤ Subgroup.normalizer (W : Set ↥K) := by
      intro x hx
      obtain ⟨h, _, rfl⟩ := Subgroup.mem_map.1 hx
      have hyE0 : ((E0K.subtype h : ↥K) : Y) ∈ E0 := Subgroup.mem_subgroupOf.1 h.2
      have hyN := hE0N hyE0
      rw [Subgroup.mem_set_normalizer_iff] at hyN ⊢
      intro n
      have := hyN (n : Y)
      simpa [W, Subgroup.mem_subgroupOf] using this
    have hWbot := hK3 E9K W hE9ea hE9card hW3 hEW
    apply hTne
    have h1 : Nat.card ↥W = 1 := by rw [hWbot]; exact Subgroup.card_bot
    rw [hW_card] at h1
    exact Subgroup.card_eq_one.1 h1
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (↥K) with hI
  have hIA_sub : I ⊓ A ≤ (π.comp E0.subtype).range := by
    intro z hz
    obtain ⟨hzI, hzA⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hzI
    have hπk : π (k : Y) = MulAut.conj k := hπK k.1 k.2
    have hkE0 : (k : Y) ∈ E0 := Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_comap.2 (by rw [hπk]; exact hzA)⟩
    exact MonoidHom.mem_range.2 ⟨⟨k.1, hkE0⟩, hπk⟩
  have hrange : Nat.card ↥((π.comp E0.subtype).range) = Nat.card ↥E0 :=
    (Nat.card_congr (MonoidHom.ofInjective hgE0).toEquiv).symm
  have hIA_card : Nat.card ↥(I ⊓ A) ≤ 3 :=
    le_trans (Subgroup.card_le_of_le hIA_sub) (by rw [hrange]; exact hE0le3)
  have hAle9 : Nat.card ↥A ≤ 9 := by
    have hle : A ≤ Subgroup.normalizer (I : Set (MulAut ↥K)) := by
      rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : I.Normal)]
      exact le_top
    have hmul := card_sup_mul_card_inf_of_le_normalizer hle
    rw [hInnCard] at hmul
    have hsup : Nat.card ↥(I ⊔ A) ≤ 3 * Nat.card ↥K := by
      have h := Subgroup.card_le_card_group (H := I ⊔ A)
      rw [hMAK] at h
      exact h
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    have key : Nat.card ↥K * Nat.card ↥A ≤ Nat.card ↥K * 9 := by
      calc Nat.card ↥K * Nat.card ↥A = Nat.card ↥(I ⊔ A) * Nat.card ↥(I ⊓ A) := hmul.symm
        _ ≤ (3 * Nat.card ↥K) * 3 := Nat.mul_le_mul hsup hIA_card
        _ = Nat.card ↥K * 9 := by ring
    exact Nat.le_of_mul_le_mul_left key hKpos
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hC26 : Nat.card ↥C < 27 := by simpa [C] using hcB
  have hB81' : 81 ≤ Nat.card ↥B := hB81
  have hA4 : 4 ≤ Nat.card ↥A := by
    by_contra h
    push Not at h
    have h1 : Nat.card ↥C * Nat.card ↥A ≤ 26 * 3 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : Nat.card ↥B = Nat.card ↥C * Nat.card ↥A := hBC
    omega
  have hAea : IsElemAbelian 3 A := ⟨isMulCommutative_of_forall A hAcomm, hAexp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hAea)
  have hA9 : Nat.card ↥A = 9 := by
    have hn2 : n ≤ 2 := by
      by_contra h
      push Not at h
      have h3 : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
      rw [← hn] at h3
      omega
    rw [hn] at hA4 hAle9 ⊢
    interval_cases n <;> simp_all
  have hAnotI : ∃ α ∈ A, α ∉ I := by
    by_contra h
    push Not at h
    have hAI : A ≤ I := fun a ha => h a ha
    have hinf : I ⊓ A = A := inf_eq_right.2 hAI
    have h9 := hIA_card
    rw [hinf, hA9] at h9
    norm_num at h9
  obtain ⟨α0, hα0A, hα0I⟩ := hAnotI
  let e : MulAut ↥K ≃* MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.congr eK
  let D : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)) := A.map e.toMonoidHom
  have hDea : IsElemAbelian 3 D := isElemAbelian_map_of_forall e.toMonoidHom e.injective hAcomm hAexp
  have hDcard : Nat.card ↥D = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hA9]
  have hmapI := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr eK
  have hDnot : ¬ D ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (↥K ⧸ Subgroup.center ↥K) := by
    intro hD
    apply hα0I
    have hD' : A.map e.toMonoidHom ≤ I.map e.toMonoidHom := by
      rw [hmapI]
      exact hD
    exact (Subgroup.map_le_map_iff_of_injective e.injective).1 hD' hα0A
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) := hfinS
  obtain ⟨α', hα'D, hα'I, F', hF'ea, hF'card, hF'fix⟩ :=
    hR (↥K ⧸ Subgroup.center ↥K) hc D hDea hDcard hDnot
  obtain ⟨α, hαA, rfl⟩ := Subgroup.mem_map.1 hα'D
  have hαI : α ∉ I := by
    intro h
    apply hα'I
    have hmem : e α ∈ I.map e.toMonoidHom := Subgroup.mem_map.2 ⟨α, h, rfl⟩
    rw [hmapI] at hmem
    exact hmem
  haveI : IsMulCommutative F' := hF'ea.1
  let F : Subgroup ↥K := F'.map eK.symm.toMonoidHom
  have hF'comm : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := fun x hx y hy =>
    comm_mem_of_isMulCommutative F' hx hy
  have hFea : IsElemAbelian 3 F :=
    isElemAbelian_map_of_forall _ eK.symm.injective hF'comm hF'ea.2
  have hFcard : Nat.card ↥F = 9 := by
    rw [Subgroup.card_map_of_injective eK.symm.injective, hF'card]
  have hFfix : ∀ x ∈ F, α x = x := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    have h2 : eK (α (eK.symm x')) = x' := hF'fix x' hx'
    have h3 := congrArg eK.symm h2
    simpa using h3
  obtain ⟨b0, hb0⟩ := (hA_mem α).1 hαA
  have htB : (b0 : Y) ∈ B := b0.2
  have ht3 : (b0 : Y) ^ 3 = 1 := hBexp _ b0.2
  have htπ : π (b0 : Y) = α := hb0
  have htne : (b0 : Y) ≠ 1 := by
    intro h
    apply hαI
    have h1 : α = 1 := by rw [← htπ, h, map_one]
    rw [h1]
    exact I.one_mem
  set t : Y := (b0 : Y) with ht
  have hcen : ∀ x ∈ F, t * (x : Y) = (x : Y) * t := by
    intro x hx
    have h1 : π t x = x := by rw [htπ]; exact hFfix x hx
    have h2 : t * (x : Y) * t⁻¹ = (x : Y) := congrArg Subtype.val h1
    calc t * (x : Y) = (t * (x : Y) * t⁻¹) * t := by group
      _ = (x : Y) * t := by rw [h2]
  let FY : Subgroup Y := F.map K.subtype
  have hFY_mem : ∀ y, y ∈ FY ↔ ∃ x ∈ F, (x : Y) = y := fun y => by
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hFYK : FY ≤ K := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := (hFY_mem y).1 hy
    exact x.2
  have hFYcomm : ∀ y1 ∈ FY, ∀ y2 ∈ FY, y1 * y2 = y2 * y1 := by
    intro y1 h1 y2 h2
    obtain ⟨x1, hx1, rfl⟩ := (hFY_mem _).1 h1
    obtain ⟨x2, hx2, rfl⟩ := (hFY_mem _).1 h2
    haveI : IsMulCommutative F := hFea.1
    exact congrArg Subtype.val (comm_mem_of_isMulCommutative F hx1 hx2)
  have hFYexp : ∀ y ∈ FY, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hFY_mem _).1 hy
    have h := hFea.2 x hx
    simpa using congrArg Subtype.val h
  have hFYC : ∀ f ∈ FY, ∀ c ∈ C, f * c = c * f := by
    intro f hf c hc
    have hcM := ((hC_mem c).1 hc).2
    exact (Subgroup.mem_centralizer_iff.1 hcM) f (hFYK hf)
  have hCcomm : ∀ c1 ∈ C, ∀ c2 ∈ C, c1 * c2 = c2 * c1 := fun c1 h1 c2 h2 =>
    hBcomm c1 ((hC_mem c1).1 h1).1 c2 ((hC_mem c2).1 h2).1
  have hCexp : ∀ c ∈ C, c ^ 3 = 1 := fun c hc => hBexp c ((hC_mem c).1 hc).1
  have hP1comm := comm_sup_forall hFYcomm hCcomm hFYC
  have hP1exp := pow3_sup_forall hFYexp hCexp hFYC
  have htFY : ∀ f ∈ FY, t * f = f * t := by
    intro f hf
    obtain ⟨x, hx, rfl⟩ := (hFY_mem _).1 hf
    exact hcen x hx
  have htC : ∀ c ∈ C, t * c = c * t := fun c hc => hBcomm t htB c ((hC_mem c).1 hc).1
  have htP1 : ∀ p ∈ FY ⊔ C, t * p = p * t := by
    intro p hp
    obtain ⟨f, hf, c, hc, rfl⟩ := mem_sup_exists_of_commute hFYC hp
    rw [← mul_assoc, htFY f hf, mul_assoc, htC c hc, ← mul_assoc]
  have hZcomm : ∀ z1 ∈ Subgroup.zpowers t, ∀ z2 ∈ Subgroup.zpowers t, z1 * z2 = z2 * z1 := by
    intro z1 h1 z2 h2
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 h1
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 h2
    exact (Commute.refl t).zpow_zpow a b
  have hZexp : ∀ z ∈ Subgroup.zpowers t, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht3, one_zpow]
  have hPZcomm : ∀ p ∈ FY ⊔ C, ∀ z ∈ Subgroup.zpowers t, p * z = z * p := by
    intro p hp z hz
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc' : Commute p t := (htP1 p hp).symm
    exact (hc'.zpow_right a).eq
  let P1 : Subgroup Y := FY ⊔ C
  let P2 : Subgroup Y := P1 ⊔ Subgroup.zpowers t
  have hP2comm : ∀ x ∈ P2, ∀ y ∈ P2, x * y = y * x := comm_sup_forall hP1comm hZcomm hPZcomm
  have hP2exp : ∀ x ∈ P2, x ^ 3 = 1 := pow3_sup_forall hP1exp hZexp hPZcomm
  have hP2ea : IsElemAbelian 3 P2 := ⟨isMulCommutative_of_forall P2 hP2comm, hP2exp⟩
  have hFYbot : FY ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyFY, hyC⟩ := Subgroup.mem_inf.1 hy
    have hyM := ((hC_mem y).1 hyC).2
    have h : y ∈ K ⊓ Subgroup.centralizer (K : Set Y) := Subgroup.mem_inf.2 ⟨hFYK hyFY, hyM⟩
    rw [hKM, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 h
  have hFYcard : Nat.card ↥FY = 9 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hFcard]
  have hCnorm : C ≤ Subgroup.normalizer (FY : Set Y) := by
    intro c hc
    apply mem_normalizer_of_comm
    intro f hf
    exact (hFYC f hf c hc).symm
  have hP1card : Nat.card ↥P1 = 9 * Nat.card ↥C := by
    have h := card_sup_mul_card_inf_of_le_normalizer hCnorm
    rw [hFYbot, Subgroup.card_bot, mul_one, hFYcard] at h
    exact h
  have hZcard : Nat.card ↥(Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht3 htne
  have hZnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (P1 : Set Y) := by
    intro z hz
    apply mem_normalizer_of_comm
    intro p hp
    exact (hPZcomm p hp z hz).symm
  have hP1Z : P1 ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP1, hxZ⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨f, hf, c, hc, hfc⟩ := mem_sup_exists_of_commute hFYC hxP1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hxZ
    have hπx : π x = α ^ j := by rw [← hj, map_zpow, htπ]
    have hπx' : π x = π f := by
      rw [← hfc, map_mul, (hπker c).2 ((hC_mem c).1 hc).2, mul_one]
    have hαj : α ^ j ∈ I := by
      rw [← hπx, hπx']
      exact hπinn f (hFYK hf)
    have h3 : α ^ (3 : ℤ) = 1 := by
      rw [zpow_ofNat]
      exact hAexp α hαA
    have hdvd : (3 : ℤ) ∣ j := by
      by_contra hnd
      have hr0 : j % 3 ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
      have hr1 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
      have hr2 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
      have hαpow : α ^ j = α ^ (j % 3) := by
        have hjd : j = j % 3 + 3 * (j / 3) := by omega
        conv_lhs => rw [hjd]
        rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
      rw [hαpow] at hαj
      have hcases : j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases hcases with h | h
      · rw [h, zpow_one] at hαj
        exact hαI hαj
      · rw [h] at hαj
        apply hαI
        have h4 : (α ^ (2 : ℤ)) ^ (2 : ℤ) = α := by
          rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, h3, mul_one, zpow_one]
        rw [← h4]
        exact I.zpow_mem hαj 2
    obtain ⟨q, hq⟩ := hdvd
    have ht3' : t ^ (3 : ℤ) = 1 := by
      rw [zpow_ofNat]
      exact ht3
    have hxone : x = 1 := by
      rw [← hj, hq, zpow_mul, ht3', one_zpow]
    exact Subgroup.mem_bot.2 hxone
  have hP2card : Nat.card ↥P2 = 27 * Nat.card ↥C := by
    have h := card_sup_mul_card_inf_of_le_normalizer hZnorm
    rw [hP1Z, Subgroup.card_bot, mul_one, hP1card, hZcard] at h
    rw [h]
    ring
  have hBcard : Nat.card ↥B = 9 * Nat.card ↥C := by
    rw [hBC, hA9, mul_comm]
  have hmax := hK.maxrank P2 le_top hP2ea
  omega

theorem kDescFam_td42_three_of_residual (hR : TD42OuterFix) : KDescFam 3 fTD42 := by
  intro _ _ Y _ _ K B hK hc hcB
  exact (td42_three_false hR hK hc hcB).elim

end Main

end CFSG.LocalAnalysis.GLTheoremA
