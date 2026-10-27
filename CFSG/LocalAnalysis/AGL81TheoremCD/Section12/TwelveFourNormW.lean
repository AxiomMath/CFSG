module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixOne
import CFSG.GroupTheory.CoprimeCovering
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.DResidualSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQSimpleQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ} {L : Subgroup G}

private theorem pCore_two_le_primeComplementCore_j15 {d : ℕ} (hdP : d.Prime) (hd2 : d ≠ 2)
    (Y : Subgroup G) :
    CFSG.pCore 2 ↥Y ≤
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d := by
  refine CFSG.RankThreeEvenClassification.Helpers.le_primeComplementCore d _ inferInstance ?_
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).exists_card_eq
  rw [hk]
  exact hdP.coprime_iff_not_dvd.mp
    (((Nat.coprime_primes hdP Nat.prime_two).mpr hd2).pow_right k)

private theorem mem_primeComplementCore_of_mem_pCoreOf_j15 {d : ℕ} (hdP : d.Prime)
    (hd2 : d ≠ 2) {Y : Subgroup G} {n : G} (hnY : n ∈ Y)
    (hn : n ∈ CFSG.Open.pCoreOf 2 Y) :
    (⟨n, hnY⟩ : ↥Y) ∈
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d :=
  pCore_two_le_primeComplementCore_j15 hdP hd2 Y
    ((mem_pCore_two_iff_mem_pCoreOf ⟨n, hnY⟩).mpr hn)

private theorem cover_centralizer_of_witness_j15 {Y O W : Subgroup G}
    (hOY : O ≤ Y) (hOnormal : (O.subgroupOf Y).Normal)
    (hWnorm : W ≤ Subgroup.normalizer (O : Set G))
    (hsolv : Group.IsSolvable ↥O) (hcop : Nat.Coprime (Nat.card O) (Nat.card W))
    (hcomm : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ O) :
    ∀ y ∈ Y, ∃ c ∈ Y ⊓ Subgroup.centralizer (W : Set G), y⁻¹ * c ∈ O := by
  intro y hy
  obtain ⟨c, hcY, hcW, hcy⟩ :=
    CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem
      (X := Y) (N := O) (R := W) hOY hOnormal hWnorm hsolv hcop hy
      (fun r hr => by simpa only [commutatorElement_def] using hcomm y hy r hr)
  refine ⟨c, ⟨hcY, ?_⟩, hcy⟩
  show c ∈ Subgroup.centralizer (W : Set G)
  rw [Subgroup.mem_centralizer_iff]
  exact fun h hh => (hcW h hh).symm

omit [Finite G] in
private lemma surjective_modPrimeComplement_inclusion_j15 {d : ℕ} {Y CW O : Subgroup G}
    (hCW : CW ≤ Y) (hOY : O ≤ Y)
    (hO : ∀ n (hn : n ∈ O), (⟨n, hOY hn⟩ : ↥Y) ∈
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d)
    (hcover : ∀ y ∈ Y, ∃ c ∈ CW, y⁻¹ * c ∈ O) :
    Function.Surjective ((QuotientGroup.mk'
      (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d)).comp
        (Subgroup.inclusion hCW)) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d) x
  obtain ⟨c, hcCW, hcy⟩ := hcover (y : G) y.2
  refine ⟨⟨c, hcCW⟩, ?_⟩
  have hmk : QuotientGroup.mk'
      (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d) y =
      QuotientGroup.mk'
        (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d)
          ⟨c, hCW hcCW⟩ := by
    simp only [QuotientGroup.mk'_apply]
    refine QuotientGroup.eq.mpr ?_
    have heq : y⁻¹ * ⟨c, hCW hcCW⟩ = (⟨y⁻¹ * c, hOY hcy⟩ : ↥Y) := by
      ext
      rfl
    rw [heq]
    exact hO (y⁻¹ * c) hcy
  simpa [MonoidHom.comp_apply, Subgroup.inclusion,
    QuotientGroup.mk'_apply] using hmk.symm

private theorem dvd_card_modPrimeComplement_j15 {d : ℕ} {Y : Subgroup G} (hdP : d.Prime)
    (hYgen : oPPrimeHull d Y = Y) (hYne : Y ≠ ⊥) :
    d ∣ Nat.card (modPrimeComplement d Y) := by
  have : Fact d.Prime := ⟨hdP⟩
  have hdY : d ∣ Nat.card Y :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.dvd_card_of_oPPrimeHull_of_ne_bot
      hYgen hYne
  have hdecomp := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d)
  have hprod : d ∣ Nat.card (modPrimeComplement d Y) * Nat.card
      (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d) := by
    rw [← hdecomp]
    exact hdY
  rcases hdP.dvd_mul.mp hprod with h | h
  · exact h
  · exfalso
    exact (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore_properties
      (↥Y) d hdP).2 h

omit [Finite G] in
private lemma ne_bot_of_isSimpleGroup_modPrimeComplement_j15 {d : ℕ} {Y : Subgroup G}
    [IsSimpleGroup (modPrimeComplement d Y)] : Y ≠ ⊥ := by
  intro hbot
  let N : Subgroup ↥Y :=
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d
  have : Subsingleton ↥Y := by
    rw [hbot]
    infer_instance
  have : Subsingleton (↥Y ⧸ N) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
      exact congrArg (QuotientGroup.mk' N) (Subsingleton.elim x y)⟩
  exact (not_subsingleton (↥Y ⧸ N)) inferInstance

private theorem simple_quotient_data_j15 {d : ℕ} (hdP : d.Prime)
    (hD : TwelveThreeData M p H d) :
    IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) ∧
      oPPrimeHull d (oPPrimeHull d (H ⊓ M)) = oPPrimeHull d (H ⊓ M) ∧
      oPPrimeHull d (H ⊓ M) ≠ ⊥ ∧
      d ∣ Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) ∧
      ¬ IsMulCommutative (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := by
  have : IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := hD.common.y_simple
  have hYgen : oPPrimeHull d (oPPrimeHull d (H ⊓ M)) = oPPrimeHull d (H ⊓ M) :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.oPPrimeHull_oPPrimeHull d (H ⊓ M)
  have hYne : oPPrimeHull d (H ⊓ M) ≠ ⊥ :=
    ne_bot_of_isSimpleGroup_modPrimeComplement_j15 (d := d)
      (Y := oPPrimeHull d (H ⊓ M))
  refine ⟨hD.common.y_simple, hYgen, hYne,
    dvd_card_modPrimeComplement_j15 hdP hYgen hYne, ?_⟩
  rintro ⟨hcomm⟩
  exact hD.common.y_nonsolvable (Group.isSolvable_of_comm hcomm.comm)

private theorem not_isPSolvable_of_simple_quot_j15 {d : ℕ} (hdP : d.Prime)
    {Y CW C O : Subgroup G} (hCW : CW ≤ Y) (hOY : O ≤ Y) (hCWleC : CW ≤ C)
    (hcover : ∀ y ∈ Y, ∃ c ∈ CW, y⁻¹ * c ∈ O)
    (hOker : ∀ n (hn : n ∈ O), (⟨n, hOY hn⟩ : ↥Y) ∈
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d)
    [IsSimpleGroup (modPrimeComplement d Y)]
    (hdvd : d ∣ Nat.card (modPrimeComplement d Y))
    (hnab : ¬ IsMulCommutative (modPrimeComplement d Y)) :
    ¬ CFSG.HallHigman.IsPSolvable d ↥C := by
  have : Fact d.Prime := ⟨hdP⟩
  let φ : ↥CW →* modPrimeComplement d Y :=
    (QuotientGroup.mk' (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore
      (G := ↥Y) d)).comp (Subgroup.inclusion hCW)
  have hφsurj : Function.Surjective φ := by
    simpa only [φ] using surjective_modPrimeComplement_inclusion_j15 hCW hOY hOker hcover
  intro hps
  have hpsCW : CFSG.HallHigman.IsPSolvable d ↥CW :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hps hCWleC
  exact CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.SimpleQuot.false_of_isPSolvable_of_surjective
    hpsCW φ hφsurj inferInstance hnab hdvd

theorem not_isPSolvable_inf_centralizer_of_twelveFourWitness (hd : d ∈ sigmaSet G M)
    (hD : TwelveThreeData M p H d) {W : Subgroup G} (hW : TwelveFourWitness M p H d W) :
    ¬ CFSG.HallHigman.IsPSolvable d ↥(M ⊓ centralizer (W : Set G)) := by
  classical
  have hdP : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have : Fact d.Prime := ⟨hdP⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup G := oPPrimeHull d (H ⊓ M)
  let O : Subgroup G := CFSG.Open.pCoreOf 2 Y
  let C : Subgroup G := M ⊓ centralizer (W : Set G)
  let CW : Subgroup G := Y ⊓ centralizer (W : Set G)
  have hXH : xSub p M H ≤ H := Subgroup.map_subtype_le _
  have hWHM : W ≤ H ⊓ M := by
    intro x hx
    exact ⟨hXH (hW.2.1 hx), hD.common.xSub_le_M (hW.2.1 hx)⟩
  have hYnorm : (Y.subgroupOf (H ⊓ M)).Normal :=
    oPPrimeHull_subgroupOf_normal d le_rfl (by simp [Subgroup.subgroupOf_self])
  have hYnormH : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oPPrimeHull_le d (H ⊓ M))).mp hYnorm
  have hWnormO : W ≤ Subgroup.normalizer (O : Set G) :=
    (hWHM.trans hYnormH).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hOpg : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  obtain ⟨k, hk⟩ := hOpg.exists_card_eq
  have hcop : Nat.Coprime (Nat.card O) (Nat.card W) := by
    rw [hk, hW.1]
    exact ((Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by norm_num)).pow_left k
  have hsolvO : Group.IsSolvable ↥O := by
    have : Group.IsNilpotent ↥O := IsPGroup.isNilpotent hOpg
    exact IsNilpotent.to_isSolvable
  have hOnormal : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hcomm : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ O := hW.2.2.1
  have hcover : ∀ y ∈ Y, ∃ c ∈ CW, y⁻¹ * c ∈ O :=
    cover_centralizer_of_witness_j15 (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) hOnormal
      hWnormO hsolvO hcop hcomm
  obtain ⟨hYsimple, -, hYne, hdvd, hnab⟩ := simple_quotient_data_j15 hdP hD
  have : IsSimpleGroup (modPrimeComplement d Y) := hYsimple
  have hCWleC : CW ≤ C := by
    intro x hx
    exact ⟨(inf_le_right : H ⊓ M ≤ M) ((oPPrimeHull_le d (H ⊓ M)) hx.1), hx.2⟩
  have hOker : ∀ n (hn : n ∈ O), (⟨n, CFSG.LieType.BorelTits.pCoreOf_le 2 Y hn⟩ : ↥Y) ∈
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d :=
    fun n hn => mem_primeComplementCore_of_mem_pCoreOf_j15 hdP hd2
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y hn) hn
  exact not_isPSolvable_of_simple_quot_j15 hdP (show CW ≤ Y from inf_le_left)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) hCWleC hcover hOker hdvd hnab

theorem normalizer_le_of_twelveFourWitness (hO812 : Section15.O812sixGen)
    (h : TwelveCtx G M p Q H) (hd : d ∈ sigmaSet G M) (hD : TwelveThreeData M p H d)
    (hA : TwelveFourStepA M d) (hL : L ∈ weakBlockSet M H) {W : Subgroup G}
    (hW : TwelveFourWitness M p H d W) : normalizer (W : Set G) ≤ M := by
  have hWM : W ≤ M := hW.2.1.trans hD.common.xSub_le_M
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h3 := hW.1
    rw [hbot, Subgroup.card_bot] at h3
    omega
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW.1]; norm_num)
  have hsolv : Group.IsSolvable (MulAut ↥W) := by
    have : Group.IsSolvable (Equiv.Perm ↥W) :=
      Equiv.Perm.isSolvable (by rw [hW.1]; norm_num)
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm (M := ↥W))
      (fun _ _ hab => MulEquiv.toEquiv_injective hab)
  have hs := forall_isStronglyPEmbedded_of_mem_weakBlockSet h hL
  have hO := hO812 G h.cstar M h.maxLocal h.sigma_nonempty hs
  exact hO d hd hA.2.2 W hWM hW3 hWne hsolv hW.2.2.2
    (not_isPSolvable_inf_centralizer_of_twelveFourWitness hd hD hW)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
