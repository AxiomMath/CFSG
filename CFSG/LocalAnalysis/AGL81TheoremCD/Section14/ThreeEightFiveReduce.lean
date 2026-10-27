module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.GroupTheory.Fitting.SimpleNormal
import CFSG.GroupTheory.PrimeOrderSubgroups
import CFSG.GroupTheory.CentralizerSup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115QuotientMembership

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem NineFourListGroup.of_mulEquiv {p : ℕ} {Y Z : Type*} [Group Y] [Group Z]
    (h : NineFourListGroup p Y) (e : Y ≃* Z) : NineFourListGroup p Z := by
  obtain ⟨hsimple, i, hi, ⟨f⟩⟩ := h
  exact ⟨(MulEquiv.isSimpleGroup_congr e).mp hsimple, i, hi, ⟨e.symm.trans f⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive

open CFSG

theorem inf_pPrimeCore_eq_bot_of_isSimpleGroup {q : ℕ} (hq : q.Prime)
    {X : Type*} [Group X] [Finite X] {K : Subgroup X} (hKnormal : K.Normal)
    (hKsimple : IsSimpleGroup ↥K) (hqK : q ∣ Nat.card ↥K) :
    K ⊓ CFSG.pPrimeCore q X = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : K.Normal := hKnormal
  let O : Subgroup X := CFSG.pPrimeCore q X
  haveI : O.Normal := CFSG.pPrimeCore_normal
  have hKOn : (K ⊓ O).Normal := Subgroup.normal_inf_normal K O
  have hsub : ((K ⊓ O).subgroupOf K).Normal := Subgroup.normal_subgroupOf
  rcases hKsimple.eq_bot_or_eq_top_of_normal ((K ⊓ O).subgroupOf K) with h | h
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ O).subgroupOf K := hx
    rw [h] at hx'
    exact congrArg Subtype.val hx'
  · exfalso
    have hKOle : K ≤ O :=
      ((Subgroup.subgroupOf_eq_top (H := K ⊓ O) (K := K)).mp h).trans inf_le_right
    have hqO : q ∣ Nat.card O := hqK.trans (Subgroup.card_dvd_of_le hKOle)
    exact absurd hqO ((Nat.Prime.coprime_iff_not_dvd hq).mp
      (CFSG.pPrimeCore_coprime_card (p := q) (G := X)))

theorem map_ne_bot_of_inf_eq_bot {X : Type*} [Group X] {O K : Subgroup X} [O.Normal]
    (hKO : K ⊓ O = ⊥) (hK : K ≠ ⊥) : K.map (QuotientGroup.mk' O) ≠ ⊥ := by
  intro hbot
  have hleker : K ≤ (QuotientGroup.mk' O).ker := (Subgroup.map_eq_bot_iff K).mp hbot
  have hleO : K ≤ O := by simpa [QuotientGroup.ker_mk' O] using hleker
  have hKbot : K = ⊥ := le_bot_iff.mp (hKO ▸ le_inf le_rfl hleO)
  exact hK hKbot

theorem map_le_generalizedFitting_of_isSimpleGroup {X : Type*} [Group X] [Finite X]
    {O K : Subgroup X} [O.Normal] [K.Normal] (hKO : K ⊓ O = ⊥)
    (hKsimple : IsSimpleGroup ↥K) :
    K.map (QuotientGroup.mk' O) ≤ CFSG.generalizedFitting (X ⧸ O) := by
  have hOK : O ⊓ K = ⊥ := by rwa [inf_comm] at hKO
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.nonempty_mulEquiv_map_mk_of_inf_eq_bot O hOK
  have hKbar_simple : IsSimpleGroup ↥(K.map (QuotientGroup.mk' O)) :=
    (MulEquiv.isSimpleGroup_congr e).mp hKsimple
  have hKbar_norm : (K.map (QuotientGroup.mk' O)).Normal :=
    (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective O)
  have hKbar_ne_bot : K.map (QuotientGroup.mk' O) ≠ ⊥ :=
    map_ne_bot_of_inf_eq_bot hKO ((Subgroup.nontrivial_iff_ne_bot K).mp hKsimple.toNontrivial)
  apply CFSG.LocalCores.le_generalizedFitting_of_minimal hKbar_norm hKbar_ne_bot
  intro M hMn hMle
  haveI : M.Normal := hMn
  haveI : (M.subgroupOf (K.map (QuotientGroup.mk' O))).Normal := Subgroup.normal_subgroupOf
  rcases hKbar_simple.eq_bot_or_eq_top_of_normal (M.subgroupOf (K.map (QuotientGroup.mk' O)))
    with h | h
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    have hm' : (⟨m, hMle hm⟩ : ↥(K.map (QuotientGroup.mk' O))) ∈
        M.subgroupOf (K.map (QuotientGroup.mk' O)) := hm
    rw [h] at hm'
    exact congrArg Subtype.val hm'
  · right
    exact le_antisymm hMle
      ((Subgroup.subgroupOf_eq_top (H := M) (K := K.map (QuotientGroup.mk' O))).mp h)

theorem generalizedFitting_quotient_eq_map {q : ℕ} (hq : q.Prime)
    {X : Type} [Group X] [Finite X] {O K : Subgroup X} [O.Normal] [K.Normal]
    (hKO : K ⊓ O = ⊥) (hKsimple : IsSimpleGroup ↥K)
    (hO : CFSG.pPrimeCore q (X ⧸ O) = ⊥)
    {N : Subgroup (X ⧸ O)} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded q N) :
    CFSG.generalizedFitting (X ⧸ O) = K.map (QuotientGroup.mk' O) := by
  have hKbar_norm : (K.map (QuotientGroup.mk' O)).Normal :=
    (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective O)
  have hKbar_ne_bot : K.map (QuotientGroup.mk' O) ≠ ⊥ :=
    map_ne_bot_of_inf_eq_bot hKO ((Subgroup.nontrivial_iff_ne_bot K).mp hKsimple.toNontrivial)
  have hKbar_le := map_le_generalizedFitting_of_isSimpleGroup hKO hKsimple
  have hFdata := CFSG.RankThree.PartOne.Sec1511.spe_fstar hq hO hN
  haveI : (CFSG.generalizedFitting (X ⧸ O)).Normal := hFdata.2.2.1
  exact le_antisymm
    (CFSG.GroupTheory.generalizedFitting_le_of_normal hFdata.1 hKbar_norm hKbar_ne_bot)
    hKbar_le

theorem generalizedFitting_quotient_data {q : ℕ} (hq : q.Prime)
    {X : Type} [Group X] [Finite X] {O K : Subgroup X} [O.Normal] [K.Normal]
    (hKO : K ⊓ O = ⊥) (hKsimple : IsSimpleGroup ↥K)
    (hO : CFSG.pPrimeCore q (X ⧸ O) = ⊥)
    {N : Subgroup (X ⧸ O)} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded q N)
    (hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q ↥K) :
    CFSG.generalizedFitting (X ⧸ O) = K.map (QuotientGroup.mk' O) ∧
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
        ↥(CFSG.generalizedFitting (X ⧸ O)) := by
  have hF := generalizedFitting_quotient_eq_map hq hKO hKsimple hO hN
  refine ⟨hF, ?_⟩
  rw [hF]
  have hOK : O ⊓ K = ⊥ := by rwa [inf_comm] at hKO
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.nonempty_mulEquiv_map_mk_of_inf_eq_bot O hOK
  exact hlist.of_mulEquiv e

theorem quotient_pPrimeCore_data {q : ℕ} (hq : q.Prime) {X : Type} [Group X] [Finite X]
    {X₁ : Subgroup X} (hX₁ : CFSG.RankThree.PartOne.IsStronglyPEmbedded q X₁)
    (hrank : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup X)) :
    ¬ q ∣ Nat.card (CFSG.pPrimeCore q X) ∧
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore q X)) ∧
      CFSG.RankThree.PartOne.IsStronglyPEmbedded q
        (X₁.map (QuotientGroup.mk' (CFSG.pPrimeCore q X))) ∧
      CFSG.pPrimeCore q (X ⧸ CFSG.pPrimeCore q X) = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (CFSG.pPrimeCore q X).Normal := CFSG.pPrimeCore_normal
  have hqO : ¬ q ∣ Nat.card (CFSG.pPrimeCore q X) :=
    (Nat.Prime.coprime_iff_not_dvd hq).mp CFSG.pPrimeCore_coprime_card
  have hOle : CFSG.pPrimeCore q X ≤ X₁ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.pPrimeCore_le_of_stronglyPEmbedded hX₁ hrank
  refine ⟨hqO, ?_, ?_, CFSG.pPrimeCore_quotient_eq_bot hq⟩
  · rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore q X) hqO]
    exact hrank
  · exact hX₁.map_quotient (N := CFSG.pPrimeCore q X) hOle hqO

theorem exists_orderOf_prime_mem_inf_centralizer {X : Type*} [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) {X₁ D : Subgroup X}
    (hdvd : q ∣ Nat.card ↥(X₁ ⊓ Subgroup.centralizer (D : Set X))) :
    ∃ x : X, x ∈ X₁ ∧ x ∈ Subgroup.centralizer (D : Set X) ∧ orderOf x = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hxord⟩ :=
    exists_prime_orderOf_dvd_card' q (G := ↥(X₁ ⊓ Subgroup.centralizer (D : Set X))) hdvd
  exact ⟨x, x.2.1, x.2.2, (Subgroup.orderOf_coe x).trans hxord⟩

theorem le_of_centralizer_of_isStronglyPEmbedded {q : ℕ} (hq : q.Prime)
    {X : Type*} [Group X] {X₁ D : Subgroup X} {x : X}
    (hX₁ : CFSG.RankThree.PartOne.IsStronglyPEmbedded q X₁) (hxX₁ : x ∈ X₁)
    (hxord : orderOf x = q) (hxD : x ∈ Subgroup.centralizer (D : Set X)) :
    D ≤ X₁ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact hq.ne_one hxord.symm
  have hxq : x ^ q = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxord] at h
  have hDleCz : D ≤ Subgroup.centralizer (Subgroup.zpowers x : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr hxD
  rw [CFSG.centralizer_zpowers_eq_centralizer_singleton] at hDleCz
  exact hDleCz.trans (hX₁.centralizer_le hx1 hxq hxX₁)

theorem centralizes_zpowers_of_mem_of_inf_eq_bot {X : Type*} [Group X] {K O : Subgroup X}
    [K.Normal] [O.Normal] (hKO : K ⊓ O = ⊥) {y : X} (hyO : y ∈ O) :
    K ≤ Subgroup.centralizer (Subgroup.zpowers y : Set X) := by
  rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (CFSG.LocalCores.commute_of_normal_of_inf_eq_bot hKO hk hyO).eq

theorem commute_of_map_commute {X : Type*} [Group X] {K O : Subgroup X}
    [hK : K.Normal] [O.Normal] (hKO : K ⊓ O = ⊥) {c y : X} (hcK : c ∈ K)
    (hcomm : QuotientGroup.mk' O c * QuotientGroup.mk' O y =
      QuotientGroup.mk' O y * QuotientGroup.mk' O c) :
    c * y = y * c := by
  have hO : (c * y)⁻¹ * (y * c) ∈ O := QuotientGroup.eq.mp (by simpa using hcomm)
  have hK' : (c * y)⁻¹ * (y * c) ∈ K := by
    simpa [mul_assoc] using K.mul_mem (hK.conj_mem _ (K.inv_mem hcK) y⁻¹) hcK
  have h1 : (c * y)⁻¹ * (y * c) ∈ (⊥ : Subgroup X) := by
    rw [← hKO]
    exact Subgroup.mem_inf.mpr ⟨hK', hO⟩
  exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp h1)

theorem not_le_of_zpowers_mem {X : Type*} [Group X] {K O D X₁ : Subgroup X}
    [K.Normal] [O.Normal] (hKO : K ⊓ O = ⊥) {y : X} (hyO : y ∈ O)
    (hDzp : D = Subgroup.zpowers y) (hKnot : ¬ K ≤ X₁)
    (hle : K ⊓ Subgroup.centralizer (D : Set X) ≤ X₁) : False := by
  have hKleCD : K ≤ Subgroup.centralizer (D : Set X) := by
    rw [hDzp]
    exact centralizes_zpowers_of_mem_of_inf_eq_bot hKO hyO
  have hKeq : K ⊓ Subgroup.centralizer (D : Set X) = K := inf_eq_left.mpr hKleCD
  exact hKnot (by simpa [hKeq] using hle)

theorem map_orderOf_eq_prime_and_isPGroup {q : ℕ} (hq : q.Prime)
    {X : Type} [Group X] {O : Subgroup X} [O.Normal]
    (hqO : ¬ q ∣ Nat.card O) {x : X} (hxord : orderOf x = q) :
    orderOf (QuotientGroup.mk' O x) = q ∧
      IsPGroup q (Subgroup.zpowers (QuotientGroup.mk' O x)) := by
  have hxO : x ∉ O := fun hxO => hqO (hxord ▸ Subgroup.orderOf_dvd_natCard O hxO)
  have hord : orderOf (QuotientGroup.mk' O x) = q :=
    CFSG.BenderSuzuki.lemma115_orderOf_quotient_eq_prime_of_not_mem O hq hxord hxO
  refine ⟨hord, CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one ?_⟩
  rw [← hord, pow_orderOf_eq_one]

theorem exists_commuting_mem_map_not_mem_of_kic {q : ℕ} (hq : q.Prime)
    {X : Type} [Group X] [Finite X] {O K X₁ D : Subgroup X} [O.Normal] [K.Normal]
    (hKO : K ⊓ O = ⊥) (hqO : ¬ q ∣ Nat.card O)
    (hF : CFSG.generalizedFitting (X ⧸ O) = K.map (QuotientGroup.mk' O))
    (hX₁ : CFSG.RankThree.PartOne.IsStronglyPEmbedded q X₁)
    (hKIC : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizerHasPElementOutside q
      (X₁.map (QuotientGroup.mk' O)))
    {x y : X} {d : ℕ} (hxX₁ : x ∈ X₁) (hxC : x ∈ Subgroup.centralizer (D : Set X))
    (hxord : orderOf x = q) (hyord : orderOf y = d) (hyO : y ∉ O)
    (hd : d.Prime) (hd2 : d ≠ 2) (hdq : d ≠ q) (hDzp : D = Subgroup.zpowers y) :
    ∃ c : X, c ∈ K ∧ c ∉ X₁ ∧ c * y = y * c := by
  obtain ⟨hπx, hπxP⟩ := map_orderOf_eq_prime_and_isPGroup hq hqO hxord
  have hπx1 : QuotientGroup.mk' O x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hπx
    exact hq.ne_one hπx.symm
  have hπy : orderOf (QuotientGroup.mk' O y) = d :=
    CFSG.BenderSuzuki.lemma115_orderOf_quotient_eq_prime_of_not_mem O hd hyord hyO
  have hyD : y ∈ D := hDzp.symm ▸ Subgroup.mem_zpowers y
  have hDleX₁ : D ≤ X₁ := le_of_centralizer_of_isStronglyPEmbedded hq hX₁ hxX₁ hxord hxC
  have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hxC) y hyD
  have hcomm : QuotientGroup.mk' O x * QuotientGroup.mk' O y =
      QuotientGroup.mk' O y * QuotientGroup.mk' O x := by
    rw [← map_mul, ← map_mul, hxy.symm]
  obtain ⟨cbar, hcbarF, hcbar_comm, -, hcbar_not⟩ :=
    hKIC (QuotientGroup.mk' O x) (QuotientGroup.mk' O y)
      (Subgroup.mem_map_of_mem _ hxX₁) (Subgroup.mem_map_of_mem _ (hDleX₁ hyD))
      hπx1 hπxP (by rw [hπy]; exact hd) (by rw [hπy]; exact hd2)
      (by rw [hπy]; exact hdq) hcomm
  have hcbarK : cbar ∈ K.map (QuotientGroup.mk' O) := by rwa [hF] at hcbarF
  obtain ⟨c, hcK, hccbar⟩ := Subgroup.mem_map.mp hcbarK
  have hcnot : c ∉ X₁ := by
    intro hcX₁
    exact hcbar_not (hccbar ▸ Subgroup.mem_map_of_mem _ hcX₁)
  have hcomm_im : QuotientGroup.mk' O c * QuotientGroup.mk' O y =
      QuotientGroup.mk' O y * QuotientGroup.mk' O c := by
    rw [hccbar]
    exact hcbar_comm
  exact ⟨c, hcK, hcnot, commute_of_map_commute hKO hcK hcomm_im⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive

theorem kFactThreeEightFive_of_centralizerHasPElementOutside
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ (Y : Type) [Group Y],
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q Y → q ∣ Nat.card Y)
    (hkic : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
      CFSG.pPrimeCore q X = ⊥ → 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup X) →
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q ↥(CFSG.generalizedFitting X) →
      ∀ N : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded q N →
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizerHasPElementOutside q N) :
    KFactThreeEightFive := by
  classical
  intro q hq hq2 X _ _ K hKnorm hlist hrank X₁ hX₁ D hD hqDvd hle
  haveI : Fact q.Prime := ⟨hq⟩
  have hqK : q ∣ Nat.card ↥K := hdvd q hq hq2 ↥K hlist
  haveI : K.Normal := hKnorm
  have hKsimple : IsSimpleGroup ↥K := hlist.1
  let O : Subgroup X := CFSG.pPrimeCore q X
  haveI : O.Normal := CFSG.pPrimeCore_normal
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  have hKO : K ⊓ O = ⊥ := inf_pPrimeCore_eq_bot_of_isSimpleGroup hq hKnorm hKsimple hqK
  have hKnot : ¬ K ≤ X₁ := fun hKle => hX₁.not_dvd_card_of_normal_le hKle hqK
  obtain ⟨hqO, hrankbar, hX₁bar, hOquot⟩ := quotient_pPrimeCore_data hq hX₁ hrank
  obtain ⟨hF, hlistF⟩ :=
    generalizedFitting_quotient_data hq hKO hKsimple hOquot hX₁bar hlist
  have hKIC : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizerHasPElementOutside q
      (X₁.map π) :=
    hkic q hq hq2 (X ⧸ O) hOquot hrankbar hlistF (X₁.map π) hX₁bar
  obtain ⟨d, hd, hd2, hdq, hDcard⟩ := hD
  obtain ⟨y, hyD, hyord, hDzp⟩ := CFSG.GroupTheory.exists_generator_of_card_prime hd hDcard
  obtain ⟨x, hxX₁, hxC, hxord⟩ := exists_orderOf_prime_mem_inf_centralizer hq hqDvd
  by_cases hyO : y ∈ O
  · exact not_le_of_zpowers_mem hKO hyO hDzp hKnot hle
  · obtain ⟨c, hcK, hcnot, hcy⟩ :=
      exists_commuting_mem_map_not_mem_of_kic hq hKO hqO hF hX₁ hKIC hxX₁ hxC hxord
        hyord hyO hd hd2 hdq hDzp
    have hcCD : c ∈ Subgroup.centralizer (D : Set X) := by
      rw [hDzp, CFSG.centralizer_zpowers_eq_centralizer_singleton]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcy
    exact hcnot (hle (Subgroup.mem_inf.mpr ⟨hcK, hcCD⟩))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
