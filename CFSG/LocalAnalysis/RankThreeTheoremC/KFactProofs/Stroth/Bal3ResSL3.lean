module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResMaxClass
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3Model
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3Rep
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3Aux
import CFSG.RankThree.PartTwo.KFacts.KS12ClassSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped Pointwise

theorem bal3ThreeSL3_of_tables (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : Bal3ThreeSL3 := by
  classical
  have hZ : Bal3ThreeCenter := bal3ThreeCenter_of_tables hGA hAlt hSpor
  intro X _ _ hcat P z D hred hz K hK huniq hfam
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  haveI hKn : K.Normal :=
    Subgroup.Normal.of_conjugate_fixed (fun g => huniq _ (isComponentOf_conj_smul hK g))
  have hPn : (P : Subgroup X) ≤ normalizer (K : Set X) := by
    rw [normalizer_eq_top]; exact le_top
  have hzK : z ∈ K := hred.mem_component hK hPn
  have hzC : z ∈ centralizer (K : Set X) :=
    mem_centralizer_component_of_mem_pCore hp3 hred.core hz hK
  have hzc : ∀ k ∈ K, z * k = k * z := fun k hk => (mem_centralizer_iff.1 hzC k hk).symm
  have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hzc k k.2).symm
  have hZne : center K ≠ ⊥ := by
    intro hbot
    rw [hbot, mem_bot] at hzZ
    have hz1 : z = 1 := congrArg Subtype.val hzZ
    have := hred.ord
    rw [hz1, orderOf_one] at this
    exact hp3.one_lt.ne this
  have hZp : IsPGroup 3 (center K) := isPGroup_center_of_isComponentOf hp3 hred.core hK
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hK.2.2
  have hcatK : IsCatalogGroup (K ⧸ center K) :=
    hcat K (center K) inferInstance hK.2.2.2 hnonab
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    have hKX : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 hp3 K.subtype
        K.subtype_injective]
      exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3 le_top
    rw [hred.pRank_top] at hKX
    exact hKX
  obtain ⟨hcyc, hcard⟩ := hZ K hK.2.2 hcatK hZne hZp hrk
  have hq : CFSG.Open.IsQuasisimple K := hK.2.2
  have hZz : ∀ y ∈ K, (∀ k ∈ K, y * k = k * y) → y ∈ zpowers z :=
    mem_zpowers_of_center hzK hzc hred.ord hcard
  have hmodel : CFSG.RankThree.PartTwo.Sec4.IsSLThreePi K :=
    isSLThreePi_of_cover hGA hq hcard hfam
  have hrank2 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := pRank_le_two_of_isSLThreePi hmodel
  have hP81 : Nat.card (P : Subgroup X) = 81 :=
    bal3MaxClassEightyOne X (P : Subgroup X) z D P.isPGroup' hred.ord hred.central hred.unique
      hred.le hred.elem hred.card hred.mem
      (fun y hy hyC => hred.mem_of_mem_inf_centralizer hy hyC) hred.rank
  have hzP : z ∈ (P : Subgroup X) := hred.le hred.mem
  obtain ⟨B, hBP, hBe, hBc⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp3 (P : Subgroup X)
  rw [hred.rank] at hBc
  have hBK : ¬ B ≤ K := fun hBK => by
    have := three_le_pRank_of_le hBK hBe hBc
    omega
  have hzB : z ∈ B :=
    mem_elem_of_pRank hBP hBe hBc hred.rank hzP hred.ord
      (fun y hy => mem_centralizer_iff.1 hred.central y (hBP hy))
  set T : Subgroup X := (P : Subgroup X) ⊓ K with hTdef
  have hTP : T ≤ (P : Subgroup X) := inf_le_left
  have hTK : T ≤ K := inf_le_right
  have hTn : (P : Subgroup X) ≤ normalizer (T : Set X) :=
    (le_inf le_normalizer hPn).trans inf_normalizer_le_normalizer_inf
  have hTnc : ¬ ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro hall
    exact not_isMulCommutative_inf (by norm_num) P hK hPn
      (hred.dvd_card_center_component hz hK hPn) ⟨⟨fun a b => Subtype.ext (hall a a.2 b b.2)⟩⟩
  have hT27 : 27 ≤ Nat.card T := by
    have h := pow_three_le_card_of_not_commutative hp3 (P.isPGroup'.to_le hTP) hTnc
    norm_num at h
    exact h
  have hTdvd : Nat.card T ∣ 81 := hP81 ▸ Subgroup.card_dvd_of_le hTP
  have hTc : Nat.card T = 27 := by
    have hle : Nat.card T ≤ 81 := Nat.le_of_dvd (by norm_num) hTdvd
    have key : Nat.card T = 27 ∨ Nat.card T = 81 := by
      generalize Nat.card T = n at hT27 hle hTdvd ⊢
      interval_cases n <;> omega
    rcases key with h | h
    · exact h
    · exfalso
      have hTeq : T = (P : Subgroup X) := Subgroup.eq_of_le_of_card_ge hTP (by omega)
      exact hBK ((le_of_le_of_eq hBP hTeq.symm).trans hTK)
  have hTB9 : Nat.card (T ⊓ B : Subgroup X) = 9 := by
    have hge := nine_le_card_inf hP81 hTP hBP hTc hBc
    have hdvd : Nat.card (T ⊓ B : Subgroup X) ∣ 27 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ B ≤ B)
      rw [hBc] at h
      norm_num at h
      exact h
    have hne : Nat.card (T ⊓ B : Subgroup X) ≠ 27 := by
      intro h27
      have h : T ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      exact hBK ((le_of_eq h.symm).trans (inf_le_left.trans hTK))
    have hle27 : Nat.card (T ⊓ B : Subgroup X) ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (T ⊓ B : Subgroup X) = n at hdvd hne hle27 hge ⊢
    interval_cases n <;> omega
  obtain ⟨x, hxD, hxz⟩ := exists_mem_notMem_zpowers hp3 hred.ord hred.card
  have hxP : x ∈ (P : Subgroup X) := hred.le hxD
  have hx3 : x ^ 3 = 1 := hred.elem.2 x hxD
  have hzx : x * z = z * x := mem_centralizer_iff.1 hred.central x hxP
  have hDgen : ∀ d ∈ D, ∃ i j : ℤ, d = z ^ i * x ^ j := fun d hd =>
    exists_zpow_mul_zpow_of_card_eq_sq hp3 hred.elem hred.card hred.ord hred.mem hxD hxz hd
  have hCB : ∀ b ∈ B, x * b = b * x → b ∈ zpowers z := by
    intro b hb hxb
    have hbz : b * z = z * b := hBe.comm hb hzB
    have hbC : b ∈ centralizer (D : Set X) := by
      rw [mem_centralizer_iff]
      intro d hd
      obtain ⟨i, j, rfl⟩ := hDgen d hd
      have h1 : Commute (z ^ i * x ^ j) b :=
        (Commute.zpow_left (show Commute z b from hbz.symm) i).mul_left
          (Commute.zpow_left (show Commute x b from hxb) j)
      exact h1.eq
    have hbD : b ∈ D := hred.mem_of_mem_inf_centralizer (hBP hb) hbC
    by_contra hbz'
    have hDB : D ≤ B := by
      intro d hd
      obtain ⟨i, j, rfl⟩ :=
        exists_zpow_mul_zpow_of_card_eq_sq hp3 hred.elem hred.card hred.ord hred.mem hbD hbz' hd
      exact B.mul_mem (B.zpow_mem hzB i) (B.zpow_mem hb j)
    have hBD : B ≤ D := by
      intro b' hb'
      refine hred.mem_of_mem_inf_centralizer (hBP hb') ?_
      rw [mem_centralizer_iff]
      intro d hd
      exact hBe.comm (hDB hd) hb'
    have := Subgroup.card_le_of_le hBD
    rw [hBc, hred.card] at this
    norm_num at this
  by_cases hxT : x ∈ T
  ·
    have hxK : x ∈ K := hTK hxT
    have hDK : D ≤ K := by
      intro d hd
      obtain ⟨i, j, rfl⟩ := hDgen d hd
      exact K.mul_mem (K.zpow_mem hzK i) (K.zpow_mem hxK j)
    have hzT : z ∈ T := ⟨hzP, hzK⟩
    have hTBK : T ⊓ B ≤ K := inf_le_left.trans hTK
    have hD'e : IsElemAbelian 3 (D.subgroupOf K) :=
      IsElemAbelian.comap hred.elem K.subtype_injective
    have hD'c : Nat.card (D.subgroupOf K) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hred.card]
      norm_num
    have hE'e : IsElemAbelian 3 ((T ⊓ B).subgroupOf K) :=
      IsElemAbelian.comap (⟨⟨⟨fun a b => Subtype.ext (hBe.comm a.2.2 b.2.2)⟩⟩, fun y hy =>
        hBe.2 y hy.2⟩ : IsElemAbelian 3 (T ⊓ B)) K.subtype_injective
    have hE'c : Nat.card ((T ⊓ B).subgroupOf K) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTBK).toEquiv]
      exact hTB9
    have hcenZ : ∀ c : K, c ∈ center K → (c : X) ∈ zpowers z := fun c hc =>
      hZz c c.2 (fun k hk => (congrArg Subtype.val (mem_center_iff.1 hc ⟨k, hk⟩)).symm)
    have hZD' : center K ≤ D.subgroupOf K := fun c hc =>
      Subgroup.mem_subgroupOf.2 (Subgroup.zpowers_le.2 hred.mem (hcenZ c hc))
    have hZE' : center K ≤ (T ⊓ B).subgroupOf K := fun c hc =>
      Subgroup.mem_subgroupOf.2
        (Subgroup.zpowers_le.2 (show z ∈ T ⊓ B from ⟨hzT, hzB⟩) (hcenZ c hc))
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.ks12ClassSL K hmodel (D.subgroupOf K)
      ((T ⊓ B).subgroupOf K) hD'e hD'c hZD' hE'e hE'c hZE'
    refine false_of_conj_plane hred.sylow (by rw [hred.card]; norm_num) hBe hBc (g := (g : X)) ?_
    intro d hd
    have hmem : (MulAut.conj g) ⟨d, hDK hd⟩ ∈ (T ⊓ B).subgroupOf K := by
      rw [hg]
      exact ⟨⟨d, hDK hd⟩, hd, rfl⟩
    have h2 : (g : X) * d * (g : X)⁻¹ ∈ T ⊓ B := hmem
    exact h2.2
  ·
    obtain ⟨t, htT, ht3, htz⟩ :=
      exists_pow_three_ne_one hP81 hBP hBe hBc hTP hTn hTc hTB9 hxP hxT hx3 hzB hred.ord hzx hCB
    obtain ⟨Q, hQ⟩ := (isSylowOf_inf_of_le_normalizer P hPn).exists_sylow_eq_subgroupOf
    have hQc : Nat.card (Q : Subgroup K) = 27 := by
      rw [hQ, ← hTc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
    have htK : t ∈ K := hTK htT
    have htQ : (⟨t, htK⟩ : K) ∈ (Q : Subgroup K) := by
      rw [hQ]
      exact Subgroup.mem_subgroupOf.2 htT
    have ht3c : (⟨t, htK⟩ : K) ^ 3 ∈ center K := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 htz
      have h1 : (⟨t, htK⟩ : K) ^ 3 = (⟨z, hzK⟩ : K) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      rw [h1]
      exact Subgroup.zpow_mem _ hzZ k
    have h243 : ¬ 243 ∣ Nat.card K := by
      intro h
      have hfac : Nat.card (Q : Subgroup K) = 3 ^ (Nat.card K).factorization 3 :=
        Sylow.card_eq_multiplicity Q
      have h5 : 5 ≤ (Nat.card K).factorization 3 :=
        (hp3.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by norm_num; exact h)
      have h6 : 3 ^ 5 ≤ 3 ^ (Nat.card K).factorization 3 :=
        Nat.pow_le_pow_right (by norm_num) h5
      rw [← hfac, hQc] at h6
      norm_num at h6
    have h1 := pow_three_eq_one_of_not_dvd_243 hmodel h243 ht3c
    exact ht3 (by simpa using congrArg Subtype.val h1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
