module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Level
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_StructAct
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem level_four_quotient {p : ℕ} (hM : ListedMultiplierBound p)
    (hH : HatOddMultiplierBound) (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hZ : IsPGroup p (Subgroup.center Q)) (hlevel : fullCoverLevel p Q = 4) :
    ¬ IsChevSimple p (Q ⧸ Subgroup.center Q) ∧
      ¬ catalogIs (Q ⧸ Subgroup.center Q) (k2 p) ∧
      ¬ catalogIs (Q ⧸ Subgroup.center Q) (k3 p) := by
  have hk : kLevel p (Q ⧸ Subgroup.center Q) = 4 := by
    rw [← fullCoverLevel_eq_kLevel hM hH hp hp2 hQ hZ, hlevel]
  have h1 : ¬ IsChevSimple p (Q ⧸ Subgroup.center Q) := by
    intro h
    have hk' := hk
    unfold kLevel at hk'
    rw [if_pos h] at hk'
    omega
  have h2 : ¬ catalogIs (Q ⧸ Subgroup.center Q) (k2 p) := by
    intro h
    have hk' := hk
    unfold kLevel at hk'
    rw [if_neg h1, if_pos h] at hk'
    omega
  have h3 : ¬ catalogIs (Q ⧸ Subgroup.center Q) (k3 p) := by
    intro h
    have hk' := hk
    unfold kLevel at hk'
    rw [if_neg h1] at hk'
    by_cases h2' : catalogIs (Q ⧸ Subgroup.center Q) (k2 p)
    · rw [if_pos h2'] at hk'
      omega
    · rw [if_neg h2', if_pos h] at hk'
      omega
  exact ⟨h1, h2, h3⟩

theorem kd264_coreHyp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : ListedMultiplierBound p) (hH : HatOddMultiplierBound)
    {Y : Type} [Group Y] [Finite Y] {K B : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore p ↥K = ⊥)
    (hlevel : fullCoverLevel p ↥K = 4) (hB : IsElemAbelian p B)
    (hmax : IsMaxRankIn p B ⊤) (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    {m c : ℕ} (hm : Nat.card (kd264Rho hBN e).range = p ^ m)
    (hc2 : c ≤ 2) (hone : 1 ≤ c) (hfour : 4 ≤ m + c)
    (hLow : KD264LiftLow p) (hNoMult : KD264LiftNoMult p) (hField : KD264LiftField p)
    (hMRJ : KD264LiftMRJ p) :
    KD264CoreHyp p d (kd264Rho hBN e).range m c := by
  have hAel : IsElemAbelian p ((kd264Rho hBN e).range) := by
    have hT : IsElemAbelian p (⊤ : Subgroup ↥B) :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.isElemAbelian_top_of hB
    have hmap := CFSG.SectionRank.isElemAbelian_map hT (kd264Rho hBN e)
    rwa [← MonoidHom.range_eq_map] at hmap
  have hZ : IsPGroup p (Subgroup.center ↥K) :=
    isPGroup_center_of_pPrimeCore_eq_bot hp hcore
  have hnot := level_four_quotient hM hH hp hp2 hq hZ hlevel
  have hnotChev : ¬ IsChevSimple p (TauCeti.CFSGIndex.lie d).Group := by
    rintro (h | h)
    · exact hnot.1 (Or.inl ((catalogIs_congr e).2 h))
    · exact hnot.1 (Or.inr ((catalogIs_congr e).2 h))
  have hnotK2 : ¬ k2Lie p d.1 := by
    intro h2
    exact hnot.2.1 ((catalogIs_congr e).2 ⟨.lie d, h2, ⟨MulEquiv.refl _⟩⟩)
  have hnotK3 : ¬ (p = 3 ∧ k3Lie d.1) := by
    intro h3
    exact hnot.2.2 ((catalogIs_congr e).2 ⟨.lie d, h3, ⟨MulEquiv.refl _⟩⟩)
  have hpdvdK : p ∣ Nat.card ↥K := by
    by_contra hpdvd
    haveI hntQ : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hq.2.toNontrivial
    haveI hntK : Nontrivial ↥K :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
    have hcop : Nat.Coprime p (Nat.card ↥(⊤ : Subgroup ↥K)) := by
      rw [Subgroup.card_top, hp.coprime_iff_not_dvd]
      exact hpdvd
    have htopbot : (⊤ : Subgroup ↥K) = ⊥ :=
      (CFSG.pPrimeCore_eq_bot_iff (p := p) (G := ↥K)).1 hcore ⊤ inferInstance hcop
    have hsub : Subsingleton ↥K := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup ↥K) := by rw [← htopbot]; exact Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup ↥K) := by rw [← htopbot]; exact Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    exact not_subsingleton ↥K hsub
  have hdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.dvd_card_quotient_center_of_quasisimple
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 hq))
        hp hpdvdK
  have hchar : d.1.characteristic ≠ p :=
    characteristic_ne_of_not_isChevSimple d.2 ⟨MulEquiv.refl _⟩ hnotChev
  refine
    { prime := hp
      odd := hp2
      elem := hAel
      card := hm
      one_le_c := hone
      c_le_two := hc2
      four_le := hfour
      notChev := hnotChev
      notK2 := hnotK2
      notK3 := hnotK3
      dvd := hdvd
      low := fun k hk => hLow Y K B hBN d e m hq hB hmax hm k hk
      noMult := fun hnm =>
        hNoMult Y K B hBN d e m hq hcore hB hmax hm (fun h => hchar h.symm) hnm
      field := fun hp3 a ha haout k hk =>
        hField Y K B hBN d e m hq hB hmax hm hp3 a ha haout k hk
      mrj := fun β hβ hβ1 J hJ e' he' hlp =>
        hMRJ Y K B hBN d e m hq hB hmax hm β hβ hβ1 J hJ e' he' hlp }

theorem kd264_good_of_lift {p : ℕ} (hp : p.Prime)
    {Y : Type} [Group Y] [Finite Y] (hLB : LBalanceAt Y p) (hGood : KD264LiftGood p)
    {K B : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥K) (hKg : CFSG.Open.IsKGroup ↥K)
    (hKn : K.Normal) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    {S : Type} [Group S] [Finite S] (e : ↥K ⧸ Subgroup.center ↥K ≃* S)
    {c : ℕ} (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ c)
    {F : Subgroup (MulAut S)} (hFA : F ≤ (kd264Rho hBN e).range)
    (hFgood : IsGood p F) (hFcard : p ^ 3 ≤ Nat.card F * p ^ c) :
    ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
  classical
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hq.1
  set Ft : Subgroup Y := (F.comap (kd264Rho hBN e)).map B.subtype with hFt
  have hker : Nat.card (kd264Rho hBN e).ker =
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    rw [ker_kd264Rho hperf hBN]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := B ⊓ Subgroup.centralizer (K : Set Y))
        (K := B) inf_le_left).toEquiv
  have hcomp : Nat.card (F.comap (kd264Rho hBN e)) =
      Nat.card F * Nat.card (kd264Rho hBN e).ker := by
    have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker
      (kd264Rho hBN e) (F.comap (kd264Rho hBN e))
    rw [Subgroup.map_comap_eq_self hFA,
      inf_eq_right.mpr (Subgroup.ker_le_comap (f := kd264Rho hBN e) F)] at h
    exact h
  have hcard : Nat.card Ft = Nat.card F * p ^ c := by
    calc Nat.card Ft = Nat.card ((F.comap (kd264Rho hBN e)).map B.subtype) := by rw [hFt]
      _ = Nat.card (F.comap (kd264Rho hBN e)) :=
        Subgroup.card_map_of_injective B.subtype_injective
      _ = Nat.card F * Nat.card (kd264Rho hBN e).ker := hcomp
      _ = Nat.card F * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by rw [hker]
      _ = Nat.card F * p ^ c := by rw [hc]
  have hFtB : Ft ≤ B := by
    rw [hFt]
    exact Subgroup.map_subtype_le _
  have hcard3 : p ^ 3 ≤ Nat.card Ft := by
    rw [hcard]
    exact hFcard
  have hgood : GLAPLayer p (K ⊓ Subgroup.centralizer (Ft : Set Y)) ≠ ⊥ := by
    rw [hFt]
    exact hGood Y K B hBN S e F hFA hFgood
  exact (kd264_goal_of_good hp hLB hKg hKn hB hFtB hcard3 hgood).1

private theorem kd264_exc_of_lift {p : ℕ} {Y : Type} [Group Y]
    {K B : Subgroup Y} (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    (hcore : GLAPPrimeCore p ↥K = ⊥)
    {m c : ℕ} (hBpow : Nat.card B = p ^ (m + c))
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ c)
    (hp3 : p = 3) (htrial : isTrialityD4Big d.1) (hm3 : m = 3) (hc1 : c = 1)
    {a : MulAut (TauCeti.CFSGIndex.lie d).Group}
    (haA : a ∈ (kd264Rho hBN e).range)
    (haout : a ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :
    p = 3 ∧ Nat.card B = 3 ^ 4 ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
      catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧
      ∃ b ∈ B, ¬ InducesInnerMod 3 K b := by
  have hcore' : GLAPPrimeCore 3 ↥K = ⊥ := by
    rw [← hp3]
    exact hcore
  have hcoreOf : GLAPPrimeCoreOf 3 K = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hcore'
  refine ⟨hp3, ?_, ?_, ⟨.lie d, htrial, ⟨e⟩⟩, ?_⟩
  · rw [hBpow, hp3, hm3, hc1]
  · rw [hc, hp3, hc1]
    norm_num
  · obtain ⟨b, rfl⟩ := haA
    refine ⟨(b : Y), b.2, ?_⟩
    intro hinner
    obtain ⟨l, hl, hcongr⟩ := hinner
    have hconj : ∀ y ∈ K, (b : Y)⁻¹ * y * b =
        ((⟨l, hl⟩ : ↥K) : Y)⁻¹ * y * ((⟨l, hl⟩ : ↥K) : Y) := by
      intro y hy
      have hmem := hcongr y hy
      rw [hcoreOf, Subgroup.mem_bot] at hmem
      simpa using (inv_mul_eq_one.mp hmem).symm
    have hinner' : kd264Rho hBN e b ∈
        (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →*
          MulAut (TauCeti.CFSGIndex.lie d).Group).range :=
      kd264Rho_mem_range_conj hBN e b ⟨l, hl⟩ hconj
    exact haout (inner_le_innAutDerived _ hinner')

theorem kd264KLie_of_coreS {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLB : ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p)
    (hM : ListedMultiplierBound p) (hH : HatOddMultiplierBound)
    (hCore : KD264CoreS p) (hGood : KD264LiftGood p) (hLow : KD264LiftLow p)
    (hNoMult : KD264LiftNoMult p) (hField : KD264LiftField p) (hMRJ : KD264LiftMRJ p) :
    KD264KLie p := by
  intro Y _ _ K B hKn hq hKg hcat hcore hlevel hB _ hB4 hmax hCne
  classical
  haveI hKnormal : K.Normal := hKn
  have hBN : B ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hlie : ∃ d : TauCeti.ValidLieTypeIndex,
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    obtain ⟨i, hi, he⟩ := hcat
    cases i <;> first
      | exact ⟨_, he⟩
      | exact absurd hi (by simp [onLie])
  obtain ⟨d, ⟨e⟩⟩ := hlie
  haveI hFinS : Finite (TauCeti.CFSGIndex.lie d).Group :=
    Finite.of_equiv (↥K ⧸ Subgroup.center ↥K) e.toEquiv
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hq.1
  have hACB : Nat.card (kd264Rho hBN e).range *
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = Nat.card B :=
    card_range_kd264Rho_mul hperf hBN e
  have hAel : IsElemAbelian p ((kd264Rho hBN e).range) := by
    have hT : IsElemAbelian p (⊤ : Subgroup ↥B) :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.isElemAbelian_top_of hB
    have hmap := CFSG.SectionRank.isElemAbelian_map hT (kd264Rho hBN e)
    rwa [← MonoidHom.range_eq_map] at hmap
  have hCel : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set Y)) :=
    CFSG.Open.IsElemAbelian.mono hB inf_le_left
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hAel.isPGroup.exists_card_eq
  obtain ⟨c, hc⟩ := hCel.isPGroup.exists_card_eq
  have hBpow : Nat.card B = p ^ (m + c) := by
    rw [← hACB, hm, hc, ← pow_add]
  have hone : 1 ≤ c := by
    by_contra h
    have hc0 : c = 0 := by omega
    apply hCne
    rw [Subgroup.eq_bot_iff_card, hc, hc0]
    simp
  have hfour : 4 ≤ m + c := by
    refine (Nat.pow_le_pow_iff_right hp.one_lt).1 ?_
    rwa [← hBpow]
  by_cases hc2 : c ≤ 2
  · have hHyp : KD264CoreHyp p d (kd264Rho hBN e).range m c :=
      kd264_coreHyp hp hp2 hM hH hq hcore hlevel hB hmax hBN d e hm hc2 hone hfour
        hLow hNoMult hField hMRJ
    rcases hCore d (kd264Rho hBN e).range m c hHyp with
      ⟨F, hFA, hFgood, hFcard⟩ | ⟨hp3, htrial, hm3, hc1, a, haA, haout⟩
    · exact Or.inl
        (kd264_good_of_lift hp (hLB Y) hGood hq hKg hKn hB hBN e hc hFA hFgood hFcard)
    · exact Or.inr
        (kd264_exc_of_lift d e hBN hcore hBpow hc hp3 htrial hm3 hc1 haA haout)
  · have h3c : 3 ≤ c := by omega
    refine Or.inl (kd264_of_card_centralizer hp hq hcore hB ?_)
    rw [hc]
    exact Nat.pow_le_pow_right hp.pos h3c

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
