module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenResidueDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenInputs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenReduce
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenK
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoA5Lift
import CFSG.HardMathSupport.Cooperstein.Proving.ConjBarM
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
import CFSG.Quasithin.Background.A1bTransvection
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe (hatOf)

variable {G : Type} [Group G] [Finite G]

variable (G) in
theorem agl81TenThirteenA10_of (hKF462 : KFactFourSixTwo) (hKFb : KFactBlockAFive)
    (h9 : AGL81NineCompetitorQ G) (hNX3 : D1NoXBlock3 G) : AGL81TenThirteenA10 G := by
  intro hS P M H Q K hd L hL I₀ hI₀ hI₀c heK f hf hker
  obtain ⟨eK⟩ := heK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hin := kFactInputs_of_cfg h9 hS hd
  haveI := hin.normal
  obtain ⟨R, E, hER, hE, hEc, hcore⟩ := hin.core
  have hLM : IsSubnormal L M := hL.subnormal
  have hI₀M : I₀ ≤ H ⊓ M := le_inf_of_cZero hLM hI₀
  have hI₀H : I₀ ≤ H := hI₀M.trans inf_le_left
  have hI₀Mle : I₀ ≤ M := hI₀M.trans inf_le_right
  have hI₀HL : I₀ ≤ H ⊓ L := hI₀.le
  have h98 : AGL81NineEightFour G := Hyp111.agl81NineEightFour_holds
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hX : ¬ InClassXBlock L := fun h =>
    hNX3 hS M L hT.maxTwoLocal_M hL.le hLM h
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 5) with hπ
  set σ : ↥I₀ →* H ⧸ primeComplementCore (G := H) 5 := π.comp (Subgroup.inclusion hI₀H) with hσ
  have hσrange : σ.range = (I₀.subgroupOf H).map π := by
    rw [hσ]
    exact CFSG.AGLEmbeddingD2.range_mk_comp_inclusion hI₀H
  have hσY : σ.range ≤ d1X0 5 M H := by
    rw [hσrange]
    exact map_mk_le_d1X0 hI₀M
  have hσsub : IsSubnormal σ.range (d1X0 5 M H) := by
    rw [hσrange]
    exact isSubnormal_map_mk_d1X0 (isSubnormal_inf_of_cZero hLM hI₀)
  have hSπ : ∀ s : ↥H, (s : G) ∈ pCoreOf 2 H → π s = 1 := by
    intro s hs
    obtain ⟨s', hs', hss'⟩ := Subgroup.mem_map.mp hs
    have hss : s' = s := Subtype.ext hss'
    rw [← hss, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine le_sSup (show CFSG.pCore 2 ↥H ∈ {N : Subgroup ↥H | N.Normal ∧
      (5 : ℕ).Coprime (Nat.card N)} from ⟨inferInstance, ?_⟩) hs'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hM2S : pCoreOf 2 M ≤ pCoreOf 2 H := hA.twoCore_le
  have hSmem : ∀ m : ↥M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M (pCoreOf 2 H ⊓ L) →
      (m : G) ∈ pCoreOf 2 H := by
    intro m hm
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hm
    have h1 : x⁻¹ * m ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥M), QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      have : (QuotientGroup.mk x : ↥M ⧸ CFSG.pCore 2 ↥M) = QuotientGroup.mk m := hxm
      rw [this, inv_mul_cancel]
    have h2 : ((x⁻¹ * m : ↥M) : G) ∈ pCoreOf 2 H := hM2S ⟨_, h1, rfl⟩
    have h3 : (x : G) ∈ pCoreOf 2 H := (Subgroup.mem_subgroupOf.mp hx).1
    have : (m : G) = (x : G) * ((x⁻¹ * m : ↥M) : G) := by simp
    rw [this]
    exact (pCoreOf 2 H).mul_mem h3 h2
  have hIX : ¬ I₀ ≤ d1PlusCore 5 H K := by
    intro h
    have htop : (d1PlusCore 5 H K).subgroupOf I₀ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_subgroupOf.mpr (h x.2)
    rw [htop] at hker
    obtain ⟨y, hy⟩ := hf ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩
    have h1 : f y = 1 := hker (Subgroup.mem_top y)
    rw [h1] at hy
    exact absurd (congrArg Subtype.val hy) (by decide)
  have hσC : ¬ σ.range ≤ centralizer (K : Set (H ⧸ primeComplementCore (G := H) 5)) := by
    intro h
    apply hIX
    rw [hσrange] at h
    exact (map_mk_le_centralizer_iff (K := K) hI₀H).mp h
  have hperf : commutator ↥I₀ = ⊤ :=
    ((CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq I₀).mpr
      hI₀c.perfect).commutator_eq_top
  have hJp : ⁅σ.range, σ.range⁆ = σ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def, hperf]
  set ψ : ↥I₀ →* ↥(barM I₀ I₀) :=
    CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub (le_rfl : I₀ ≤ I₀) with hψ
  have hψs : Function.Surjective ψ :=
    CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective (le_rfl : I₀ ≤ I₀)
  have hψk : IsPGroup 2 ψ.ker := by
    rw [hψ, CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub]
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp g.2)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) ⟨x, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hthis := congrArg (fun y => ((y : ↥I₀) : G)) (congrArg Subtype.val hk)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hthis ⊢
    rw [← hxg]
    exact hthis
  have hQ : CFSG.Open.IsQuasisimple ↥(barM I₀ I₀) := hI₀c.component.2.2
  have hirrI := TenFourteenTwo.joinIrreducible_of_isQuasisimple (q := 2) hperf ψ hψs hQ hψk
  have hJirr := TenFourteenTwo.joinIrreducible_map σ.rangeRestrict σ.rangeRestrict_surjective
    hirrI
  obtain ⟨T, hN, hF⟩ := AltTen.core_le_of_altTen eK hin.cent R hER hE hEc hcore
  obtain ⟨k, hkY, ⟨n, hkn⟩, hC1, hC2⟩ := AltTen.exists_swap_of_altTen eK hin.cent hd.not_le_X0
    T hN hF hσY hσsub hJp hσC hJirr
  obtain ⟨x, hxHM, hxk⟩ := Subgroup.mem_map.mp hkY
  have hxM : (x : G) ∈ M := (Subgroup.mem_subgroupOf.mp hxHM).2
  obtain ⟨b, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hkord : orderOf ((k : ↥K) : H ⧸ primeComplementCore (G := H) 5) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← Subgroup.coe_pow, hkn, Subgroup.coe_one])
  have hcop : r.Coprime (orderOf ((k : ↥K) : H ⧸ primeComplementCore (G := H) 5)) :=
    Nat.Coprime.coprime_dvd_right hkord (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hr))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  set tH : ↥H := (x ^ r) ^ m with htH
  have htk : π tH = ((k : ↥K) : H ⧸ primeComplementCore (G := H) 5) := by
    rw [htH, map_pow, map_pow, hxk, hm]
  set t : G := (tH : G) with ht
  have htHmem : t ∈ H := tH.2
  have htM : t ∈ M := by
    rw [ht, htH, Subgroup.coe_pow, Subgroup.coe_pow]
    exact M.pow_mem (M.pow_mem hxM r) m
  have ht2 : t ^ 2 ^ b = 1 := by
    rw [ht, htH, ← Subgroup.coe_pow, ← pow_mul, ← pow_mul,
      show r * (m * 2 ^ b) = 2 ^ b * r * m by ring, pow_mul, ← hord, pow_orderOf_eq_one,
      one_pow, Subgroup.coe_one]
  have htS : t ∈ normalizer (pCoreOf 2 H : Set G) := by rw [hNH]; exact htHmem
  have hI₀' : I₀ ∈ cZero (normalizer (pCoreOf 2 H : Set G) ⊓ L) := by rw [hNH]; exact hI₀
  obtain ⟨hpart1, hpart2⟩ := hKFb G M (pCoreOf 2 H) L I₀ hK hA hL hX hI₀' hI₀c ⟨f, hf⟩
  have hconjπ : ∀ i : ↥I₀, ∀ hi : t * (i : G) * t⁻¹ ∈ H,
      π ⟨t * (i : G) * t⁻¹, hi⟩ = ((k : ↥K) : H ⧸ primeComplementCore (G := H) 5) * σ i *
        ((k : ↥K) : H ⧸ primeComplementCore (G := H) 5)⁻¹ := by
    intro i hi
    rw [← htk]
    have : (⟨t * (i : G) * t⁻¹, hi⟩ : ↥H) = tH * Subgroup.inclusion hI₀H i * tH⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    rfl
  have hMloc : IsTwoLocal M := hT.maxTwoLocal_M.1
  have h3M := CFSG.Quasithin.A1b.pRank_le_evenRank Nat.prime_three (by norm_num) hMloc
  rw [hS.rank] at h3M
  have hO2I : pCoreOf 2 I₀ ≤ pCoreOf 2 H := by
    have h1 := CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2
      (isSubnormal_inf_of_cZero hLM hI₀)
    have h2 := hA.twoRadical.2.2
    rw [hNH, inf_comm] at h2
    exact h1.trans h2.symm.le
  have htL : t ∈ normalizer (L : Set G) := by
    by_contra hne
    have hne' : L.map (MulAut.conj t).toMonoidHom ≠ L := by
      intro h
      apply hne
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← h]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [← h] at hy
        obtain ⟨y', hy', hyy'⟩ := hy
        have : y' = y := by
          have h1 : t * y' * t⁻¹ = t * y * t⁻¹ := hyy'
          simpa using h1
        exact this ▸ hy'
    obtain ⟨ht2N, j, hjI, hinner⟩ := hpart2 h3M t htM htS ⟨b, ht2⟩ hne'
    apply hC2 (σ ⟨j, hjI⟩) ⟨⟨j, hjI⟩, rfl⟩
    rintro y ⟨i, rfl⟩
    have hg : t ^ 2 * (i : G) * (t ^ 2)⁻¹ * (j * (i : G) * j⁻¹)⁻¹ ∈ pCoreOf 2 H :=
      hO2I (hinner i i.2)
    set jH : ↥H := ⟨j, hI₀H hjI⟩
    set iH : ↥H := ⟨i, hI₀H i.2⟩
    have hgeq : ((tH ^ 2 * iH * (tH ^ 2)⁻¹ * (jH * iH * jH⁻¹)⁻¹ : ↥H) : G) =
        t ^ 2 * (i : G) * (t ^ 2)⁻¹ * (j * (i : G) * j⁻¹)⁻¹ := by
      simp [jH, iH, ht]
    have h4 := hSπ (tH ^ 2 * iH * (tH ^ 2)⁻¹ * (jH * iH * jH⁻¹)⁻¹) (hgeq ▸ hg)
    simp only [map_mul, map_inv, map_pow] at h4
    rw [← htk]
    exact mul_inv_eq_one.mp h4
  rcases hpart1 with h2 | hnorm
  swap
  ·
    have htI := hnorm t htM htS htL
    apply hC1
    rintro y ⟨i, rfl⟩
    have hti : t * (i : G) * t⁻¹ ∈ I₀ := (mem_normalizer_iff.mp htI (i : G)).mp i.2
    rw [← hconjπ i (hI₀H hti)]
    exact ⟨⟨_, hti⟩, rfl⟩
  obtain ⟨hcl, hpar, hO2⟩ := h2
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  rw [hNS] at hpar hO2
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπM
  set Pb := barM M (H ⊓ L) with hPb
  set Jb := barM M I₀ with hJb
  set tb : ↥M ⧸ CFSG.pCore 2 ↥M := πM ⟨t, htM⟩ with htb
  have hO2P : pCoreOf 2 Pb = barM M (pCoreOf 2 H ⊓ L) := hO2.symm
  have htransfer : ∀ g : ↥M, ∀ hgH : (g : G) ∈ H, πM g ∈ pCoreOf 2 Pb →
      π ⟨g, hgH⟩ = 1 := by
    intro g hgH hg
    rw [hO2P] at hg
    exact hSπ ⟨g, hgH⟩ (hSmem g hg)
  have hmemJb : ∀ i : ↥I₀, πM ⟨i, hI₀Mle i.2⟩ ∈ Jb := fun i =>
    ⟨⟨i, hI₀Mle i.2⟩, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  have hJP : Jb ≤ Pb := Subgroup.map_mono fun y hy => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hI₀HL hy
  have hO2L : pCoreOf 2 (barM M L) = ⊥ := by
    have h1 := CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2
      hL.component.2.1
    have h2 : pCoreOf 2 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
      have h3 := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := ↥M ⧸ CFSG.pCore 2 ↥M))
      rw [CFSG.GH74.GLS.Stage2.Signalizer.pCore_quotient_pCore (A := ↥M) 2] at h3
      have h4 : CFSG.pCore 2 ↥(⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h3
      rw [pCoreOf, h4, Subgroup.map_bot]
    exact eq_bot_iff.mpr (h1.trans h2.le)
  have hsubJ : IsSubnormal (hatOf Pb Jb) ⊤ := by
    have h1 : IsSubnormal (I₀.subgroupOf M) ((H ⊓ L).subgroupOf M) :=
      hI₀.subnormal.comap M.subtype
    have h2 := h1.map πM
    have h3 : IsSubnormal (Jb.subgroupOf Pb) (Pb.subgroupOf Pb) := h2.comap Pb.subtype
    rw [Subgroup.subgroupOf_self] at h3
    have h4 := h3.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb))
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h4
  set φ₀ : ↥I₀ →* ↥Pb := (πM.comp (Subgroup.inclusion hI₀Mle)).codRestrict Pb
    (fun i => hJP (hmemJb i)) with hφ₀
  set φ : ↥I₀ →* ↥(hatOf Pb Jb) := ((QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)).comp φ₀).codRestrict
    (hatOf Pb Jb) (fun i => ⟨φ₀ i, Subgroup.mem_subgroupOf.mpr (hmemJb i), rfl⟩) with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨w, hw⟩
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨m₀, hm₀, hm₀w⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hw₀)
    refine ⟨⟨m₀, Subgroup.mem_subgroupOf.mp hm₀⟩, Subtype.ext ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥Pb) (φ₀ _) = _
    congr 1
    exact Subtype.ext hm₀w
  have hφker : φ.ker ≤ f.ker := by
    intro i hi
    apply hker
    rw [← comap_centralizer_eq_subgroupOf (K := K) hI₀H, Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Pb) (φ₀ i) = 1 := congrArg Subtype.val hi
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : πM ⟨i, hI₀Mle i.2⟩ ∈ pCoreOf 2 Pb := ⟨φ₀ i, h1, rfl⟩
    have h3 := htransfer ⟨i, hI₀Mle i.2⟩ (hI₀H i.2) h2
    have h4 : σ i = 1 := h3
    rw [h4]
    exact Subgroup.one_mem _
  have hJA5 : ∃ f'' : ↥(hatOf Pb Jb) →* alternatingGroup (Fin 5), Function.Surjective f'' := by
    refine ⟨(MonoidHom.liftOfSurjective φ hφs) ⟨f, hφker⟩, fun a => ?_⟩
    obtain ⟨y, rfl⟩ := hf a
    exact ⟨φ y, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  have htbL : tb ∈ normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_barM (z := ⟨t, htM⟩) htL
  have htHL : t ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 := mem_normalizer_iff.mp (le_normalizer htHmem : t ∈ normalizer (H : Set G)) y
    have h2 := mem_normalizer_iff.mp htL y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have htbP : tb ∈ normalizer (Pb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_barM (z := ⟨t, htM⟩) htHL
  have htb2 : ∃ k : ℕ, tb ^ 2 ^ k = 1 := ⟨b, by
    rw [htb, ← map_pow]
    have : (⟨t, htM⟩ : ↥M) ^ 2 ^ b = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]⟩
  have hne : hatOf Pb (Jb.map (MulAut.conj tb).toMonoidHom) ≠ hatOf Pb Jb := by
    intro heq
    apply hC1
    rintro y ⟨i, rfl⟩
    have hxbP : πM ⟨i, hI₀Mle i.2⟩ ∈ Pb := hJP (hmemJb i)
    have hcP : tb * πM ⟨i, hI₀Mle i.2⟩ * tb⁻¹ ∈ Pb :=
      (mem_normalizer_iff.mp htbP _).mp hxbP
    have hcJ : tb * πM ⟨i, hI₀Mle i.2⟩ * tb⁻¹ ∈ Jb.map (MulAut.conj tb).toMonoidHom :=
      ⟨_, hmemJb i, rfl⟩
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥Pb) ⟨_, hcP⟩ ∈
        hatOf Pb (Jb.map (MulAut.conj tb).toMonoidHom) :=
      ⟨⟨_, hcP⟩, Subgroup.mem_subgroupOf.mpr hcJ, rfl⟩
    rw [heq] at hmem
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨i', hi', hi'w⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hw)
    have hi'I : (i' : G) ∈ I₀ := Subgroup.mem_subgroupOf.mp hi'
    have h1 : w⁻¹ * ⟨_, hcP⟩ ∈ CFSG.pCore 2 ↥Pb := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Pb), QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      have : (QuotientGroup.mk w : ↥Pb ⧸ CFSG.pCore 2 ↥Pb) = QuotientGroup.mk ⟨_, hcP⟩ := hwe
      rw [this, inv_mul_cancel]
    set gM : ↥M := i'⁻¹ * (⟨t, htM⟩ * ⟨i, hI₀Mle i.2⟩ * (⟨t, htM⟩ : ↥M)⁻¹) with hgM
    have h2 : πM gM ∈ pCoreOf 2 Pb := by
      refine ⟨_, h1, ?_⟩
      rw [hgM, map_mul, map_inv, map_mul, map_mul, map_inv, hi'w]
      rfl
    set i'H : ↥H := ⟨i', hI₀H hi'I⟩
    set iH : ↥H := ⟨i, hI₀H i.2⟩
    have hgeq : (gM : G) = ((i'H⁻¹ * (tH * iH * tH⁻¹) : ↥H) : G) := by
      rw [hgM]
      simp [i'H, iH, ht]
    have h3 := htransfer gM (hgeq ▸ (i'H⁻¹ * (tH * iH * tH⁻¹)).2) h2
    have h4 : π (i'H⁻¹ * (tH * iH * tH⁻¹)) = 1 := by
      rw [← h3]
      exact congrArg π (Subtype.ext hgeq.symm)
    rw [map_mul, map_inv, map_mul, map_mul, map_inv] at h4
    rw [← htk]
    refine ⟨⟨i', hi'I⟩, ?_⟩
    exact inv_mul_eq_one.mp h4
  have hpR : Open.pRank 3 (barM M L) ≤ 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hker3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
      obtain ⟨k₀, hk₀⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
      rw [hk₀]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hdvd)
      omega
    calc Open.pRank 3 (barM M L)
        ≤ Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = Open.pRank 3 (⊤ : Subgroup ↥M) := CFSG.SectionRank.pRank_quotient_eq _ hker3
      _ = Open.pRank 3 M := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup M).symm
      _ ≤ 3 := h3M
  have hJO2 : CFSG.pCore 2 ↥(hatOf Pb Jb) = ⊥ := by
    have h1 := CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hsubJ
    have h2 : pCoreOf 2 (⊤ : Subgroup (↥Pb ⧸ CFSG.pCore 2 ↥Pb)) = ⊥ := by
      have h3 := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := ↥Pb ⧸ CFSG.pCore 2 ↥Pb))
      rw [CFSG.GH74.GLS.Stage2.Signalizer.pCore_quotient_pCore (A := ↥Pb) 2] at h3
      have h4 : CFSG.pCore 2 ↥(⊤ : Subgroup (↥Pb ⧸ CFSG.pCore 2 ↥Pb)) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h3
      rw [pCoreOf, h4, Subgroup.map_bot]
    have h5 : pCoreOf 2 (hatOf Pb Jb) = ⊥ := eq_bot_iff.mpr (h1.trans h2.le)
    rw [pCoreOf] at h5
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h5
  have hkerψφ : ψ.ker = φ.ker := by
    rw [hψ, CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hx
      have hx'' : x' = x := Subtype.ext hxx'
      have hmap : φ x ∈ (CFSG.pCore 2 ↥I₀).map φ := ⟨x, hx'' ▸ hx', rfl⟩
      have hle : (CFSG.pCore 2 ↥I₀).map φ ≤ CFSG.pCore 2 ↥(hatOf Pb Jb) :=
        le_sSup ⟨(CFSG.pCore_normal (G := ↥I₀) (p := 2)).map φ hφs,
          (CFSG.pCore_isPGroup (G := ↥I₀) (p := 2)).map φ⟩
      have := hle hmap
      rw [hJO2] at this
      exact this
    · intro x hx
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Pb) (φ₀ x) = 1 := congrArg Subtype.val hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 : πM ⟨x, hI₀Mle x.2⟩ ∈ pCoreOf 2 Pb := ⟨φ₀ x, h1, rfl⟩
      rw [hO2P] at h2
      have h3 : (x : G) ∈ pCoreOf 2 H := hSmem ⟨x, hI₀Mle x.2⟩ h2
      rw [Subgroup.mem_subgroupOf]
      have hN : ((pCoreOf 2 H).subgroupOf I₀).Normal := by
        refine ⟨fun a ha g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at ha ⊢
        have hgN : (g : G) ∈ normalizer (pCoreOf 2 H : Set G) := by
          rw [hNH]
          exact hI₀H g.2
        simpa using (mem_normalizer_iff.mp hgN (a : G)).mp ha
      have hP : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf I₀) := by
        intro a
        obtain ⟨h₀, hh₀, hh₀a⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp a.2)
        obtain ⟨k₀, hk₀⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥H) ⟨h₀, hh₀⟩
        refine ⟨k₀, Subtype.ext (Subtype.ext ?_)⟩
        have hthis := congrArg (fun z => ((z : ↥H) : G)) (congrArg Subtype.val hk₀)
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hthis ⊢
        rw [← hh₀a]
        exact hthis
      have hle : (pCoreOf 2 H).subgroupOf I₀ ≤ CFSG.pCore 2 ↥I₀ := le_sSup ⟨hN, hP⟩
      exact ⟨x, hle (Subgroup.mem_subgroupOf.mpr h3), rfl⟩
  have hJq : Open.IsQuasisimple ↥(hatOf Pb Jb) :=
    Open.IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkerψφ.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))) hQ
  obtain ⟨-, j, hjJ, hinner⟩ := hKF462 (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) Pb Jb tb
    hL.component.2.2 hO2L hcl hpar hpR hJP hsubJ hJq hJA5 htbL htbP htb2 hne
  obtain ⟨i₀, hi₀, hi₀j⟩ := Subgroup.mem_map.mp hjJ
  have hi₀I : (i₀ : G) ∈ I₀ := Subgroup.mem_subgroupOf.mp hi₀
  apply hC2 (σ ⟨i₀, hi₀I⟩) ⟨⟨i₀, hi₀I⟩, rfl⟩
  rintro y ⟨i, rfl⟩
  have h1 := hinner (πM ⟨i, hI₀Mle i.2⟩) (hmemJb i)
  set gM : ↥M := (⟨t, htM⟩ : ↥M) ^ 2 * ⟨i, hI₀Mle i.2⟩ * ((⟨t, htM⟩ : ↥M) ^ 2)⁻¹ *
    (i₀ * ⟨i, hI₀Mle i.2⟩ * i₀⁻¹)⁻¹ with hgM
  have h2 : πM gM ∈ pCoreOf 2 Pb := by
    have : πM gM = tb ^ 2 * πM ⟨i, hI₀Mle i.2⟩ * (tb ^ 2)⁻¹ *
        (j * πM ⟨i, hI₀Mle i.2⟩ * j⁻¹)⁻¹ := by
      rw [hgM, ← hi₀j]
      simp only [map_mul, map_inv, map_pow]
      rfl
    rw [this]
    exact h1
  set i₀H : ↥H := ⟨i₀, hI₀H hi₀I⟩
  set iH : ↥H := ⟨i, hI₀H i.2⟩
  have hgeq : (gM : G) = ((tH ^ 2 * iH * (tH ^ 2)⁻¹ * (i₀H * iH * i₀H⁻¹)⁻¹ : ↥H) : G) := by
    rw [hgM]
    simp [i₀H, iH, ht]
  have h3 := htransfer gM (hgeq ▸ (tH ^ 2 * iH * (tH ^ 2)⁻¹ * (i₀H * iH * i₀H⁻¹)⁻¹).2) h2
  have h4 : π (tH ^ 2 * iH * (tH ^ 2)⁻¹ * (i₀H * iH * i₀H⁻¹)⁻¹) = 1 := by
    rw [← h3]
    exact congrArg π (Subtype.ext hgeq.symm)
  simp only [map_mul, map_inv, map_pow] at h4
  rw [← htk]
  exact mul_inv_eq_one.mp h4

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
