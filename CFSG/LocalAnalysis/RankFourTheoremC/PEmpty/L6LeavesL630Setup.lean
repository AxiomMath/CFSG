module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankD smallRankF smallRankCenter smallRankOmega
  Lemma628Concl Lemma629Concl)

variable {G : Type} [Group G] [Finite G]

theorem rankThreePrimeCore_le_self (p : ℕ) (H : Subgroup G) : rankThreePrimeCore p H ≤ H := by
  unfold rankThreePrimeCore relPPrimeCore
  exact sSup_le fun _ hN => hN.1

theorem pCoreOf_le_self (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H := by
  unfold pCoreOf
  exact Subgroup.map_subtype_le _

theorem le_pCoreOf {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hpN : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hsub : IsPGroup p (N.subgroupOf H) := hpN.comap_subtype
  have h1 : N.subgroupOf H ≤ CFSG.pCore p ↥H := le_sSup ⟨hN, hsub⟩
  have h2 : N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
  unfold pCoreOf
  calc N = (N.subgroupOf H).map H.subtype := h2
    _ ≤ _ := Subgroup.map_mono h1

theorem pCoreOf_subgroupOf_normal (p : ℕ) (H : Subgroup G) :
    ((pCoreOf p H).subgroupOf H).Normal := by
  unfold pCoreOf
  show (Subgroup.comap H.subtype ((CFSG.pCore p ↥H).map H.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

theorem pCoreOf_isPGroup (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) := by
  unfold pCoreOf
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

theorem rankThreePrimeCore_subgroupOf_normal {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    ((rankThreePrimeCore p C).subgroupOf C).Normal :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal hp C

theorem conj_mem_pCoreOf {q : ℕ} {C D : Subgroup G} (hDC : D ≤ C)
    (hD : (D.subgroupOf C).Normal) (hq : q.Prime) {g : G} (hg : g ∈ C) {k : G}
    (hk : k ∈ pCoreOf q D) : g * k * g⁻¹ ∈ pCoreOf q D := by
  haveI : Fact q.Prime := ⟨hq⟩
  set K : Subgroup G := pCoreOf q D with hKdef
  have hKD : K ≤ D := pCoreOf_le_self q D
  have hKn : (K.subgroupOf D).Normal := pCoreOf_subgroupOf_normal q D
  have hKp : IsPGroup q K := pCoreOf_isPGroup q D
  have hginvC : g⁻¹ ∈ C := C.inv_mem hg
  have hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro d hd
    have := hD.conj_mem (⟨d, hDC hd⟩ : ↥C) (Subgroup.mem_subgroupOf.mpr hd) (⟨g, hg⟩ : ↥C)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hginvD : ∀ d ∈ D, g⁻¹ * d * g ∈ D := by
    intro d hd
    have := hD.conj_mem (⟨d, hDC hd⟩ : ↥C) (Subgroup.mem_subgroupOf.mpr hd) (⟨g⁻¹, hginvC⟩ : ↥C)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  set N : Subgroup G := K.map (MulAut.conj g).toMonoidHom with hNdef
  have hND : N ≤ D := by
    rintro _ ⟨y, hy, rfl⟩
    exact hgD y (hKD hy)
  have hNn : (N.subgroupOf D).Normal := by
    refine ⟨fun n hn d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.mp hn
    have hd' : g⁻¹ * (d : G) * g ∈ D := hginvD (d : G) d.2
    have hyK : (⟨g⁻¹ * (d : G) * g, hd'⟩ : ↥D) * ⟨y, hKD hy⟩ *
        (⟨g⁻¹ * (d : G) * g, hd'⟩ : ↥D)⁻¹ ∈ K.subgroupOf D :=
      hKn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hy) _
    rw [Subgroup.mem_subgroupOf] at hyK
    have hn_eq : (n : G) = g * y * g⁻¹ := by
      rw [← hyn]
      rfl
    refine Subgroup.mem_map.mpr ⟨_, hyK, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hn_eq]
    group
  have hNp : IsPGroup q N := hKp.map (MulAut.conj g).toMonoidHom
  have hN_le : N ≤ pCoreOf q D := le_pCoreOf hND hNn hNp
  exact hN_le (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

theorem conj_mem_closure_of_gen {S : Set G} (g : G)
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) : ∀ a ∈ closure S, g * a * g⁻¹ ∈ closure S := by
  have hle : closure S ≤ (closure S).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro s hs
    exact h s hs
  intro a ha
  exact hle ha

theorem mem_normalizer_smallRankF {p f : ℕ} {x g : G} (hp : p.Prime) (hf : f.Prime)
    (hg : g ∈ centralizer ({x} : Set G)) :
    g ∈ normalizer ((smallRankF p f x : Subgroup G) : Set G) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := smallRankD p x with hD
  set K : Subgroup G := pCoreOf f D with hK
  have hDC : D ≤ C := rankThreePrimeCore_le_self p C
  have hDn : (D.subgroupOf C).Normal := rankThreePrimeCore_subgroupOf_normal hp C
  set S : Set G := {a : G | a ∈ smallRankCenter K ∧ a ^ f = 1} with hS
  have hFS : smallRankF p f x = closure S := rfl
  have hSgen : ∀ h ∈ C, ∀ s ∈ S, h * s * h⁻¹ ∈ closure S := by
    intro h hh s hs
    obtain ⟨hsZ, hsf⟩ := hs
    rw [smallRankCenter, Subgroup.mem_inf] at hsZ
    obtain ⟨hsK, hsC⟩ := hsZ
    have hhK : h⁻¹ ∈ C := C.inv_mem hh
    have hmem : h * s * h⁻¹ ∈ S := by
      refine ⟨?_, ?_⟩
      · rw [smallRankCenter, Subgroup.mem_inf]
        refine ⟨conj_mem_pCoreOf hDC hDn hf hh hsK, ?_⟩
        rw [mem_centralizer_iff]
        intro k hk
        have hk' : h⁻¹ * k * h ∈ K := by
          have := conj_mem_pCoreOf hDC hDn hf hhK hk
          simpa [mul_assoc] using this
        have hc : s * (h⁻¹ * k * h) = (h⁻¹ * k * h) * s :=
          (mem_centralizer_iff.mp hsC _ hk').symm
        calc k * (h * s * h⁻¹) = h * ((h⁻¹ * k * h) * s) * h⁻¹ := by group
          _ = h * (s * (h⁻¹ * k * h)) * h⁻¹ := by rw [hc]
          _ = h * s * h⁻¹ * k := by group
      · rw [conj_pow, hsf]
        simp
    exact subset_closure hmem
  have hfwd : ∀ h ∈ C, ∀ a ∈ smallRankF p f x, h * a * h⁻¹ ∈ smallRankF p f x := by
    intro h hh a ha
    rw [hFS] at ha ⊢
    exact conj_mem_closure_of_gen h (hSgen h hh) a ha
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact hfwd g hg a ha
  · intro ha
    have := hfwd g⁻¹ (C.inv_mem hg) _ ha
    simpa [mul_assoc] using this

theorem smallRankF_le_centralizer {p f : ℕ} {x : G} (hf : f.Prime) :
    smallRankF p f x ≤ centralizer ({x} : Set G) := by
  have hK : smallRankF p f x ≤ pCoreOf f (smallRankD p x) := by
    unfold smallRankF smallRankOmega
    rw [Subgroup.closure_le]
    intro a ha
    exact (inf_le_left : smallRankCenter (pCoreOf f (smallRankD p x)) ≤
      pCoreOf f (smallRankD p x)) ha.1
  have hDC : smallRankD p x ≤ centralizer ({x} : Set G) :=
    rankThreePrimeCore_le_self p (centralizer ({x} : Set G))
  exact hK.trans ((pCoreOf_le_self f _).trans hDC)

theorem le_fittingSubgroupOf_of_normal {H N : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hnil : Group.IsNilpotent N) :
    N ≤ fittingSubgroupOf H := by
  have h1 : Group.IsNilpotent (N.subgroupOf H) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ fittingSubgroup ↥H := le_sSup ⟨hN, h1⟩
  have h2 : N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
  unfold fittingSubgroupOf
  calc N = (N.subgroupOf H).map H.subtype := h2
    _ ≤ _ := Subgroup.map_mono hle

theorem smallRankF_inf_eq_bot {p f : ℕ} {x : G} {M : Subgroup G} (hf : f.Prime) (hf2 : f ≠ 2)
    (hfit : fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥) :
    smallRankF p f x ⊓ M = ⊥ := by
  haveI : Fact f.Prime := ⟨hf⟩
  set D : Subgroup G := smallRankD p x with hD
  set K : Subgroup G := pCoreOf f D with hK
  set O : Subgroup G := rankThreePrimeCore 2 D with hO
  have hKD : K ≤ D := pCoreOf_le_self f D
  have hKn : (K.subgroupOf D).Normal := pCoreOf_subgroupOf_normal f D
  have hKp : IsPGroup f K := pCoreOf_isPGroup f D
  have hOD : O ≤ D := rankThreePrimeCore_le_self 2 D
  have hcop : Nat.Coprime 2 (Nat.card K) := by
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hKp
    exact Nat.Coprime.coprime_dvd_right hn
      (Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hf).mpr (Ne.symm hf2)))
  have hKO : K ≤ O := le_sSup ⟨hKD, hKn, hcop⟩
  have hKOn : (K.subgroupOf O).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hh : (h : G) ∈ D := hOD h.2
    have := hKn.conj_mem (⟨(n : G), hOD n.2⟩ : ↥D)
      (Subgroup.mem_subgroupOf.mpr hn) (⟨(h : G), hh⟩ : ↥D)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hnil : Group.IsNilpotent K := hKp.isNilpotent
  have hKfit : K ≤ fittingSubgroupOf O := le_fittingSubgroupOf_of_normal hKO hKOn hnil
  have hFK : smallRankF p f x ≤ K := by
    unfold smallRankF smallRankOmega
    rw [Subgroup.closure_le]
    intro a ha
    exact (inf_le_left : smallRankCenter K ≤ K) ha.1
  exact eq_bot_iff.mpr ((inf_le_inf_right M (hFK.trans hKfit)).trans hfit.le)

theorem pRank_le_card {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ Nat.card G := by
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  intro k hk
  obtain ⟨E, _, _, hk'⟩ := hk
  have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  rw [hk'] at h1
  exact (Nat.lt_pow_self hp).le.trans h1

theorem odd_card_centralizer_of_rank {f : ℕ} (hf : f.Prime) {F : Subgroup G}
    (hFe : IsElemAbelian f F) (hFc : Nat.card F = f ^ 4) (hloc : rankThreeLocalRank f G ≤ 3) :
    Odd (Nat.card (centralizer (F : Set G))) := by
  classical
  by_contra hne
  have h2 : 2 ∣ Nat.card (centralizer (F : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne)
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set t : G := (t' : G) with htdef
  have ht : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe, ht']
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have htC : t ∈ centralizer (F : Set G) := t'.2
  have hFC : F ≤ centralizer ({t} : Set G) := by
    intro a ha
    have hc : a * t = t * a := (mem_centralizer_iff.mp htC) a ha
    exact mem_centralizer_singleton_iff.mpr hc
  have hFH : F ≤ normalizer ((zpowers t : Subgroup G) : Set G) :=
    hFC.trans (CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_singleton_le_normalizer_zpowers t)
  have hTwo : IsTwoLocal (normalizer ((zpowers t : Subgroup G) : Set G)) := by
    refine ⟨zpowers t, ?_, ?_, rfl⟩
    · exact zpowers_eq_bot.not.mpr ht1
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have hr : 4 ≤ CFSG.Open.pRank f (normalizer ((zpowers t : Subgroup G) : Set G)) :=
    CFSG.SectionRank.le_pRank hf.one_lt hFH hFe hFc
  have hBdd : BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank f H = k} :=
    ⟨Nat.card G, by rintro k ⟨H, -, rfl⟩; exact pRank_le_card hf.one_lt H⟩
  have h4 : 4 ≤ twoLocalPrimeRank f G :=
    hr.trans (le_csSup hBdd ⟨_, hTwo, rfl⟩)
  unfold rankThreeLocalRank at hloc
  omega

theorem eq_one_of_mem_smallRankF_comm {p f : ℕ} {x z : G} {M : Subgroup G}
    (hC : centralizer ({z} : Set G) ≤ M) (hFM : smallRankF p f x ⊓ M = ⊥)
    {a : G} (ha : a ∈ smallRankF p f x) (hz : a * z = z * a) : a = 1 := by
  have hmem : a ∈ smallRankF p f x ⊓ M :=
    ⟨ha, hC (mem_centralizer_singleton_iff.mpr hz)⟩
  rw [hFM] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem central_mem_normalizer_smallRankF {p f : ℕ} {P : Sylow p G} {x z : G} (hp : p.Prime)
    (hf : f.Prime) (hx : x ∈ (P : Subgroup G)) (hz : z ∈ centralizer ((P : Subgroup G) : Set G)) :
    z ∈ normalizer ((smallRankF p f x : Subgroup G) : Set G) := by
  apply mem_normalizer_smallRankF hp hf
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz x hx).symm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
