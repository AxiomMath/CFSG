module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wResDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDerive
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yChar
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySylow
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wConjTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wSylowX
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wBurnside
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr630e_not_two_dvd_card_centralizer {f : ℕ} (hfp : f.Prime) {F : Subgroup G}
    (hFe : IsElemAbelian f F) (hF4 : Nat.card F = f ^ 4) (hlr : rankThreeLocalRank f G ≤ 3) :
    ¬ 2 ∣ Nat.card (centralizer (F : Set G)) := by
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hto : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have ht2 : (t : G) ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one _
  have ht1 : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hbound := smallRankInvolutionRankLE_of_localRank hfp (zpowers (t : G)) F hlr (t : G)
    (mem_zpowers _) ht2 ht1
  have hFC : F ⊓ centralizer ({(t : G)} : Set G) = F := by
    refine inf_eq_left.mpr fun a ha => ?_
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp t.2 a ha)
  rw [hFC] at hbound
  have h4 : 4 ≤ CFSG.Open.pRank f F := CFSG.SectionRank.le_pRank hfp.one_lt le_rfl hFe hF4
  omega

theorem sr630_exists_sylow (hS : Setting G)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T : Subgroup G} {f : ℕ}
    (hyp : Lemma630Hyp G p P M x z T f) : ∃ E : Subgroup G, SmallRankSBSylow p f x z T E := by
  obtain ⟨hf, -, h28, hfp, hf2, hfD, h29⟩ := hyp
  have hp : p.Prime := hf.prime
  have hp2 : p ≠ 2 := hf.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  obtain ⟨hp35, -, -, hfit⟩ := h28
  obtain ⟨-, -, -, hFe, hF4, -⟩ := h29
  have hFne : smallRankF p f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF p f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFD : smallRankF p f x ≤ smallRankD p x :=
    (sr629_omega_center_le f _).trans (CFSG.LieType.BorelTits.pCoreOf_le f _)
  have hDC : smallRankD p x ≤ centralizer ({x} : Set G) := sSup_le fun _ hK => hK.1
  have hxCF : x ∈ centralizer (smallRankF p f x : Set G) :=
    mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hDC (hFD ha))
  have hzx : z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem).symm
  have hxx : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hCN : ∀ g ∈ centralizer ({x} : Set G),
      g ∈ normalizer (centralizer (smallRankF p f x : Set G) : Set G) := fun g hg =>
    sr630c_mem_normalizer_centralizer (sr629_centralizer_le_normalizer_F hp x hg)
  have hCzM : centralizer ({z} : Set G) ≤ M :=
    (sr628_centralizer_le_normalizer_zpowers z).trans (hf.normalizer_zpowers_le hS)
  have hzCF : z ∉ centralizer (smallRankF p f x : Set G) := by
    intro hz
    apply hFne
    rw [eq_bot_iff, ← hFM]
    refine fun a ha => ⟨ha, hCzM ?_⟩
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz a ha)
  have hpl : SmallRankPlane p (P : Subgroup G) x z :=
    SmallRankPlane.of_situation hS hf.situation hf.point hf.central
  have hPx : IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) :=
    isSylowOf_iff.mpr ⟨inf_le_right, P.isPGroup'.to_inf_left, hf.point.sylow_centralizer⟩
  have hrank : CFSG.Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hf.situation.largeObstruction_empty x ⟨hf.sylow_le hS hf.point.mem, hf.point.ne_one,
      hf.point.pow_eq_one, by omega, hf.point.not_centralizer_le⟩
  have hCx : ∀ E : Subgroup G, E ≤ centralizer ({x} : Set G) → IsElemAbelian p E →
      Nat.card E ≤ p ^ 2 := by
    intro E hE hEe
    have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk2 := CFSG.SectionRank.le_pRank hp.one_lt hE hEe hk
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hA3 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
    obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hf.situation.mem_sigmaA
      hf.situation.isCoreMaxLocal
    obtain ⟨A, hAP, hAe, hAc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (P : Subgroup G)
    exact ⟨A, hAP, hAe, hP3 ▸ hAc⟩
  have hsyl : IsSylowOf p (zpowers x) (centralizer (smallRankF p f x : Set G)) :=
    sr630e_zpowers_isSylowOf hp hp2 hpl hf.central.centralizes hf.point.ne_one
      hf.point.pow_eq_one hPx hCx hA3 hxCF hzCF (hCN z hzx)
  have hodd := sr630e_not_two_dvd_card_centralizer hfp hFe hF4
    (smallRank_localRank_le_three hS hfp hf2)
  obtain ⟨K, hKC, hcardC, hpK, hKchar⟩ :=
    sr630e_normal_complement hp hp35 hf.point.ne_one hf.point.pow_eq_one hsyl hodd
  have hKN : ∀ g ∈ normalizer (centralizer (smallRankF p f x : Set G) : Set G),
      g ∈ normalizer (K : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhC := hKC hh
      have hghC := (mem_normalizer_iff.mp hg h).mp hhC
      rw [hKchar _ hghC, sr630e_orderOf_conj]
      exact (hKchar h hhC).mp hh
    · intro hh
      have hghC := hKC hh
      have hhC := (mem_normalizer_iff.mp hg h).mpr hghC
      rw [hKchar h hhC]
      have h1 := (hKchar _ hghC).mp hh
      rwa [sr630e_orderOf_conj] at h1
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card hpl.card_eq
  obtain ⟨hAcard, hAsolv⟩ :=
    sr628_card_sup_and_solvable hp hp2 hf.S_isPGroup hBp hf.B_le_normalizer_S
  have hAC : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ centralizer ({x} : Set G) :=
    sup_le inf_le_right (sup_le (zpowers_le.mpr hxx) (zpowers_le.mpr hzx))
  have hAK : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (K : Set G) := fun g hg =>
    hKN g (hCN g (hAC hg))
  have hKodd : Odd (Nat.card K) := by
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hodd ?_)
    rw [hcardC]
    exact h.mul_right p
  have hcop : Nat.Coprime (Nat.card ↥(smallRankS x T ⊔ (zpowers x ⊔ zpowers z)))
      (Nat.card K) := by
    rw [hAcard]
    obtain ⟨a, ha⟩ := hf.S_isPGroup.exists_card_eq
    obtain ⟨b, hb⟩ := hBp.exists_card_eq
    rw [ha, hb]
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hKodd)
    · exact Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK)
  have : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
  have : Group.IsSolvable ↥(smallRankS x T ⊔ (zpowers x ⊔ zpowers z)) := hAsolv
  obtain ⟨E, hEK, hEp, hEc, hEA⟩ := sr628_exists_invariant_sylow hAK hcop hfp
  have hv : (Nat.card (centralizer (smallRankF p f x : Set G))).factorization f =
      (Nat.card K).factorization f := by
    rw [hcardC, Nat.factorization_mul Nat.card_pos.ne' hp.ne_zero, Finsupp.add_apply,
      hp.factorization, Finsupp.single_apply, ite_eq_right (Ne.symm hfp'), add_zero]
  have hEsyl : IsSylowOf f E (centralizer (smallRankF p f x : Set G)) :=
    isSylowOf_of_card (hEK.trans hKC) (by rw [hEc, hv])
  exact ⟨E, hEK.trans hKC, hEp, (isSylowOf_iff.mp hEsyl).2.2, hEA⟩

theorem GL83SmallRankLemma630Res.toCore (hS : Setting G) (h : GL83SmallRankLemma630Res G) :
    GL83SmallRankLemma630Core G where
  exists_sylow := fun _ _ _ _ _ _ _ hyp => sr630_exists_sylow hS hyp
  evasion := h.evasion
  iii := h.iii

end CFSG.LocalAnalysis.RankThreeTheoremC
