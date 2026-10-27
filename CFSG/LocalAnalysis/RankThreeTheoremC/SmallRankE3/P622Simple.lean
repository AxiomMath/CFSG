module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Lemma61
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiPx
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii PComp)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple (relPPrimeCore_conj_mem)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S : Subgroup G}

private theorem p622S_mem_sup_aux {A B : Subgroup G} (hB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    {n : G} (hn : n ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = n := by
  rw [Subgroup.sup_eq_closure] at hn
  refine Subgroup.closure_induction (p := fun g _ => ∃ a ∈ A, ∃ b ∈ B, a * b = g)
    ?_ ?_ ?_ ?_ hn
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  · rintro x y hx hy ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    have hc : a₂⁻¹ * b₁ * a₂ ∈ B := by
      have h1 := hB a₂⁻¹ (A.inv_mem ha₂) b₁ hb₁
      rwa [inv_inv] at h1
    exact ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, a₂⁻¹ * b₁ * a₂ * b₂, B.mul_mem hc hb₂, by group⟩
  · rintro x hx ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, hB a ha b⁻¹ (B.inv_mem hb), by group⟩

private theorem p622S_simpleSection_aux {H K O : Subgroup G} (hKH : K ≤ H) (hOH : O ≤ H)
    (hO : H ≤ normalizer (O : Set G)) (hperf : ⁅K, K⁆ = K) (hlt : K ⊓ O < K)
    (hmax : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K) :
    S622IsSimpleSection (K ⊔ O) O := by
  have hKO : ∀ a ∈ K, ∀ b ∈ O, a * b * a⁻¹ ∈ O := fun a ha b hb =>
    (Subgroup.mem_normalizer_iff.mp (hO (hKH ha)) b).mp hb
  have hLN : K ⊔ O ≤ normalizer (O : Set G) := sup_le (hKH.trans hO) (hOH.trans hO)
  have hOL : (O.subgroupOf (K ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : O ≤ K ⊔ O)).mpr hLN
  unfold S622IsSimpleSection
  refine ⟨le_sup_right, hOL, ?_, ?_, ?_⟩
  · intro h
    have hKO' : K ≤ O := (le_sup_left : K ≤ K ⊔ O).trans h.ge
    exact (ne_of_lt hlt) (inf_eq_left.mpr hKO')
  · intro N hON hNL hNn
    have hNn' : ∀ h k, h ∈ N → k ∈ K ⊔ O → k * h * k⁻¹ ∈ N :=
      fun h k hh hk => (Subgroup.normal_subgroupOf_iff hNL).mp hNn h k hh hk
    have hNK : ((N ⊓ K).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h k hh hk
      exact ⟨hNn' h k hh.1 (Subgroup.mem_sup_left hk),
        K.mul_mem (K.mul_mem hk hh.2) (K.inv_mem hk)⟩
    rcases hmax (N ⊓ K) inf_le_right hNK (le_inf (inf_le_right.trans hON) inf_le_left) with
      h1 | h1
    · left
      refine le_antisymm ?_ hON
      intro n hn
      obtain ⟨a, ha, b, hb, hab⟩ := p622S_mem_sup_aux hKO (hNL hn)
      have haN : a ∈ N := by
        have e : a = n * b⁻¹ := by
          rw [← hab]
          group
        rw [e]
        exact N.mul_mem hn (N.inv_mem (hON hb))
      have haNK : a ∈ N ⊓ K := ⟨haN, ha⟩
      rw [h1] at haNK
      rw [← hab]
      exact O.mul_mem haNK.2 hb
    · right
      have hKN : K ≤ N := by
        have h2 : N ⊓ K ≤ N := inf_le_left
        rwa [h1] at h2
      exact le_antisymm hNL (sup_le hKN hON)
  · intro hall
    have hcomm : ⁅K, K⁆ ≤ K ⊓ O := by
      refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ⟨?_, ?_⟩
      · have h := Subgroup.commutator_mem_commutator hg₁ hg₂
        rwa [hperf] at h
      · exact hall g₁ (Subgroup.mem_sup_left hg₁) g₂ (Subgroup.mem_sup_left hg₂)
    rw [hperf] at hcomm
    exact (ne_of_lt hlt) (le_antisymm inf_le_left hcomm)

theorem p622_apply_pcomp (hK64 : KFact64ii) (hS : Setting G) (c : P622Conf p P M x z T S)
    (hnc : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x)) :
    ∃ K : Subgroup G, PComp p ((M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x)
      (centralizer ({x} : Set G)) K z := by
  have hsit := c.failure.situation
  have hx := c.failure.point
  have hz := c.failure.central
  have hprime : p.Prime := c.failure.prime
  have hp2 : p ≠ 2 := c.failure.ne_two
  haveI : Fact p.Prime := ⟨hprime⟩
  have hKH : CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) :=
    fun K L _ _ hsimple _ => k631_isKGroup_centralizer hS hx.ne_one K (L.subgroupOf K) hsimple
  have hxo : orderOf x = p := orderOf_eq_prime hx.pow_eq_one hx.ne_one
  have hzo : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hxnz : x ∉ zpowers z := p622_x_not_mem_zpowers hS hsit hx hz
  have hPCp : IsPGroup p ↥((P : Subgroup G) ⊓ centralizer ({x} : Set G)) :=
    P.isPGroup'.to_le inf_le_left
  have hsub : IsPGroup p ↥(((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
      (centralizer ({x} : Set G))) :=
    hPCp.of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) := by
    refine ⟨hsub.toSylow hx.sylow_centralizer, ?_⟩
    rw [IsPGroup.toSylow_coe]
    exact map_subgroupOf_eq_of_le inf_le_right
  have hBQ : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    le_inf c.B_le_P c.B_le_centralizer
  have hΩQ : ∀ q ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), q ^ p = 1 →
      q ∈ zpowers x ⊔ zpowers z := by
    intro q hq hqp
    have hqP : q ∈ (P : Subgroup G) := hq.1
    have hqC : q ∈ centralizer ({x} : Set G) := hq.2
    have hBq : zpowers x ⊔ zpowers z ≤ centralizer ({q} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hqC).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp hz.centralizes q hqP).symm))
    have hqcent : q ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun b hb => mem_centralizer_singleton_iff.mp (hBq hb)
    exact (SmallRankPlane.of_situation hS hsit hx hz).mem_of_mem_centralizer q hqcent hqp
  have hfr := x_not_mem_frattini3 hS hsit hx hQsyl.isPGroup
  have hwc : ∀ h ∈ centralizer ({x} : Set G), h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z →
      h * z * h⁻¹ ∈ zpowers z := fun h _ hh => p622_conj_mem_zpowers hS hsit hx hz hh
  have hQM : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ M ⊓ centralizer ({x} : Set G) :=
    le_inf (inf_le_left.trans (c.failure.sylow_le hS)) inf_le_right
  have hNZ : normalizer ((zpowers z : Subgroup G) : Set G) ⊓ centralizer ({x} : Set G) ≤
      M ⊓ centralizer ({x} : Set G) := fun g hg =>
    ⟨normalizer_zpowers_le_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
      hsit.largeObstruction_empty hz.mem hz.centralizes hz.ne_one hz.pow_eq_one hg.1, hg.2⟩
  exact (hK64 G p (centralizer ({x} : Set G)) ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (M ⊓ centralizer ({x} : Set G)) x z hprime hp2 hKH hxo hzo hxz hxnz hQsyl hBQ hΩQ hfr hwc
    hQM inf_le_right hNZ hnc).1

theorem p622_simpleSection_of_pcomp {H K Y : Subgroup G} (hK : PComp p Y H K z)
    (hY : rankThreePrimeCore p H ≤ Y) :
    S622IsSimpleSection (K ⊔ rankThreePrimeCore p H) (rankThreePrimeCore p H) ∧
      K ⊔ rankThreePrimeCore p H ≤ H ∧ z ∈ K ⊔ rankThreePrimeCore p H ∧
      ¬ K ⊔ rankThreePrimeCore p H ≤
        (Y ⊓ (K ⊔ rankThreePrimeCore p H)) ⊔ rankThreePrimeCore p H ∧
      H ≤ normalizer ((K ⊔ rankThreePrimeCore p H : Subgroup G) : Set G) := by
  have hOH : rankThreePrimeCore p H ≤ H := sSup_le fun _ hN => hN.1
  have hO_norm : H ≤ normalizer ((rankThreePrimeCore p H : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact SetLike.mem_coe.mpr (relPPrimeCore_conj_mem (SetLike.mem_coe.mp hn) hh)
    · intro hn
      have h1 := relPPrimeCore_conj_mem (SetLike.mem_coe.mp hn) (H.inv_mem hh)
      have e : h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n := by group
      rw [e] at h1
      exact SetLike.mem_coe.mpr h1
  have hS := p622S_simpleSection_aux hK.le hOH hO_norm hK.perfect hK.lt hK.maximal
  refine ⟨hS, sup_le hK.le hOH, mem_sup_left (hK.mem (mem_zpowers z)), ?_, ?_⟩
  · intro hle
    apply hK.not_le
    calc K ≤ K ⊔ rankThreePrimeCore p H := le_sup_left
      _ ≤ (Y ⊓ (K ⊔ rankThreePrimeCore p H)) ⊔ rankThreePrimeCore p H := hle
      _ ≤ Y := sup_le inf_le_left hY
  · intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK.normal hh),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hO_norm hh)]

theorem p622_kxData_of_pcomp_bot {H K Y : Subgroup G} (hK : PComp p Y H K z)
    (hD : rankThreePrimeCore p H = ⊥) :
    S622IsSimpleSection K ⊥ ∧ K ≤ H ∧ z ∈ K ∧ CFSG.Open.pRank p K ≤ 1 ∧ ¬ K ≤ Y ∧
      H ≤ normalizer (K : Set G) := by
  have hlt : ⊥ < K := by
    have h := hK.lt
    rw [hD, inf_bot_eq] at h
    exact h
  refine ⟨?_, hK.le, hK.mem (mem_zpowers z), hK.rank_one.le, hK.not_le, hK.normal⟩
  unfold S622IsSimpleSection
  refine ⟨bot_le, ?_, ne_of_lt hlt, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · intro N _ hNK hNn
    have h := hK.maximal N hNK hNn (by rw [hD, inf_bot_eq]; exact bot_le)
    rw [hD, inf_bot_eq] at h
    exact h
  · intro hall
    have hcomm : ⁅K, K⁆ ≤ ⊥ :=
      Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => hall g₁ hg₁ g₂ hg₂
    rw [hK.perfect] at hcomm
    exact (lt_iff_le_not_ge.mp hlt).2 hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
