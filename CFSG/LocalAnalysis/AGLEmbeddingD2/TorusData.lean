module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreD2
import CFSG.LocalAnalysis.AGLEmbeddingD2.PrimeBlocksD2
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

section Data

variable {G : Type} [Group G] [Finite G]

structure D2TorusData (p : ℕ) [Fact p.Prime] (M H R X : Subgroup G) : Prop where
  pair : AGLPair p M H R
  eq_R : X = R
  elem : IsElemAbelian p X
  card : Nat.card X = p ^ 2
  torus : ∃ t ∈ H ⊓ M, t ∈ Subgroup.normalizer (X : Set G) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ X, t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧
    (∀ x ∈ X, t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
    ∀ k, 0 < k → k < m → ∀ Y₀ : Subgroup G, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set G)
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  pcore_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) → Y ≤ X ⊔ GLBPrimeCore p H
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ 2
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H

end Data

namespace D2TorusData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem le_M (h : D2TorusData p M H R X) : X ≤ M :=
  h.eq_R.le.trans h.pair.le_M

theorem le_inf_normalizer (h : D2TorusData p M H R X) :
    X ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  h.pair.inf_eq_inf_normalizer_twoCore ▸ h.eq_R.le.trans h.pair.R_le_inf

theorem coprime_of_perfect (h : D2TorusData p M H R X) :
    ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) → ⁅Y, Y⁆ = Y →
      p.Coprime (Nat.card Y) := by
  intro Y hY hperf
  have hYN := h.perfect_le Y (h.pair.inf_eq_inf_normalizer_twoCore ▸ hY) hperf
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYN)
    (glbPrimeCore_coprime p H)

theorem isElemAbelian_barM (h : D2TorusData p M H R X) : IsElemAbelian p (barM M X) :=
  AGLPair.isElemAbelian_barM_of_isElemAbelian h.elem

theorem card_barM (h : D2TorusData p M H R X) : Nat.card (barM M X) = p ^ 2 :=
  h.pair.card_barM_of_isElemAbelian h.le_M h.elem h.card

theorem le_normalizer_weakSBlock (hD1 : D1For G) (h : D2TorusData p M H R X) (hp5 : 5 ≤ p)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    X ≤ Subgroup.normalizer (L : Set G) := fun x hxX =>
  h.pair.mem_normalizer_weakSBlock hD1 hB3 h.pair.prime hp5 (h.pair.R_le_inf (h.eq_R ▸ hxX))
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using h.elem.2 x hxX)) hL

theorem le_pCore_of_forall_le_centralizer (h : D2TorusData p M H R X) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _))
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
  h.pair.toTwoLocalPhaseThree.le_pCore_of_forall_le_centralizer h.pair.isKGroup.1 h.pair.ne_two
    h.normal_dichotomy h.isElemAbelian_barM h84 hD2 hcomp hodd

theorem false_of_oddCore_not_centralized (h : D2TorusData p M H R X) (hD1 : D1For G)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) (hp5 : 5 ≤ p) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p)
    (hns : ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    False := by
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨t, htK, htX, m, lam, -, hm, hlam, -, hscal, -, horb⟩ := h.torus
  have htM : t ∈ M := htK.2
  have hpm : 5 ≤ (p - 1) * m :=
    calc 5 ≤ 4 * 2 := by norm_num
      _ ≤ (p - 1) * m := Nat.mul_le_mul (by omega) hm
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : 4 ≤ Open.pRank s Sg :=
    stmtOddCoreRankOrbit hs hs2 hp hpm hsp Sg (barM M X) (mk ⟨t, htM⟩) lam
      CFSG.pCore_isPGroup (le_top.trans hSgN) h.isElemAbelian_barM h.card_barM
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htX) hlam
      (barM_conj_pow_eq_pow htM hscal)
      (fun k hk0 hkm _ hY₀ hcard =>
        h.pair.pow_notMem_normalizer_barM_of_isElemAbelian h.elem h.le_M htM htX horb hk0 hkm hY₀
          hcard)
      hns
  have hSgK : Sg ≤ barM M (H ⊓ M) :=
    h.pair.le_barM_inf_of_le_centralizer
      ((pCore_le_pPrimeCore_two hs hs2).trans (h.pair.oddCore_le_centralizer h84 hD2))
  have h4 : 4 ≤ Open.pRank s (H ⊓ M) :=
    hrank.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono s hs hSgK).trans
      (pRank_barM_le hs hs2 M (H ⊓ M) inf_le_right))
  exact h.pair.false_of_four_le_pRank hD1 hs hs2 h4

theorem le_centralizer_oddCore (h : D2TorusData p M H R X) (hD1 : D1For G)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) (hp5 : 5 ≤ p) :
    ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) :=
  fun _ hs hs2 hsp => by_contra fun hns =>
    h.false_of_oddCore_not_centralized hD1 h84 hD2 hp5 hs hs2 hsp hns

theorem le_pCore_of_forall_le_centralizer_components (h : D2TorusData p M H R X)
    (hD1 : D1For G) (hp5 : 5 ≤ p) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
  h.le_pCore_of_forall_le_centralizer h84 hD2 hcomp (h.le_centralizer_oddCore hD1 h84 hD2 hp5)

theorem pow_six_mem_normalizer_weakSBlock (hD1 : D1For G)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (h : D2TorusData p M H R X) {t : G} (ht : t ∈ H ⊓ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : t ^ 6 ∈ Subgroup.normalizer (L : Set G) := by
  have htM : t ∈ M := ht.2
  have htS : t ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h.pair.inf_eq_inf_normalizer_twoCore ▸ ht).2
  refine pow_six_mem_normalizer_of_bound fun m hmove => ?_
  have hinj := injective_map_conj_pow_aux' (L := L) (t := t) (m := m) hmove
  have h1 := h.pair.card_le_pRank_three_of_blocks hB3
    (fun i : Fin m => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom)
    (fun i => hL.map_conj (M.pow_mem htM _) (Subgroup.pow_mem _ htS _)) hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact h1.trans (h.pair.pRank_inf_le_three hD1 Nat.prime_three (by decide))

theorem barM_le_centralizer_of_weakSBlock (hD1 : D1For G) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hD2 : NoXBlockFor G) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2TorusData p M H R X) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := Fact.out
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L := fun L hL =>
    h.pair.blockHasThree h85 h86 h93 hD2 hK2 hC3 hK5 hL
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := h.le_normalizer_weakSBlock hD1 hp5 hB3 hL
  obtain ⟨t, htK, htX, m, lam, e, -, -, h6, -, hinv, -⟩ := h.torus
  obtain ⟨c, hc⟩ := h6
  have hιL : t ^ e ∈ Subgroup.normalizer (L : Set G) := by
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (h.pow_six_mem_normalizer_weakSBlock hD1 hB3 htK hL) c
  obtain ⟨j, hj, ⟨k, hjk⟩, hinv2⟩ := exists_two_element_inverting hinv
  have hιM : t ^ e ∈ M := M.pow_mem htK.2 _
  have hι2M : (t ^ e) ^ j ∈ M := M.pow_mem hιM j
  have hι2L : (t ^ e) ^ j ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hιL j
  have hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V →
        p.Coprime (Nat.card V) :=
    fun V hV hVp => coprime_card_of_le_barM_of_perfect (inf_le_right.trans hL.le)
      (fun W hW hWp => h.coprime_of_perfect W
        (le_inf (hW.trans (inf_le_right.trans hL.le)) (hW.trans inf_le_left)) hWp) hV hVp
  have hP := h.pair.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3p hK5p hL hp hp5 hPq
  have hMtop : M ≠ ⊤ := fun hM => h.pair.not_le (hM ▸ le_top)
  have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    ((catalogSimpleSections_of_isKProper h.pair.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hL.component
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := (h.le_inf_normalizer hxX).2
  have hxp : x ^ p = 1 := h.elem.2 x hxX
  set xb := mk ⟨x, hxM⟩ with hxb
  set yb := mk ⟨(t ^ e) ^ j, hι2M⟩ with hyb
  have hxbN : xb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hxM (hXL hxX)
  have hybN : yb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hι2M hι2L
  have hyb2 : ∃ k : ℕ, yb ^ 2 ^ k = 1 := by
    refine ⟨k, ?_⟩
    have : (⟨(t ^ e) ^ j, hι2M⟩ : M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hjk)
    rw [hyb, ← map_pow, this, map_one]
  have hxbp : xb ^ p = 1 := by
    have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [hxb, ← map_pow, this, map_one]
  have hinvb : yb * xb * yb⁻¹ = xb⁻¹ := by
    have h1 : (⟨(t ^ e) ^ j, hι2M⟩ : M) * ⟨x, hxM⟩ * (⟨(t ^ e) ^ j, hι2M⟩ : M)⁻¹ =
        (⟨x, hxM⟩ : M)⁻¹ := Subtype.ext (by simpa using hinv2 x hxX)
    have h2 := congrArg mk h1
    simpa only [hyb, hxb, map_mul, map_inv] using h2
  have hclos := mem_closure_two_elements_of_inverted (N := Subgroup.normalizer
      (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hp.odd_of_ne_two (by omega)) hxbN hybN hyb2 hxbp
    hinvb
  have hsup := hKin (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) hL.component hcat p hp hp5
    (h.pair.twoGenInner_hyp h85 h93 hD2 hL hP) xb hclos ⟨1, by simpa using hxbp⟩
  exact h.pair.mem_centralizer_of_mem_sup h84 h86 hD2 hL hP hsup
    (mem_normalizer_barM hxM hxS) (k := 1) (by simpa using hxbp)

theorem pCore_ne_bot_of_components (h : D2TorusData p M H R X) (hD1 : D1For G) (hp5 : 5 ≤ p)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hK : ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _))
    (hB : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _)) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ := by
  have hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _) := by
    intro Lbar hLbar
    obtain ⟨L, hL2, hbar, hL⟩ := h.pair.exists_weakSBlock_or_le_inf hLbar
    rw [← hbar]
    rcases hL with hblock | hle
    · exact hB L hblock
    · exact hK L hL2 hle
  have hle := h.le_pCore_of_forall_le_centralizer_components hD1 hp5 h84 hD2 hcomp
  intro hbot
  rw [hbot, le_bot_iff] at hle
  have hc := h.card_barM
  rw [hle, Subgroup.card_bot] at hc
  have := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
  omega

end D2TorusData

end CFSG.AGLEmbeddingD2
