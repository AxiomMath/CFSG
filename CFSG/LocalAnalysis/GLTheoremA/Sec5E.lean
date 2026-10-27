module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5D
public import CFSG.LocalAnalysis.GLTheoremA.PCompJoin
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_isPGroup_two_of_le {T O : Subgroup G} (hT : IsPGroup 2 T) (hTO : T ≤ O)
    (hO : Odd (Nat.card O)) : T = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT
  have hd : Nat.card T ∣ Nat.card O := Subgroup.card_dvd_of_le hTO
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.card_eq_one.1 hn
  · exfalso
    rw [hn] at hd
    have h2 : 2 ∣ Nat.card O := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hd
    exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 h2)

theorem tripleLevel_le_five (p : ℕ) (B L : Subgroup G) : tripleLevel p B L ≤ 5 := by
  classical
  unfold tripleLevel
  by_cases h : IsGStar p B L
  · rw [if_pos h]
  · rw [if_neg h]
    exact (Nat.min_le_left 4 _).trans (by norm_num)

theorem exists_isS0 {p : ℕ} (hS3 : Stage3 G p) (hBex : ∃ B : Subgroup G, GLAIsBmax p B) :
    ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0 p B x L := by
  classical
  set T : Set ℕ := {j | ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L ∧
    tripleLevel p B L = j}
  obtain ⟨B, hB⟩ := hBex
  obtain ⟨x, L, hS⟩ := hS3.1 B hB
  have hne : T.Nonempty := ⟨_, B, x, L, hS, rfl⟩
  have hbdd : BddAbove T := ⟨5, by
    rintro j ⟨B, x, L, -, rfl⟩
    exact tripleLevel_le_five p B L⟩
  obtain ⟨B', x', L', hS', hlev⟩ := Nat.sSup_mem hne hbdd
  exact ⟨B', x', L', hS', hlev⟩

theorem exists_isS0Max {p : ℕ} (hS3 : Stage3 G p) (hS4 : Stage4Order G p)
    (hBex : ∃ B : Subgroup G, GLAIsBmax p B) :
    ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0Max p B x L := by
  obtain ⟨B, x, L, h⟩ := exists_isS0 hS3 hBex
  obtain ⟨B', x', L', h', -⟩ := hS4.2.2.1 B x L h
  exact ⟨B', x', L', h'⟩

theorem odd_card_glaPPrimeCoreOf_of_not_prop55 {p : ℕ} (hp : p.Prime)
    (hno : ¬ Prop55At G p) {B L : Subgroup G} {x : G} (hBxL : IsS0Max p B x L) :
    Odd (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))
  have hB : GLAIsBmax p B := hBxL.1.1.1
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    (isElemAbelian_le_centralizer hB.1 hBxL.1.1.2.1.1).trans (le_normalizer_glaPPrimeCoreOf p _)
  have hcop : Nat.Coprime p (Nat.card O) := by
    rw [show Nat.card O = Nat.card (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) from
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact CFSG.pPrimeCore_coprime_card
  obtain ⟨P, -, hPO, hP2, hPidx, hBP⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.exists_invariant_sylow_containing_of_pGroup
      hp Nat.prime_two (isPGroup_of_isElemAbelian hB.1) hBO
      ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop) (bot_le : (⊥ : Subgroup G) ≤ O) IsPGroup.of_bot
      (fun b _ => Subgroup.mem_normalizer_iff.2 fun h => by simp)
  by_cases hPbot : P = ⊥
  · rw [hPbot, Subgroup.relIndex_bot_left] at hPidx
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hPidx)
  · exact absurd ⟨B, x, L, hBxL, P, hPO.trans le_sup_right, hPbot, hP2, hBP⟩ hno

theorem lemma57i {p : ℕ} (hc : Sec5Ctx G p) (hno : ¬ Prop55At G p) {B L J : Subgroup G} {x : G}
    (hBxL : IsS0Max p B x L) (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hT : ∃ T : Subgroup G, T ≤ J ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)) :
    ¬ IsGB p B J := by
  intro hGB
  have hp := hc.prime
  have hS4 := hc.stage4Order
  have hSJ : IsSTriple p B x J := ⟨hBxL.1.1.1, hBxL.1.1.2.1, hJ⟩
  have hcl : closureIn J B = J := closureIn_eq_self hBJ
  have hGS : IsGStar p B J := by
    obtain ⟨E, hEB, hE, hEc, -, hEL⟩ := hGB
    exact ⟨E, hEB, hE, hEc, by rwa [hcl]⟩
  have hlev : tripleLevel p B J = 5 := by
    unfold tripleLevel
    rw [if_pos hGS]
  have hbdd : BddAbove {j | ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L ∧
      tripleLevel p B L = j} := ⟨5, by
    rintro j ⟨B', x', L', -, rfl⟩
    exact tripleLevel_le_five p B' L'⟩
  have hd : dLevel G p = 5 := by
    apply le_antisymm
    · refine csSup_le ⟨_, B, x, J, hSJ, rfl⟩ ?_
      rintro j ⟨B', x', L', -, rfl⟩
      exact tripleLevel_le_five p B' L'
    · exact le_csSup hbdd ⟨B, x, J, hSJ, hlev⟩
  have hS0J : IsS0 p B x J := ⟨hSJ, hlev.trans hd.symm⟩
  obtain ⟨B', x', L', hS0', hrel⟩ := hS4.2.2.1 B x J hS0J
  obtain ⟨T, hTJ, hTne, hT2, hBT⟩ := hT
  have hodd := odd_card_glaPPrimeCoreOf_of_not_prop55 hp hno hBxL
  have hnG : ¬ nGen B (closureIn J B) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
    intro hle
    have hTle : T ≤ nGen B (closureIn J B) := by
      rw [hcl]
      exact le_iSup₂_of_le T ⟨hTJ, hT2, hBT⟩ le_rfl
    exact hTne (eq_bot_of_isPGroup_two_of_le hT2 (hTle.trans hle) hodd)
  have h' := hS4.2.2.2.2.2.1 (B, x, J) (B', x', L') hrel hnG
  apply hno
  by_contra hP
  apply h'
  refine iSup₂_le fun T' hT' => ?_
  have hT'bot : T' = ⊥ := by
    by_contra hT'ne
    refine hP ⟨B', x', L', hS0', T', ?_, hT'ne, hT'.2.1, hT'.2.2⟩
    exact (hT'.1.trans (closureIn_eq_self hS0'.2.2).le).trans le_sup_left
  rw [hT'bot]
  exact bot_le

theorem lemma57ii {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) {B L J A : Subgroup G} {x : G}
    (hBxL : IsS0Max p B x L) (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J)
    (hJL : J ≠ L) (hA : GLAIsBmax p A) (hAx : A ≤ Subgroup.centralizer ({x} : Set G))
    (hU : ∃ U : Subgroup G, U ≤ Subgroup.centralizer ({x} : Set G) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set G))
    (hdec : ∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ J, a = u * v) :
    A ⊓ J ≤ Subgroup.zpowers x := by
  have hp := hc.prime
  obtain ⟨U, hUx, hUne, hU2, hAU⟩ := hU
  have hxA : x ∈ A := by
    have hxp : x ^ p = 1 := hBxL.1.1.1.1.2 x hBxL.1.1.2.1.1
    have hAx' : A ≤ Subgroup.centralizer ({x} : Set G) := hAx
    have hE := isElemAbelian_sup_zpowers hA.1 hAx' hxp
    have hxU : x ∈ Subgroup.normalizer (U : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun u hu => ?_)
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hUx hu))
    have := GLAIsBmax.eq_of_le hp hA le_sup_left hE hUne hU2
      (sup_le hAU (Subgroup.zpowers_le.2 hxU))
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hJL' : J ≤ centModSubgroup p L := le_centModSubgroup_of_ne hp hJ hBxL.1.1.2.2 hJL
  have hdec' : ∀ a ∈ A, ∃ u ∈ B ⊓ A, ∃ v ∈ A, CentMod p L v ∧ a = u * v := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec a ha
    exact ⟨u, ⟨hu.2, hu.1⟩, v, hv.1, centMod_iff.2 (hJL' hv.2), rfl⟩
  have h52 := lemma52 hc h51 hBxL hA hxA hdec'
  intro v hv
  exact (h52 v hv.1).1 (centMod_iff.2 (hJL' hv.2))

end CFSG.LocalAnalysis.GLTheoremA
