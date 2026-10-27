module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Comp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

@[expose] def IsCharTwoLieIndex : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q | .E6 q | .E7 q | .E8 q
  | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.p = 2
  | .suzuki _ | .reeF4 _ | .tits => True
  | .reeG2 _ => False

@[expose] def IsChevTwo (Q : Type*) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsCharTwoLieIndex d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

structure Input25_2Facts : Prop where
  chevTwo : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ → ∀ b : Y, b ∈ Subgroup.normalizer (K : Set Y) →
    b ^ 3 ∈ Subgroup.centralizer (K : Set Y) → ∀ J : Subgroup Y,
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J →
    IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) → IsChevTwo (↥K ⧸ Subgroup.center ↥K)
  generation : ∀ (Y : Type) [Group Y] [Finite Y] (K E J : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore 3 ↥K = ⊥ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
    E ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 E → Nat.card E = 9 →
    ¬ E ≤ Subgroup.centralizer (K : Set Y) →
    J ≤ K ⊓ Subgroup.centralizer (E : Set Y) →
    (J.subgroupOf (K ⊓ Subgroup.centralizer (E : Set Y))).Normal →
    CFSG.Open.IsQuasisimple ↥J → 3 ∣ Nat.card ↥J →
    ∃ b ∈ E, b ≠ 1 ∧ ¬ ((J ⊔ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))).subgroupOf
      (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal

private theorem c25_localCores_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

private theorem c25_not_comm {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (h : ∀ a b : Q, a * b = b * a) : False := by
  have hc : Subgroup.center Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    exact fun y => h y x
  have := hQ.2.toNontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  apply hz
  rw [QuotientGroup.eq_one_iff, hc]
  trivial

theorem input25_2_of_facts (F : Input25_2Facts) : Input25_2 := by
  intro Y _ _ K E J hKq hKK hKc hEN hEel hE9 hJle hJn hJq hJL hb
  by_cases hEC : E ≤ Subgroup.centralizer (K : Set Y)
  ·
    have hKle : K ≤ Subgroup.centralizer (E : Set Y) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.1 (hEC he) k hk).symm
    have hKE : K ⊓ Subgroup.centralizer (E : Set Y) = K := inf_eq_left.2 hKle
    rw [hKE] at hJle hJn
    have hJK : K ≤ J := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups (c25_localCores_isQuasisimple hKq) hJn
        with h | h
      · exact Subgroup.subgroupOf_eq_top.mp h
      · exfalso
        refine c25_not_comm hJq fun a b => ?_
        have ha : (⟨a.1, hJle a.2⟩ : ↥K) ∈ Subgroup.center ↥K :=
          h (Subgroup.mem_subgroupOf.2 a.2)
        have h1 := Subgroup.mem_center_iff.1 ha ⟨b.1, hJle b.2⟩
        exact Subtype.ext (by simpa using congrArg Subtype.val h1.symm)
    obtain rfl : J = K := le_antisymm hJle hJK
    exact IsLThreeFour.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hKc).trans QuotientGroup.quotientBot) hJL
  · exfalso
    obtain ⟨b, hbE, hb1⟩ : ∃ b ∈ E, b ≠ 1 := by
      have hEne : E ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hE9
        omega
      obtain ⟨⟨b, hb⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hEne
      exact ⟨b, hb, fun h => hne (Subtype.ext h)⟩
    have hCb : K ⊓ Subgroup.centralizer (E : Set Y) ≤ K ⊓ Subgroup.centralizer ({b} : Set Y) :=
      inf_le_inf_left K (Subgroup.centralizer_le (by simpa using hbE))
    have hJb : J ≤ K ⊓ Subgroup.centralizer ({b} : Set Y) := hJle.trans hCb
    have hJq' : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
      obtain ⟨hs, hna⟩ := isSimpleGroup_of_isLThreeFour hJL
      exact c25_isQuasisimple_of_simple hs hna
    obtain ⟨J', hJ', ⟨e⟩⟩ := exists_component_of_normal_sup hJb (hb b hbE hb1) hJq'
    have hChev := F.chevTwo Y K hKq hKK hKc b (hEN hbE) (by
      rw [hEel.2 b hbE]
      exact Subgroup.one_mem _) J' hJ' (IsLThreeFour.of_mulEquiv e.symm hJL)
    have h3 : 3 ∣ Nat.card ↥J := by
      have h1 := card_eq_of_isLThreeFour hJL
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥J)
      rw [h1] at h2
      exact Dvd.dvd.trans (by norm_num) (Dvd.intro _ h2.symm)
    obtain ⟨b', hb'E, hb'1, hbn⟩ := F.generation Y K E J hKq hKc hChev hEN hEel hE9 hEC hJle hJn
      hJq h3
    exact hbn (hb b' hb'E hb'1)

end CFSG.HardMathSupport.Solomon.Coordinator
