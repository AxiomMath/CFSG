module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

variable {X : Type*} [Group X] [Finite X]

private theorem card_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun p : ↥A × ↥B => (⟨(p.1 : G) * p.2, ?_⟩ : ↥(A ⊔ B))) ⟨?_, ?_⟩
  · exact Subgroup.mul_mem_sup p.1.2 p.2.2
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [hmem, mul_one]
    have hb2 : b = b' := by
      have h : b' * b⁻¹ = 1 := by rw [← h2, hmem]
      calc b = (b' * b⁻¹)⁻¹ * b' := by group
        _ = b' := by rw [h]; group
    subst this; subst hb2; rfl
  · rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hg
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

private theorem pRank_coe_top (p : ℕ) :
    CFSG.pRank p (⊤ : Subgroup X) = CFSG.Open.pRank p (⊤ : Subgroup X) :=
  (CFSG.SectionRank.pRank_eq_open_pRank_top p (⊤ : Subgroup X)).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)).symm

theorem zpowers_inf_centralizer_eq_bot {p : ℕ} (hp : p.Prime) {C : Subgroup X} {e : X}
    (hord : orderOf e = p) (hnc : ∃ c ∈ C, e * c ≠ c * e) :
    zpowers e ⊓ centralizer (C : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxpow : x ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.1
    have hep : e ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hord]
      exact pow_orderOf_eq_one e
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hep, one_zpow]
  haveI : Fact p.Prime := ⟨hp⟩
  have hordx : orderOf x = p := orderOf_eq_prime hxpow hx1
  have hxcard : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hordx]
  have hecard : Nat.card (zpowers e) = p := by rw [Nat.card_zpowers, hord]
  have hle : zpowers x ≤ zpowers e := Subgroup.zpowers_le.mpr hx.1
  have heq : zpowers x = zpowers e :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hecard, hxcard])
  have hcent : zpowers x ≤ centralizer (C : Set X) := Subgroup.zpowers_le.mpr hx.2
  have hle' : zpowers e ≤ centralizer (C : Set X) := heq ▸ hcent
  have he_cent : e ∈ centralizer (C : Set X) := Subgroup.zpowers_le.mp hle'
  obtain ⟨c, hc, hnc⟩ := hnc
  exact hnc (Subgroup.mem_centralizer_iff.mp he_cent c hc).symm

theorem isElemAbelian_sup_zpowers {p : ℕ} (hp : p.Prime) {A C : Subgroup X} {e : X} {a : ℕ}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ a) (hAC : A ≤ centralizer (C : Set X))
    (he : e ∈ C) (hord : orderOf e = p) (hnc : ∃ c ∈ C, e * c ≠ c * e) :
    IsElemAbelian p (A ⊔ zpowers e) ∧ Nat.card ↥(A ⊔ zpowers e) = p ^ (a + 1) := by
  have hep : e ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one e
  have hEab : IsElemAbelian p (zpowers e) := isElemAbelian_zpowers hep
  have hcardE : Nat.card (zpowers e) = p := by rw [Nat.card_zpowers, hord]
  have heA : e ∈ centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a' ha'
    exact (Subgroup.mem_centralizer_iff.mp (hAC ha') e he).symm
  have hEA : zpowers e ≤ centralizer (A : Set X) := Subgroup.zpowers_le.mpr heA
  have hc : ∀ a ∈ A, ∀ b ∈ zpowers e, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hEA hb) a ha
  have hinf : A ⊓ zpowers e = ⊥ := by
    apply le_bot_iff.mp
    calc A ⊓ zpowers e ≤ zpowers e ⊓ centralizer (C : Set X) :=
          le_inf inf_le_right (inf_le_left.trans hAC)
      _ = ⊥ := zpowers_inf_centralizer_eq_bot hp hord hnc
  refine ⟨IsElemAbelian.sup_of_commute hA hEab hc, ?_⟩
  rw [card_sup_of_commute hc hinf, hAc, hcardE, pow_succ]

theorem add_one_le_pRank_of_le_centralizer {p : ℕ} (hp : p.Prime) {A C : Subgroup X} {e : X}
    {a : ℕ} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ a)
    (hAC : A ≤ centralizer (C : Set X)) (he : e ∈ C) (hord : orderOf e = p)
    (hnc : ∃ c ∈ C, e * c ≠ c * e) : a + 1 ≤ pRank p (⊤ : Subgroup X) := by
  obtain ⟨hEab, hcard⟩ := isElemAbelian_sup_zpowers hp hA hAc hAC he hord hnc
  rw [pRank_coe_top p]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEab hcard

theorem card_le_pRank_of_components {p : ℕ} (hp : p.Prime) (s : Finset (Subgroup X))
    (hs : ∀ C ∈ s, CFSG.IsComponent C ∧ ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e) :
    s.card ≤ pRank p (⊤ : Subgroup X) := by
  classical
  have main : ∀ s : Finset (Subgroup X),
      (∀ C ∈ s, CFSG.IsComponent C ∧
        ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e) →
      ∃ A : Subgroup X, A ≤ ⨆ C ∈ s, C ∧ IsElemAbelian p A ∧ Nat.card A = p ^ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨⊥, bot_le, CFSG.SectionRank.isElemAbelian_bot p, ?_⟩
        rw [Finset.card_empty, pow_zero]
        exact Subgroup.card_bot
    | insert D s hD ih =>
        intro hs'
        have hs : ∀ C ∈ s, CFSG.IsComponent C ∧
            ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e :=
          fun C hC => hs' C (Finset.mem_insert_of_mem hC)
        obtain ⟨A, hA_le, hAab, hAcard⟩ := ih hs
        obtain ⟨hDcomp, e, heD, hord, hnce⟩ := hs' D (Finset.mem_insert_self D s)
        have hAcent : A ≤ centralizer (D : Set X) := by
          refine hA_le.trans (iSup₂_le fun C hC => ?_)
          have hCcomp : CFSG.IsComponent C := (hs C hC).1
          have hCD : C ≠ D := fun h => hD (h ▸ hC)
          have hcomm : ⁅C, D⁆ = ⊥ :=
            (CFSG.LocalCores.distinct_components_commute hCcomp hDcomp).resolve_left hCD
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        obtain ⟨hTab, hTcard⟩ := isElemAbelian_sup_zpowers hp hAab hAcard hAcent heD hord hnce
        refine ⟨A ⊔ zpowers e, ?_, hTab, ?_⟩
        · refine sup_le (hA_le.trans (iSup₂_le fun C hC =>
              le_iSup₂_of_le C (Finset.mem_insert_of_mem hC) le_rfl)) ?_
          exact (Subgroup.zpowers_le.mpr heD).trans
            (le_iSup₂_of_le D (Finset.mem_insert_self D s) le_rfl)
        · rw [Finset.card_insert_of_notMem hD]
          exact hTcard
  obtain ⟨A, -, hAab, hAcard⟩ := main s hs
  rw [pRank_coe_top p]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hAab hAcard

theorem add_two_le_pRank_of_three_components {p : ℕ} (hp : p.Prime) {L J J' : Subgroup X}
    (hL : CFSG.IsComponent L) (hJ : CFSG.IsComponent J) (hJ' : CFSG.IsComponent J')
    (hLJ : L ≠ J) (hLJ' : L ≠ J') (hJJ' : J ≠ J') {B : Subgroup X} {b : ℕ} (hBL : B ≤ L)
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ b)
    (hJe : ∃ e ∈ J, orderOf e = p ∧ ∃ c ∈ J, e * c ≠ c * e)
    (hJe' : ∃ e ∈ J', orderOf e = p ∧ ∃ c ∈ J', e * c ≠ c * e) :
    b + 2 ≤ pRank p (⊤ : Subgroup X) := by
  have hLJc : L ≤ centralizer (J : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL hJ).resolve_left hLJ)
  have hLJ'c : L ≤ centralizer (J' : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL hJ').resolve_left hLJ')
  have hJJ'c : J ≤ centralizer (J' : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hJ hJ').resolve_left hJJ')
  obtain ⟨e, heJ, horde, hnce⟩ := hJe
  obtain ⟨e', heJ', horde', hnce'⟩ := hJe'
  obtain ⟨h1ab, h1card⟩ :=
    isElemAbelian_sup_zpowers hp hB hBc (hBL.trans hLJc) heJ horde hnce
  have hTcent : B ⊔ zpowers e ≤ centralizer (J' : Set X) :=
    sup_le (hBL.trans hLJ'c) ((Subgroup.zpowers_le.mpr heJ).trans hJJ'c)
  obtain ⟨h2ab, h2card⟩ :=
    isElemAbelian_sup_zpowers hp h1ab h1card hTcent heJ' horde' hnce'
  have hbound := CFSG.SectionRank.le_pRank hp.one_lt le_top h2ab h2card
  rw [pRank_coe_top p]
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
