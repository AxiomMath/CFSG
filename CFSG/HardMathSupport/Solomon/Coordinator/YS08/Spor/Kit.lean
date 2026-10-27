module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.L3Orders
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

theorem eq_bot_or_eq_top_of_isSubnormal {S : Type} [Group S] [IsSimpleGroup S] {J K : Subgroup S}
    (h : CFSG.Open.IsSubnormal J K) (hK : K = ⊤) : J = ⊥ ∨ J = ⊤ := by
  induction h with
  | refl H => right; exact hK
  | @step H M K' hHM hn _ ih =>
    rcases ih hK with hM | hM
    · left
      rw [hM] at hHM
      exact le_bot_iff.1 hHM
    · have hHn : H.Normal := ⟨fun n hn' g => by
        have h1 := hn.conj_mem ⟨n, hHM hn'⟩
          (show (⟨n, hHM hn'⟩ : ↥M) ∈ H.subgroupOf M from hn') ⟨g, hM ▸ Subgroup.mem_top g⟩
        exact h1⟩
      haveI := hHn
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

theorem card_barOf_top_of_simple {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnt : Nontrivial (barOf 3 (⊤ : Subgroup S))) :
    Nat.card (barOf 3 (⊤ : Subgroup S)) = Nat.card S := by
  haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup_congr.2 inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥(⊤ : Subgroup S)) with h | h
  · have e : barOf 3 (⊤ : Subgroup S) ≃* ↥(⊤ : Subgroup S) :=
      (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot
    rw [Nat.card_congr e.toEquiv, Subgroup.card_top]
  · exfalso
    have hsub : Subsingleton (barOf 3 (⊤ : Subgroup S)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact QuotientGroup.eq.2 (h ▸ Subgroup.mem_top _)
    exact (not_nontrivial_iff_subsingleton.2 hsub) hnt

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  haveI := hQ.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial

theorem sporL3DownInner_of_model {s : TauCeti.SporadicName} (M : Type) [Group M] [Finite M]
    (hM : Nonempty (M ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (hcard : NoL3Eq (Nat.card M))
    (hC : ∀ x : M, orderOf x = 3 → Nat.card (Subgroup.centralizer ({x} : Set M)) < 20160) :
    SporL3DownInner s := by
  intro S _ _ hS hnab hSs x hx J hJ p hL
  have e : S ≃* M := hSs.some.trans hM.some.symm
  have hdvd : Nat.card (barOf 3 J) ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJ.1)
  have hge := isL3Kind_ge hL
  by_cases hx1 : x = 1
  · subst hx1
    have hCtop : Subgroup.centralizer ({1} : Set S) = ⊤ := by simp
    have hsn : CFSG.Open.IsSubnormal J ⊤ := hCtop ▸ hJ.2.1
    haveI := hS
    have hq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
    have hnt := nontrivial_of_isQuasisimple hq
    rcases eq_bot_or_eq_top_of_isSubnormal hsn rfl with hJ0 | hJ1
    · exfalso
      subst hJ0
      have hsub : Subsingleton (barOf 3 (⊥ : Subgroup S)) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim a b]
      exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
    · subst hJ1
      have hbar := card_barOf_top_of_simple hnt
      obtain ⟨r, ε, e', he', hc, hcd⟩ := isL3Kind_card_forms hL
      rw [hbar, Nat.card_congr e.toEquiv] at hcd
      exact hcard r ε e' he' hc hcd
  · have hx3 : orderOf x = 3 := orderOf_eq_prime hx hx1
    have h1 := hC (e x) (by rw [MulEquiv.orderOf_eq]; exact hx3)
    have hcc : Nat.card (Subgroup.centralizer ({x} : Set S)) =
        Nat.card (Subgroup.centralizer ({e x} : Set M)) := by
      rw [← map_centralizer_mulEquiv e x, Subgroup.card_map_of_injective e.injective]
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega

theorem sporL3DownInner_of_ninth {s : TauCeti.SporadicName} (M : Type) [Group M] [Finite M]
    (hM : Nonempty (M ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (h9 : ¬ 9 ∣ Nat.card M) :
    SporL3DownInner s := by
  intro S _ _ hS hnab hSs x hx J hJ p hL
  have e : S ≃* M := hSs.some.trans hM.some.symm
  have h1 : 9 ∣ Nat.card (barOf 3 J) := isL3Kind_ninth hL
  have h2 : Nat.card (barOf 3 J) ∣ Nat.card S :=
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJ.1)).trans
      (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_congr e.toEquiv] at h2
  exact h9 (h1.trans h2)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
