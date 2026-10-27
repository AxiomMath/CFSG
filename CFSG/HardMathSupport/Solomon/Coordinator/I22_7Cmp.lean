module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CmpC
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Fi22
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Certified
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CmpB
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator.I1420

section Main

variable {K : Type} [Group K] [Finite K]

theorem i227cmp_three_dvd (hcore : GLAPPrimeCore 3 K = ⊥) {L : Subgroup K}
    (hL : IsComponentOf L ⊤) : 3 ∣ Nat.card L := by
  by_contra hnd
  have hcop : Nat.Coprime 3 (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
  have h1 : L ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup K) := by
    rw [← glaPPrimeCoreOf_eq_self_of_coprime hcop]
    exact glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1
  rw [glaPPrimeCoreOf_top_eq_bot_of_eq_bot hcore, le_bot_iff] at h1
  have hnt : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h1

end Main

theorem i227cmp_main
    (hOut : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsKGroup Q → ∀ {J : Subgroup Q},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J))
    (hFi : ∀ (X : Type) [Group X], IsFiTwentyTwo X →
      IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) : I22_7Comps := by
  intro K _ _ hK h3 J hJW hJsn hJq P _ hPc
  have hJc : IsComponentOf J ⊤ := ⟨le_top, hJsn, hJq⟩
  have hJR : J ≤ GLAPPrimeCore 5 K := hJW.trans (Subgroup.commutator_le_left _ _)
  obtain ⟨hS, hnc⟩ := hFi _ hK.fi
  have hcov : ∀ C : Subgroup K, C.Normal → C ⊔ GLAPPrimeCore 5 K = ⊤ → C = ⊤ :=
    fun C _ hC => i227cmp_cover_eq_top hK hS hnc C hC
  set O : Set (Subgroup K) := Set.range fun k : K => GLBConj k J with hO
  have hOc : ∀ L ∈ O, IsComponentOf L ⊤ := by
    rintro _ ⟨k, rfl⟩
    exact isComponentOf_gLBConj hJc k
  rcases i227cmp_orbit_dichotomy hK.perfect J with h5 | hnorm
  · change 5 ≤ Nat.card O at h5
    refine i227cmp_core_all O ?_ (by omega) ?_ ?_ P hPc
    · rintro k _ ⟨k', rfl⟩
      exact ⟨k' * k, by simp only [gLBConj_gLBConj]⟩
    · intro L hL
      obtain ⟨x, hx, hxc⟩ := exists_orderOf_eq_prime_not_mem_center (hOc L hL).2.2
        Nat.prime_three (by norm_num) (i227cmp_three_dvd h3 (hOc L hL))
      refine ⟨x, x.2, ?_, ?_⟩
      · rw [← hx]; exact Subgroup.orderOf_coe x
      · by_contra hno
        push Not at hno
        refine hxc (Subgroup.mem_center_iff.2 fun g => ?_)
        exact Subtype.ext (hno g g.2).symm
    · intro L hL L' hL' hne a ha b hb
      have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' (hOc L hL)
        (hOc L' hL') hne
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot] at hmem
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [hmem, one_mul]
  · have hN : J.Normal := ⟨fun n hn g => by
      have : n ∈ GLBConj g J := by rw [hnorm g]; exact hn
      exact mem_gLBConj.1 this⟩
    exact (i227cmp_not_normal hK.perfect hJR hJq (hOut K hK.kgroup hJc) hcov).elim

theorem i227cmp_fi22_simple
    {X : Type} [Group X] (h : IsFiTwentyTwo X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨e⟩ := h
  obtain ⟨hs, hc⟩ := I1420.fi22_facts
  have hX : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  refine ⟨hX, ?_⟩
  by_contra hno
  push Not at hno
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hno }
  have hp := IsSimpleGroup.prime_card (α := X)
  rw [Nat.card_congr e.toEquiv, hc] at hp
  have := hp.eq_one_or_self_of_dvd 2 (by norm_num)
  omega

section Certified


theorem i227_comps_holds : I22_7Comps :=
  i227cmp_main
    (fun _ _ _ hQ _ hJ => outer_solvable_of_component_certified hQ hJ)
    (fun _ _ h => i227cmp_fi22_simple h)

end Certified

end CFSG.HardMathSupport.Solomon.Coordinator
