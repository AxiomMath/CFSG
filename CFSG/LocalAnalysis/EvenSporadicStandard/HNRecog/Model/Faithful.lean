module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Rho
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Sigma

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Recognition.HSMultiplier CFSG.EvenSporadicStandard.TwoHS
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem injective_of_quasisimple {E P : Type*} [Group E] [Group P] (ρ : E →* P)
    (hperf : Group.IsPerfect E) (hZ : Nat.card (center E) = 2)
    (hsimple : IsSimpleGroup (E ⧸ center E)) {t : E} (ht : t ∈ center E) (hρt : ρ t ≠ 1) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have htne : t ≠ 1 := fun h => hρt (by rw [h, map_one])
  by_cases hxz : x ∈ center E
  · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center E))).1 hZ
    have h1 : (⟨x, hxz⟩ : ↥(center E)) = y := hy _ (fun h => hx1 (congrArg Subtype.val h))
    have h2 : (⟨t, ht⟩ : ↥(center E)) = y := hy _ (fun h => htne (congrArg Subtype.val h))
    have : x = t := congrArg Subtype.val (h1.trans h2.symm)
    exact hρt (by rw [← this, hx])
  · let q : E →* E ⧸ center E := QuotientGroup.mk' (center E)
    have hQ : ((ρ.ker).map q).Normal :=
      Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective (center E))
    have hQne : (ρ.ker).map q ≠ ⊥ := by
      intro h
      have : q x ∈ (ρ.ker).map q := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact hxz ((QuotientGroup.eq_one_iff x).1 this)
    have hQtop : (ρ.ker).map q = ⊤ := by
      have := hQ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ρ.ker).map q) with h | h
      · exact absurd h hQne
      · exact h
    have hfac : ∀ e : E, ∃ c ∈ center E, ρ e = ρ c := by
      intro e
      have he : q e ∈ (ρ.ker).map q := by rw [hQtop]; trivial
      obtain ⟨n, hn, hne⟩ := he
      refine ⟨n⁻¹ * e, ?_, ?_⟩
      · rw [← QuotientGroup.ker_mk' (center E), MonoidHom.mem_ker]
        show q (n⁻¹ * e) = 1
        rw [map_mul, map_inv, hne, inv_mul_cancel]
      · have hn' : ρ n = 1 := hn
        rw [map_mul, map_inv, hn', inv_one, one_mul]
    have hcomm : commutator E ≤ ρ.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨c, hc, hac⟩ := hfac a
      obtain ⟨d, hd, hbd⟩ := hfac b
      rw [MonoidHom.mem_ker, map_commutatorElement, hac, hbd, ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 hc) d).symm, map_one]
    rw [Group.isPerfect_def.1 hperf] at hcomm
    exact hρt (hcomm trivial)

section Simple


theorem HSCtx.isSimpleGroup_quotient (hΛ : HSCtx) : IsSimpleGroup (HSCover ⧸ center HSCover) := by
  obtain ⟨e⟩ := hΛ.quotient
  exact isSimpleGroup_of_mulEquiv e CFSG.Sporadic.HS.isSimpleGroup_HS

end Simple

section Faithful


theorem HSCtx.rho1408_injective (hΛ : HSCtx) : Function.Injective rho1408 := by
  exact injective_of_quasisimple rho1408 hΛ.perfect hΛ.card_center
    (HSCtx.isSimpleGroup_quotient hΛ)
    (t := relVal h1408R25) (relVal_mem_center h1408R25_mem) rho1408_relVal_R25_ne_one

end Faithful

end CFSG.EvenSporadicStandard.HNRecog
