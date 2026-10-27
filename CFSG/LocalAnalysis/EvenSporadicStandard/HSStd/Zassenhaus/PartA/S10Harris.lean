module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10HS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Odd

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
  CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

theorem s10_nonab6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

theorem s10_perfect6 : commutator (alternatingGroup (Fin 6)) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6)))
    with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := s10_nonab6
    apply hab
    have : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 6)) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem s10_conj_mem_commutator (s : alternatingGroup (Fin 6)) :
    (MulAut.conj s : MulAut (alternatingGroup (Fin 6))) ∈
      commutator (MulAut (alternatingGroup (Fin 6))) := by
  have hs : s ∈ ⁅(⊤ : Subgroup (alternatingGroup (Fin 6))),
      (⊤ : Subgroup (alternatingGroup (Fin 6)))⁆ := by
    rw [← _root_.commutator_def, s10_perfect6]
    trivial
  have h1 := Subgroup.mem_map_of_mem
    (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) hs
  rw [Subgroup.map_commutator] at h1
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top h1

section Main

set_option linter.unusedSectionVars false


theorem card_z2_mulAut_alt6 : Nat.card (Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) =
    2880 := by
  rw [Nat.card_prod, Wreath.card_multiplicative_zmod_two,
    CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]

theorem harris_hs (hHiS : Harris311HiS) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.SectionRank.IsKGroupCat X)
    (hO : fusionOddCore X = ⊥) {t : X} (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set X)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (g : X) (hg : orderOf g = 3)
    (hgS : Nonempty (↥(centralizer ({g} : Set X)) ⧸ fusionOddCore ↥(centralizer ({g} : Set X)) ≃*
      Equiv.Perm (Fin 5))) :
    Nonempty (X ≃* NativeSporadic.HS) := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  set K : Subgroup X := normalClosureOf (centralizerDerived t) with hKdef
  have hK : IsSporadic ↥K .HS := hHiS X hKX hO t ht ⟨e⟩ g hg hgS
  obtain ⟨ψ⟩ := hK
  have : K.Normal := Subgroup.normalClosure_normal
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have hcardC : Nat.card ↥(centralizer ({t} : Set X)) = 2880 := by
    rw [Nat.card_congr e.toEquiv, card_z2_mulAut_alt6]
  have hKcard : Nat.card K = 44352000 := card_eq_of_isSporadic_hs ⟨ψ⟩
  have hJK : centralizerDerived t ≤ K := Subgroup.subset_normalClosure
  set R : Subgroup X := centralizer (K : Set X) with hRdef
  have htR : t ∉ R := by
    intro htR
    have hle : K ≤ centralizer ({t} : Set X) := fun k hk =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htR k hk)
    have := Subgroup.card_le_of_le hle
    omega
  set C : Subgroup X := centralizer ({t} : Set X) with hCdef
  have htC : t ∈ C := mem_centralizer_singleton_iff.2 rfl
  have het : (e ⟨t, htC⟩).2 = 1 := by
    have hcent : (e ⟨t, htC⟩).2 ∈ Subgroup.center (MulAut (alternatingGroup (Fin 6))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hz : (⟨t, htC⟩ : ↥C) ∈ Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro g'
        exact Subtype.ext (mem_centralizer_singleton_iff.1 g'.2)
      have := (Subgroup.mem_center_iff.1 hz (e.symm (1, g))).symm
      have h2 := congrArg (fun x => (e x).2) this
      simpa using h2.symm
    rw [center_mulAut_eq_bot s10_nonab6, mem_bot] at hcent
    exact hcent
  have het1 : (e ⟨t, htC⟩).1 ≠ 1 := by
    intro h1
    have : e ⟨t, htC⟩ = 1 := Prod.ext h1 het
    have h3 : (⟨t, htC⟩ : ↥C) = 1 := e.injective (by rw [this, map_one])
    have h4 : t = 1 := congrArg Subtype.val h3
    rw [h4, orderOf_one] at ht
    omega
  have hfix : ∀ r ∈ R, t * r = r * t → r = 1 := by
    intro r hr hrt
    have hrC : r ∈ C := mem_centralizer_singleton_iff.2 hrt.symm
    let π₂ : ↥C →* MulAut (alternatingGroup (Fin 6)) := (MonoidHom.snd _ _).comp e.toMonoidHom
    have hπ₂ : Function.Surjective π₂ := fun a => ⟨e.symm (1, a), by simp [π₂]⟩
    have hmap : (commutator ↥C).map π₂ = commutator (MulAut (alternatingGroup (Fin 6))) := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 hπ₂, _root_.commutator_def]
    have hcommAut : ∀ s : alternatingGroup (Fin 6),
        π₂ ⟨r, hrC⟩ * MulAut.conj s = MulAut.conj s * π₂ ⟨r, hrC⟩ := by
      intro s
      have hs : (MulAut.conj s : MulAut (alternatingGroup (Fin 6))) ∈ (commutator ↥C).map π₂ := by
        rw [hmap]
        exact s10_conj_mem_commutator s
      obtain ⟨j, hj, hjs⟩ := hs
      have hjK : (j : X) ∈ K := hJK ⟨j, hj, rfl⟩
      have h1 : r * (j : X) = (j : X) * r := mem_centralizer_iff.1 hr (j : X) hjK |>.symm
      have h2 : (⟨r, hrC⟩ : ↥C) * j = j * ⟨r, hrC⟩ := Subtype.ext h1
      rw [← hjs, ← map_mul, ← map_mul, h2]
    have ha1 : π₂ ⟨r, hrC⟩ = 1 := eq_one_of_commute_conj s10_nonab6 _ hcommAut
    have her : e ⟨r, hrC⟩ = ((e ⟨r, hrC⟩).1, 1) := Prod.ext rfl ha1
    rcases Wreath.zmod2_cases (e ⟨r, hrC⟩).1 with h1 | h1
    · have : e ⟨r, hrC⟩ = 1 := by rw [her, h1]; rfl
      have h3 : (⟨r, hrC⟩ : ↥C) = 1 := e.injective (by rw [this, map_one])
      exact congrArg Subtype.val h3
    · exfalso
      have h2 := (Wreath.zmod2_cases (e ⟨t, htC⟩).1).resolve_left het1
      have : e ⟨r, hrC⟩ = e ⟨t, htC⟩ := by
        rw [her, h1, ← h2]
        exact Prod.ext rfl het.symm
      have h3 : (⟨r, hrC⟩ : ↥C) = ⟨t, htC⟩ := e.injective this
      have h4 : r = t := congrArg Subtype.val h3
      exact htR (h4 ▸ hr)
  have hinv := inv_of_centralizer_eq_bot (O := R) ht2
    (fun o ho => (inferInstance : R.Normal).conj_mem o ho t) hfix
  have hRodd : Odd (Nat.card R) := by
    by_contra hodd
    have h2 : 2 ∣ Nat.card R := by
      rcases Nat.not_odd_iff_even.1 hodd with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxx : (x : X) * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      exact congrArg Subtype.val this
    have hx1 : (x : X) = 1 := by
      apply hfix x x.2
      have h3 := hinv.1 x x.2
      have h4 : (x : X)⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      rw [h4] at h3
      calc t * (x : X) = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [h3]
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    omega
  have hRbot : R = ⊥ := by
    have := le_fusionOddCore_of_odd' (N := R) hRodd
    rw [hO] at this
    exact le_bot_iff.1 this
  have hKtop : K = ⊤ := eq_top_of_card_centralizer_hs K ⟨ψ⟩ hRbot ht hcardC
  exact ⟨((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv).symm.trans ψ⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
