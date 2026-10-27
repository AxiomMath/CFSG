module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.AutInn
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Derived
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.InnEquiv
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Fixed
import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.SolomonRed
open scoped commutatorElement
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt6IsSimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt6NonAb : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
  exists_noncommute_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))

theorem alt6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem natCard_mult_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]

theorem mul_self_mult_zmod_two (x : Multiplicative (ZMod 2)) : x * x = 1 := by
  revert x
  decide

structure Cfg (G : Type) [Group G] [Finite G] (S : Subgroup G) [S.Normal] (t : G) : Prop where
  simple : IsSimpleGroup ↥S
  nonab : ∃ a b : ↥S, a * b ≠ b * a
  cent : centralizer (S : Set G) = ⊥
  ord : orderOf t = 2

section Setup

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal] {t : G}

theorem not_mem_center (h : Cfg G S t) : t ∉ Subgroup.center G := by
  intro htc
  have hmem : t ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    exact Subgroup.mem_center_iff.mp htc s
  rw [h.cent, Subgroup.mem_bot] at hmem
  have h2 := h.ord
  rw [hmem, orderOf_one] at h2
  omega

theorem harris_setting (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Setting G t ((MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range.map (embA ζ)) := by
  haveI := alt6IsSimple
  haveI := h.simple
  have hO : fusionOddCore G = ⊥ := fusionOddCore_eq_bot S h.nonab h.cent
  exact setting_of_RHyp (rhyp_mulAut alt6NonAb) hO h.ord ζ (not_mem_center h)

theorem harris_derived_eq
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    centralizerDerived t =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map
        (embA ζ) := by
  rw [centralizerDerived_eq_map ζ, commutator_mulAut_alt6]

theorem harris_derived_le (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    centralizerDerived t ≤ S := by
  haveI := h.simple
  have hfd : FixedData G S := by
    obtain ⟨a, b, hab⟩ := h.nonab
    exact ⟨inferInstance, h.simple, ⟨a, a.2, b, b.2, fun h' => hab (Subtype.ext h')⟩, h.cent⟩
  rw [harris_derived_eq ζ]
  exact setting_le_of_fixedData (harris_setting h ζ) hfd

theorem harris_derived_equiv
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nonempty (↥(centralizerDerived t) ≃* alternatingGroup (Fin 6)) := by
  haveI := alt6IsSimple
  obtain ⟨hiso⟩ := nonempty_mulEquiv_range_conj alt6NonAb
  exact ⟨(MulEquiv.subgroupCongr (harris_derived_eq ζ)).trans
    ((Subgroup.equivMapOfInjective _ (embA ζ) (embA_injective ζ)).symm.trans hiso)⟩

theorem card_derived
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥(centralizerDerived t) = 360 := by
  obtain ⟨e⟩ := harris_derived_equiv ζ
  rw [Nat.card_congr e.toEquiv, alt6_card]

theorem derived_isPerfect
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Group.IsPerfect ↥(centralizerDerived t) := by
  haveI := alt6IsSimple
  obtain ⟨e⟩ := harris_derived_equiv ζ
  haveI : IsSimpleGroup ↥(centralizerDerived t) := e.isSimpleGroup
  refine isPerfect_of_simple_of_nonab' ?_
  obtain ⟨a, b, hab⟩ := alt6NonAb
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem derived_le_centralizer : centralizerDerived t ≤ centralizer ({t} : Set G) :=
  Subgroup.map_subtype_le _

theorem card_centralizer_eq
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥(centralizer ({t} : Set G)) = 2880 := by
  rw [Nat.card_congr ζ.toEquiv, Nat.card_prod, natCard_mult_zmod_two,
    CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]

theorem commutator_mem_derived {c d : G} (hc : c ∈ centralizer ({t} : Set G))
    (hd : d ∈ centralizer ({t} : Set G)) : c * d * c⁻¹ * d⁻¹ ∈ centralizerDerived t := by
  refine ⟨⁅(⟨c, hc⟩ : ↥(centralizer ({t} : Set G))), ⟨d, hd⟩⁆, ?_, ?_⟩
  · rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rfl

theorem sq_mem_derived
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    {c : G} (hc : c ∈ centralizer ({t} : Set G)) : c * c ∈ centralizerDerived t := by
  rw [harris_derived_eq ζ]
  obtain ⟨a, ha⟩ := outSq_alternatingGroup_six (ζ ⟨c, hc⟩).2
  have hsq : ζ (⟨c, hc⟩ * ⟨c, hc⟩) = (1, (ζ ⟨c, hc⟩).2 * (ζ ⟨c, hc⟩).2) := by
    rw [map_mul]
    ext
    · exact mul_self_mult_zmod_two _
    · rfl
  refine ⟨(ζ ⟨c, hc⟩).2 * (ζ ⟨c, hc⟩).2, MonoidHom.mem_range.mpr ⟨a, ?_⟩, ?_⟩
  · refine MulEquiv.ext fun x => ?_
    simpa [MulAut.conj_apply, MulAut.mul_apply] using (ha x).symm
  · rw [embA_apply, ← hsq]
    simp

theorem range_fixed_eq (t : G) :
    (S.subtype.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype).range =
      S ⊓ centralizer ({t} : Set G) := by
  ext g
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s.2, (mem_fixedSubgroup_conjNormal_iff t s).mp hs⟩
  · rintro ⟨hgS, hgC⟩
    exact ⟨⟨⟨g, hgS⟩, (mem_fixedSubgroup_conjNormal_iff t ⟨g, hgS⟩).mpr hgC⟩, rfl⟩

theorem card_fixedSubgroup_eq (t : G) :
    Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) =
      Nat.card ↥(S ⊓ centralizer ({t} : Set G)) := by
  have hφ : Function.Injective
      (S.subtype.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype) :=
    S.subtype_injective.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype_injective
  exact Nat.card_congr ((MonoidHom.ofInjective hφ).trans
    (MulEquiv.subgroupCongr (range_fixed_eq t))).toEquiv

theorem card_fixed_dvd
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ∣ 2880 := by
  rw [card_fixedSubgroup_eq, ← card_centralizer_eq ζ]
  exact Subgroup.card_dvd_of_le inf_le_right

theorem dvd_card_fixed (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    360 ∣ Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) := by
  rw [card_fixedSubgroup_eq, ← card_derived ζ]
  exact Subgroup.card_dvd_of_le (le_inf (harris_derived_le h ζ) derived_le_centralizer)

theorem commutator_fixed_equiv (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nonempty (↥(commutator ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S))) ≃*
      alternatingGroup (Fin 6)) := by
  have hφ : Function.Injective
      (S.subtype.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype) :=
    S.subtype_injective.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype_injective
  have hmap : (commutator ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S))).map
      (S.subtype.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype) =
      centralizerDerived t := by
    have h1 : (commutator ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S))).map
        (S.subtype.comp (fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)).subtype) =
        ⁅S ⊓ centralizer ({t} : Set G), S ⊓ centralizer ({t} : Set G)⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, range_fixed_eq]
    have hX : centralizerDerived t = ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
      unfold centralizerDerived
      exact Subgroup.map_subtype_commutator _
    have hXle : centralizerDerived t ≤ S ⊓ centralizer ({t} : Set G) :=
      le_inf (harris_derived_le h ζ) derived_le_centralizer
    have hperf : ⁅centralizerDerived t, centralizerDerived t⁆ = centralizerDerived t :=
      Subgroup.isPerfect_iff.mp (derived_isPerfect ζ)
    rw [h1]
    apply le_antisymm
    · rw [hX]
      exact Subgroup.commutator_mono inf_le_right inf_le_right
    · calc centralizerDerived t = ⁅centralizerDerived t, centralizerDerived t⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono hXle hXle
  obtain ⟨e⟩ := harris_derived_equiv ζ
  exact ⟨((commutator ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S))).equivMapOfInjective
    _ hφ).trans ((MulEquiv.subgroupCongr hmap).trans e)⟩

theorem card_subgroupOf_eq (A B : Subgroup G) :
    Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
  rw [← Subgroup.subgroupOf_map_subtype A B]
  exact (Subgroup.card_map_of_injective B.subtype_injective).symm

theorem card_centralizer_le_mul (t : G) {k : ℕ} (hk : Nat.card G ≤ k * Nat.card ↥S) :
    Nat.card ↥(centralizer ({t} : Set G)) ≤ k * Nat.card ↥(S ⊓ centralizer ({t} : Set G)) := by
  have hKC := card_subgroupOf_eq S (centralizer ({t} : Set G))
  have h1 := Subgroup.card_mul_index (S.subgroupOf (centralizer ({t} : Set G)))
  have h2 : (S.subgroupOf (centralizer ({t} : Set G))).index ∣ S.index :=
    Subgroup.relIndex_dvd_index_of_normal S (centralizer ({t} : Set G))
  have h3 := Subgroup.card_mul_index S
  have hSpos : 0 < Nat.card ↥S := Nat.card_pos
  have hidxS : S.index ≤ k := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥S * (k + 1) ≤ Nat.card ↥S * S.index := Nat.mul_le_mul_left _ hlt
    nlinarith
  have hidxK : (S.subgroupOf (centralizer ({t} : Set G))).index ≤ S.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2
  calc Nat.card ↥(centralizer ({t} : Set G))
      = Nat.card ↥(S.subgroupOf (centralizer ({t} : Set G))) *
        (S.subgroupOf (centralizer ({t} : Set G))).index := h1.symm
    _ ≤ Nat.card ↥(S ⊓ centralizer ({t} : Set G)) * k := by
        rw [hKC]
        exact Nat.mul_le_mul_left _ (hidxK.trans hidxS)
    _ = k * Nat.card ↥(S ⊓ centralizer ({t} : Set G)) := mul_comm _ _

theorem outerKlein_of_card_le (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (hF : Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ≤ 720) :
    OuterKlein (MulAut.conjNormal t : MulAut ↥S) := by
  haveI : (S.subgroupOf (centralizer ({t} : Set G))).Normal :=
    Subgroup.Normal.comap inferInstance (centralizer ({t} : Set G)).subtype
  have hKcard : Nat.card ↥(S.subgroupOf (centralizer ({t} : Set G))) ≤ 720 := by
    rw [card_subgroupOf_eq, ← card_fixedSubgroup_eq]
    exact hF
  have hidx : 2 < (S.subgroupOf (centralizer ({t} : Set G))).index := by
    by_contra hle
    push Not at hle
    have h1 := Subgroup.card_mul_index (S.subgroupOf (centralizer ({t} : Set G)))
    have h2 : Nat.card ↥(S.subgroupOf (centralizer ({t} : Set G))) *
        (S.subgroupOf (centralizer ({t} : Set G))).index ≤
        Nat.card ↥(S.subgroupOf (centralizer ({t} : Set G))) * 2 := Nat.mul_le_mul_left _ hle
    rw [h1, card_centralizer_eq ζ] at h2
    omega
  obtain ⟨c₁, c₂, h1, h2, h12⟩ :=
    exists_three_of_index_gt_two (S.subgroupOf (centralizer ({t} : Set G))) hidx
  have hmem : ∀ c : ↥(centralizer ({t} : Set G)), (c : G) * t = t * c := fun c =>
    Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hsqS : ∀ c : ↥(centralizer ({t} : Set G)), (c : G) * c ∈ S := fun c =>
    harris_derived_le h ζ (sq_mem_derived ζ c.2)
  have hin := conjNormal_mem_range_iff (S := S) h.cent
  refine ⟨MulAut.conjNormal (c₁ : G), MulAut.conjNormal (c₂ : G), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hmem c₁]
  · rw [← map_mul, ← map_mul, hmem c₂]
  · rw [← map_mul, hin]
    exact hsqS c₁
  · rw [← map_mul, hin]
    exact hsqS c₂
  · have hc : (MulAut.conjNormal (c₁ : G) * MulAut.conjNormal (c₂ : G) *
        (MulAut.conjNormal (c₁ : G))⁻¹ * (MulAut.conjNormal (c₂ : G))⁻¹ : MulAut ↥S) =
        MulAut.conjNormal ((c₁ : G) * c₂ * (c₁ : G)⁻¹ * (c₂ : G)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hc, hin]
    exact harris_derived_le h ζ (commutator_mem_derived c₁.2 c₂.2)
  · rw [hin]
    intro hS1
    exact h1 (Subgroup.mem_subgroupOf.mpr hS1)
  · rw [hin]
    intro hS2
    exact h2 (Subgroup.mem_subgroupOf.mpr hS2)
  · rw [← map_mul, hin]
    intro hS12
    exact h12 (Subgroup.mem_subgroupOf.mpr (by simpa using hS12))

theorem t_not_mem_derived (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    t ∉ centralizerDerived t := by
  haveI := alt6IsSimple
  rw [harris_derived_eq ζ]
  rintro ⟨b, -, hbt⟩
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h1 : ζ.symm (1, b) = ⟨t, htC⟩ := Subtype.ext hbt
  have h2 : ζ ⟨t, htC⟩ = (1, b) := by
    rw [← h1]
    exact ζ.apply_symm_apply _
  have hcentral : ∀ b' : MulAut (alternatingGroup (Fin 6)), b' * b = b * b' := by
    intro b'
    have hcomm : ζ.symm (1, b') * ⟨t, htC⟩ = ⟨t, htC⟩ * ζ.symm (1, b') :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (ζ.symm (1, b')).2)
    have := congrArg ζ hcomm
    rw [map_mul, map_mul, h2, MulEquiv.apply_symm_apply] at this
    exact congrArg Prod.snd this
  have hb1 : b = 1 := (rhyp_mulAut alt6NonAb).center b fun y => hcentral y
  have h3 : (⟨t, htC⟩ : ↥(centralizer ({t} : Set G))) = 1 := by
    apply ζ.injective
    rw [h2, hb1, map_one]
    rfl
  have h4 : t = 1 := congrArg Subtype.val h3
  have h5 := h.ord
  rw [h4, orderOf_one] at h5
  omega

end Setup

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
