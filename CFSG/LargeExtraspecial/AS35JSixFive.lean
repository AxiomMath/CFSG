module

public import CFSG.LargeExtraspecial.AS35HSixEightB
public import CFSG.LargeExtraspecial.AS35JThreeT
public import CFSG.LargeExtraspecial.AS35ESixSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary

namespace AS35J

theorem center_commutator_of_mulEquiv_timmesfeldPSU {X : Type} [Group X] {n : ℕ} (hn : 4 ≤ n)
    (e : X ≃* timmesfeldPSU n) :
    center X = ⊥ ∧ IsSimpleGroup (commutator X) ∧
      ∃ x y : commutator X, x * y ≠ y * x := by
  set e' : X ≃* PG n := e.trans (AS35U.pgEquiv (by omega)).symm with he'
  have hcomm : commutator X = ⊤ := (commutator_eq_top_congr e').2 (commutator_PG hn)
  refine ⟨?_, ?_, ?_⟩
  · have h := Subgroup.map_center_eq e'
    rw [center_PG hn] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).1 h
  · have := isSimpleGroup_PG hn
    exact (((MulEquiv.subgroupCongr hcomm).trans Subgroup.topEquiv).trans e').isSimpleGroup
  · have hm2 : 2 ≤ n := by omega
    obtain ⟨u, hu0, hu, hvu⟩ := exists_partner_frob (isoVec_ne_zero hm2) (isoVec_isotropic hm2)
    have hnc : tq (isoVec hm2) * tq u ≠ tq u * tq (isoVec hm2) := by
      intro h
      have h1 := (tq_commute_iff (by omega) (isoVec_ne_zero hm2) (isoVec_isotropic hm2) hu0
        hu).mp h
      rw [hvu] at h1
      exact one_ne_zero h1
    refine ⟨⟨e'.symm (tq (isoVec hm2)), hcomm ▸ mem_top _⟩, ⟨e'.symm (tq u), hcomm ▸ mem_top _⟩,
      fun h => hnc ?_⟩
    have h1 := congrArg (fun x : commutator X => e' x) h
    simpa using h1

end AS35J

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem mul_self_of_mem_DbarAsc_J {d : S.O} (hd : d ∈ S.DbarAsc) : d * d = 1 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

theorem conj_mem_DbarAsc_J {g : S.O} (hg : g ∈ closure S.DbarAsc) {d : S.O}
    (hd : d ∈ S.DbarAsc) : g * d * g⁻¹ ∈ S.DbarAsc := by
  have key : ∀ e ∈ S.DbarAsc, ∀ d ∈ S.DbarAsc, e * d * e⁻¹ ∈ S.DbarAsc := by
    rintro _ ⟨s, -, hsM, rfl⟩ _ ⟨t, ht, htM, rfl⟩
    refine ⟨s * t * s⁻¹, S.conj_mem_DSet hsM ht,
      S.M.mul_mem (S.M.mul_mem hsM htM) (S.M.inv_mem hsM), ?_⟩
    have e : (⟨s * t * s⁻¹, S.M.mul_mem (S.M.mul_mem hsM htM) (S.M.inv_mem hsM)⟩ : S.M) =
        ⟨s, hsM⟩ * ⟨t, htM⟩ * ⟨s, hsM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hP : ∀ x ∈ closure S.DbarAsc, ∀ d ∈ S.DbarAsc,
      x * d * x⁻¹ ∈ S.DbarAsc ∧ x⁻¹ * d * x ∈ S.DbarAsc := by
    intro x hx
    induction hx using closure_induction with
    | mem e he =>
      intro d hd
      have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (S.mul_self_of_mem_DbarAsc_J he)
      refine ⟨key e he d hd, ?_⟩
      rw [hinv]
      have := key e he d hd
      rwa [hinv] at this
    | one => exact fun d hd => ⟨by simpa using hd, by simpa using hd⟩
    | mul x y _ _ ihx ihy =>
      intro d hd
      refine ⟨?_, ?_⟩
      · rw [show x * y * d * (x * y)⁻¹ = x * (y * d * y⁻¹) * x⁻¹ by group]
        exact (ihx _ (ihy d hd).1).1
      · rw [show (x * y)⁻¹ * d * (x * y) = y⁻¹ * (x⁻¹ * d * x) * y by group]
        exact (ihy _ (ihx d hd).2).2
    | inv x _ ih =>
      intro d hd
      refine ⟨(ih d hd).2, ?_⟩
      rw [inv_inv]
      exact (ih d hd).1
  exact (hP g hg d hd).1

theorem sixFiveTransvection_J (hS : S.SixHyp) (h65 : S.SixFiveConcl) :
    (∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, a * b = b * a → a ≠ b →
      ∃ c ∈ S.DbarAsc, c * a = a * c ∧ c * b ≠ b * c) ∧
    (∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, orderOf (a * b) = 3 →
      ∃ c ∈ S.DbarAsc, c * a = a * c ∧ c * b = b * c) := by
  have hLM : closure S.DbarAsc ≤ S.Mbar := by
    rw [closure_le]
    rintro _ ⟨t, -, htM, rfl⟩
    exact ⟨⟨t, htM⟩, rfl⟩
  have : Finite S.Mbar := Finite.of_surjective _ S.ρ.rangeRestrict_surjective
  have : Finite (closure S.DbarAsc) := Finite.of_injective _ (Subgroup.inclusion_injective hLM)
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  obtain ⟨e⟩ := h65.psu
  obtain ⟨hZ, hsimp, hna⟩ := AS35J.center_commutator_of_mulEquiv_timmesfeldPSU
    h65.four_le_width e
  obtain ⟨h1, h2⟩ := AS35J.transvection_props_of_quotient
    (D := Subtype.val ⁻¹' S.DbarAsc) closure_closure_coe_preimage
    ⟨⟨S.ρ ⟨t, htM⟩, subset_closure (S.ρ_mem_DbarAsc ht htM)⟩, S.ρ_mem_DbarAsc ht htM⟩
    (fun a ha b hb => by
      obtain ⟨g, hg, hgab⟩ := h65.conj _ ha _ hb
      exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩)
    (fun g a ha => S.conj_mem_DbarAsc_J g.2 ha)
    (fun a ha => Subtype.ext (S.mul_self_of_mem_DbarAsc_J ha))
    (fun a ha b hb => by
      rw [← Subgroup.orderOf_coe]
      exact h65.three _ ha _ hb) hZ hsimp hna
  refine ⟨fun a ha b hb hab hne => ?_, fun a ha b hb hab3 => ?_⟩
  · obtain ⟨c, hc, hca, hcb⟩ := h1 ⟨a, subset_closure ha⟩ ha ⟨b, subset_closure hb⟩ hb
      (Subtype.ext hab) (fun h => hne (congrArg Subtype.val h))
    exact ⟨c, hc, congrArg Subtype.val hca, fun h => hcb (Subtype.ext h)⟩
  · obtain ⟨c, hc, hca, hcb⟩ := h2 ⟨a, subset_closure ha⟩ ha ⟨b, subset_closure hb⟩ hb
      (by rw [← Subgroup.orderOf_coe]; exact hab3)
    exact ⟨c, hc, congrArg Subtype.val hca, congrArg Subtype.val hcb⟩

end Setting

namespace S14

theorem sixFiveTransvectionStmt : SixFiveTransvectionStmt :=
  fun _ _ _ S hS h65 => S.sixFiveTransvection_J hS h65

end S14

end CFSG.LargeExtraspecial
