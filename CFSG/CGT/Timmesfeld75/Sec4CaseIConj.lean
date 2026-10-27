module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIBender
public import CFSG.CGT.Timmesfeld75.Sec4Two

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open CFSG.BenderSuzuki (PSU3Model IsBenderGroup)

section Count

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.card_conj_gt
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card T = Nat.card (normIn T T₁) * 2 ^ f ∧
      (2 ^ f) ^ 3 < Set.ncard {U : Subgroup G | ∃ y ∈ sec4Y T T₁ T₂, U = conjSubgroup y T} := by
  obtain ⟨f, hf2, hcardT, hN, ⟨e⟩⟩ :=
    h.sec4_two_of_le hAsc hq le_rfl h.sec4Y_le_normalizer h.normalClosure_sec4Y
  refine ⟨f, hf2, hcardT, ?_⟩
  have hTK : T ≤ sec4Y T T₁ T₂ := left_le_sec4Y
  have hstrong := h.strongWC_img_of_le (K := sec4Y T T₁ T₂) h.sec4Y_le_normalizer hTK
  have hTZ := h.img_inf_center_eq_bot_of_le (K := sec4Y T T₁ T₂) le_rfl h.sec4Y_le_normalizer hTK
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hcardbar : Nat.card ((T.subgroupOf (sec4Y T T₁ T₂)).map
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))) = 2 ^ f := by
    have h1 := card_img_mul_card_inf (K := sec4Y T T₁ T₂) (N := sec4N T T₁ T₂) (T := T) hTK
    rw [h.inf_sec4N_eq, hcardT] at h1
    exact Nat.eq_of_mul_eq_mul_left hLpos (by linarith)
  have hT'strong := hstrong.map_center hTZ
  have hT'card : Nat.card (((T.subgroupOf (sec4Y T T₁ T₂)).map
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).map
        (QuotientGroup.mk' (Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
          (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))))  = 2 ^ f := by
    rw [card_map_mk_center_of_inf_eq_bot hTZ, hcardbar]
  have hBender := IsBenderGroup.isPSU3 f hf2 e
  have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hcount := exists_card_conj_gt hBender (fusionBenderBorel_of_psu3 hf2 e) hT'strong.1
    hT'card hq1
  let π : ↥(sec4Y T T₁ T₂) →* (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) :=
    (QuotientGroup.mk' (Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).comp
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let F : Subgroup G → Subgroup ((↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸ Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
        (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) :=
    fun U => (U.subgroupOf (sec4Y T T₁ T₂)).map π
  have hsub : {C | ∃ g, C = conjSubgroup g (((T.subgroupOf (sec4Y T T₁ T₂)).map
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).map
        (QuotientGroup.mk' (Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
          (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))))} ⊆
      F '' {U : Subgroup G | ∃ y ∈ sec4Y T T₁ T₂, U = conjSubgroup y T} := by
    rintro C ⟨g, rfl⟩
    obtain ⟨y, rfl⟩ := hπ g
    refine ⟨conjSubgroup (y : G) T, ⟨y, y.2, rfl⟩, ?_⟩
    show ((conjSubgroup (y : G) T).subgroupOf (sec4Y T T₁ T₂)).map π = _
    rw [← conjSubgroup_subgroupOf, map_conjSubgroup, Subgroup.map_map]
  have hfin : {U : Subgroup G | ∃ y ∈ sec4Y T T₁ T₂, U = conjSubgroup y T}.Finite :=
    Set.toFinite _
  calc (2 ^ f) ^ 3 < _ := hcount
    _ ≤ (F '' {U : Subgroup G | ∃ y ∈ sec4Y T T₁ T₂, U = conjSubgroup y T}).ncard :=
      Set.ncard_le_ncard hsub (hfin.image F)
    _ ≤ _ := Set.ncard_image_le hfin

end Count

end CFSG.CGT.Timmesfeld75
