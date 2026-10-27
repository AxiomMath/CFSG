module

public import CFSG.CGT.Timmesfeld75.Sec4TwoStruct
public import CFSG.CGT.Timmesfeld75.Sec4TwoBender

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement
open CFSG.BenderSuzuki (PSU3Model)

section Main

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem img_map_iota_eq {X₁ Y N M : Subgroup G} (hXY : X₁ ≤ Y) (hT : T ≤ X₁)
    [(M.subgroupOf X₁).Normal] [(N.subgroupOf Y).Normal]
    (ι : (↥X₁ ⧸ M.subgroupOf X₁) →* (↥Y ⧸ N.subgroupOf Y))
    (hι : ∀ x : ↥X₁, ι (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion hXY x)) :
    ((T.subgroupOf X₁).map (QuotientGroup.mk' (M.subgroupOf X₁))).map ι =
      (T.subgroupOf Y).map (QuotientGroup.mk' (N.subgroupOf Y)) := by
  rw [Subgroup.map_map]
  have h1 : ι.comp (QuotientGroup.mk' (M.subgroupOf X₁)) =
      (QuotientGroup.mk' (N.subgroupOf Y)).comp (Subgroup.inclusion hXY) :=
    MonoidHom.ext fun x => hι x
  rw [h1, ← Subgroup.map_map]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
  · intro hy
    exact ⟨⟨(y : G), hT (Subgroup.mem_subgroupOf.1 hy)⟩,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hy), rfl⟩

theorem Sec4Hyp.exists_L2_embedding (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {K : Subgroup G}
    (hKY : sec4Y T T₁ T₂ ≤ K) [((sec4N T T₁ T₂).subgroupOf K).Normal] :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card T = Nat.card (normIn T T₁) * 2 ^ f ∧
      ∃ (X : Type) (_ : Group X) (S : Subgroup X) (ι : X →* ↥K ⧸ (sec4N T T₁ T₂).subgroupOf K),
        IsSimpleGroup X ∧ IsL2Pair X S (2 ^ f) ∧
        (T.subgroupOf K).map (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf K)) = S.map ι ∧
        (ι.range = ⊤ → ∀ y ∈ sec4Y T T₁ T₂, ∃ x ∈ T ⊔ T₁, x⁻¹ * y ∈ sec4N T T₁ T₂) := by
  have hTK : T ≤ K := left_le_sec4Y.trans hKY
  obtain ⟨hM, f, hf, ⟨e⟩⟩ := h.sec3Iso
  have := hM
  have hpair := h.sec3.isL2Pair_quotient hf ⟨e⟩
  have hcardT := h.sec3.card_eq_mul hf ⟨e⟩
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    subst hf1
    rw [hcardT] at hq
    norm_num at hq
    omega
  have hfin := hpair.finite
  have hsimple : IsSimpleGroup (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    isSimpleGroup_of_psl2 hf2 e
  obtain ⟨ι, hι⟩ := exists_iota (K := K) (N := sec4N T T₁ T₂) (sup_le hTK (mid_le_sec4Y.trans hKY))
    cfgM_le_sec4N
  have hTS := img_map_iota_eq (T := T) (X₁ := T ⊔ T₁) (Y := K) (N := sec4N T T₁ T₂)
    (M := cfgM T T₁) (sup_le hTK (mid_le_sec4Y.trans hKY)) (le_sup_left : T ≤ T ⊔ T₁) ι hι
  refine ⟨f, hf2, hcardT, _, inferInstance, _, ι, hsimple, hpair, hTS.symm, fun hrange y hy => ?_⟩
  have hmem : QuotientGroup.mk (⟨y, hKY hy⟩ : ↥K) ∈ ι.range := by
    rw [hrange]
    trivial
  obtain ⟨xb, hxb⟩ := hmem
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  rw [hι] at hxb
  have h1 := QuotientGroup.eq.1 hxb
  exact ⟨(x : G), x.2, Subgroup.mem_subgroupOf.1 h1⟩

theorem Sec4Hyp.sec4_two_of_le
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {K : Subgroup G}
    (hKY : sec4Y T T₁ T₂ ≤ K) (hKN : K ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hcl : Subgroup.normalClosure ((T.subgroupOf K : Subgroup ↥K) : Set ↥K) = ⊤) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card T = Nat.card (normIn T T₁) * 2 ^ f ∧
      ∃ _ : ((sec4N T T₁ T₂).subgroupOf K).Normal,
        Nonempty ((↥K ⧸ (sec4N T T₁ T₂).subgroupOf K) ⧸
          Subgroup.center (↥K ⧸ (sec4N T T₁ T₂).subgroupOf K) ≃* PSU3Model f) := by
  have hTK : T ≤ K := left_le_sec4Y.trans hKY
  have hNK : sec4N T T₁ T₂ ≤ K := sec4N_le_sec4Y.trans hKY
  have hN : ((sec4N T T₁ T₂).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  obtain ⟨f, hf2, hcardT, X, _, S, ι, hsimple, hpair, hTS, hrange⟩ :=
    h.exists_L2_embedding hq hKY (K := K)
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hfin := hpair.finite
  have hstrong := h.strongWC_img_of_le hKN hTK
  have hcl' := normalClosure_img_eq_top (K := K) (N := sec4N T T₁ T₂) (T := T) hcl
  have hTZ := h.img_inf_center_eq_bot_of_le hKY hKN hTK
  have hnn : ¬ ∀ g : ↥K ⧸ (sec4N T T₁ T₂).subgroupOf K,
      conjSubgroup g ((T.subgroupOf K).map
        (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf K))) =
        (T.subgroupOf K).map (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf K)) := by
    obtain ⟨c, hcT₁, hct⟩ := h.exists_mem_mid_not_mem_sec4N
    obtain ⟨x, hx, hx'⟩ := h.exists_mem_sec4Y_conj₁
    exact not_normal_img (hKY hx) (by rw [← hx']; exact hcT₁) hTK hct
  have hcardbar : Nat.card ((T.subgroupOf K).map
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf K))) = 2 ^ f := by
    have h1 := card_img_mul_card_inf (K := K) (N := sec4N T T₁ T₂) (T := T) hTK
    rw [h.inf_sec4N_eq, hcardT] at h1
    exact Nat.eq_of_mul_eq_mul_left hLpos (by linarith)
  rcases bender_identification hAsc hstrong hnn hcl' hTZ hf2 hcardbar hsimple hpair ι hTS with
    hr | hU3
  ·
    exfalso
    obtain ⟨x, hx, hx'⟩ := h.exists_mem_sup_conj_of_forall (hrange hr)
    have hne : conjSubgroup x T ≠ T := hx' ▸ h.ne_left
    have hle := h.sec3.trans x hx hne
    rw [← hx'] at hle
    have haM : a ∈ cfgM T T₁ := hle h.mem_normIn₂
    exact h.haL (sup_le (le_trans (normIn_le T T₁) le_sup_left) le_sup_right haM)
  · exact ⟨f, hf2, hcardT, hN, hU3⟩

theorem Sec4Hyp.sec4_two
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    T ⊓ sec4N T T₁ T₂ = normIn T T₁ ∧ ∃ f : ℕ, 2 ≤ f ∧
      Nat.card T = Nat.card (normIn T T₁) * 2 ^ f ∧
      ∃ _ : ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal,
        Nonempty ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
          Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
            (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ≃* PSU3Model f) :=
  ⟨h.inf_sec4N_eq, h.sec4_two_of_le hAsc hq le_rfl h.sec4Y_le_normalizer h.normalClosure_sec4Y⟩

end Main

end CFSG.CGT.Timmesfeld75
