module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFinal2
public import CFSG.CGT.Timmesfeld75.Fusion

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a x : G}

theorem Sec4Hyp.false_of_normalizes
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction)
    (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) (hxD : x ∈ classD T)
    (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxR' : x ∈ Subgroup.normalizer (sec4R T T₁ T₂ : Set G)) (hxR : x ∉ sec4R T T₁ T₂) :
    False := by
  have hTab := h.pair.wc.1
  have hxN := h.mem_normalizer_sec4N hxR' hxT
  obtain ⟨-, -, -, -, hlt⟩ := h.exists_acts_like_t hnab hind hAsc hA hC hq h16 hxD hxT hxN hxR
  have hxT' : x ∉ T := fun hx => hxR (left_le_sec4R hx)
  obtain ⟨g, t', ht', ht'1, hxg⟩ := hxD
  have hxT₃ : x ∈ conjSubgroup g⁻¹ T := mem_conjSubgroup.2 (by
    rw [inv_inv, hxg]
    have e : g * (g⁻¹ * t' * g) * g⁻¹ = t' := by group
    rw [e]
    exact ht')
  have hne : conjSubgroup g⁻¹ T ≠ T := fun h' => hxT' (h' ▸ hxT₃)
  have hx1 : x ≠ 1 := fun h1 => ht'1 (by
    have : t' = g * x * g⁻¹ := by rw [hxg]; group
    rw [this, h1]
    group)
  have hxN₃ : x ∈ normIn (conjSubgroup g⁻¹ T) T := mem_normIn.2 ⟨hxT₃, hxT⟩
  have hL' : normIn (conjSubgroup g⁻¹ T) T ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨x, hxN₃⟩, fun h' => hx1 (congrArg Subtype.val h')⟩
  have hL : normIn T (conjSubgroup g⁻¹ T) ≠ ⊥ := normIn_ne_bot_of_conj h.pair.wc hne hL'
  have hc : Cfg T (conjSubgroup g⁻¹ T) :=
    cfg_of_conj_conj h.pair.wc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g⁻¹, rfl⟩ hne hL
  have hS : Sec3 T (conjSubgroup g⁻¹ T) :=
    sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ ⟨g⁻¹, rfl⟩ hne hL
  have hI : Sec3Iso T (conjSubgroup g⁻¹ T) :=
    sec3Iso_of_conj_conj h.iso ⟨1, (conjSubgroup_one T).symm⟩ ⟨g⁻¹, rfl⟩ hne hL
  have hCx : T ⊓ Subgroup.centralizer ({x} : Set G) = normIn T (conjSubgroup g⁻¹ T) :=
    hc.inf_centralizer_eq_normIn hxN₃ hx1
  have hc3 : Nat.card (normIn (conjSubgroup g⁻¹ T) T) = Nat.card (normIn T (conjSubgroup g⁻¹ T)) :=
    (hc.card_normIn_eq ⟨g⁻¹, rfl⟩).symm
  rw [hCx] at hlt
  have hsq := hS.card_le_sq_card_normIn hI
  have hTI : T ⊓ conjSubgroup g⁻¹ T = ⊥ := h.pair.wc.inf_conj_eq_bot hne
  have hL₃P : IsPGroup 2 ↥(normIn (conjSubgroup g⁻¹ T) T) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_of_le (isElemAbelian_conjSubgroup hTab g⁻¹)
      (normIn_le _ _))
  obtain ⟨U, hU, hUN, hRU, c, hcN, hcU⟩ := exists_pGroup_containing_conjSubgroup
    (C := Subgroup.normalizer (T : Set G)) h.isPGroup_sec4R hL₃P sec4R_le_normalizer_left
    (inf_le_right : normIn (conjSubgroup g⁻¹ T) T ≤ Subgroup.normalizer (T : Set G))
  have hVU : ∀ v ∈ conjSubgroup c (normIn (conjSubgroup g⁻¹ T) T), v ∈ U := fun v hv => hcU hv
  have hVprop : ∀ v ∈ conjSubgroup c (normIn (conjSubgroup g⁻¹ T) T), v ≠ 1 →
      v ∈ classD T ∧ v ∈ Subgroup.normalizer (T : Set G) ∧ v ∉ sec4R T T₁ T₂ := by
    intro v hv hv1
    obtain ⟨y, hy, hvy⟩ : ∃ y ∈ normIn (conjSubgroup g⁻¹ T) T, v = c * y * c⁻¹ :=
      ⟨c⁻¹ * v * c, mem_conjSubgroup.1 hv, by group⟩
    have hy1 : y ≠ 1 := fun h1 => hv1 (by rw [hvy, h1]; group)
    have hyD : y ∈ classD T := mem_classD_of_mem_conjSubgroup (mem_normIn.1 hy).1 hy1
    have hvD : v ∈ classD T := hvy ▸ conj_mem_classD hyD c
    have hvT : v ∈ Subgroup.normalizer (T : Set G) := hvy ▸
      (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hcN (mem_normIn.1 hy).2)
        ((Subgroup.normalizer (T : Set G)).inv_mem hcN)
    have hvC : Nat.card ↥(T ⊓ Subgroup.centralizer ({v} : Set G)) =
        Nat.card ↥(normIn T (conjSubgroup g⁻¹ T)) := by
      rw [hvy, card_inf_centralizer_conj_of_mem_normalizer hcN,
        hc.inf_centralizer_eq_normIn hy hy1]
    refine ⟨hvD, hvT, fun hvR => ?_⟩
    rcases h.mem_or_mem_sec4N_of_mem_sec4R ⟨hvD, hvT⟩ hvR with hvT' | hvN'
    · have hyT : y ∈ T := by
        have e : y = c⁻¹ * v * c := by rw [hvy]; group
        rw [e]
        simpa using conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hcN)
          hvT'
      have hy' : y ∈ T ⊓ conjSubgroup g⁻¹ T := ⟨hyT, (mem_normIn.1 hy).1⟩
      rw [hTI, Subgroup.mem_bot] at hy'
      exact hy1 hy'
    · have hLC : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := fun l hl =>
        ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_singleton_iff.2
          (elemAbelian_mul_comm h.isElemAbelian_sec4N (normIn_le_sec4N_left hl) hvN')⟩
      have := Subgroup.card_le_of_le hLC
      rw [hvC] at this
      exact absurd this (not_le.2 hlt)
  have hVinfo : ∀ v ∈ conjSubgroup c (normIn (conjSubgroup g⁻¹ T) T), v ≠ 1 →
      ∃ t ∈ T, t ∉ normIn T T₁ ∧ Sec4ActsTriv T T₁ T₂ (v * t) := by
    intro v hv hv1
    obtain ⟨hvD, hvT, hvR⟩ := hVprop v hv hv1
    have hvR' := h.mem_normalizer_sec4R hnab hind hAsc hA hC hq h16 hU hRU hUN (hVU v hv)
    have hvN := h.mem_normalizer_sec4N hvR' hvT
    obtain ⟨t, htT, htL, hact, -⟩ :=
      h.exists_acts_like_t hnab hind hAsc hA hC hq h16 hvD hvT hvN hvR
    exact ⟨t, htT, htL, hact⟩
  have hVacts : ∀ v ∈ conjSubgroup c (normIn (conjSubgroup g⁻¹ T) T),
      ∃ t ∈ T, Sec4ActsTriv T T₁ T₂ (v * t) := by
    intro v hv
    by_cases hv1 : v = 1
    · exact ⟨1, T.one_mem, by rw [hv1, mul_one]; exact (sec4Ker T T₁ T₂).one_mem⟩
    · obtain ⟨t, htT, -, hact⟩ := hVinfo v hv hv1
      exact ⟨t, htT, hact⟩
  have hVker : ∀ v ∈ conjSubgroup c (normIn (conjSubgroup g⁻¹ T) T),
      Sec4ActsTriv T T₁ T₂ v → v = 1 := by
    intro v hv hvk
    by_contra hv1
    obtain ⟨t, htT, htL, hact⟩ := hVinfo v hv hv1
    apply htL
    rw [← h.inf_sec4Ker_eq]
    refine ⟨htT, ?_⟩
    have h1 : v⁻¹ * (v * t) ∈ sec4Ker T T₁ T₂ :=
      (sec4Ker T T₁ T₂).mul_mem ((sec4Ker T T₁ T₂).inv_mem hvk) hact
    simpa using h1
  have hemb := h.card_mul_le_of_acts_like_t hVacts hVker
  rw [card_conjSubgroup, hc3] at hemb
  have hpos : 0 < Nat.card ↥(normIn T (conjSubgroup g⁻¹ T)) := Nat.card_pos
  have h2 : Nat.card ↥(normIn T (conjSubgroup g⁻¹ T)) * Nat.card (normIn T T₁) ≤
      Nat.card ↥(normIn T (conjSubgroup g⁻¹ T)) * Nat.card ↥(normIn T (conjSubgroup g⁻¹ T)) :=
    hemb.trans (hsq.trans_eq (pow_two _))
  exact absurd (Nat.le_of_mul_le_mul_left h2 hpos) (not_le.2 hlt)

theorem Sec4Hyp.closure_inter_classD_eq
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction) (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hRS : sec4R T T₁ T₂ ≤ S) :
    Subgroup.closure ((S : Set G) ∩ classD T) = sec4R T T₁ T₂ := by
  have hgen := h.closure_sec4R_inter_eq
  have hR : Subgroup.closure (((S : Set G) ∩ classD T) ∩ (sec4R T T₁ T₂ : Set G)) =
      sec4R T T₁ T₂ :=
    le_antisymm ((Subgroup.closure_le _).2 Set.inter_subset_right)
      (calc sec4R T T₁ T₂ = Subgroup.closure ((sec4R T T₁ T₂ : Set G) ∩ classD T) := hgen.symm
        _ ≤ Subgroup.closure (((S : Set G) ∩ classD T) ∩ (sec4R T T₁ T₂ : Set G)) :=
          Subgroup.closure_mono fun d hd => ⟨⟨hRS hd.1, hd.2⟩, hd.1⟩)
  by_contra hne
  obtain ⟨x, ⟨hxS, hxD⟩, hxN, hxR⟩ := exists_mem_normalizer_of_closure_ne hS
    Set.inter_subset_left (fun s hs d hd => ⟨S.mul_mem (S.mul_mem hs hd.1) (S.inv_mem hs),
      conj_mem_classD hd.2 s⟩) hRS hR hne
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := by
    refine mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup h.pair.wc hS
      (left_le_sec4R.trans hRS) ?_)
    exact conjSubgroup_le_of_forall_mem fun t ht =>
      hRS ((Subgroup.mem_normalizer_iff.1 hxN t).1 (left_le_sec4R ht))
  exact h.false_of_normalizes hnab hind hAsc hA hC hq h16 hxD hxT hxN hxR

end CFSG.CGT.Timmesfeld75
