module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeXE
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.NoOffenderTight

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Blueprint.NativeSporadic CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

theorem center_XE_eq_bot
    (hm : M24Out G E t) : Subgroup.center ↥(S44.XE E) = ⊥ := by
  obtain ⟨e⟩ := xe_equiv_m24 hm
  have h1 : (Subgroup.center ↥(S44.XE E)).map e.toMonoidHom = Subgroup.center (Carrier .M24) :=
    Subgroup.map_center_eq e
  have h2 : Subgroup.center (Carrier .M24) = ⊥ := Sporadic.Schreier.m24_center_eq_bot'
  rw [h2] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1

theorem isQuasisimple_XE
    (hm : M24Out G E t) : CFSG.IsQuasisimple ↥(S44.XE E) := by
  obtain ⟨e⟩ := xe_equiv_m24 hm
  have hs : IsSimpleGroup (Carrier .M24) := Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hnc : ∃ a b : Carrier .M24, a * b ≠ b * a :=
    ⟨Sporadic.Mathieu.m24a, Sporadic.Mathieu.m24b, Sporadic.Schreier.m24_gens_not_comm⟩
  exact CFSG.IsQuasisimple.of_mulEquiv e (LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem nonempty_cqEquivXE
    (hm : M24Out G E t) : Nonempty (CQ (S44.XE E) ≃* Carrier .M24) := by
  obtain ⟨e⟩ := xe_equiv_m24 hm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (center_XE_eq_bot hm)).trans
    (QuotientGroup.quotientBot.trans e)⟩

section Image

variable {A : Subgroup G}

@[expose] def actA (hA : A ≤ Nrm E) : ↥A →* MulAut ↥E :=
  (S44.actN E).comp (Subgroup.inclusion hA)

theorem ker_actA (hm : M24Out G E t) (hA : A ≤ Nrm E) :
    (actA hA).ker = (A ⊓ E).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have h1 : actA hA a = 1 ↔ (a : G) ∈ E := by
    have h2 : (⟨(a : G), hA a.2⟩ : ↥(normalizer (E : Set G))) ∈ (S44.actN E).ker ↔
        (a : G) ∈ E := by
      rw [S44.mem_ker_actN_iff_mem_centralizer, hm.centralizer_eq]
    exact h2
  rw [h1]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

theorem relIndex_eq_card_range (hm : M24Out G E t) (hA : A ≤ Nrm E) :
    (A ⊓ E).relIndex A = Nat.card ↥(actA hA).range := by
  rw [Subgroup.relIndex, ← ker_actA hm hA, Subgroup.index_ker]

theorem range_actA_le (hA : A ≤ Nrm E) : (actA hA).range ≤ S44.XE E := by
  rintro _ ⟨a, rfl⟩
  exact ⟨_, rfl⟩

theorem isElemAbelian2_range_actA (hm : M24Out G E t) (hA : A ≤ Nrm E)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    @IsElemAbelian2 ↥E (commGroupOfM24Out hm) (actA hA).range := by
  constructor
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hcomm a a.2 b b.2))
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hsq a a.2)
    rw [this, map_one]

theorem range_actA_ne_bot (hm : M24Out G E t) (hA : A ≤ Nrm E) (hAE : ¬ A ≤ E) :
    (actA hA).range ≠ ⊥ := by
  intro h
  apply hAE
  intro a ha
  have h1 : actA hA ⟨a, ha⟩ = 1 := by
    have : actA hA ⟨a, ha⟩ ∈ (actA hA).range := ⟨⟨a, ha⟩, rfl⟩
    rw [h] at this
    exact this
  have h2 : ⟨a, ha⟩ ∈ (actA hA).ker := h1
  rw [ker_actA hm hA, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
  exact h2.2

theorem card_inf_centralizer_eq (hm : M24Out G E t) (hA : A ≤ Nrm E) :
    Nat.card ↥(E ⊓ centralizer (A : Set G)) =
      Nat.card ↥(@fixV ↥E (commGroupOfM24Out hm) (actA hA).range) := by
  let _ := commGroupOfM24Out hm
  have h1 : (fixV (actA hA).range).map E.subtype = E ⊓ centralizer (A : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2, fun a ha => ?_⟩
      have h2 : actA hA ⟨a, ha⟩ v = v := hv _ ⟨⟨a, ha⟩, rfl⟩
      have h3 : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val h2
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
    · rintro ⟨hxE, hx⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      rintro _ ⟨a, rfl⟩
      apply Subtype.ext
      show (a : G) * x * (a : G)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact hx a a.2
  rw [← h1, Subgroup.card_map_of_injective E.subtype_injective]

end Image

theorem exists_card_eq_two_pow_of_sq {H : Type*} [Group H] [Finite H] (h : ∀ x : H, x ^ 2 = 1) :
    ∃ n : ℕ, Nat.card H = 2 ^ n :=
  (IsPGroup.iff_card (p := 2)).1 fun x => ⟨1, by simpa using h x⟩

theorem noOffender_of_m24Out
    [Finite G] (hm : M24Out G E t) {A : Subgroup G} (hA : A ≤ Nrm E)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAE : ¬ A ≤ E) :
    (A ⊓ E).relIndex A * Nat.card ↥(E ⊓ centralizer (A : Set G)) ≤ 2 ^ 10 := by
  letI := commGroupOfM24Out hm
  rw [relIndex_eq_card_range hm hA, card_inf_centralizer_eq hm hA]
  have hel := isElemAbelian2_range_actA hm hA hsq hcomm
  have hne := range_actA_ne_bot hm hA hAE
  have hW := m24Out_E_mul_self hm
  have hN : (actA hA).range ≤ normalizer (S44.XE E : Set (MulAut ↥E)) :=
    (range_actA_le hA).trans le_normalizer
  rcases QuasithinUnique.Setup.X1.m24_weight_lt_or_tight (W := ↥E) hW (L := S44.XE E)
      (E := (actA hA).range) (isQuasisimple_XE hm) (isIrrOn_XE hm)
      (Classical.choice (nonempty_cqEquivXE hm)) hN hne hel with h | ⟨h1, h2⟩
  · rw [hm.card_E] at h
    obtain ⟨a, ha⟩ := exists_card_eq_two_pow_of_sq (H := ↥(actA hA).range) fun x =>
      Subtype.ext (hel.2 x x.2)
    obtain ⟨b, hb⟩ := exists_card_eq_two_pow_of_sq (H := ↥(fixV (actA hA).range)) fun x =>
      Subtype.ext (m24Out_E_sq hm x.1)
    rw [ha, hb, ← pow_add] at h ⊢
    have h' : a + b < 11 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact (m24TightNoQuad ↥E hW (S44.XE E) (actA hA).range (isQuasisimple_XE hm) (isIrrOn_XE hm)
      (nonempty_cqEquivXE hm) hN hne hel h1 h2).elim

theorem noOffender_holds :
    ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (t : G), M24Out G E t →
      ∀ A : Subgroup G, A ≤ Nrm E → (∀ a ∈ A, a ^ 2 = 1) →
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → ¬ A ≤ E →
        (A ⊓ E).relIndex A * Nat.card ↥(E ⊓ centralizer (A : Set G)) ≤ 2 ^ 10 :=
  fun _ _ _ _ _ hm _ hA hsq hcomm hAE => noOffender_of_m24Out hm hA hsq hcomm hAE

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
