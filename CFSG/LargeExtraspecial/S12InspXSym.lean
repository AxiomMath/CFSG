module

public import CFSG.LargeExtraspecial.S12TriExcl
public import CFSG.Fischer.Classification.Recognition.CaseSym

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm
open scoped commutatorElement

namespace S12Insp4

variable {m : ℕ} {a b : Fin m}

theorem mem_map_ofSubtype_alternatingGroup {σ : Perm (Fin m)} :
    σ ∈ (alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b}).map ofSubtype ↔
      sign σ = 1 ∧ σ a = a ∧ σ b = b := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨by rw [sign_ofSubtype]; exact mem_alternatingGroup.mp hτ,
      ofSubtype_apply_of_not_mem τ fun h => h.1 rfl,
      ofSubtype_apply_of_not_mem τ fun h => h.2 rfl⟩
  · rintro ⟨hs, ha, hb⟩
    have hp : ∀ x, (σ x ≠ a ∧ σ x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
      intro x
      have ea : σ x = a ↔ x = a :=
        ⟨fun h => σ.injective (h.trans ha.symm), fun h => by rw [h, ha]⟩
      have eb : σ x = b ↔ x = b :=
        ⟨fun h => σ.injective (h.trans hb.symm), fun h => by rw [h, hb]⟩
      rw [Ne, Ne, ea, eb]
    have hmove : ∀ x, σ x ≠ x → x ≠ a ∧ x ≠ b := fun x hx =>
      ⟨fun h => hx (by rw [h, ha]), fun h => hx (by rw [h, hb])⟩
    refine ⟨σ.subtypePerm hp, ?_, ofSubtype_subtypePerm hp hmove⟩
    rw [SetLike.mem_coe, mem_alternatingGroup, ← sign_ofSubtype, ofSubtype_subtypePerm hp hmove,
      hs]

theorem commutator_centralizer_swap (hab : a ≠ b) (hm : 7 ≤ m) :
    ⁅centralizer {swap a b}, centralizer {swap a b}⁆ =
      (alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b}).map ofSubtype := by
  have hΩ := CFSG.Fischer.Classification.Recognition.SymO.card_compl hab
  apply le_antisymm
  · rw [commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [mem_map_ofSubtype_alternatingGroup]
    refine ⟨by rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm], ?_⟩
    rcases CFSG.Fischer.Classification.Recognition.SymO.apply_of_mem_centralizer hab h₁ with
      ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;>
    rcases CFSG.Fischer.Classification.Recognition.SymO.apply_of_mem_centralizer hab h₂ with
      ⟨q1, q2, q3, q4⟩ | ⟨q1, q2, q3, q4⟩ <;>
    simp [commutatorElement_def, Perm.mul_apply, p1, p2, p3, p4, q1, q2, q3, q4]
  · rw [← alternatingGroup.commutator_perm_eq (α := {x : Fin m // x ≠ a ∧ x ≠ b})
      (by rw [hΩ]; omega), _root_.commutator_def, map_commutator]
    refine commutator_mono ?_ ?_ <;>
    · rintro _ ⟨σ, -, rfl⟩
      rw [mem_centralizer_singleton_iff, mul_swap_eq_swap_mul,
        ofSubtype_apply_of_not_mem σ fun h => h.1 rfl,
        ofSubtype_apply_of_not_mem σ fun h => h.2 rfl]

noncomputable def commutatorCentralizerSwapEquiv (hab : a ≠ b) (hm : 7 ≤ m) :
    alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b} ≃*
      (⁅centralizer {swap a b}, centralizer {swap a b}⁆ : Subgroup (Perm (Fin m))) :=
  (Subgroup.equivMapOfInjective _ _ ofSubtype_injective).trans
    (MulEquiv.subgroupCongr (commutator_centralizer_swap hab hm).symm)

theorem isSimpleGroup_commutator_centralizer_swap (hab : a ≠ b) (hm : 7 ≤ m) :
    IsSimpleGroup
      (⁅centralizer {swap a b}, centralizer {swap a b}⁆ : Subgroup (Perm (Fin m))) := by
  have hΩ := CFSG.Fischer.Classification.Recognition.SymO.card_compl hab
  have := alternatingGroup.isSimpleGroup (α := {x : Fin m // x ≠ a ∧ x ≠ b}) (by omega)
  exact (commutatorCentralizerSwapEquiv hab hm).symm.isSimpleGroup

theorem card_commutator_centralizer_swap (hab : a ≠ b) (hm : 7 ≤ m) :
    Nat.card (⁅centralizer {swap a b}, centralizer {swap a b}⁆ : Subgroup (Perm (Fin m))) =
      (m - 2).factorial / 2 := by
  have hΩ := CFSG.Fischer.Classification.Recognition.SymO.card_compl hab
  have : Nontrivial {x : Fin m // x ≠ a ∧ x ≠ b} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rw [← Nat.card_congr (commutatorCentralizerSwapEquiv hab hm).toEquiv,
    nat_card_alternatingGroup, hΩ]

theorem factorial_div_two_facts {k : ℕ} (hk : 5 ≤ k) :
    3 ∣ k.factorial / 2 ∧ 1 < k.factorial / 2 := by
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hk
  have h5 : Nat.factorial 5 = 120 := rfl
  rw [h5] at hc
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc
      exact absurd hc (Nat.factorial_ne_zero k)
    · exact h
  rw [hc, show 120 * c = 2 * (60 * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨Dvd.intro (20 * c) (by ring), by omega⟩

theorem not_isSolvable_alternatingGroup_compl (hab : a ≠ b) (hm : 7 ≤ m) :
    ¬ Group.IsSolvable (alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b}) := by
  intro hs
  have hΩ := CFSG.Fischer.Classification.Recognition.SymO.card_compl hab
  have h5 : 5 ≤ Nat.card {x : Fin m // x ≠ a ∧ x ≠ b} := by omega
  have := alternatingGroup.isSimpleGroup h5
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable
    (G := alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b})).mpr hs
  have hbot : commutator (alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b}) = ⊥ := by
    rw [_root_.commutator_def, eq_bot_iff, commutator_le]
    intro x _ y _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm x y
  rw [commutator_alternatingGroup_eq_top h5] at hbot
  have : Nontrivial {x : Fin m // x ≠ a ∧ x ≠ b} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have h1 : Nat.card (alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b}) = 1 := by
    rw [← Subgroup.card_top, hbot, Subgroup.card_bot]
  rw [nat_card_alternatingGroup, hΩ] at h1
  exact absurd h1 (factorial_div_two_facts (by omega)).2.ne'

end S12Insp4

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_perm_ge_seven {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {m : ℕ} (hm : 7 ≤ m)
    (φ : S.Xbar12 g ≃* Equiv.Perm (Fin m))
    (hφ : ∀ x : S.Xbar12 g, x ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ↔
      (φ x).IsSwap) : False := by
  have htE := mem_Ebar12_of_mem_Lbar ht htA
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 htE
  obtain ⟨a, b, hab, hτ⟩ := (hφ ⟨t, htX⟩).mp htE
  set θ : Equiv.Perm (Fin m) →* S.O := (S.Xbar12 g).subtype.comp φ.symm.toMonoidHom with hθ
  have hθinj : Function.Injective θ := (subtype_injective _).comp φ.symm.injective
  have hθt : θ (swap a b) = t := by
    rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hτ, MulEquiv.symm_apply_apply]
    rfl
  set C : Subgroup S.O := S.Xbar12 g ⊓ centralizer {t} with hC
  have hCmap : C = (centralizer {swap a b}).map θ := by
    ext c
    rw [hC, mem_inf, mem_map]
    constructor
    · rintro ⟨hcX, hct⟩
      refine ⟨φ ⟨c, hcX⟩, ?_, ?_⟩
      · rw [mem_centralizer_singleton_iff] at hct ⊢
        rw [← hτ, ← map_mul, ← map_mul]
        exact congrArg φ (Subtype.ext hct)
      · simp [hθ]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by simp [hθ], ?_⟩
      rw [mem_centralizer_singleton_iff] at hy ⊢
      rw [← hθt, ← map_mul, ← map_mul, hy]
  set K : Subgroup S.O := ⁅C, C⁆ with hK
  have hKmap : K = ⁅centralizer {swap a b}, centralizer {swap a b}⁆.map θ := by
    rw [hK, hCmap, map_commutator]
  let eK : (⁅centralizer {swap a b}, centralizer {swap a b}⁆ : Subgroup (Perm (Fin m))) ≃* K :=
    (Subgroup.equivMapOfInjective _ _ hθinj).trans (MulEquiv.subgroupCongr hKmap.symm)
  have hsimple : IsSimpleGroup K := by
    have := S12Insp4.isSimpleGroup_commutator_centralizer_swap hab hm
    exact eK.symm.isSimpleGroup
  have hcard : Nat.card K = (m - 2).factorial / 2 := by
    rw [← Nat.card_congr eK.toEquiv, S12Insp4.card_commutator_centralizer_swap hab hm]
  have hKC : K ≤ C := commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) (C.inv_mem hx)) (C.inv_mem hy)
  have hKM : K ≤ S.Mbar := hKC.trans (inf_le_left.trans Xbar12_le_Mbar)
  have hKt : ∀ c ∈ K, c * t = t * c := fun c hc =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hKC hc)).2
  have hconj : ∀ ℓ ∈ S.Lbar g, ∀ k ∈ C, ℓ * k * ℓ⁻¹ ∈ C := by
    intro ℓ hℓ k hk
    have hℓt : ℓ * t = t * ℓ :=
      congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨ℓ, hℓ⟩ ⟨t, ht⟩)
    have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp (mem_inf.mp hk).2
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12
      (S.Lbar_le_Mbar g hℓ)) k).mp (mem_inf.mp hk).1, mem_centralizer_singleton_iff.mpr ?_⟩
    have hℓt' : ℓ⁻¹ * t = t * ℓ⁻¹ := by
      calc ℓ⁻¹ * t = ℓ⁻¹ * (t * ℓ) * ℓ⁻¹ := by group
        _ = ℓ⁻¹ * (ℓ * t) * ℓ⁻¹ := by rw [hℓt]
        _ = t * ℓ⁻¹ := by group
    calc ℓ * k * ℓ⁻¹ * t = ℓ * k * (ℓ⁻¹ * t) := by group
      _ = ℓ * k * (t * ℓ⁻¹) := by rw [hℓt']
      _ = ℓ * (k * t) * ℓ⁻¹ := by group
      _ = ℓ * (t * k) * ℓ⁻¹ := by rw [hkt]
      _ = ℓ * t * k * ℓ⁻¹ := by group
      _ = t * ℓ * k * ℓ⁻¹ := by rw [hℓt]
      _ = t * (ℓ * k * ℓ⁻¹) := by group
  have hLK : S.Lbar g ≤ normalizer (K : Set S.O) := by
    intro ℓ hℓ
    have hℓC : ℓ ∈ normalizer (C : Set S.O) := mem_normalizer_iff.mpr fun k => by
      refine ⟨hconj ℓ hℓ k, fun h => ?_⟩
      have := hconj ℓ⁻¹ ((S.Lbar g).inv_mem hℓ) _ h
      rwa [show ℓ⁻¹ * (ℓ * k * ℓ⁻¹) * ℓ⁻¹⁻¹ = k by group] at this
    rw [mem_normalizer_iff_map_conj_eq] at hℓC ⊢
    rw [hK, map_commutator, hℓC]
  have hK2 : S12NoNormalTwo K := by
    intro P hPK hP2 hKP
    have hN : (P.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hPK).mpr hKP
    rcases hsimple.eq_bot_or_eq_top_of_normal (P.subgroupOf K) with h | h
    · rw [subgroupOf_eq_bot] at h
      exact eq_bot_iff.mpr fun x hx => h.le_bot ⟨hx, hPK hx⟩
    · rw [subgroupOf_eq_top] at h
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hP2.to_le h)
      have h3 := (S12Insp4.factorial_div_two_facts (k := m - 2) (by omega)).1
      rw [← hcard, hj] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)
  have hsolv := isSolvable_of_commute_of_le_normalizer haQ hne hn ht htA hKM hKt hLK hK2
  have hsolv' : Group.IsSolvable
      (⁅centralizer {swap a b}, centralizer {swap a b}⁆ : Subgroup (Perm (Fin m))) :=
    Group.isSolvable_of_surjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  exact S12Insp4.not_isSolvable_alternatingGroup_compl hab hm
    (Group.isSolvable_of_surjective
      (f := (S12Insp4.commutatorCentralizerSwapEquiv hab hm).symm.toMonoidHom)
      (S12Insp4.commutatorCentralizerSwapEquiv hab hm).symm.surjective)

end Setting

end CFSG.LargeExtraspecial
