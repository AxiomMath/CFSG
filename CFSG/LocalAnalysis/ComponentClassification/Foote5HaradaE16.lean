module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HaradaE16C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5GH74

public section

namespace CFSG.ComponentClassification.Foote5

open Subgroup CFSG.ABGLocalTools

theorem harE16_gen4_twoGroup (hMW : MacWilliamsStatement) {S : Type} [Group S] [Finite S]
    (hS : IsPGroup 2 S) {T U : Subgroup S} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTsq : ∀ a ∈ T, a * a = 1) (hT16 : Nat.card T = 16) (hUT : U ≤ T) (hU4 : Nat.card U = 4)
    (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T) (P : Subgroup S) :
    ∃ X : Finset S, X.card ≤ 4 ∧ closure (X : Set S) = P := by
  by_cases htop : normalizer (T : Set S) = ⊤
  · have hS64 : Nat.card S ≤ 64 := by
      have h1 := harE16_card_normalizer_le hS hTab hTsq hT16 hUT hU4 hcent
      rwa [htop, card_top] at h1
    exact OddStandard.Harada75.gen4_of_noE32 hS
      (harE16_noE32 hTab hT16 hUT hU4 hcent hS64 fun g => htop ▸ mem_top g) P
  · exact hMW S hS (harE16_no_normal_e8 hS hTab hTsq hT16 hUT hU4 hcent htop) P

variable {G : Type} [Group G] [Finite G]

theorem gen4_of_harada_e16 (hMW : MacWilliamsStatement) {T U : Subgroup G}
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTsq : ∀ a ∈ T, a * a = 1)
    (hT16 : Nat.card T = 16) (hUT : U ≤ T) (hU4 : Nat.card U = 4)
    (hsyl : ∀ u ∈ U, u ≠ 1 → IsSylowOf 2 T (centralizer ({u} : Set G))) : GH74.Gen4 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 4) (by rw [hT16]; norm_num)
  obtain ⟨Q, hTQ⟩ := hT2.exists_le_sylow
  have hSsyl : IsSylowOf 2 (Q : Subgroup G) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, Q.isPGroup', by rw [relIndex_top_right]; exact Q.not_dvd_index⟩
  have hcentG : ∀ u ∈ U, u ≠ 1 → ∀ g ∈ (Q : Subgroup G), g * u = u * g → g ∈ T := by
    intro u hu hu1 g hg hgu
    have hTC : T ≤ centralizer ({u} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (hTab x hx u (hUT hu))
    have heq := (hsyl u hu hu1).eq_of_le (le_inf hTQ hTC) inf_le_right Q.isPGroup'.to_inf_left
    rw [← heq]
    exact mem_inf.mpr ⟨hg, mem_centralizer_singleton_iff.mpr hgu⟩
  have hgen := harE16_gen4_twoGroup hMW Q.isPGroup' (T := T.subgroupOf Q) (U := U.subgroupOf Q)
    (fun a ha b hb => Subtype.ext (hTab _ ha _ hb)) (fun a ha => Subtype.ext (hTsq _ ha))
    (by rw [← hT16]; exact Nat.card_congr (subgroupOfEquivOfLe hTQ).toEquiv) (fun x hx => hUT hx)
    (by rw [← hU4]; exact Nat.card_congr (subgroupOfEquivOfLe (hUT.trans hTQ)).toEquiv)
    fun u hu hu1 g hgu =>
      hcentG u hu (fun h => hu1 (Subtype.ext h)) g g.2 (congrArg Subtype.val hgu)
  refine gen4_of_isSylowOf hSsyl fun P hP => ?_
  obtain ⟨X, hX, hXP⟩ := hgen (P.subgroupOf Q)
  refine ⟨X.image (Q : Subgroup G).subtype, Finset.card_image_le.trans hX, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXP, map_subgroupOf_eq_of_le hP]

omit [Finite G] in
theorem harE16_mul_self_of_mem_sup {A B : Subgroup G}
    (hab : ∀ y ∈ A ⊔ B, ∀ y' ∈ A ⊔ B, y * y' = y' * y) (hA : ∀ a ∈ A, a * a = 1)
    (hB : ∀ b ∈ B, b * b = 1) {y : G} (hy : y ∈ A ⊔ B) : y * y = 1 := by
  let H : Subgroup G :=
    { carrier := {y | y ∈ A ⊔ B ∧ y * y = 1}
      mul_mem' := fun {x y} hx hy => ⟨(A ⊔ B).mul_mem hx.1 hy.1, by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hab y hy.1 x hx.1]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨(A ⊔ B).one_mem, mul_one 1⟩
      inv_mem' := fun {x} hx => ⟨(A ⊔ B).inv_mem hx.1, by rw [← mul_inv_rev, hx.2, inv_one]⟩ }
  have hle : A ⊔ B ≤ H :=
    sup_le (fun a ha => ⟨mem_sup_left ha, hA a ha⟩) (fun b hb => ⟨mem_sup_right hb, hB b hb⟩)
  exact (hle hy).2

end CFSG.ComponentClassification.Foote5
