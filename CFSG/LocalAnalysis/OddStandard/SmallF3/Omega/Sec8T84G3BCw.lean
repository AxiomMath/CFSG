module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BRg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec8t84g3b_pow_mod {X N : Subgroup G} (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hc : a * b * a⁻¹ * b⁻¹ ∈ N) (n : ℕ) :
    (a * b) ^ n * (a ^ n * b ^ n)⁻¹ ∈ N := by
  haveI : (N.subgroupOf X).Normal := ⟨fun x hx g => hN g.1 g.2 x hx⟩
  let ρ : ↥X →* ↥X ⧸ N.subgroupOf X := QuotientGroup.mk' _
  have key : ∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ N := fun x => QuotientGroup.eq_one_iff x
  let a' : ↥X := ⟨a, ha⟩
  let b' : ↥X := ⟨b, hb⟩
  have hcomm : ρ a' * ρ b' = ρ b' * ρ a' := by
    have h3 : ρ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := (key _).mpr hc
    simp only [map_mul, map_inv] at h3
    have h4 : ρ a' * ρ b' * (ρ a')⁻¹ = ρ b' := mul_inv_eq_one.mp h3
    calc ρ a' * ρ b' = (ρ a' * ρ b' * (ρ a')⁻¹) * ρ a' := by group
      _ = ρ b' * ρ a' := by rw [h4]
  have h5 : ρ ((a' * b') ^ n * (a' ^ n * b' ^ n)⁻¹) = 1 := by
    simp only [map_mul, map_pow, map_inv]
    rw [(Commute.mul_pow (show Commute (ρ a') (ρ b') from hcomm)) n]
    exact mul_inv_cancel _
  simpa using (key _).mp h5

theorem sec8t84g3b_cent_sup {A B : Subgroup G} {y : G} (hAB : A ⊓ B = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hB : ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    (A ⊔ B) ⊓ centralizer ({y} : Set G) =
      (A ⊓ centralizer ({y} : Set G)) ⊔ (B ⊓ centralizer ({y} : Set G)) := by
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84g3b_mem_sup_comm hc hx
    have hxy : y * (a * b) = a * b * y := Subgroup.mem_centralizer_iff.mp hxc y rfl
    have h1 : (y * a * y⁻¹) * (y * b * y⁻¹) = a * b := by
      calc (y * a * y⁻¹) * (y * b * y⁻¹) = y * (a * b) * y⁻¹ := by group
        _ = a * b := by rw [hxy, mul_inv_cancel_right]
    have h2 : a⁻¹ * (y * a * y⁻¹) = b * (y * b * y⁻¹)⁻¹ := by
      have h3 : (y * a * y⁻¹) * (y * b * y⁻¹) = a * b := h1
      calc a⁻¹ * (y * a * y⁻¹) = a⁻¹ * ((y * a * y⁻¹) * (y * b * y⁻¹)) * (y * b * y⁻¹)⁻¹ := by
            group
        _ = a⁻¹ * (a * b) * (y * b * y⁻¹)⁻¹ := by rw [h3]
        _ = b * (y * b * y⁻¹)⁻¹ := by group
    have hmem : a⁻¹ * (y * a * y⁻¹) ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha) (hA a ha), by
      rw [h2]; exact B.mul_mem hb (B.inv_mem (hB b hb))⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    have hya : y * a * y⁻¹ = a := (inv_mul_eq_one.mp hmem).symm
    have hyb : y * b * y⁻¹ = b := by
      rw [hya] at h1
      exact mul_left_cancel h1
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, Subgroup.mem_centralizer_iff.mpr
      (fun z hz => ?_)⟩) (Subgroup.mem_sup_right ⟨hb, Subgroup.mem_centralizer_iff.mpr
      (fun z hz => ?_)⟩)
    · rw [Set.mem_singleton_iff.mp hz]
      exact mul_inv_eq_iff_eq_mul.mp hya
    · rw [Set.mem_singleton_iff.mp hz]
      exact mul_inv_eq_iff_eq_mul.mp hyb
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

variable {E E0 Y Y' V V' F F' P H : Subgroup G}

namespace Sec8T84G3BSide

variable [Finite G]

theorem W_inf_Y (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H)
    (hW : E ⊔ E0 = (V ⊔ F) ⊔ (V' ⊔ F')) : (E ⊔ E0) ⊓ Y ≤ V ⊔ F := by
  intro w hw
  have hw1 : w ∈ (V ⊔ F) ⊔ (V' ⊔ F') := hW ▸ hw.1
  obtain ⟨u, hu, u', hu', rfl⟩ := sec8t84g3b_mem_sup_comm S.UU'_comm hw1
  have hu'Y : u' ∈ Y := by
    have h1 := Y.mul_mem (Y.inv_mem (S.U_le_Y hu)) hw.2
    simpa using h1
  have hu'N : u' ∈ oddCoreIn (normalizer (E : Set G)) := S.inf ⟨hu'Y, S.U'_le_Y' hu'⟩
  have h2 : u' ∈ (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨S.U'_le_W hu', hu'N⟩
  rw [S.W_inf, Subgroup.mem_bot] at h2
  rw [h2, mul_one]
  exact hu

theorem conj_eq (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {a b u : G} (ha : a ∈ Y)
    (hb : b ∈ Y') (hu : u ∈ Y) :
    ∃ n ∈ oddCoreIn (normalizer (E : Set G)),
      a * b * u * (a * b)⁻¹ = n * (a * u * a⁻¹) := by
  refine ⟨a * (b * u * b⁻¹ * u⁻¹) * a⁻¹, ?_, by group⟩
  have h1 : b * u * b⁻¹ * u⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
    have h2 := (oddCoreIn (normalizer (E : Set G))).inv_mem (S.comm u hu b hb)
    have h3 : (u * b * u⁻¹ * b⁻¹)⁻¹ = b * u * b⁻¹ * u⁻¹ := by group
    rwa [h3] at h2
  exact CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (S.Y_le ha) h1

theorem conj_U (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H)
    (hW : E ⊔ E0 = (V ⊔ F) ⊔ (V' ⊔ F')) {a b : G} (ha : a ∈ Y) (hb : b ∈ Y')
    (hy : a * b ∈ sec8t84g_Q E E0) : ∀ u ∈ V ⊔ F, (a * b) * u * (a * b)⁻¹ ∈ V ⊔ F := by
  intro u hu
  have hW' : (a * b) * u * (a * b)⁻¹ ∈ E ⊔ E0 := sec8t84g3b_conj_W hy u (S.U_le_W hu)
  obtain ⟨n, hn, hne⟩ := S.conj_eq ha hb (S.U_le_Y hu)
  have hY : (a * b) * u * (a * b)⁻¹ ∈ Y := by
    rw [hne]
    exact Y.mul_mem (S.N_le hn) (Y.mul_mem (Y.mul_mem ha (S.U_le_Y hu)) (Y.inv_mem ha))
  exact S.W_inf_Y hW ⟨hW', hY⟩

end Sec8T84G3BSide

end CFSG.OddStandard.SmallF3.Omega
