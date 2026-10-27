module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Main

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

theorem mem_of_index_two_of_cube {X : Type} [Group X] {H : Subgroup X} (hH : H.index = 2)
    {x : X} (hx : x * x * x = 1) : x ∈ H := by
  have h := Subgroup.sq_mem_of_index_two hH (x ^ 2)
  have e : (x ^ 2) ^ 2 = x := by
    calc (x ^ 2) ^ 2 = (x * x * x) * x := by rw [sq, sq]; simp only [mul_assoc]
      _ = x := by rw [hx, one_mul]
  rwa [e] at h

variable {G : Type} [Group G] {L A : Subgroup G} {e : L ≃* S24}
  (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hA


theorem ker_tetE_le_of_index_two (hAL : A ≤ L) {H : Subgroup (egNL L A)} (hH : H.index = 2) :
    (tetE hA).ker ≤ H := by
  have hω3 := Certificates.certificate24848.2.1
  have hcube := Certificates.certificate24864.2.2.2.2.2.2.2.2.2.2
  have hwN : qdIota e qdOmega ∈ egNL L A := qdIota_mem_egNL e hAL hA qdNorm_qdOmega
  have hwH : (⟨qdIota e qdOmega, hwN⟩ : egNL L A) ∈ H := by
    refine mem_of_index_two_of_cube hH (Subtype.ext ?_)
    show qdIota e qdOmega * qdIota e qdOmega * qdIota e qdOmega = 1
    rw [← map_mul, ← map_mul, hω3, map_one]
  have hwe : nlE e (⟨qdIota e qdOmega, hwN⟩ : egNL L A) = qdOmega := nlE_mk e _ hwN
  have key : ∀ x ∈ m24E1l, ∃ u ∈ H, nlE e u = qdOmega * x := by
    intro x hx
    have hu := qdIota_mem_egNL e hAL hA (qdNorm_qdOmega.mul (qdNorm_of_mem hx))
    refine ⟨⟨_, hu⟩, mem_of_index_two_of_cube hH (Subtype.ext ?_), nlE_mk e _ hu⟩
    show qdIota e (qdOmega * x) * qdIota e (qdOmega * x) * qdIota e (qdOmega * x) = 1
    rw [← map_mul, ← map_mul, hcube x hx, map_one]
  intro h hh
  rw [MonoidHom.mem_ker, tetE_eq_one_iff] at hh
  have hK := mem_sxK0_of_fix (nlE_norm hA h) hh
  simp only [sxK0, List.mem_append, List.mem_map] at hK
  rcases hK with (hK | ⟨x, hx, hxe⟩) | ⟨x, hx, hxe⟩
  · obtain ⟨u, huH, hu⟩ := key _ hK
    have h1 : h = (⟨qdIota e qdOmega, hwN⟩ : egNL L A)⁻¹ * u :=
      nlE_injective e (by rw [map_mul, map_inv, hwe, hu]; group)
    rw [h1]
    exact H.mul_mem (H.inv_mem hwH) huH
  · obtain ⟨u, huH, hu⟩ := key x hx
    have h1 : h = u := nlE_injective e (by rw [hu, hxe])
    rw [h1]
    exact huH
  · obtain ⟨u, huH, hu⟩ := key x hx
    have h1 : h = (⟨qdIota e qdOmega, hwN⟩ : egNL L A)⁻¹ *
        (⟨qdIota e qdOmega, hwN⟩ : egNL L A)⁻¹ * u :=
      nlE_injective e (by rw [map_mul, map_mul, map_inv, hwe, hu, ← hxe]; group)
    rw [h1]
    exact H.mul_mem (H.mul_mem (H.inv_mem hwH) (H.inv_mem hwH)) huH

theorem index_two_iff (hAL : A ≤ L) (H : Subgroup (egNL L A)) :
    H.index = 2 ↔ H = (alternatingGroup (Fin 6)).comap (tetE hA) := by
  constructor
  · intro hH
    have hle := ker_tetE_le_of_index_two hA hAL hH
    have hmap : (H.map (tetE hA)).index = 2 := by
      rw [Subgroup.index_map_eq (hf1 := tetE_surjective hA hAL) (hf2 := hle), hH]
    rw [← Subgroup.comap_map_eq_self hle, Equiv.Perm.eq_alternatingGroup_of_index_eq_two hmap]
  · rintro rfl
    rw [Subgroup.index_comap_of_surjective (hf := tetE_surjective hA hAL),
      alternatingGroup.index_eq_two]

theorem card_egNL_eq (hAL : A ≤ L) : Nat.card (egNL L A) = 138240 := by
  have h1 := Subgroup.card_mul_index (tetE hA).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (tetE_surjective hA hAL),
    card_ker_tetE hA hAL, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at h1
  rw [← h1]
  decide

theorem card_comap_alt (hAL : A ≤ L) :
    Nat.card ((alternatingGroup (Fin 6)).comap (tetE hA)) = 69120 := by
  have h1 := Subgroup.card_mul_index ((alternatingGroup (Fin 6)).comap (tetE hA))
  rw [(index_two_iff hA hAL _).2 rfl, card_egNL_eq hA hAL] at h1
  omega

end CFSG.EvenSporadicStandard.M24Std.Sym6

namespace CFSG.EvenSporadicStandard.M24Std

open Sym6

variable {G : Type} [Group G]

theorem sym6Index_of_type
    {L A : Subgroup G} (h : SextetType L A) :
    Nat.card (egNL L A) = 138240 ∧
      ∃ φ : egNL L A →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        A.subgroupOf (egNL L A) ≤ φ.ker ∧ Nat.card φ.ker = 192 ∧
        (Equiv.Perm.sign.comp φ).ker = (alternatingGroup (Fin 6)).comap φ ∧
        Nat.card ((alternatingGroup (Fin 6)).comap φ) = 69120 ∧
        ∀ H : Subgroup (egNL L A), H.index = 2 ↔ H = (alternatingGroup (Fin 6)).comap φ := by
  obtain ⟨hAL, e, hA⟩ := h
  exact ⟨card_egNL_eq hA hAL, tetE hA, tetE_surjective hA hAL, le_ker_tetE hA,
    card_ker_tetE hA hAL, (MonoidHom.comap_ker _ _).symm, card_comap_alt hA hAL,
    index_two_iff hA hAL⟩

end CFSG.EvenSporadicStandard.M24Std
