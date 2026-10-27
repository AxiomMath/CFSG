module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8UArg
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Frame
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhCaseTwo

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup CFSG.Quasithin

namespace Child8Weyl

variable {W : Type} [Group W] [Finite W] (M : Child8Weyl W) {G : Type} [Group G] {ψ : W →* G}

theorem exists_sylow_TG [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = M.T.map ψ :=
  exists_sylow_map hψ hH M.card_T M.card_W (by decide) M.z_mem_T M.z_ne_one M.center_T

theorem E1G_le_TG : (ψ.comp M.ιE1).range ≤ M.T.map ψ := by
  rintro _ ⟨v, rfl⟩
  exact mem_map_of_mem ψ (M.ιE1_mem_T v)

theorem wc_E1G (hψ : Function.Injective ψ) :
    IsWeaklyClosedIn (ψ.comp M.ιE1).range (M.T.map ψ) :=
  isWeaklyClosedIn_of_elementary_unique (fun _ ha => by
      rw [pow_two]
      exact mul_self_of_mem_frameRange ha)
    (fun B hB hB2 hBc => M.elem_TG8 hψ hB (fun b hb => by rw [← pow_two]; exact hB2 b hb)
      (hBc.trans (M.card_E1G hψ)))

theorem zG_mem_E1G : ψ M.z ∈ (ψ.comp M.ιE1).range :=
  ⟨Multiplicative.ofAdd frameZ, by rw [MonoidHom.comp_apply, M.ιE1_frameZ]⟩

theorem normalizer_E1G_fixes [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) :
    ∀ n ∈ normalizer (Set.range (ψ.comp M.ιE1)), n * ψ M.z * n⁻¹ = ψ M.z := by
  have hι : Function.Injective (ψ.comp M.ιE1) := hψ.comp M.ιE1_injective
  let _ : MulAction (normalizer (Set.range (ψ.comp M.ιE1))) FrameVec :=
    coordAction (ψ.comp M.ιE1) hι
  have key := normalizer_fixes_frameZ (N := normalizer (Set.range (ψ.comp M.ιE1)))
    (coordConj_add hι) (fun n hn => ?_) (fun σ hσ => ?_) (fun n B hB h => ?_)
  · intro n hn
    have h := (coordConj_eq_iff hψ M.ιE1_injective ⟨n, hn⟩ frameZ).1 (key ⟨n, hn⟩)
    rwa [M.ιE1_frameZ] at h
  · have hz := (coordConj_eq_iff hψ M.ιE1_injective n frameZ).1 hn
    rw [M.ιE1_frameZ] at hz
    obtain ⟨w, hw⟩ := (hH n).2 (by
      calc (n : G) * ψ M.z = (n : G) * ψ M.z * (n : G)⁻¹ * n := by group
        _ = ψ M.z * n := by rw [hz])
    have hconj : ∀ v, w * M.ιE1 v * w⁻¹ =
        M.ιE1 (Multiplicative.ofAdd (coordConj (ψ.comp M.ιE1) n (Multiplicative.toAdd v))) :=
      fun v => (coordConj_of_eq hψ hw (Multiplicative.toAdd v)).symm
    obtain ⟨σ, hσ, hσw⟩ := M.frame_up w (fun v => by rw [hconj]; exact ⟨_, rfl⟩)
    exact ⟨σ, hσ, fun v => M.ιE1_injective ((hconj (Multiplicative.ofAdd v)).symm.trans
      (hσw v))⟩
  · obtain ⟨w, -, hw⟩ := M.frame_gens σ hσ
    obtain ⟨hn, hnv⟩ := coordConj_of_conj hψ M.ιE1_injective (w := w) (f := permVec σ)
      (fun v => hw (Multiplicative.toAdd v))
    exact ⟨⟨ψ w, hn⟩, hnv⟩
  · obtain ⟨w, -, hw⟩ := M.exists_conj_plane hB
    have hspec := coordConj_spec (ψ.comp M.ιE1) n frameZ
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, M.ιE1_frameZ] at hspec
    apply M.not_isConj hψ hH
    refine isConj_iff.2 ⟨ψ w * n, ?_⟩
    have h' : coordConj (ψ.comp M.ιE1) n frameZ = blockVec B := h
    rw [h'] at hspec
    rw [← hw, map_mul, map_mul, map_inv, hspec]
    group

theorem false_of_case_two [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hψ : Function.Injective ψ) (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) :
    False := by
  obtain ⟨P, hP⟩ := M.exists_sylow_TG hψ hH
  have hz2 : orderOf (ψ M.z) = 2 :=
    orderOf_eq_prime (by rw [pow_two, M.zG_mul_self]) (M.zG_ne_one hψ)
  refine false_of_isolated_involution hnonab hz2 fun y hy hzy => ?_
  obtain ⟨y', rfl⟩ := (hH y).2 (mem_centralizer_singleton_iff.1 hy)
  have hy2 : y' * y' = 1 := hψ (by
    rw [map_mul, map_one]
    exact mul_self_of_isConj M.zG_mul_self hzy)
  obtain ⟨w, v, hv⟩ := M.inv_W y' hy2
  have hx : ψ (M.ιE1 v) ∈ (ψ.comp M.ιE1).range := ⟨v, rfl⟩
  have hzx : IsConj (ψ M.z) (ψ (M.ιE1 v)) :=
    hzy.trans (isConj_iff.2 ⟨ψ w, by rw [hv, map_mul, map_mul, map_inv]⟩)
  obtain ⟨n, hn, hnx⟩ := exists_normalizer_conj_of_isWeaklyClosedIn P (hP ▸ M.E1G_le_TG)
    (fun _ ha _ hb => comm_of_mem_frameRange ha hb) (hP ▸ M.wc_E1G hψ) M.zG_mem_E1G hx hzx
  rw [M.normalizer_E1G_fixes hψ hH n hn, hv, map_mul, map_mul, map_inv] at hnx
  calc ψ y' = (ψ w)⁻¹ * (ψ w * ψ y' * (ψ w)⁻¹) * ψ w := by group
    _ = (ψ w)⁻¹ * ψ M.z * ψ w := by rw [← hnx]
    _ = (ψ w)⁻¹ * (ψ M.z * ψ w) := by group
    _ = ψ M.z := by rw [← M.zG_comm hH w]; group

end Child8Weyl

end CFSG.EvenSmallLie.OmegaEight.Child8
