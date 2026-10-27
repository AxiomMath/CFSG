module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.Trans

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_zpowers {g r : G} (h : g * r * g⁻¹ ∈ zpowers r) :
    g ∈ normalizer (zpowers r : Set G) := by
  have hmap : (zpowers r).map (MulAut.conj g).toMonoidHom = zpowers r := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.2 (by simpa using h)
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hmap]
    exact ⟨x, hx, by simp⟩
  · rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    rwa [← mul_left_cancel (mul_right_cancel hyx)]

theorem exists_conj_mem_zpowers {H : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hH : ¬ p ^ 2 ∣ Nat.card H) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hxo : orderOf x = p)
    (hyo : orderOf y = p) : ∃ d ∈ H, d * y * d⁻¹ ∈ zpowers x := by
  have key : ∀ w : H, orderOf w = p → ∀ S : Sylow p H, zpowers w ≤ S →
      (S : Subgroup H) = zpowers w := by
    intro w hw S hS
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 S.isPGroup'
    have hdvd : p ^ k ∣ Nat.card H := hk ▸ Subgroup.card_subgroup_dvd_card (S : Subgroup H)
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact hH (dvd_trans (pow_dvd_pow p (by omega)) hdvd)
    refine (Subgroup.eq_of_le_of_card_ge hS ?_).symm
    rw [Nat.card_zpowers, hw, hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hk1
      _ = p := pow_one p
  have hx'o : orderOf (⟨x, hx⟩ : H) = p := by rw [← Subgroup.orderOf_coe]; exact hxo
  have hy'o : orderOf (⟨y, hy⟩ : H) = p := by rw [← Subgroup.orderOf_coe]; exact hyo
  have hpx : IsPGroup p (zpowers (⟨x, hx⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o, pow_one])
  have hpy : IsPGroup p (zpowers (⟨y, hy⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'o, pow_one])
  obtain ⟨Sx, hSx⟩ := hpx.exists_le_sylow
  obtain ⟨Sy, hSy⟩ := hpy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Sy Sx
  have hmem : (⟨y, hy⟩ : H) ∈ (Sy : Subgroup H) := hSy (mem_zpowers _)
  have h2 : MulAut.conj g • (⟨y, hy⟩ : H) ∈ (Sx : Subgroup H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  rw [key _ hx'o Sx hSx] at h2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
  refine ⟨g, g.2, mem_zpowers_iff.2 ⟨k, ?_⟩⟩
  have := congrArg Subtype.val hk
  simpa [MulAut.smul_def] using this

theorem not_dvd_card_NL {L A : Subgroup G} {z : G}
    (hs : LocalSetting G L z) : ¬ 5 ^ 2 ∣ Nat.card (egNL L A) := by
  intro h
  have hL : Nat.card L = 244823040 := by
    obtain ⟨e⟩ := hs.sporadic
    have e' : L ≃* NativeSporadic.M24 := e
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  have := dvd_trans h (Subgroup.card_dvd_of_le (inf_le_right : egNL L A ≤ L))
  rw [hL] at this
  norm_num at this

end CFSG.EvenSporadicStandard.M24Std.Trans
