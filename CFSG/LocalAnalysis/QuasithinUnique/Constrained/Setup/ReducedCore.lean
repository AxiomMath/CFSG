module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6

section OddResidual

variable {H : Type*} [Group H]

@[expose] def oddResidualPreimage (H : Type*) [Group H] : Subgroup H :=
  (Subgroup.closure {x : H ⧸ CFSG.Open.pCore 2 H | Odd (orderOf x)}).comap
    (QuotientGroup.mk' (CFSG.Open.pCore 2 H))

theorem closure_odd_eq_map_oddOrderSubgroup [Finite H] {Y : Type*} [Group Y] {φ : H →* Y}
    (hφ : Function.Surjective φ) :
    Subgroup.closure {y : Y | Odd (orderOf y)} = (oddOrderSubgroup (⊤ : Subgroup H)).map φ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφ y
    obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (Subgroup.mem_top x)
    exact mem_of_odd_orderOf_of_pow_mem hy (k := k)
      (by rw [← map_pow]; exact Subgroup.mem_map_of_mem φ hk)
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure (Odd.of_dvd_nat hx.2 (orderOf_map_dvd φ x))

theorem oddResidualPreimage_eq [Finite H] :
    oddResidualPreimage H = twoResidual (⊤ : Subgroup H) ⊔ CFSG.Open.pCore 2 H := by
  have h := closure_odd_eq_map_oddOrderSubgroup (H := H)
    (φ := QuotientGroup.mk' (CFSG.Open.pCore 2 H)) (QuotientGroup.mk'_surjective _)
  unfold oddResidualPreimage
  rw [h, oddOrderSubgroup_eq_twoResidual, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem twoResidual_top_normal [Finite H] : (twoResidual (⊤ : Subgroup H)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))

theorem oddResidualPreimage_normal [Finite H] : (oddResidualPreimage H).Normal := by
  rw [oddResidualPreimage_eq]
  have := twoResidual_top_normal (H := H)
  infer_instance

end OddResidual

section Core

variable {H : Type*} [Group H] [Finite H] {T X : Subgroup H}

theorem qt_A7_unique_Sylow_overgroup_core_and_simple_section
    (hT : IsSylowTwoOf T (⊤ : Subgroup H)) (hTn : ¬ T.Normal) (hTX : T ≤ X) (hXH : X < ⊤)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ X) :
    (CFSG.Open.pCore 2 H ≤ kerIn X ⊤ ∧ kerIn X ⊤ < oddResidualPreimage H) ∧
    (Group.IsNilpotent ((kerIn X ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))) ∧
      Odd (Nat.card ((kerIn X ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)))) ∧
      Group.IsSolvable (kerIn X ⊤)) ∧
    oddResidualPreimage H ⊔ T = ⊤ ∧
    ((oddResidualPreimage H).Normal ∧
      ∀ N : Subgroup H, N.Normal → kerIn X ⊤ ≤ N → N ≤ oddResidualPreimage H →
        N = kerIn X ⊤ ∨ N = oddResidualPreimage H) ∧
    (∀ N : Subgroup H, N.Normal → CFSG.Open.pCore 2 H ≤ N → ¬ N ≤ kerIn X ⊤ →
      oddResidualPreimage H ≤ N) ∧
    (¬ Group.IsSolvable H →
      ∃ L : Subgroup (H ⧸ kerIn X ⊤), IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
        L ≤ (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤)) ∧
        (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤)) =
          ⨆ t ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)), conjSub t L ∧
        sSupIndep {S : Subgroup (H ⧸ kerIn X ⊤) |
          ∃ t ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)), S = conjSub t L} ∧
        (∀ t ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)),
          ((conjSub t L).subgroupOf
            ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤)))).Normal) ∧
        (∀ t ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)),
          IsSimpleGroup (conjSub t L) ∧ ¬ IsMulCommutative (conjSub t L)) ∧
        (∀ t ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)),
          ∀ t' ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)),
          (∃ s ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)), conjSub t (conjSub t' L) = conjSub s L) ∧
          ∃ s ∈ T.map (QuotientGroup.mk' (kerIn X ⊤)),
            conjSub s (conjSub t L) = conjSub t' L)) := by
  have hTn' : ¬ (⊤ : Subgroup H) ≤ Subgroup.normalizer (T : Set H) := fun hle =>
    hTn (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle))
  have h : MinParabolic (⊤ : Subgroup H) T X := minParabolic_of_uniqueMax hT hTn' hTX hXH hmax
  set R := CFSG.Open.pCore 2 H
  set J := kerIn X ⊤
  set φ₂ := QuotientGroup.mk' R with hφ₂
  have hsurj₂ : Function.Surjective φ₂ := QuotientGroup.mk'_surjective _
  have hker₂ : φ₂.ker ≤ X := by
    rw [hφ₂, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hRJ : R ≤ J := h.pCore_le_kerIn
  have hmpY := h.map_of_surjective hsurj₂ hker₂
  have hOY : CFSG.Open.pCore 2 (H ⧸ R) = ⊥ := B6.pCore_quotient_pCore
  have hJmap : kerIn (X.map φ₂) ⊤ = J.map φ₂ := kerIn_map_top hsurj₂ hker₂
  have hnil : Group.IsNilpotent (J.map φ₂) := by
    have h1 := hmpY.isNilpotent_kerIn hOY
    rw [hJmap] at h1
    exact h1
  have hodd : Odd (Nat.card (J.map φ₂)) := by
    have := hmpY.card_kerIn_odd hOY
    rw [hJmap] at this
    exact Nat.not_even_iff_odd.mp (fun he => this (even_iff_two_dvd.mp he))
  have hK0 : oddResidualPreimage H = twoResidual (⊤ : Subgroup H) ⊔ R := oddResidualPreimage_eq
  have hKK0 : twoResidual (⊤ : Subgroup H) ≤ oddResidualPreimage H := by
    rw [hK0]
    exact le_sup_left
  have hJK0 : J ≤ oddResidualPreimage H := by
    intro j hj
    rw [oddResidualPreimage, Subgroup.mem_comap]
    refine Subgroup.subset_closure ?_
    have hmem : φ₂ j ∈ J.map φ₂ := Subgroup.mem_map_of_mem _ hj
    have h1 : orderOf (⟨φ₂ j, hmem⟩ : J.map φ₂) ∣ Nat.card (J.map φ₂) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hJlt : J < oddResidualPreimage H :=
    lt_of_le_of_ne hJK0 fun heq => h.not_twoResidual_le_kerIn (hKK0.trans heq.symm.le)
  have hdich : ∀ N : Subgroup H, N.Normal → N ≤ J ∨ twoResidual (⊤ : Subgroup H) ≤ N :=
    fun N hN => h.le_kerIn_or_twoResidual_le le_top (Subgroup.normalizer_eq_top_iff.mpr hN).ge
  have hcontains : ∀ N : Subgroup H, N.Normal → R ≤ N → ¬ N ≤ J → oddResidualPreimage H ≤ N := by
    intro N hN hRN hNJ
    rw [hK0]
    exact sup_le ((hdich N hN).resolve_left hNJ) hRN
  refine ⟨⟨hRJ, hJlt⟩, ⟨hnil, hodd, h.isSolvable_kerIn⟩, ?_, ⟨oddResidualPreimage_normal, ?_⟩,
    hcontains, ?_⟩
  ·
    refine top_unique ?_
    exact (sup_twoResidual_eq hT).symm.le.trans (sup_le le_sup_right (hKK0.trans le_sup_left))
  · intro N hN hJN hNK
    by_cases hNJ : N ≤ J
    · exact Or.inl (le_antisymm hNJ hJN)
    · exact Or.inr (le_antisymm hNK (hcontains N hN (hRJ.trans hJN) hNJ))
  · intro hns
    obtain ⟨L, hL, hLn, hLK, hgen, hind, hnorm, -, -⟩ := h.nonsolvable_structure hns
    have hRmap : R.map (QuotientGroup.mk' J) = ⊥ := by
      rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
      intro r hr
      rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hRJ hr
    have hK0map : (oddResidualPreimage H).map (QuotientGroup.mk' J) =
        (twoResidual (⊤ : Subgroup H)).map (QuotientGroup.mk' J) := by
      rw [hK0, Subgroup.map_sup, hRmap, sup_bot_eq]
    rw [hK0map]
    refine ⟨L, hL, hLn, hLK, hgen, hind, hnorm, fun t _ => ⟨?_, ?_⟩, fun t ht t' ht' => ⟨?_, ?_⟩⟩
    · exact ((MulAut.conj t).subgroupMap L).symm.isSimpleGroup
    · intro hc
      refine hLn ⟨⟨fun a b => ?_⟩⟩
      apply ((MulAut.conj t).subgroupMap L).injective
      rw [map_mul, map_mul]
      exact hc.is_comm.comm _ _
    · exact ⟨t * t', Subgroup.mul_mem _ ht ht', (conjSub_mul t t' L).symm⟩
    · refine ⟨t' * t⁻¹, Subgroup.mul_mem _ ht' (Subgroup.inv_mem _ ht), ?_⟩
      rw [← conjSub_mul, inv_mul_cancel_right]

end Core

end CFSG.QuasithinUnique.Setup
