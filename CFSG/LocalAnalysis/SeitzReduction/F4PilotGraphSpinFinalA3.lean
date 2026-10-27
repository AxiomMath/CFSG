module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalComm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear
  blockSpecialLinear_mono blockSpecialLinear_eq_closure transvection_mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.Timmesfeld.LieEmbed (a5Root)

local instance f4PilotGraphSpinFinalA3NeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotGraphSpinFinalA3NeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Transvection

variable {F : Type} [Field F]

theorem transvection_commutator_six {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (s t : F) :
    SpecialLinearGroup.transvection hij s * SpecialLinearGroup.transvection hjk t *
        (SpecialLinearGroup.transvection hij s)⁻¹ * (SpecialLinearGroup.transvection hjk t)⁻¹ =
      SpecialLinearGroup.transvection hik (s * t) := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij s : Matrix (Fin 6) (Fin 6) F) *
      (SpecialLinearGroup.transvection hjk t : Matrix (Fin 6) (Fin 6) F) *
      (SpecialLinearGroup.transvection hij (-s) : Matrix (Fin 6) (Fin 6) F) *
      (SpecialLinearGroup.transvection hjk (-t) : Matrix (Fin 6) (Fin 6) F) =
      (SpecialLinearGroup.transvection hik (s * t) : Matrix (Fin 6) (Fin 6) F)
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hjk.symm,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hik.symm]
  simp only [zero_mul, add_zero, mul_neg, neg_mul, neg_neg, ← single_neg]
  abel

theorem sl6BlockA_le_blockSpecialLinear :
    sl6BlockA F ≤ blockSpecialLinear (K := F) lin6BlockA := by
  rw [sl6BlockA, closure_le]
  rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
  exact transvection_mem_blockSpecialLinear hij hi hj c

end Transvection

section A3


variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem xm_single_mem_e6ScLevi_A3 {k : Fin 5} (hk : k = 1 ∨ k = 2 ∨ k = 3) (c : K) :
    e6Data_valid.xm K (Pi.single (E6Pilot.chainNode k) 1) c ∈ e6ScLevi K e6A3Nodes ∧
      e6Data_valid.xm K (-Pi.single (E6Pilot.chainNode k) 1) c ∈ e6ScLevi K e6A3Nodes := by
  have hnode : E6Pilot.chainNode k ∈ e6A3Nodes := by
    rcases hk with rfl | rfl | rfl <;> decide
  have hrank : CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup (E6Pilot.chainNode k) ≤
      e6ScLevi K e6A3Nodes := CFSG.LieType.CurtisTits.rankOne_le_levi _ hnode
  rw [CFSG.LieType.CurtisTits.rankOne] at hrank
  exact ⟨hrank (mem_sup_left (e6Data_valid.xm_mem_rootGroup K _ c)),
    hrank (mem_sup_right (e6Data_valid.xm_mem_rootGroup K _ c))⟩

theorem graphParamHom_transvection_mem_A3 {i j : Fin 6} (hij : i ≠ j) (hi : i ∈ lin6BlockA)
    (hj : j ∈ lin6BlockA) (c : K) :
    graphParamHom K (RingEquiv.refl K) (SpecialLinearGroup.transvection hij c) ∈
      e6ScLevi K e6A3Nodes := by
  set Θ := graphParamHom K (RingEquiv.refl K) with hΘ
  have hs : ∀ (i j : Fin 6) (hij : i ≠ j) (k : Fin 5), (k = 1 ∨ k = 2 ∨ k = 3) →
      ((graphSwapPerm.symm i = k.castSucc ∧ graphSwapPerm.symm j = k.succ) ∨
        (graphSwapPerm.symm i = k.succ ∧ graphSwapPerm.symm j = k.castSucc)) →
      ∀ c : K, Θ (SpecialLinearGroup.transvection hij c) ∈ e6ScLevi K e6A3Nodes := by
    intro i j hij k hk h c
    rw [hΘ, graphParamHom_transvection]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, E6Pilot.a5Root_castSucc_succ]
      exact (xm_single_mem_e6ScLevi_A3 hk c).1
    · rw [h1, h2, E6Pilot.a5Root_succ_castSucc]
      exact (xm_single_mem_e6ScLevi_A3 hk c).2
  have hc : ∀ {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (c : K),
      (∀ c : K, Θ (SpecialLinearGroup.transvection hij c) ∈ e6ScLevi K e6A3Nodes) →
      (∀ c : K, Θ (SpecialLinearGroup.transvection hjk c) ∈ e6ScLevi K e6A3Nodes) →
      Θ (SpecialLinearGroup.transvection hik c) ∈ e6ScLevi K e6A3Nodes := by
    intro i j k hij hjk hik c h1 h2
    rw [← mul_one c, ← transvection_commutator_six hij hjk hik c 1, map_mul, map_mul, map_mul,
      map_inv, map_inv]
    exact mul_mem (mul_mem (mul_mem (h1 c) (h2 1)) (inv_mem (h1 c))) (inv_mem (h2 1))
  have s12 := hs 1 2 (by decide) 1 (by decide) (.inl ⟨by decide, by decide⟩)
  have s21 := hs 2 1 (by decide) 1 (by decide) (.inr ⟨by decide, by decide⟩)
  have s25 := hs 2 5 (by decide) 2 (by decide) (.inl ⟨by decide, by decide⟩)
  have s52 := hs 5 2 (by decide) 2 (by decide) (.inr ⟨by decide, by decide⟩)
  have s54 := hs 5 4 (by decide) 3 (by decide) (.inl ⟨by decide, by decide⟩)
  have s45 := hs 4 5 (by decide) 3 (by decide) (.inr ⟨by decide, by decide⟩)
  have s15 : ∀ c : K, Θ (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 5 by decide) c) ∈
      e6ScLevi K e6A3Nodes := fun c => hc (by decide) (by decide) _ c s12 s25
  have s51 : ∀ c : K, Θ (SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 1 by decide) c) ∈
      e6ScLevi K e6A3Nodes := fun c => hc (by decide) (by decide) _ c s52 s21
  have s24 : ∀ c : K, Θ (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 4 by decide) c) ∈
      e6ScLevi K e6A3Nodes := fun c => hc (by decide) (by decide) _ c s25 s54
  have s42 : ∀ c : K, Θ (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 2 by decide) c) ∈
      e6ScLevi K e6A3Nodes := fun c => hc (by decide) (by decide) _ c s45 s52
  have s14 : ∀ c : K, Θ (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) c) ∈
      e6ScLevi K e6A3Nodes := fun c => hc (by decide) (by decide) _ c s12 s24
  have s41 : ∀ c : K, Θ (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) c) ∈
      e6ScLevi K e6A3Nodes := fun c => hc (by decide) (by decide) _ c s42 s21
  simp only [lin6BlockA, Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
  · exact absurd rfl hij
  · exact s12 c
  · exact s14 c
  · exact s15 c
  · exact s21 c
  · exact absurd rfl hij
  · exact s24 c
  · exact s25 c
  · exact s41 c
  · exact s42 c
  · exact absurd rfl hij
  · exact s45 c
  · exact s51 c
  · exact s52 c
  · exact s54 c
  · exact absurd rfl hij

theorem e6ScLevi_A3_eq_map_blockSpecialLinear :
    e6ScLevi K e6A3Nodes =
      (blockSpecialLinear (K := K) lin6BlockA).map (graphParamHom K (RingEquiv.refl K)) := by
  refine le_antisymm (e6ScLevi_A3_le_map_sl6BlockA.trans (map_mono sl6BlockA_le_blockSpecialLinear))
    ?_
  rw [blockSpecialLinear_eq_closure, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨i, j, hij, c, hi, hj, rfl⟩, rfl⟩
  exact graphParamHom_transvection_mem_A3 hij hi hj c

end A3

section Pieces


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

omit
  [Finite K] [CharP K 2] in
theorem scLeviRestrict_injective_of_injective {S J : Finset (Fin (Tag.rank .E6))}
    {Φ : e6ScLevi K S →* G} (hΦ : Function.Injective Φ)
    (h : J ⊆ S) : Function.Injective (scLeviRestrict Φ h) :=
  hΦ.comp (Subgroup.inclusion_injective _)

theorem scLeviRestrict_A3_injective {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hkA : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes)) :
    Function.Injective (scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set Θ := graphParamEquiv K (RingEquiv.refl K) with hΘ
  rw [scLeviRestrict_apply] at hx
  have hxc := hkA hx
  obtain ⟨b, hb, hbx⟩ := (e6ScLevi_A3_eq_map_blockSpecialLinear (K := K)).le x.2
  have hΘb : Θ b = ⟨x, CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6A5Nodes x.2⟩ :=
    Subtype.ext hbx
  have hbc : b ∈ center (SpecialLinearGroup (Fin 6) K) := by
    rw [← Subgroup.map_center_eq Θ.symm]
    refine ⟨Θ b, ?_, Θ.symm_apply_apply b⟩
    rw [hΘb]
    exact hxc
  have hbot := inf_center_eq_bot_of_le_blockSpecialLinear (F := K) (j := 0) (by decide)
    (le_refl (blockSpecialLinear (K := K) lin6BlockA))
  have hb1 : b = 1 := by
    have : b ∈ blockSpecialLinear (K := K) lin6BlockA ⊓ center _ := ⟨hb, hbc⟩
    rw [hbot] at this
    exact this
  apply Subtype.ext
  rw [← hbx, hb1, map_one]
  rfl

theorem range_scLeviRestrict_A3_eq_pieceCore_A [Finite G] (hq : 4 ≤ Nat.card K)
    {e₁ : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hrA : ΦA.range = neighbourCore e₁ .X) (hkA : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hnA : IsLeviNormalizedA e₁ ΦA) :
    (scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes).range = pieceCore e₁ {1, 2} := by
  classical
  refine le_antisymm (range_scLeviRestrict_A3_le_pieceCore_A hq (N := .X) rfl hrA hnA) ?_
  obtain ⟨a₀, ha₀⟩ := exists_units_sq_ne_one_of_four_le hq
  set Θ := graphParamEquiv K (RingEquiv.refl K) with hΘ
  set Ψ : SpecialLinearGroup (Fin 6) K →* G := ΦA.comp Θ.toMonoidHom with hΨ
  have hr : Ψ.range = neighbourCore e₁ .X := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Θ.surjective,
      ← MonoidHom.range_eq_map, hrA]
  have hk : Ψ.ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
    intro x hx
    have h1 : Θ x ∈ center (e6ScLevi K e6A5Nodes) := hkA hx
    rw [← Subgroup.map_center_eq Θ.symm]
    exact ⟨Θ x, h1, Θ.symm_apply_apply x⟩
  have hn : Ψ.comp sp6ToSL6 = levi6Hom e₁ (RingEquiv.refl K) := MonoidHom.ext fun s => hnA s
  have h12 : leviTorusG e₁ {1, 2} ⊓ neighbourLeviG e₁ .X =
      (linTorusA (lin6Torus K) ⊤).map Ψ := by
    rw [← map_levi6Hom_sp6TorusA e₁ (RingEquiv.refl K), ← hn, ← Subgroup.map_map,
      map_sp6ToSL6_sp6TorusA]
  have hM := pieceCore_eq_map_of_cover e₁ hr hk (by decide) h12
    (rigid_lin6 (.inl rfl) (mem_top a₀) ha₀)
  rw [perfectCore_centralizer_lin6TorusA hq (mem_top a₀) ha₀] at hM
  rw [hM]
  rintro _ ⟨b, hb, rfl⟩
  have hbA3 : graphParamHom K (RingEquiv.refl K) b ∈ e6ScLevi K e6A3Nodes :=
    (e6ScLevi_A3_eq_map_blockSpecialLinear (K := K)).ge ⟨b, hb, rfl⟩
  refine ⟨⟨_, hbA3⟩, ?_⟩
  rw [scLeviRestrict_apply, hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 1

theorem range_scLeviRestrict_A3_D_eq_A [Finite G] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* adjointGroup .F4 K} {N₁ N₂ : AmalgamNeighbour}
    {e₁ e₂ : L ≃* adjointGroup .F4 K} (he₁ : IsNeighbourFrame e e₁ N₁)
    (he₂ : IsNeighbourFrame e e₂ N₂) {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hrA : ΦA.range = neighbourCore e N₁) (hkA : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hnA : IsLeviNormalizedA e₁ ΦA) {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e N₂) (hiY : Function.Injective ΦY)
    (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) :
    (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes).range =
      (scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes).range := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hA : (scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes).range = pieceCore e {1, 2} := by
    rw [← pieceCore_one_two_of_frame he₁]
    exact range_scLeviRestrict_A3_eq_pieceCore_A hq (hrA.trans (neighbourFrame_eq he₁).1) hkA hnA
  have hD := range_scLeviRestrict_A3_le_pieceCore_of_frame hK hf he₂ hrY hn
  have hdi : Function.Injective
      (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes) := by
    have h1 : Function.Injective (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) := by
      rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
      exact hiY.comp (spinEquivD4 K).symm.injective
    exact scLeviRestrict_injective_of_injective h1 _
  have hai := scLeviRestrict_A3_injective hkA
  refine Subgroup.eq_of_le_of_card_ge (hD.trans hA.ge) ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hdi).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective hai).toEquiv]

end Pieces

end CFSG.SeitzReduction.F4Pilot
