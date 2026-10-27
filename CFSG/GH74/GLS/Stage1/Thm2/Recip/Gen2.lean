module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.GH74.GLS.TwoThin.Rank

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_two_involutions_of_two_le_pRank {H : Subgroup G} (h : 2 ≤ pRank 2 ↥H) :
    ∃ a b : G, a ∈ H ∧ b ∈ H ∧ orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b := by
  have h' : 2 ≤ CFSG.Open.pRank 2 H := by rwa [← TwoThin.pRank_two_subgroup_eq_open H]
  obtain ⟨E, hEH, hE, hcard⟩ := SectionRank.exists_pRank one_lt_two H
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 H := Nat.pow_le_pow_right (by norm_num) h'
  have hnc : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  have h1 : 1 < ((E : Set G) \ {1}).ncard := by
    have := Set.ncard_sdiff_singleton_of_mem (s := (E : Set G)) (a := 1) (one_mem E)
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1
  have ha1 : a ≠ 1 := fun h => ha.2 (by simp [h])
  have hb1 : b ≠ 1 := fun h => hb.2 (by simp [h])
  have ha2 : a ^ 2 = 1 := hE.2 a ha.1
  have hb2 : b ^ 2 = 1 := hE.2 b hb.1
  refine ⟨a, b, hEH ha.1, hEH hb.1, orderOf_eq_prime ha2 ha1, orderOf_eq_prime hb2 hb1, ?_, hab⟩
  have hc := hE.1.is_comm.comm (⟨a, ha.1⟩ : E) ⟨b, hb.1⟩
  exact congrArg Subtype.val hc

theorem mem_normalizer_of_barMk_commute {C W Λ : Subgroup G} (hWC : W ≤ C)
    (hΛ : IsPCompIn 2 W Λ) {a : G} (haW : a ∈ W)
    (hcomm : ∀ (q : G) (hq : q ∈ Λ),
      TwoThin.barMk ↥C ⟨a, hWC haW⟩ * TwoThin.barMk ↥C ⟨q, hWC (hΛ.1 hq)⟩ =
        TwoThin.barMk ↥C ⟨q, hWC (hΛ.1 hq)⟩ * TwoThin.barMk ↥C ⟨a, hWC haW⟩) :
    a ∈ normalizer (Λ : Set G) := by
  set Λ' := Λ.map (MulAut.conj a).toMonoidHom with hΛ'
  have hW : W.map (MulAut.conj a).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer haW)
  have hΛ'W : IsPCompIn 2 W Λ' := by
    have h := isPCompIn_map_conj hΛ a
    rwa [hW] at h
  have hΛ'le : Λ' ≤ W := hΛ'W.1
  let f₀ : ↥W →* TwoThin.barQ ↥C := (TwoThin.barMk ↥C).comp (Subgroup.inclusion hWC)
  let f : ↥W →* ↥f₀.range := f₀.rangeRestrict
  have hsurj : Function.Surjective f := MonoidHom.rangeRestrict_surjective f₀
  have hodd : Odd (Nat.card f.ker) := by
    have hker : f.ker = f₀.ker := MonoidHom.ker_rangeRestrict f₀
    rw [hker]
    let incl : f₀.ker →* (TwoThin.barMk ↥C).ker :=
      { toFun := fun w => ⟨Subgroup.inclusion hWC w.1, w.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective incl := by
      intro u v h
      have h1 := congrArg (fun z : (TwoThin.barMk ↥C).ker => (z : ↥C)) h
      apply Subtype.ext
      exact Subgroup.inclusion_injective hWC h1
    exact TwoThin.odd_card_ker_barMk.of_dvd_nat (Subgroup.card_dvd_of_injective incl hinj)
  have hconj : ∀ q : G, (hq : q ∈ Λ) →
      TwoThin.barMk ↥C ⟨a * q * a⁻¹, hWC (hΛ'le ⟨q, hq, by simp [MulAut.conj_apply]⟩)⟩ =
        TwoThin.barMk ↥C ⟨q, hWC (hΛ.1 hq)⟩ := by
    intro q hq
    have h := hcomm q hq
    have e : (⟨a * q * a⁻¹, hWC (hΛ'le ⟨q, hq, by simp [MulAut.conj_apply]⟩)⟩ : ↥C) =
        ⟨a, hWC haW⟩ * ⟨q, hWC (hΛ.1 hq)⟩ * ⟨a, hWC haW⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  have hΛ2 : TwoComponents.IsTwoComponent (Λ.subgroupOf W) := (TwoThin.isPCompIn_two_iff.mp hΛ).2
  have hΛ'2 : TwoComponents.IsTwoComponent (Λ'.subgroupOf W) :=
    (TwoThin.isPCompIn_two_iff.mp hΛ'W).2
  have himg : (Λ.subgroupOf W).map f = (Λ'.subgroupOf W).map f := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwΛ : (w : G) ∈ Λ := hw
      have hwC : (w : G) ∈ C := hWC w.2
      refine ⟨⟨a * w * a⁻¹, (mem_normalizer_iff.mp (le_normalizer haW) w).mp w.2⟩,
        ⟨w, hwΛ, by simp [MulAut.conj_apply]⟩, ?_⟩
      apply Subtype.ext
      have := hconj w hwΛ
      exact this
    · rintro ⟨w', hw', rfl⟩
      obtain ⟨q, hq, hqw⟩ := hw'
      have hqW : q ∈ W := (hΛ.1 hq)
      refine ⟨⟨q, hqW⟩, hq, ?_⟩
      apply Subtype.ext
      have := hconj q hq
      have hw'q : (w' : G) = a * q * a⁻¹ := by
        calc (w' : G) = W.subtype w' := rfl
          _ = (MulAut.conj a).toMonoidHom q := hqw.symm
          _ = a * q * a⁻¹ := by simp [MulAut.conj_apply]
      have e : f₀ w' = TwoThin.barMk ↥C ⟨a * q * a⁻¹, hWC (hΛ'le ⟨q, hq, by simp [MulAut.conj_apply]⟩)⟩ := by
        show TwoThin.barMk ↥C (Subgroup.inclusion hWC w') = _
        congr 1
        exact Subtype.ext hw'q
      show TwoThin.barMk ↥C ⟨q, hWC hqW⟩ = (f₀ w' : TwoThin.barQ ↥C)
      rw [e, this]
  have heq := OddKernelTwoComponents.lift_unique f hsurj hodd _ _ hΛ2 hΛ'2 himg
  have heq' := Subgroup.subgroupOf_inj.mp heq
  rw [inf_eq_left.mpr hΛ.1, inf_eq_left.mpr hΛ'le] at heq'
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq'.symm

theorem eq_or_eq_of_isPCompIn_le_sup {X A B K : Subgroup G} (hA : IsPCompIn 2 X A)
    (hB : IsPCompIn 2 X B) (hK : IsPCompIn 2 X K) (hle : K ≤ A ⊔ B) : K = A ∨ K = B := by
  obtain ⟨hAX, hA2⟩ := TwoThin.isPCompIn_two_iff.mp hA
  obtain ⟨hBX, hB2⟩ := TwoThin.isPCompIn_two_iff.mp hB
  obtain ⟨hKX, hK2⟩ := TwoThin.isPCompIn_two_iff.mp hK
  have hle' : K.subgroupOf X ≤ A.subgroupOf X ⊔ B.subgroupOf X := by
    rw [← Subgroup.subgroupOf_sup hAX hBX]
    exact fun k hk => hle hk
  have hmap : (K.subgroupOf X).map (TwoThin.barMk ↥X) ≤
      (A.subgroupOf X).map (TwoThin.barMk ↥X) ⊔ (B.subgroupOf X).map (TwoThin.barMk ↥X) := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hle'
  rcases eq_or_eq_of_isComponent_le_sup (TwoThin.isComponent_map_barMk hK2)
      (TwoThin.isComponent_map_barMk hA2) (TwoThin.isComponent_map_barMk hB2) hmap with h | h
  · left
    have := OddKernelTwoComponents.lift_unique (TwoThin.barMk ↥X) TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk _ _ hK2 hA2 h
    have h4 := Subgroup.subgroupOf_inj.mp this
    rwa [inf_eq_left.mpr hKX, inf_eq_left.mpr hAX] at h4
  · right
    have := OddKernelTwoComponents.lift_unique (TwoThin.barMk ↥X) TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk _ _ hK2 hB2 h
    have h4 := Subgroup.subgroupOf_inj.mp this
    rwa [inf_eq_left.mpr hKX, inf_eq_left.mpr hBX] at h4

theorem pLayerOf_map_conj_le {X : Subgroup G} {g : G} (hg : g ∈ X) :
    (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom ≤ pLayerOf 2 X := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hX : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
  have h := isPCompIn_map_conj hK g
  rw [hX] at h
  exact le_sSup h

end CFSG.GH74.GLS.Stage1.Thm2.Recip
