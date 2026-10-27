module

public import CFSG.CGT.T75E.Basic

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T : Subgroup G}

abbrev toCenterQuot (G : Type) [Group G] : G →* G ⧸ Subgroup.center G :=
  QuotientGroup.mk' (Subgroup.center G)

theorem card_map_center_quot [Finite G] (h : Lemma26Hyp G T) :
    Nat.card (T.map (toCenterQuot G)) = Nat.card T := by
  have hker : T ⊓ (toCenterQuot G).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact hyp_inf_center_eq_bot h
  have hinj : Function.Injective ((toCenterQuot G).comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ T ⊓ (toCenterQuot G).ker := ⟨x.2, hx⟩
    rw [hker, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hr : ((toCenterQuot G).comp T.subtype).range = T.map (toCenterQuot G) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm

theorem isWC_map_center_quot [Finite G] (h : Lemma26Hyp G T) :
    IsWC (T.map (toCenterQuot G)) := by
  refine IsWC.map_of_ker_le_center h.1 (toCenterQuot G) (QuotientGroup.mk'_surjective _) ?_ ?_
  · rw [QuotientGroup.ker_mk']
  · rw [QuotientGroup.ker_mk']
    exact hyp_inf_center_eq_bot h

theorem classD_map_center_quot [Finite G] (h : Lemma26Hyp G T) :
    classD (T.map (toCenterQuot G)) = (toCenterQuot G) '' classD T := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := exists_mem_classD_of_mem_classD_map (QuotientGroup.mk'_surjective _) hy
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine map_mem_classD_map _ hx ?_
    intro h1
    exact hyp_classD_inf_center h hx ((QuotientGroup.eq_one_iff x).1 h1)

theorem hyp_map [Finite G] (h : Lemma26Hyp G T) :
    Lemma26Hyp (G ⧸ Subgroup.center G) (T.map (toCenterQuot G)) := by
  have hsurj : Function.Surjective (toCenterQuot G) := QuotientGroup.mk'_surjective _
  have hD := classD_map_center_quot h
  refine ⟨isWC_map_center_quot h, ?_, ?_, ?_, ?_⟩
  · rw [card_map_center_quot h]
    exact h.2.1
  · obtain ⟨d₀, hd₀⟩ := h.2.2.1
    refine ⟨toCenterQuot G d₀, ?_⟩
    rw [hD, hd₀]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MonoidHom.map_isConj _ hx
    · intro hy
      obtain ⟨c, hc⟩ := isConj_iff.1 hy
      obtain ⟨g, rfl⟩ := hsurj c
      exact ⟨g * d₀ * g⁻¹, isConj_iff.2 ⟨g, rfl⟩, by rw [map_mul, map_mul, map_inv]; exact hc⟩
  · exact isRootInvolutionSet_classD_map hsurj h.2.2.2.1
  · rw [hD, ← MonoidHom.map_closure, h.2.2.2.2, Subgroup.map_top_of_surjective _ hsurj]

theorem eq_of_map_eq_center_quot [Finite G] (h : Lemma26Hyp G T) {x y : G}
    (hUV : (conjSubgroup x T).map (toCenterQuot G) = (conjSubgroup y T).map (toCenterQuot G)) :
    conjSubgroup x T = conjSubgroup y T := by
  have hUwc : IsWC (conjSubgroup x T) := h.1.conj x
  have hUbot : conjSubgroup x T ≠ ⊥ := by
    intro hb
    have := card_conjSubgroup x T
    rw [hb, Subgroup.card_bot] at this
    have := h.2.1
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUbot
  have hu1' : u ≠ 1 := fun e => hu1 (Subtype.ext e)
  have hπu : toCenterQuot G u ∈ (conjSubgroup y T).map (toCenterQuot G) := by
    rw [← hUV]
    exact Subgroup.mem_map_of_mem _ hu
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hπu
  have hz : v⁻¹ * u ∈ Subgroup.center G := QuotientGroup.eq.1 hvu
  have hcent : conjSubgroup (y * x⁻¹) (conjSubgroup x T) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwv : w * v = v * w := elemAbelian_mul_comm (isElemAbelian_conjSubgroup h.1.1 y) hw hv
    have hzw : (v⁻¹ * u) * w = w * (v⁻¹ * u) := (Subgroup.mem_center_iff.1 hz w).symm
    have hu_eq : u = v * (v⁻¹ * u) := by group
    symm
    calc u * w = v * (v⁻¹ * u) * w := by rw [← hu_eq]
      _ = v * (w * (v⁻¹ * u)) := by rw [mul_assoc, hzw]
      _ = (v * w) * (v⁻¹ * u) := by rw [mul_assoc]
      _ = (w * v) * (v⁻¹ * u) := by rw [hwv]
      _ = w * (v * (v⁻¹ * u)) := by rw [mul_assoc]
      _ = w * u := by rw [← hu_eq]
  have := (hUwc.2 u hu hu1').2 (y * x⁻¹) hcent
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right] at this
  exact this.symm

end CFSG.CGT.T75E
