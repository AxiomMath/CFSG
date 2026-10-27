module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_card_le_of_sylow {H S W : Subgroup G} (hS : IsSylow2Of S H) (hW : W ≤ H)
    (hW2 : IsPGroup 2 W) : Nat.card W ≤ Nat.card S := by
  obtain ⟨Q, hQ, hWQ⟩ := exists_isSylow2Of_ge hW2 hW
  obtain ⟨a, ha, hiff⟩ := IsSylow2Of.exists_conj_mem hS hQ
  have hmap : Q.map (MulAut.conj a⁻¹).toMonoidHom = S := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      simpa [MulAut.conj_apply] using (hiff y).mp hy
    · intro hx
      refine ⟨a * x * a⁻¹, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [hiff]
      simpa [mul_assoc] using hx
  have hcard : Nat.card Q = Nat.card S := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective]
  calc Nat.card W ≤ Nat.card Q := Subgroup.card_le_of_le hWQ
    _ = Nat.card S := hcard

theorem sec8t84_isSylow2Of_of_card_ge {H U V : Subgroup G} (hV : IsSylow2Of V H) (hU : U ≤ H)
    (hU2 : IsPGroup 2 U) (hcard : Nat.card V ≤ Nat.card U) : IsSylow2Of U H := by
  have hcard' : Nat.card U ≤ Nat.card V := sec8t84_card_le_of_sylow hV hU hU2
  have hcardeq : Nat.card U = Nat.card V := le_antisymm hcard' hcard
  refine ⟨hU, hU2, ?_⟩
  have h1 : U.relIndex H * Nat.card U = Nat.card H := by
    have h := Subgroup.relIndex_mul_card (H := U) (K := H)
    rwa [inf_eq_left.mpr hU] at h
  have h2 : V.relIndex H * Nat.card V = Nat.card H := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := H)
    rwa [inf_eq_left.mpr hV.1] at h
  have hrel : U.relIndex H = V.relIndex H := by
    have hmul : U.relIndex H * Nat.card U = V.relIndex H * Nat.card U := by
      calc U.relIndex H * Nat.card U = Nat.card H := h1
        _ = V.relIndex H * Nat.card V := h2.symm
        _ = V.relIndex H * Nat.card U := by rw [← hcardeq]
    haveI : Nonempty U := ⟨1, U.one_mem⟩
    exact Nat.mul_right_cancel (Finite.card_pos (α := U)) hmul
  rw [hrel]
  exact hV.2.2

theorem sec8t84_two_syl_conj {H U V : Subgroup G} (hV : IsSylow2Of V H) (hU : U ≤ H)
    (hU2 : IsPGroup 2 U) (hcard : Nat.card V ≤ Nat.card U) :
    ∃ h ∈ H, U = V.map (MulAut.conj h).toMonoidHom := by
  have hU' : IsSylow2Of U H := sec8t84_isSylow2Of_of_card_ge hV hU hU2 hcard
  obtain ⟨a, ha, hiff⟩ := IsSylow2Of.exists_conj_mem hV hU'
  refine ⟨a, ha, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨a⁻¹ * x * a, (hiff x).mp hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨v, hv, rfl⟩
    rw [hiff]
    simpa [mul_assoc] using hv

theorem sec8t84_normalizing_le {H T W : Subgroup G} (hT : IsSylow2Of T H) (hW : W ≤ H)
    (hW2 : IsPGroup 2 W) (hWT : W ≤ normalizer (T : Set G)) : W ≤ T := by
  have hsup2 : IsPGroup 2 (T ⊔ W : Subgroup G) := hT.2.1.to_sup_of_normal_left' hW2 hWT
  have hsupH : (T ⊔ W : Subgroup G) ≤ H := sup_le hT.1 hW
  have heq : (T ⊔ W : Subgroup G) = T :=
    IsSylow2Of.eq_of_le hT hsupH hsup2 le_sup_left
  exact heq ▸ le_sup_right

theorem sec8t84_normalizer_map (E : Subgroup G) (u : G) :
    normalizer ((E.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) =
      (normalizer (E : Set G)).map (MulAut.conj u).toMonoidHom := by
  exact (Subgroup.map_equiv_normalizer_eq E (MulAut.conj u)).symm

theorem sec8t84_centralizer_map (B : Subgroup G) (u : G) :
    centralizer ((B.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (B : Set G)).map (MulAut.conj u).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_map]
    refine ⟨u⁻¹ * x * u, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    apply (MulAut.conj u).injective
    have h := hx (u * b * u⁻¹) ⟨b, hb, by simp [MulAut.conj_apply]⟩
    simpa [map_mul, MulAut.conj_apply, mul_assoc] using h
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have h := congrArg (fun z => MulAut.conj u z) (hc b hb)
    simpa [map_mul] using h

theorem sec8t84_isSylow2Of_map {H K : Subgroup G} (hK : IsSylow2Of K H) (u : G) :
    IsSylow2Of (K.map (MulAut.conj u).toMonoidHom) (H.map (MulAut.conj u).toMonoidHom) := by
  simpa [CFSG.conjugate, inv_inv] using hK.conjugate u⁻¹

end CFSG.OddStandard.SmallF3.Omega
