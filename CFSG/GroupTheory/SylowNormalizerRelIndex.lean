module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.PGroup.PrimePartTransport

public section

open Subgroup

namespace CFSG.GroupTheory

theorem exists_orderOf_eq_prime_mem_normalizer_sylow_of_relIndex
    {G : Type} [Group G] [Finite G] {Z W U : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hUW : U ≤ W) (hWZ : W ≤ Z) (hW : (W.subgroupOf Z).Normal)
    (hU : (U.subgroupOf Z).Normal)
    (hidx : W.relIndex Z = p) (h2 : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ U)
    {R₀ : Subgroup G} (hR₀ : CFSG.ABGLocalTools.IsSylowOf 2 R₀ U)
    (hNU : ¬ p ∣ Nat.card ↥(U ⊓ Subgroup.normalizer (R₀ : Set G))) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R W ∧
      ∃ b ∈ Z, b ∉ W ∧ orderOf b = p ∧ b ∈ Subgroup.normalizer (R : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hUZ : U ≤ Z := hUW.trans hWZ
  have hZU : Z ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUZ).mp hU
  have hWU : W ≤ Subgroup.normalizer (U : Set G) := hWZ.trans hZU
  have hZW : Z ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWZ).mp hW
  have hR₀W : R₀ ≤ W := hR₀.le.trans hUW
  have hR₀Wp : IsPGroup 2 ↥(R₀.subgroupOf W) := hR₀.isPGroup.comap_subtype
  obtain ⟨Q, hQ⟩ := hR₀Wp.exists_le_sylow
  let R : Subgroup G := (Q : Subgroup ↥W).map W.subtype
  have hR : CFSG.ABGLocalTools.IsSylowOf 2 R W := ⟨Q, rfl⟩
  have hR₀R : R₀ ≤ R := by
    intro x hx
    exact ⟨⟨x, hR₀W hx⟩, hQ hx, rfl⟩
  have hRinfU : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ U) U :=
    hR.inf_of_le_normalizer hUW hWU
  have hR₀eq : R ⊓ U = R₀ :=
    hR₀.eq_of_le (le_inf hR₀R hR₀.le) inf_le_right hRinfU.isPGroup
  have hnotdvdNW : ¬ p ∣ Nat.card ↥(W ⊓ Subgroup.normalizer (R : Set G)) := by
    rintro hdvd
    obtain ⟨x, hxord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(W ⊓ Subgroup.normalizer (R : Set G))) p hdvd
    have hxW : (x : G) ∈ W := x.2.1
    have hxNR : (x : G) ∈ Subgroup.normalizer (R : Set G) := x.2.2
    have hxordG : orderOf (x : G) = p := by
      have h := orderOf_injective (Subgroup.subtype (W ⊓ Subgroup.normalizer (R : Set G)))
        Subtype.val_injective x
      exact h.trans hxord
    have hxp : (x : G) ^ p = 1 := by
      simpa [hxordG] using pow_orderOf_eq_one (x : G)
    obtain ⟨k, hk⟩ := h2 (x : G) hxW
    have hxU : (x : G) ∈ U :=
      CFSG.GroupTheory.mem_of_pow_two_pow_mem_of_orderOf_dvd_prime_pow hp hp2
        (by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hxp) hk
    have hxU' : (x : G) ∈ Subgroup.normalizer (U : Set G) := hWU hxW
    have hxnR₀ : (x : G) ∈ Subgroup.normalizer (R₀ : Set G) := by
      rw [← hR₀eq]
      rw [Subgroup.mem_normalizer_iff] at hxNR hxU' ⊢
      intro r
      constructor
      · rintro ⟨hrR, hrU⟩
        exact ⟨(hxNR r).mp hrR, (hxU' r).mp hrU⟩
      · rintro ⟨hrR, hrU⟩
        exact ⟨(hxNR r).mpr hrR, (hxU' r).mpr hrU⟩
    have hxN : (x : G) ∈ U ⊓ Subgroup.normalizer (R₀ : Set G) := ⟨hxU, hxnR₀⟩
    have hpdvd : p ∣ Nat.card ↥(U ⊓ Subgroup.normalizer (R₀ : Set G)) := by
      have hdvd' := Subgroup.orderOf_dvd_natCard (U ⊓ Subgroup.normalizer (R₀ : Set G)) hxN
      rwa [hxordG] at hdvd'
    exact hNU hpdvd
  let NZ : Subgroup G := Z ⊓ Subgroup.normalizer (R : Set G)
  let NW : Subgroup G := W ⊓ Subgroup.normalizer (R : Set G)
  have hZle : Z ≤ W ⊔ NZ := by
    intro z hz
    have hzNW : z ∈ Subgroup.normalizer (W : Set G) := hZW hz
    have hRz : CFSG.ABGLocalTools.IsSylowOf 2
        (R.map (MulAut.conj z).toMonoidHom) W := by
      have hWmap : W.map (MulEquiv.toMonoidHom (MulAut.conj z)) = W := by
        simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hzNW)
      rw [← hWmap]
      exact CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono hR.le) (by
        rw [Subgroup.card_map_of_injective (f := (MulAut.conj z).toMonoidHom)
            (MulAut.conj z).injective,
          Subgroup.card_map_of_injective (f := (MulAut.conj z).toMonoidHom)
            (MulAut.conj z).injective, hR.card_eq])
    obtain ⟨w, hwW, hconj⟩ := hR.exists_mem_conj hRz
    have hnZ : w⁻¹ * z ∈ Z := Z.mul_mem (Z.inv_mem (hWZ hwW)) hz
    have hnN : w⁻¹ * z ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        have hx : z * r * z⁻¹ ∈ R.map (MulEquiv.toMonoidHom (MulAut.conj z)) :=
          ⟨r, hr, rfl⟩
        have h := (hconj (z * r * z⁻¹)).mp hx
        rwa [show w⁻¹ * (z * r * z⁻¹) * w = (w⁻¹ * z) * r * (w⁻¹ * z)⁻¹ from by
          group] at h
      · intro hr
        have hx : z * r * z⁻¹ ∈ R.map (MulEquiv.toMonoidHom (MulAut.conj z)) := by
          refine (hconj (z * r * z⁻¹)).mpr ?_
          rwa [show w⁻¹ * (z * r * z⁻¹) * w = (w⁻¹ * z) * r * (w⁻¹ * z)⁻¹ from by
            group]
        obtain ⟨r', hr', heq⟩ := hx
        have hrr' : r' = r := by
          have hz : z * r' * z⁻¹ = z * r * z⁻¹ := heq
          calc r' = z⁻¹ * (z * r' * z⁻¹) * z := by group
            _ = z⁻¹ * (z * r * z⁻¹) * z := by rw [hz]
            _ = r := by group
        simpa [hrr'] using hr'
    have hzdecomp : z = w * (w⁻¹ * z) := by group
    rw [hzdecomp]
    exact Subgroup.mul_mem_sup hwW ⟨hnZ, hnN⟩
  have hsupZ : W ⊔ NZ = Z := le_antisymm (sup_le hWZ inf_le_left) hZle
  have hNZleZ : NZ ≤ Z := inf_le_left
  have hNW_eq : NW = W ⊓ NZ := by
    ext x
    simp only [NW, NZ, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxW, hxN⟩
      exact ⟨hxW, ⟨hWZ hxW, hxN⟩⟩
    · rintro ⟨hxW, _, hxN⟩
      exact ⟨hxW, hxN⟩
  have hidxNW : NW.relIndex NZ = p := by
    have hsup' : W.subgroupOf Z ⊔ NZ.subgroupOf Z = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hWZ hNZleZ, hsupZ, Subgroup.subgroupOf_self]
    have h1 : (W.subgroupOf Z).relIndex (NZ.subgroupOf Z) = p := by
      rw [← Subgroup.relIndex_sup_left (NZ.subgroupOf Z) (W.subgroupOf Z), hsup',
        Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex] using hidx
    have h2 : W.relIndex NZ = (W.subgroupOf Z).relIndex (NZ.subgroupOf Z) :=
      (Subgroup.relIndex_subgroupOf (H := W) (K := NZ) (L := Z) hNZleZ).symm
    have h3 : NW.relIndex NZ = W.relIndex NZ := by
      rw [hNW_eq]
      exact Subgroup.inf_relIndex_right W NZ
    rw [h3, h2, h1]
  have hNWleNZ : NW ≤ NZ := le_inf (inf_le_left.trans hWZ) inf_le_right
  have hcardNZ : Nat.card ↥NZ = p * Nat.card ↥NW := by
    have h := Subgroup.relIndex_mul_card NW NZ
    rw [hidxNW, inf_eq_left.mpr hNWleNZ] at h
    exact h.symm
  have hpdvdNZ : p ∣ Nat.card ↥NZ := ⟨Nat.card ↥NW, by rw [hcardNZ, mul_comm]⟩
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card' (G := ↥NZ) p hpdvdNZ
  have hbordG : orderOf (b : G) = p := by
    have h := orderOf_injective (Subgroup.subtype NZ) Subtype.val_injective b
    exact h.trans hbord
  refine ⟨R, hR, (b : G), b.2.1, ?_, hbordG, b.2.2⟩
  intro hbW
  have hbNW : (b : G) ∈ NW := ⟨hbW, b.2.2⟩
  have hd : p ∣ Nat.card ↥NW := by
    have hd' := Subgroup.orderOf_dvd_natCard NW hbNW
    rwa [hbordG] at hd'
  exact hnotdvdNW hd

end CFSG.GroupTheory
