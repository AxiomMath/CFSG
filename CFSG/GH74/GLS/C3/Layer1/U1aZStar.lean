module

public import CFSG.GH74.GLS.C3.Layer1.U1aSetup
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup

variable {G : Type} [Group G] [Finite G] {M L N W Q T : Subgroup G}

theorem exists_commuting_conj (S : Setup M L N W Q T) {y : G} (hy : orderOf y = 2) (hyM : y ∈ M)
    (hyW : y ∉ W) :
    ∃ l ∈ L, l * y * l⁻¹ ≠ y ∧ (l * y * l⁻¹) * y = y * (l * y * l⁻¹) := by
  by_contra hcon0
  have hcon : ∀ l ∈ L, l * y * l⁻¹ ≠ y → (l * y * l⁻¹) * y ≠ y * (l * y * l⁻¹) :=
    fun l hl h1 h2 => hcon0 ⟨l, hl, h1, h2⟩
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy
  have hyinv : y⁻¹ = y := inv_eq_self_of_orderOf_eq_two hy
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy
  have hyL : ∀ l ∈ L, y * l * y⁻¹ ∈ L := S.L_norm y hyM
  have hynorm : zpowers y ≤ normalizer L := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    refine ⟨hyL h, fun hh => ?_⟩
    have h2 := hyL _ hh
    have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
      rw [hyinv, ← mul_assoc, ← mul_assoc, hyy, one_mul, mul_assoc, hyy, mul_one]
    rwa [e] at h2
  have hmem : ∀ g ∈ L ⊔ zpowers y, ∃ l ∈ L, ∃ z ∈ zpowers y, g = l * z := by
    intro g hg
    have hg' : g ∈ ((L ⊔ zpowers y : Subgroup G) : Set G) := hg
    rw [coe_mul_of_right_le_normalizer_left L (zpowers y) hynorm] at hg'
    obtain ⟨l, hl, z, hz, rfl⟩ := hg'
    exact ⟨l, hl, z, hz, rfl⟩
  have hLH : L ≤ L ⊔ zpowers y := le_sup_left
  have hyH : y ∈ L ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hconj : ∀ g ∈ L ⊔ zpowers y, ∃ l ∈ L, g * y * g⁻¹ = l * y * l⁻¹ := by
    intro g hg
    obtain ⟨l, hl, z, hz, rfl⟩ := hmem g hg
    refine ⟨l, hl, ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hzy : y ^ k * y = y * y ^ k := (Commute.self_zpow y k).eq.symm
    calc l * y ^ k * y * (l * y ^ k)⁻¹ = l * (y ^ k * y * (y ^ k)⁻¹) * l⁻¹ := by group
      _ = l * y * l⁻¹ := by rw [hzy]; group
  have hiso : ∀ g : ↥(L ⊔ zpowers y),
      (g * ⟨y, hyH⟩ * g⁻¹) * ⟨y, hyH⟩ = ⟨y, hyH⟩ * (g * ⟨y, hyH⟩ * g⁻¹) →
      g * ⟨y, hyH⟩ * g⁻¹ = ⟨y, hyH⟩ := by
    intro g hg
    obtain ⟨l, hl, hl'⟩ := hconj g g.2
    have hg' : ((g : G) * y * (g : G)⁻¹) * y = y * ((g : G) * y * (g : G)⁻¹) :=
      congrArg Subtype.val hg
    rw [hl'] at hg'
    by_cases hly : l * y * l⁻¹ = y
    · exact Subtype.ext (by simpa using hl'.trans hly)
    · exact absurd hg' (hcon l hl hly)
  have : Fintype ↥(L ⊔ zpowers y) := Fintype.ofFinite _
  obtain ⟨N₁, hN₁n, hN₁odd, hN₁c⟩ := CFSG.ZStar.glauberman_zStar ↥(L ⊔ zpowers y) ⟨y, hyH⟩
    (fun h => hy1 (congrArg Subtype.val h)) (Subtype.ext hyy) hiso
  have hN'norm : ∀ l ∈ L, ∀ n ∈ N₁.map (L ⊔ zpowers y).subtype ⊓ L,
      l * n * l⁻¹ ∈ N₁.map (L ⊔ zpowers y).subtype ⊓ L := by
    intro l hl n hn
    obtain ⟨⟨m, hm, rfl⟩, hnL⟩ := hn
    exact ⟨⟨⟨l, hLH hl⟩ * m * ⟨l, hLH hl⟩⁻¹, hN₁n.conj_mem m hm _, rfl⟩,
      L.mul_mem (L.mul_mem hl hnL) (L.inv_mem hl)⟩
  have hN'odd : Odd (Nat.card ↥(N₁.map (L ⊔ zpowers y).subtype ⊓ L)) := by
    have h1 := card_dvd_of_le (inf_le_left : N₁.map (L ⊔ zpowers y).subtype ⊓ L ≤
      N₁.map (L ⊔ zpowers y).subtype)
    rw [Subgroup.card_map_of_injective (L ⊔ zpowers y).subtype_injective] at h1
    exact Odd.of_dvd_nat hN₁odd h1
  have hN'N := S.N_max _ inf_le_right hN'norm hN'odd
  have hcomm : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ N := by
    intro l hl
    have h1 := hN₁c ⟨l, hLH hl⟩
    have hL1 : l * y * l⁻¹ * y⁻¹ ∈ L := by
      have h3 : l * (y * l⁻¹ * y⁻¹) ∈ L := L.mul_mem hl (hyL l⁻¹ (L.inv_mem hl))
      simpa [mul_assoc] using h3
    have h2 : l * y * l⁻¹ * y⁻¹ ∈ N₁.map (L ⊔ zpowers y).subtype ⊓ L :=
      ⟨⟨_, h1, rfl⟩, hL1⟩
    have h3 := hN'N h2
    have e : (l * y * l⁻¹ * y⁻¹)⁻¹ = y * l * y⁻¹ * l⁻¹ := by group
    rw [← e]
    exact N.inv_mem h3
  exact hyW (S.W_full y hyM hcomm)

end CFSG.GH74.GLS.C3.Layer1.U1a
