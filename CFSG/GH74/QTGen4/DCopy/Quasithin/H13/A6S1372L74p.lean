module

public import CFSG.Quasithin.H13.A6S1372L74p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L74l

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Odd

variable {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
  (hHK : H ≤ Subgroup.normalizer (K : Set G))
include hH hKH hHK

theorem comm_L1_of_card_nine_F4 (h1227 : U3.Stmt13_2_2_7_F4) (hhat : ¬ IsHatA6 L)
    (hB : ¬ H13.IsA6Block L) (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (hexp : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 K)
    (hcomm : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 K)
    (hCK : K ⊓ Subgroup.centralizer
      (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) = pCoreOf 2 K)
    (h9 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 9) {x : G} (hxL : x ∈ S.L1) (hx3 : x ^ 3 = 1) :
    ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hJ := not_thompsonJ_le_F4 hH hKH hHK h1227 hhat hB hKM Nat.prime_three hp2 hexp hCK
  obtain ⟨hsyl, hred, -, -⟩ := R2_data hH hKH hHK Nat.prime_three hp2 hexp hCK
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hR2 : IsPGroup 2 (pCoreOf 2 (S.L1 ⊔ T)) := pCoreOf_isPGroup 2 _
  set X := K ⊔ pCoreOf 2 (S.L1 ⊔ T) with hX
  set U := twoReducedProduct X with hU
  have hUe : IsElemAbelian 2 U := hred.2.2.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hXU
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have : Finite (MulAut (IntMod U hUe)) :=
    Finite.of_injective (fun φ : MulAut (IntMod U hUe) => (φ : IntMod U hUe → IntMod U hUe))
      DFunLike.coe_injective
  have hsolv : Group.IsSolvable ↥(autI hUe X) := by
    rw [← range_convHom hUe X hXU]
    have := A6L74.isSolvable_sup hcomm hR2 hRK
    exact Group.isSolvable_of_surjective (f := (convHom hUe X hXU).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨I, -, hJX, hcI, hindI, hnat, -⟩ :=
    B2F.structure_of_not_le_of_quot hUe hred hsolv hsyl hJ
  have hI : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hI
    subst hI
    have hbot : autI hUe (thompsonJ X) = ⊥ := by
      rw [hJX]
      simp
    rw [autI_eq_bot_iff hUe ((thompsonJ_le_self X).trans hXU)] at hbot
    exact hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hsyl).trans hbot)

  have hOC : ∀ g ∈ pCoreOf 2 K, g ∈ Subgroup.centralizer (U : Set G) := fun g hg =>
    (hCK.symm ▸ hg : g ∈ K ⊓ Subgroup.centralizer (U : Set G)).2
  have hK3 : ∀ φ ∈ autI hUe K, φ ^ 3 = 1 := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hUe).1 hφ
    rw [← map_pow, convI_eq_one_iff]
    exact hOC _ (by simpa using hexp _ hg)
  have hKc : ∀ a ∈ autI hUe K, ∀ b ∈ autI hUe K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g₁, hg₁, rfl⟩ := (mem_autI hUe).1 ha
    obtain ⟨g₂, hg₂, rfl⟩ := (mem_autI hUe).1 hb
    have h1 : convI hUe (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := by
      rw [convI_eq_one_iff]
      exact hOC _ (by simpa using hcomm _ hg₁ _ hg₂)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hK9 : Nat.card (autI hUe K) = 9 := by
    rw [card_autI_eq hUe hKU, hCK, ← h9]
    have e : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      ext k
      rw [Subgroup.mem_subgroupOf]
      exact A6L74.mem_pCoreOf_iff k
    rw [Subgroup.relIndex, e]
    rfl
  have hYK : ∀ y ∈ autI hUe (thompsonJ X), y ^ 3 = 1 → y ∈ autI hUe K := fun y hy hy3 =>
    A6L74.mem_autI_of_cube hUe hR2 hRK hXU (autI_mono hUe (thompsonJ_le_self X) hy) hy3
  have hXJ : X ≤ Subgroup.normalizer (thompsonJ X : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ X)
  have hKY : ∀ φ ∈ autI hUe K, ∀ y ∈ autI hUe (thompsonJ X),
      φ * y * φ⁻¹ ∈ autI hUe (thompsonJ X) := by
    intro φ hφ y hy
    obtain ⟨g, hg, rfl⟩ := (mem_autI hUe).1 hφ
    exact A6L74.convI_conj_mem hUe g.2 (hXJ (Subgroup.mem_sup_left hg)) hy

  have hL1N : S.L1 ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hH.1.1).trans hHK
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL)
  have hxX : x ∈ Subgroup.normalizer (X : Set G) := A6L74.mem_normalizer_sup hRK (hL1N hxL) hxR
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := A6L74.mem_normalizer_twoReducedProduct hxX
  have hxJ : x ∈ Subgroup.normalizer (thompsonJ X : Set G) :=
    normalizer_le_normalizer_thompsonJ X hxX
  have hσ3 : convI hUe ⟨x, hxU⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxU⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hcomm' := A6L74.comm_of_blocks hK3 hKc hK9 hYK hKY hJX hcI hindI
    (fun L' hL' => by obtain ⟨e, -, -⟩ := hnat L' hL'; exact ⟨e⟩) hI hσ3
    (fun φ hφ => A6L74.convI_conj_mem hUe hxU (hL1N hxL) hφ)
    (fun φ hφ => A6L74.convI_conj_mem hUe hxU hxJ hφ)
  intro k hk
  have hkU : k ∈ Subgroup.normalizer (U : Set G) := hKU hk
  have h1 := hcomm' (convI hUe ⟨k, hkU⟩) (convI_mem_autI hUe hk hkU)
  have h2 : convI hUe (⟨x, hxU⟩ * ⟨k, hkU⟩ * ⟨x, hxU⟩⁻¹ * ⟨k, hkU⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, mul_inv_cancel_right, mul_inv_cancel]
  have h3 := (convI_eq_one_iff hUe _).1 h2
  rw [← hCK]
  refine ⟨?_, h3⟩
  have hxk : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hL1N hxL) k).mp hk
  exact K.mul_mem hxk (K.inv_mem hk)

end Odd

end Setting4

end CFSG.Quasithin.H13.A6
