module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem sl23_involution : ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by decide

theorem sl23_pow_eight : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g ^ 4 = 1 := by decide

theorem sl23_escape : ∀ x : SL(2, ZMod 3), x ^ 4 ≠ 1 → ∃ k : SL(2, ZMod 3), k ^ 4 = 1 ∧
    k * (x * k⁻¹ * x⁻¹) ≠ 1 ∧ k * (x * k⁻¹ * x⁻¹) ≠ -1 := by decide

theorem sl23_card_fourth :
    (Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1)).card = 8 := by decide

theorem sl23_card : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem sl23_mem_of_pow_four {P : Subgroup SL(2, ZMod 3)} (hP : Nat.card P = 8) {g : SL(2, ZMod 3)}
    (hg : g ^ 4 = 1) : g ∈ P := by
  have hsub : (P : Set SL(2, ZMod 3)) ⊆
      ((Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) : Finset SL(2, ZMod 3)) :
        Set SL(2, ZMod 3)) := by
    intro p hp
    have h8 : p ^ 8 = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := P) (x := ⟨p, hp⟩))
      rw [hP] at this
      simpa using this
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact sl23_pow_eight p h8
  have hcard : ((Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) : Finset SL(2, ZMod 3)) :
      Set SL(2, ZMod 3)).ncard ≤ (P : Set SL(2, ZMod 3)).ncard := by
    rw [Set.ncard_coe_finset, sl23_card_fourth, ← Nat.card_coe_set_eq]
    exact hP.ge
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Finset.finite_toSet _)
  have hmem : g ∈ ((Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) : Finset SL(2, ZMod 3)) :
      Set SL(2, ZMod 3)) := by
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact hg
  rw [← heq] at hmem
  exact hmem

theorem sl23_escape_group {H : Type*} [Group H] (φ : H ≃* SL(2, ZMod 3)) {P : Subgroup H}
    (hP : Nat.card P = 8) {z : H} (hz1 : z ≠ 1) (hzz : z * z = 1) {x : H} (hx : x ∉ P) :
    ∃ k ∈ P, k * (x * k⁻¹ * x⁻¹) ≠ 1 ∧ k * (x * k⁻¹ * x⁻¹) ≠ z := by
  have hφz : φ z = -1 := by
    have hinv : φ z * φ z = 1 := by rw [← map_mul, hzz, map_one]
    refine (sl23_involution (φ z) hinv).resolve_left ?_
    intro h
    apply hz1
    apply φ.injective
    rw [h, map_one]
  set P' : Subgroup SL(2, ZMod 3) := P.map φ.toMonoidHom with hP'def
  have hP' : Nat.card P' = 8 := by
    have := Nat.card_congr (P.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv
    rw [← this, hP]
  have hx' : φ x ∉ P' := by
    intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    have : y = x := φ.injective hyx
    exact hx (this ▸ hy)
  have h4 : (φ x) ^ 4 ≠ 1 := fun h => hx' (sl23_mem_of_pow_four hP' h)
  obtain ⟨k', hk4, hk1, hk2⟩ := sl23_escape (φ x) h4
  have hk' : k' ∈ P' := sl23_mem_of_pow_four hP' hk4
  obtain ⟨k, hk, hkk⟩ := Subgroup.mem_map.mp hk'
  have key : φ (k * (x * k⁻¹ * x⁻¹)) = k' * (φ x * k'⁻¹ * (φ x)⁻¹) := by
    rw [← hkk]
    simp [map_mul, map_inv]
  refine ⟨k, hk, ?_, ?_⟩
  · intro h
    apply hk1
    rw [← key, h, map_one]
  · intro h
    apply hk2
    rw [← key, h, hφz]

theorem mem_zpowers_of_sq_eq_one {H : Type*} [Group H] {z h : H} (hz : z * z = 1)
    (hh : h ∈ Subgroup.zpowers z) : h = 1 ∨ h = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  have hsplit : z ^ n = z ^ (n % 2) * (z ^ (2 : ℤ)) ^ (n / 2) := by
    rw [show z ^ n = z ^ (n % 2 + 2 * (n / 2)) from by congr 1; omega, zpow_add, zpow_mul]
  rw [hsplit, hz2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h0 <;> rw [h0] <;> simp

theorem conj_mem_of_subgroupOf_normal {G : Type*} [Group G] {L K : Subgroup G} (hKL : K ≤ L)
    (hK : (K.subgroupOf L).Normal) {a : G} (ha : a ∈ L) {k : G} (hk : k ∈ K) :
    a * k * a⁻¹ ∈ K := by
  have hmem := hK.conj_mem ⟨k, hKL hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨a, ha⟩
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

theorem nonempty_mulEquiv_sl23_of_card {H : Type*} [Group H] (hH : Nat.card H = 24)
    (hq : Nonempty (H ⧸ classicalInvolutionOddCore H ≃* SL(2, ZMod 3))) :
    Nonempty (H ≃* SL(2, ZMod 3)) := by
  obtain ⟨e⟩ := hq
  have hidx : (classicalInvolutionOddCore H).index = 24 := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv, sl23_card]
  have hmul := Subgroup.card_mul_index (classicalInvolutionOddCore H)
  rw [hidx, hH] at hmul
  have hone : Nat.card (classicalInvolutionOddCore H) = 1 := by omega
  have hbot : classicalInvolutionOddCore H = ⊥ := Subgroup.eq_bot_of_card_eq _ hone
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot).symm).trans e⟩

theorem one_side_false {G : Type*} [Group G] {A B K X : Subgroup G} {z n l m : G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hKA : K ≤ A) (hKn : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hNK : ∀ g ∈ X, g ∈ A ⊔ B → g ∈ K → g ∈ Subgroup.zpowers z)
    (hfin : ∀ a ∈ A, a ∉ K → ∃ k ∈ K, k * (a * k⁻¹ * a⁻¹) ∉ Subgroup.zpowers z)
    (hn : n ∈ X) (hnAB : n ∈ A ⊔ B) (hnlm : n = l * m) (hl : l ∈ A) (hm : m ∈ B)
    (hlK : l ∉ K) : False := by
  obtain ⟨k, hk, hbad⟩ := hfin l hl hlK
  apply hbad
  have hkA : k ∈ A := hKA hk
  have hkAB : k ∈ A ⊔ B := Subgroup.mem_sup_left hkA
  have hmk : k⁻¹ * m = m * k⁻¹ := (Commute.inv_left (hcomm k hkA m hm : Commute k m)).eq
  have he : k * (l * k⁻¹ * l⁻¹) = (k * n * k⁻¹) * n⁻¹ := by
    rw [hnlm]
    calc k * (l * k⁻¹ * l⁻¹) = k * l * (k⁻¹ * m) * m⁻¹ * l⁻¹ := by group
      _ = k * l * (m * k⁻¹) * m⁻¹ * l⁻¹ := by rw [hmk]
      _ = (k * (l * m) * k⁻¹) * (l * m)⁻¹ := by group
  have h1 : k * (l * k⁻¹ * l⁻¹) ∈ K := K.mul_mem hk (hKn l hl k⁻¹ (K.inv_mem hk))
  have hconj : k * n * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hKX hk) n).mp hn
  have hconjAB : k * n * k⁻¹ ∈ A ⊔ B :=
    (A ⊔ B).mul_mem ((A ⊔ B).mul_mem hkAB hnAB) ((A ⊔ B).inv_mem hkAB)
  have hX' : k * (l * k⁻¹ * l⁻¹) ∈ X := by
    rw [he]; exact X.mul_mem hconj (X.inv_mem hn)
  have hAB' : k * (l * k⁻¹ * l⁻¹) ∈ A ⊔ B := by
    rw [he]; exact (A ⊔ B).mul_mem hconjAB ((A ⊔ B).inv_mem hnAB)
  exact hNK _ hX' hAB' h1

theorem exact_hfin {G : Type*} [Group G] {L K : Subgroup G} {z : G}
    (ψ : L ≃* SL(2, ZMod 3)) (hK : K ≤ L) (hK8 : Nat.card K = 8) (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzz : z * z = 1) :
    ∀ a ∈ L, a ∉ K → ∃ k ∈ K, k * (a * k⁻¹ * a⁻¹) ∉ Subgroup.zpowers z := by
  intro a ha haK
  have hP : Nat.card (K.subgroupOf L) = 8 := by
    rw [← hK8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hz1' : (⟨z, hzL⟩ : L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzz' : (⟨z, hzL⟩ : L) * ⟨z, hzL⟩ = 1 := Subtype.ext hzz
  have hx : (⟨a, ha⟩ : L) ∉ K.subgroupOf L := fun h => haK (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨k', hk', hne1, hne2⟩ :=
    sl23_escape_group ψ hP hz1' hzz' hx
  refine ⟨(k' : G), Subgroup.mem_subgroupOf.mp hk', ?_⟩
  intro hmem
  rcases mem_zpowers_of_sq_eq_one hzz hmem with h | h
  · apply hne1
    apply Subtype.ext
    simpa using h
  · apply hne2
    apply Subtype.ext
    simpa using h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
