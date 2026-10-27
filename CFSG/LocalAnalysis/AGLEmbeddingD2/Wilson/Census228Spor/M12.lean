module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.M12
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofThreeFive

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint
open CFSG.GH74.M12.Hyp (G12)
open CFSG.AGLEmbeddingD2.Wilson.Census424Rest
open CFSG.RankThree.PartTwo.Toolkit.M12 (E F A A' P0)
open scoped commutatorElement

theorem not_five_dvd_card_of_equiv {N : Type*} [Group N]
    (e : N ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) : ¬ 5 ∣ Nat.card N := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have h3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have h4 : Nat.card (alternatingGroup (Fin 4)) ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin 4))
    have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
    rwa [h24] at h
  rw [h3]
  intro h
  have h5 : (5 : ℕ).Prime := by norm_num
  rcases (Nat.Prime.dvd_mul h5).mp h with h6 | h6
  · omega
  · have := Nat.le_of_dvd (by norm_num) (h6.trans h4)
    have h24 : 5 ∣ 24 := h6.trans h4
    omega

theorem not_five_dvd_card_centralizer_of_mem_nine
    {B : Subgroup G12} (hB : B = E ∨ B = F ∨ B = A ∨ B = A') {v : G12} (hv : v ∈ B)
    (hv1 : v ≠ 1) : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set G12)) := by
  have h54 : ∀ u : G12, Nat.card (Subgroup.centralizer ({u} : Set G12)) = 54 →
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({u} : Set G12)) := fun u h => by
    rw [h]; norm_num
  have hN : ∀ u : G12, Nonempty (Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G12) : Set G12) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) →
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({u} : Set G12)) := fun u ⟨e⟩ h =>
    not_five_dvd_card_of_equiv e
      (h.trans (Subgroup.card_dvd_of_le (centralizer_le_normalizer_zpowers u)))
  have hZE : v ∈ (Subgroup.center P0).map P0.subtype → v ∈ E := by
    intro h
    rw [CFSG.RankThree.PartTwo.Toolkit.M12.center_P0] at h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.zpow_mem _ z_mem_E k
  rcases hB with rfl | rfl | rfl | rfl
  · exact h54 v (Item434SporGen.card_centralizer_E hv hv1)
  · exact h54 v (Item434SporGen.card_centralizer_F hv hv1)
  · by_cases hZ : v ∈ (Subgroup.center P0).map P0.subtype
    · exact h54 v (Item434SporGen.card_centralizer_E (hZE hZ) hv1)
    · exact hN v (CFSG.RankThree.PartTwo.Toolkit.M12.na_A hv hZ)
  · by_cases hZ : v ∈ (Subgroup.center P0).map P0.subtype
    · exact h54 v (Item434SporGen.card_centralizer_E (hZE hZ) hv1)
    · exact hN v (CFSG.RankThree.PartTwo.Toolkit.M12.na_A' hv hZ)


theorem exists_conj_mem_nine
    {X : Type} [Group X] [Finite X] (e : X ≃* G12) {x : X}
    (hx3 : orderOf x = 3) :
    ∃ ψ : X ≃* G12, ∃ B : Subgroup G12, (B = E ∨ B = F ∨ B = A ∨ B = A') ∧ ψ x ∈ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D' : Subgroup G12 := Subgroup.zpowers (e x) with hD'
  have hD'card : Nat.card D' = 3 := by
    rw [hD', Nat.card_zpowers, MulEquiv.orderOf_eq, hx3]
  have hD'p : IsPGroup 3 D' := IsPGroup.of_card (n := 1) (by rw [hD'card, pow_one])
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    Res423Two.card_P0_eq hD'p
  have hle := Item434AltPerm.map_conj_inv_le hg
  let ψ : X ≃* G12 := e.trans (MulAut.conj g⁻¹)
  have hvP0 : ψ x ∈ P0 :=
    hle ⟨e x, Subgroup.mem_zpowers _, rfl⟩
  have hv3 : (ψ x) ^ 3 = 1 := by
    rw [← map_pow, show x ^ 3 = 1 by rw [← hx3]; exact pow_orderOf_eq_one x, map_one]
  have hv1 : ψ x ≠ 1 := by
    intro h
    have : x = 1 := ψ.injective (h.trans (map_one ψ).symm)
    rw [this, orderOf_one] at hx3
    omega
  refine ⟨ψ, ?_⟩
  have hzP0 : ⁅CFSG.RankThree.PartTwo.Toolkit.M12.x, CFSG.RankThree.PartTwo.Toolkit.M12.y⁆ ∈ P0 :=
    CFSG.RankThree.PartTwo.Toolkit.M12.z_mem_P0
  set z := ⁅CFSG.RankThree.PartTwo.Toolkit.M12.x, CFSG.RankThree.PartTwo.Toolkit.M12.y⁆ with hz
  by_cases hvz : ψ x ∈ Subgroup.zpowers z
  · exact ⟨E, Or.inl rfl, by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvz
      rw [← hk]
      exact Subgroup.zpow_mem _ z_mem_E k⟩
  ·
    have hz3 : z ^ 3 = 1 := CFSG.RankThree.PartTwo.Toolkit.M12.cube_of_mem_P0 hzP0
    have hz1 : z ≠ 1 := CFSG.RankThree.PartTwo.Toolkit.M12.z_ne_one
    have hbot : CFSG.Assembly.IsElemAbelian 3 (⊥ : Subgroup G12) :=
      ⟨⟨⟨fun a b => by
          rw [show a = 1 from Subtype.ext (Subgroup.mem_bot.mp a.2),
            show b = 1 from Subtype.ext (Subgroup.mem_bot.mp b.2)]⟩⟩, fun a ha => by
          rw [Subgroup.mem_bot.mp ha, one_pow]⟩
    have hzcomm : ∀ v ∈ P0, z * v = v * z := by
      intro v hv
      have hzc := Subgroup.mem_center_iff.mp
        (CFSG.RankThree.PartTwo.Toolkit.M12.z_mem_center) ⟨v, hv⟩
      exact (congrArg Subtype.val hzc).symm
    obtain ⟨hA1, hA1c⟩ := Sec5.isElemAbelian_sup_zpowers hbot
      (show z ∉ (⊥ : Subgroup G12) from fun h => hz1 (Subgroup.mem_bot.mp h)) hz3
      (fun a ha => by rw [Subgroup.mem_bot.mp ha, one_mul, mul_one])
    rw [bot_sup_eq] at hA1 hA1c
    have hvnot : ψ x ∉ Subgroup.zpowers z := hvz
    obtain ⟨hA2, hA2c⟩ := Sec5.isElemAbelian_sup_zpowers hA1 hvnot hv3 (fun a ha => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact ((Commute.zpow_left (show Commute z (ψ x) from hzcomm _ hvP0) n)).eq)
    have hB9 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers (ψ x) : Subgroup G12) = 9 := by
      rw [hA2c, hA1c, Subgroup.card_bot]
    have hBle : (Subgroup.zpowers z ⊔ Subgroup.zpowers (ψ x) : Subgroup G12) ≤ P0 :=
      sup_le ((Subgroup.zpowers_le).mpr hzP0) ((Subgroup.zpowers_le).mpr hvP0)
    have hmem : (Subgroup.zpowers z ⊔ Subgroup.zpowers (ψ x) : Subgroup G12) ∈
        {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} := ⟨hBle, hB9⟩
    rw [CFSG.RankThree.PartTwo.Toolkit.M12.nine_eq] at hmem
    refine ⟨Subgroup.zpowers z ⊔ Subgroup.zpowers (ψ x), ?_,
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem threeFiveData228_M12 :
    ThreeFiveData228 (NativeSporadic.Carrier .M12) := by
  intro x k hx hk hxk
  exfalso
  obtain ⟨ψ, B, hB, hxB⟩ := exists_conj_mem_nine (X := NativeSporadic.Carrier .M12)
    (e := (MulEquiv.refl _ : NativeSporadic.Carrier .M12 ≃* G12)) hx
  have hx1 : ψ x ≠ 1 := by
    intro h
    have : x = 1 := ψ.injective (h.trans (map_one ψ).symm)
    rw [this, orderOf_one] at hx
    omega
  have h5not := not_five_dvd_card_centralizer_of_mem_nine hB hxB hx1
  have hkC : k ∈ Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .M12)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxk.symm
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .M12))) := by
    have := orderOf_dvd_natCard (⟨k, hkC⟩ : Subgroup.centralizer ({x} : Set _))
    rwa [Subgroup.orderOf_mk, hk] at this
  rw [Nat.card_congr (centralizerEquivOfMulEquiv ψ x).toEquiv] at h5
  exact h5not h5

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
