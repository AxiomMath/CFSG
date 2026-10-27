module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelCard
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR
  CFSG.Quasithin.H13.NQCore.L3Odd

theorem sq_sub_one_mul_cube_sub_one (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 3 - 1) = (q - 1) ^ 2 * ((q + 1) * (q ^ 2 + q + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  have h2 : (r + 1) ^ 3 - 1 = r * (r ^ 2 + 3 * r + 3) := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  rw [h1, h2, Nat.add_sub_cancel]
  ring

theorem no_sylow_two_in_flag {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (T : Subgroup (projectiveSL 3 F)) (hT : IsSylowOf 2 T ⊤)
    (L W : Submodule F (Fin 3 → F)) (hLW : L ≤ W) (hL : Module.finrank F L = 1)
    (hW : Module.finrank F W = 2)
    (hT' : ∀ g : SpecialLinearGroup (Fin 3) F, proj 3 F g ∈ T →
      g ∈ stabilizer L ∧ g ∈ stabilizer W) : False := by
  have hqodd : Odd (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two (by rwa [ringChar.eq F p]))
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  set Tst : Subgroup (SpecialLinearGroup (Fin 3) F) := T.comap (proj 3 F) with hTst
  obtain ⟨s, hs1, hs2⟩ := exists_map_flagSpace_eq_of_le (n := 3) (by norm_num) hLW hL hW
  let f : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
    (MulAut.conj s⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj s⁻¹).injective
  have hup : Tst.map f ≤ upperTriangular 3 F := by
    rintro _ ⟨g, hg, rfl⟩
    have e : f g = s⁻¹ * g * s := by
      change s⁻¹ * g * s⁻¹⁻¹ = _
      rw [inv_inv]
    rw [e]
    exact mem_upperTriangular_of_map_flagSpace (map_flagSpace_conj hs1 (hT' g hg).1)
      (map_flagSpace_conj hs2 (hT' g hg).2)
  have hdvd : Nat.card ↥Tst ∣ Nat.card F ^ 3 * (Nat.card F - 1) ^ 2 := by
    refine Dvd.dvd.trans ?_ card_upperTriangular_dvd
    rw [← Subgroup.card_map_of_injective hf]
    exact Subgroup.card_dvd_of_le hup
  have hidx : Tst.index = T.index := Subgroup.index_comap_of_surjective T (proj_surjective 3 F)
  have hTodd : ¬ 2 ∣ T.index := by
    have := ((isSylowOf_iff).mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hSL : Nat.card (SpecialLinearGroup (Fin 3) F) = Nat.card ↥Tst * Tst.index :=
    (Subgroup.card_mul_index Tst).symm
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
    rw [card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
      Finset.prod_pair (by norm_num)]
  obtain ⟨c, hc⟩ := hdvd
  have hmain : Nat.card ↥Tst * Tst.index =
      Nat.card F ^ 3 * ((Nat.card F - 1) ^ 2 *
        ((Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1))) := by
    rw [← hSL, hcardSL, sq_sub_one_mul_cube_sub_one _ hq1]
  have h3 : Nat.card ↥Tst * Tst.index = Nat.card ↥Tst * (c * ((Nat.card F + 1) *
      (Nat.card F ^ 2 + Nat.card F + 1))) := by
    calc Nat.card ↥Tst * Tst.index = Nat.card F ^ 3 * ((Nat.card F - 1) ^ 2 *
          ((Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1))) := hmain
      _ = (Nat.card F ^ 3 * (Nat.card F - 1) ^ 2) * ((Nat.card F + 1) *
          (Nat.card F ^ 2 + Nat.card F + 1)) := by ring
      _ = (Nat.card ↥Tst * c) * ((Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1)) := by
          rw [hc]
      _ = Nat.card ↥Tst * (c * ((Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1))) := by
          ring
  have h4 : Tst.index = c * ((Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1)) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  have h5 : Nat.card F + 1 ∣ Tst.index :=
    ⟨c * (Nat.card F ^ 2 + Nat.card F + 1), by rw [h4]; ring⟩
  have h6 : 2 ∣ Nat.card F + 1 := even_iff_two_dvd.mp hqodd.add_one
  exact hTodd (hidx ▸ h6.trans h5)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
