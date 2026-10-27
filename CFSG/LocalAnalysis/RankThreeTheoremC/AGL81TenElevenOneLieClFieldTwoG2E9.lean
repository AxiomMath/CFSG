module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.Chevalley

namespace LieClAut


theorem exists_conj_e9_adjointG2_split {K : Type} [Field K] [Finite K]
    (h31 : 3 ∣ Nat.card K - 1) {E F : Subgroup ↥(adjointGroup .G2 K)} (hE : IsElemAbelian 3 E)
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 9) :
    ∃ g : ↥(adjointGroup .G2 K), ∀ e ∈ E, g * e * g⁻¹ ∈ F := by
  obtain ⟨gE, hgE⟩ := CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.exists_conj_torus_of_elemAbelian
    h31 hE
  obtain ⟨gF, hgF⟩ := CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.exists_conj_torus_of_elemAbelian
    h31 hF
  refine ⟨gF⁻¹ * gE, fun e he => ?_⟩
  obtain ⟨b, hb3, hb⟩ := hgE e he
  obtain ⟨x, hx, hxb⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.forall_exists_of_nine_le hgF hFc.ge b hb3
  have h : gE * e * gE⁻¹ = gF * x * gF⁻¹ := Subtype.ext (hb.trans hxb.symm)
  have : gF⁻¹ * gE * e * (gF⁻¹ * gE)⁻¹ = x := by
    calc gF⁻¹ * gE * e * (gF⁻¹ * gE)⁻¹ = gF⁻¹ * (gE * e * gE⁻¹) * gF := by group
      _ = gF⁻¹ * (gF * x * gF⁻¹) * gF := by rw [h]
      _ = x := by group
  rw [this]
  exact hx

theorem exists_conj_e9_adjointG2_qplus {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) {E F : Subgroup ↥(adjointGroup .G2 K)} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 9) (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 9) :
    ∃ g : ↥(adjointGroup .G2 K), ∀ e ∈ E, g * e * g⁻¹ ∈ F := by
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius_all K
  haveI : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K₂ := Module.finite_of_finite K
  obtain ⟨M⟩ := QPlusModel.nonempty_of_charTwo hdeg hσ
  have hel : ∀ D : Subgroup ↥(adjointGroup .G2 K), IsElemAbelian 3 D →
      CFSG.IsElementaryAbelian 3 D := fun D hD =>
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hD.2 g g.2) }
  haveI := hel E hE
  haveI := hel F hF
  obtain ⟨yE, hyEΓ, hyE⟩ := M.exists_conj_plane_to_torsion hdeg hσ h3 E (by rw [hEc]; norm_num)
  obtain ⟨yF, hyFΓ, hyF⟩ := M.exists_conj_plane_to_torsion hdeg hσ h3 F (by rw [hFc]; norm_num)
  obtain ⟨c, hc⟩ := M.exists_twistEmb_eq (mul_mem (inv_mem hyFΓ) hyEΓ)
  refine ⟨c, fun e he => ?_⟩
  have hmem : yE * twistEmb M.g e * yE⁻¹ ∈ torusTorsion K₂ 3 := by
    rw [← hyE]
    exact ⟨_, ⟨e, he, rfl⟩, by simp⟩
  rw [← hyF] at hmem
  obtain ⟨_, ⟨x, hx, rfl⟩, hxe⟩ := hmem
  have hxe' : yF * twistEmb M.g x * yF⁻¹ = yE * twistEmb M.g e * yE⁻¹ := by simpa using hxe
  have : c * e * c⁻¹ = x := by
    apply twistEmb_injective M.g
    rw [map_mul, map_mul, map_inv, hc]
    calc yF⁻¹ * yE * twistEmb M.g e * (yF⁻¹ * yE)⁻¹
        = yF⁻¹ * (yE * twistEmb M.g e * yE⁻¹) * yF := by group
      _ = yF⁻¹ * (yF * twistEmb M.g x * yF⁻¹) * yF := by rw [hxe']
      _ = twistEmb M.g x := by group
  rw [this]
  exact hx

theorem exists_conj_e9_adjointG2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {E F : Subgroup ↥(adjointGroup .G2 K)} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 9) :
    ∃ g : ↥(adjointGroup .G2 K), ∀ e ∈ E, g * e * g⁻¹ ∈ F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card K = 2 ^ m := by
    haveI := Fintype.ofFinite K
    obtain ⟨k', hk'⟩ := FiniteField.card K 2
    exact ⟨k', by rw [Nat.card_eq_fintype_card, hk'.2]⟩
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hm]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hQ : 1 ≤ Nat.card K := Nat.card_pos
  rcases (show Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 by omega) with h | h
  · exact exists_conj_e9_adjointG2_split (by omega) hE hF hFc
  · exact exists_conj_e9_adjointG2_qplus (by omega) hE hEc hF hFc

end LieClAut

end CFSG.LocalAnalysis.RankThreeTheoremC
