module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Cent
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Phi
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Good
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint Q3L5
open scoped MatrixGroups

namespace Q3L5

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.good_of_u₁ (hD : TightDatum R S t) {N : Subgroup Y} [N.Normal]
    {ι : SL(2 + 3, ZMod 3) →* Y} (hι : Function.Injective ι) (hιN : ι.range = N)
    (hιu : ι u₁ = t) {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) :
    GoodThreeElement R t := by
  obtain ⟨⟨hHN, hHt, hHp⟩, hmax, hRH⟩ := TightDatum.maxPerfect_of_model hD hι hιN hιu H₁_le
    perfect_le_H₁ noOddNormal_H₁
  refine TightDatum.good_of_gl2 hD hHN hHt hHp hmax hRH (θ := ι.comp φ) (hι.comp φ_injective) ?_
    (by rw [MonoidHom.comp_apply, φ_neg_one, hιu]) hsR hsN hs4
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    have hA : φ A ∈ Subgroup.centralizer {u₁} ⊓
        Subgroup.centralizer (H₁ : Set SL(2 + 3, ZMod 3)) := range_φ ▸ ⟨A, rfl⟩
    have h1 : φ A ∈ Subgroup.centralizer {u₁} := hA.1
    have h2 : φ A ∈ Subgroup.centralizer (H₁ : Set SL(2 + 3, ZMod 3)) := hA.2
    have hN' : (ι.comp φ) A ∈ N := hιN ▸ ⟨φ A, rfl⟩
    have ht' : (ι.comp φ) A ∈ Subgroup.centralizer {t} := by
      rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← hιu, ← map_mul,
        ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp h1]
    have hH' : (ι.comp φ) A ∈ Subgroup.centralizer (H₁.map ι : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp h2 h hh]
    exact ⟨⟨hN', ht'⟩, hH'⟩
  · rintro g ⟨⟨hgN, hgt⟩, hgH⟩
    obtain ⟨p, rfl⟩ : g ∈ ι.range := hιN ▸ hgN
    obtain ⟨hpu, hpH⟩ := mem_centralizer_of_model hι hιu hgt hgH
    obtain ⟨A, rfl⟩ := mem_range_φ hpu hpH
    exact ⟨A, rfl⟩

theorem TightDatum.good_of_sl5 (hD : TightDatum R S t) {N : Subgroup Y} [N.Normal]
    (e₀ : N ≃* SL(5, ZMod 3)) (htN : t ∈ N) {s : Y} (hsR : s ∈ R) (hsN : s ∈ N)
    (hs4 : orderOf s = 4) : GoodThreeElement R t := by
  have ht2 : t * t = 1 := by rw [← sq, ← hD.order, pow_orderOf_eq_one]
  have hz : e₀ ⟨t, htN⟩ * e₀ ⟨t, htN⟩ = 1 := by
    rw [← map_mul, ← map_one e₀]
    exact congrArg e₀ (Subtype.ext ht2)
  have hz1 : e₀ ⟨t, htN⟩ ≠ 1 := fun h => by
    have h1 : (⟨t, htN⟩ : N) = 1 := e₀.injective (h.trans (map_one e₀).symm)
    have := hD.order
    rw [show t = 1 from congrArg Subtype.val h1, orderOf_one] at this
    exact absurd this (by norm_num)
  obtain ⟨c, hc⟩ := exists_conj_u hz hz1
  set e : N ≃* SL(5, ZMod 3) := e₀.trans (MulAut.conj c⁻¹) with he
  set ι : SL(5, ZMod 3) →* Y := N.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hιN : ι.range = N := by
    rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hιt : ι (c⁻¹ * e₀ ⟨t, htN⟩ * c) = t := by
    have h1 : e ⟨t, htN⟩ = c⁻¹ * e₀ ⟨t, htN⟩ * c := by
      rw [he, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
    rw [hιdef, MonoidHom.comp_apply, ← h1]
    simp
  rcases hc with hc | hc
  · exact TightDatum.good_of_u₁ hD (ι := ι) hι hιN ((congrArg ι hc.symm).trans hιt) hsR hsN hs4
  · exact (TightDatum.false_of_u₂ hD (ι := ι) hι hιN ((congrArg ι hc.symm).trans hιt) hsR hsN
      hs4).elim

end Q3L5

theorem good_l53 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)]
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hP' : LieModel ↥(genFittingFStar Y) .PSL 5 3 1) {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hD : TightDatum R S t) : GoodThreeElement R t := by
  have := genFittingFStar_normal Y
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD
    (Nobq.centralizer_genFittingFStar_eq_bot hnab)
    (outTwoCyclic_PSL5 Nat.prime_three le_rfl (by norm_num) hP')
  obtain ⟨e₀⟩ := exists_mulEquiv_sl5 hP'
  exact Q3L5.TightDatum.good_of_sl5 hD e₀ htN hsR hsN hs4

theorem smallSimpleLeaf_l53 : SmallSimpleLeaf fun F _ => LieModel F .PSL 5 3 1 := by
  intro Y _ _ _ _ hnab _ hP R S t hD _ _
  exact Or.inr (good_l53 hnab hP hD)

end CFSG.ClassicalInvolution.Q3.TA3
