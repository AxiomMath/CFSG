module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ChainFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ChainLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.TypeADevissage
public import CFSG.GroupTheory.ElementaryAbelianNormalizerBound
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private theorem commutator_mem {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

private theorem IsLayer.map_commutator {X₀ X : Subgroup G} {ψ : G → G}
    (h : IsLayer L A X₀ X ψ) {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    ψ ⁅x, y⁆ = ⁅ψ x, ψ y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hx' : x⁻¹ ∈ X := X.inv_mem hx
  have hy' : y⁻¹ ∈ X := X.inv_mem hy
  have hxy : x * y ∈ X := X.mul_mem hx hy
  rw [h.map_mul ((x * y) * x⁻¹) (X.mul_mem hxy hx') y⁻¹ hy',
    h.map_mul (x * y) hxy x⁻¹ hx', h.map_mul x hx y hy, h.map_inv hx,
    h.map_inv hy]

theorem ChainHyp.of_isLayer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {F X : Subgroup G} {φ : G → G} (hF : ChainHyp L A D t F) (hφ : IsLayer L A F X φ)
    (hXC : X ≤ centralizer (D : Set G)) (hXF : X ≤ normalizer (F : Set G))
    (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : ChainHyp L A D t X := by
  classical
  have hF_le_X : F ≤ X := hφ.le
  have hD_le_X : D ≤ X := hF.D_le.trans hF_le_X
  have hD_le_F : D ≤ F := hF.D_le
  let Z1 : Subgroup G :=
    { carrier := {f | f ∈ F ∧ ∀ x ∈ X, ⁅x, f⁆ ∈ D}
      one_mem' := ⟨F.one_mem, fun x _ => by
        rw [commutatorElement_def]
        simp⟩
      mul_mem' := by
        rintro f f' ⟨hf, hfD⟩ ⟨hf', hf'D⟩
        refine ⟨F.mul_mem hf hf', fun x hx => ?_⟩
        have hcF : ⁅x, f'⁆ ∈ F := hD_le_F (hf'D x hx)
        have hconj : f * ⁅x, f'⁆ * f⁻¹ = ⁅x, f'⁆ := by
          rw [hF.comm f hf _ hcF]
          group
        rw [commutatorElement_mul_right_eq_mul_conj x f f']
        rw [show ⁅x, f⁆ * f * ⁅x, f'⁆ * f⁻¹ = ⁅x, f⁆ * ⁅x, f'⁆ by
          calc ⁅x, f⁆ * f * ⁅x, f'⁆ * f⁻¹
              = ⁅x, f⁆ * (f * ⁅x, f'⁆ * f⁻¹) := by group
            _ = ⁅x, f⁆ * ⁅x, f'⁆ := by rw [hconj]]
        exact D.mul_mem (hfD x hx) (hf'D x hx)
      inv_mem' := by
        rintro f ⟨hf, hfD⟩
        refine ⟨F.inv_mem hf, fun x hx => ?_⟩
        have hfx : ⁅f, x⁆ = ⁅x, f⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        have hcF : ⁅f, x⁆ ∈ F := by
          rw [hfx]; exact F.inv_mem (hD_le_F (hfD x hx))
        have hconj : f⁻¹ * ⁅f, x⁆ * f = ⁅f, x⁆ := by
          rw [hF.comm (f⁻¹) (F.inv_mem hf) _ hcF]
          group
        rw [commutatorElement_inv_right, hconj, hfx]
        exact D.inv_mem (hfD x hx) }
  have hZ1_le_F : Z1 ≤ F := fun _ hf => hf.1
  have hZ1_le_X : Z1 ≤ X := hZ1_le_F.trans hF_le_X
  let Z2 : Subgroup G :=
    { carrier := {f | f ∈ F ∧ ∀ x ∈ X, ⁅x, f⁆ ∈ Z1}
      one_mem' := ⟨F.one_mem, fun x _ => by
        simpa [commutatorElement_def] using (Z1.one_mem : (1 : G) ∈ Z1)⟩
      mul_mem' := by
        rintro f f' ⟨hf, hfZ⟩ ⟨hf', hf'Z⟩
        refine ⟨F.mul_mem hf hf', fun x hx => ?_⟩
        have hcF : ⁅x, f'⁆ ∈ Z1 := hf'Z x hx
        have hconj : f * ⁅x, f'⁆ * f⁻¹ = ⁅x, f'⁆ := by
          rw [hF.comm f hf _ (hZ1_le_F hcF)]
          group
        rw [commutatorElement_mul_right_eq_mul_conj x f f']
        rw [show ⁅x, f⁆ * f * ⁅x, f'⁆ * f⁻¹ = ⁅x, f⁆ * ⁅x, f'⁆ by
          calc ⁅x, f⁆ * f * ⁅x, f'⁆ * f⁻¹
              = ⁅x, f⁆ * (f * ⁅x, f'⁆ * f⁻¹) := by group
            _ = ⁅x, f⁆ * ⁅x, f'⁆ := by rw [hconj]]
        exact Z1.mul_mem (hfZ x hx) hcF
      inv_mem' := by
        rintro f ⟨hf, hfZ⟩
        refine ⟨F.inv_mem hf, fun x hx => ?_⟩
        have hcF : ⁅x, f⁆ ∈ Z1 := hfZ x hx
        have hfx : ⁅f, x⁆ = ⁅x, f⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        have hcF' : ⁅f, x⁆ ∈ Z1 := by
          rw [hfx]; exact Z1.inv_mem hcF
        have hconj : f⁻¹ * ⁅f, x⁆ * f = ⁅f, x⁆ := by
          rw [hF.comm (f⁻¹) (F.inv_mem hf) _ (hZ1_le_F hcF')]
          group
        rw [commutatorElement_inv_right, hconj, hfx]
        exact Z1.inv_mem hcF }
  have hZ2_le_F : Z2 ≤ F := fun _ hf => hf.1
  have hDZ1 : D ≤ Z1 := by
    intro d hd
    refine ⟨hD_le_F hd, fun x hx => ?_⟩
    have hcomm : x * d * x⁻¹ = d := by
      rw [show x * d = d * x from (mem_centralizer_iff.1 (hXC hx) d hd).symm]
      group
    rw [commutatorElement_def, hcomm]
    simp
  have hZ1Z2 : Z1 ≤ Z2 := by
    intro f hf
    exact ⟨hf.1, fun x hx => hDZ1 (hf.2 x hx)⟩
  have hDnorm : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ D, n * y * n⁻¹ ∈ D := by
    intro n hn y hy
    have hnD : n ∈ L ⊓ normalizer (D : Set G) := by
      rw [H.inf_normalizer_D_eq W W2 hD]
      exact hn
    exact (Subgroup.mem_normalizer_iff.1 hnD.2 y).1 hy
  have hZ1norm : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Z1, n * y * n⁻¹ ∈ Z1 := by
    intro n hn y hy
    have hnin : n⁻¹ ∈ L ⊓ normalizer (A : Set G) :=
      (L ⊓ normalizer (A : Set G)).inv_mem hn
    have hnD : n ∈ L ⊓ normalizer (D : Set G) := by
      rw [H.inf_normalizer_D_eq W W2 hD]
      exact hn
    refine ⟨hF.conj_mem n hn y hy.1, fun x hx => ?_⟩
    have hx' : n⁻¹ * x * n ∈ X := by
      simpa using hφ.conj_mem n⁻¹ hnin x hx
    have heq : ⁅x, n * y * n⁻¹⁆ = n * ⁅n⁻¹ * x * n, y⁆ * n⁻¹ := by
      have h : ⁅n * (n⁻¹ * x * n) * n⁻¹, n * y * n⁻¹⁆ =
          n * ⁅n⁻¹ * x * n, y⁆ * n⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at h
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.1 hnD.2 _).1 (hy.2 _ hx')
  have hZ2norm : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Z2, n * y * n⁻¹ ∈ Z2 := by
    intro n hn y hy
    have hnin : n⁻¹ ∈ L ⊓ normalizer (A : Set G) :=
      (L ⊓ normalizer (A : Set G)).inv_mem hn
    have hnZ1 : n ∈ normalizer (Z1 : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨hZ1norm n hn y, fun hy => by
        have h := hZ1norm n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn)
          (n * y * n⁻¹) hy
        rwa [show n⁻¹ * (n * y * n⁻¹) * (n⁻¹)⁻¹ = y by group] at h⟩
    refine ⟨hF.conj_mem n hn y hy.1, fun x hx => ?_⟩
    have hx' : n⁻¹ * x * n ∈ X := by
      simpa using hφ.conj_mem n⁻¹ hnin x hx
    have heq : ⁅x, n * y * n⁻¹⁆ = n * ⁅n⁻¹ * x * n, y⁆ * n⁻¹ := by
      have h : ⁅n * (n⁻¹ * x * n) * n⁻¹, n * y * n⁻¹⁆ =
          n * ⁅n⁻¹ * x * n, y⁆ * n⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at h
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.1 hnZ1 _).1 (hy.2 _ hx')
  have hZF : F ⊔ Z1 = F := sup_eq_left.mpr hZ1_le_F
  have hDF : F ⊔ D = F := sup_eq_left.mpr hD_le_F
  have hZ1F : F ⊓ Z1 = Z1 := inf_eq_right.mpr hZ1_le_F
  have hDZ1inf : D ⊓ Z1 = D := inf_eq_left.mpr hDZ1
  have hZ1Z2inf : Z1 ⊓ Z2 = Z1 := inf_eq_left.mpr hZ1Z2
  have hFZ2 : F ⊓ Z2 = Z2 := inf_eq_right.mpr hZ2_le_F
  have hY4 : IsTypeA L A Z1 Z2 := by
    have hcomm : ∀ x ∈ F ⊔ Z1, ∀ y ∈ F ⊔ Z1, x * y = y * x := by
      intro x hx y hy
      rw [hZF] at hx hy
      exact hF.comm x hx y hy
    have hsup : IsTypeA L A (⊥ ⊔ Z1) (F ⊔ Z1) := hF.typeA.sup W hZ1norm hcomm
    rw [bot_sup_eq, hZF] at hsup
    have hinf := hsup.inf W hZ2norm
    rwa [hZ1Z2inf, hFZ2] at hinf
  have hZ4 : IsTypeA L A D Z1 := by
    have hcomm : ∀ x ∈ F ⊔ D, ∀ y ∈ F ⊔ D, x * y = y * x := by
      intro x hx y hy
      rw [hDF] at hx hy
      exact hF.comm x hx y hy
    have hsup : IsTypeA L A (⊥ ⊔ D) (F ⊔ D) := hF.typeA.sup W hDnorm hcomm
    rw [bot_sup_eq, hDF] at hsup
    have hinf := hsup.inf W hZ1norm
    rwa [hDZ1inf, hZ1F] at hinf
  have hZ2D : ∀ x ∈ X, ∀ y ∈ Z2, ⁅x, y⁆ ∈ D := by
    refine IsTypeA.bilinear_mem W hφ hY4 hZ4 (fun x y => ⁅x, y⁆) ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun x hx y hy => hy.2 x hx
    · exact fun x hx y hy => by
        have hcomm : x * y = y * x := hF.comm x hx y hy.1
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
        exact D.one_mem
    · exact fun x hx y hy => hy.2 x hx
    · intro x hx x' hx' y hy
      have hc : ⁅x, y⁆ ∈ Z1 := hy.2 x hx
      have hc' : ⁅x', y⁆ ∈ Z1 := hy.2 x' hx'
      have hd : ⁅x, ⁅x', y⁆⁆ ∈ D := hc'.2 x hx
      have hcF : ⁅x, y⁆ ∈ F := hZ1_le_F hc
      have hc'F : ⁅x', y⁆ ∈ F := hZ1_le_F hc'
      have hdF : ⁅x, ⁅x', y⁆⁆ ∈ F := hD_le_F hd
      have hxconj : x * ⁅x', y⁆ * x⁻¹ = ⁅x, ⁅x', y⁆⁆ * ⁅x', y⁆ := by
        rw [commutatorElement_def]; group
      have hkey : (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * ⁅x * x', y⁆ = ⁅x, ⁅x', y⁆⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul x x' y, hxconj]
        calc (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * (⁅x, ⁅x', y⁆⁆ * ⁅x', y⁆ * ⁅x, y⁆)
            = (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * ⁅x, ⁅x', y⁆⁆ * (⁅x', y⁆ * ⁅x, y⁆) := by group
          _ = ⁅x, ⁅x', y⁆⁆ * (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * (⁅x', y⁆ * ⁅x, y⁆) := by
              rw [hF.comm (⁅x, y⁆ * ⁅x', y⁆)⁻¹ (F.inv_mem (F.mul_mem hcF hc'F))
                ⁅x, ⁅x', y⁆⁆ hdF]
          _ = ⁅x, ⁅x', y⁆⁆ * ((⁅x, y⁆ * ⁅x', y⁆)⁻¹ * (⁅x', y⁆ * ⁅x, y⁆)) := by group
          _ = ⁅x, ⁅x', y⁆⁆ * 1 := by
              rw [hF.comm ⁅x, y⁆ hcF ⁅x', y⁆ hc'F]; group
          _ = ⁅x, ⁅x', y⁆⁆ := by group
      rw [hkey]; exact hd
    · intro x hx y hy y' hy'
      have hc : ⁅x, y⁆ ∈ Z1 := hy.2 x hx
      have hc' : ⁅x, y'⁆ ∈ Z1 := hy'.2 x hx
      have hcF : ⁅x, y⁆ ∈ F := hZ1_le_F hc
      have hc'F : ⁅x, y'⁆ ∈ F := hZ1_le_F hc'
      have hconj : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by
        rw [hF.comm y hy.1 _ hc'F]; group
      have hkey : (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ * ⁅x, y * y'⁆ = 1 := by
        rw [commutatorElement_mul_right_eq_mul_conj x y y']
        rw [show ⁅x, y⁆ * y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) by group,
          hconj]
        group
      rw [hkey]
      exact D.one_mem
    · intro n hn x hx y hy
      exact (show ⁅n * x * n⁻¹, n * y * n⁻¹⁆ = n * ⁅x, y⁆ * n⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group)
  have hZ2Z1 : Z2 ≤ Z1 := by
    intro y hy
    exact ⟨hy.1, fun x hx => hZ2D x hx y hy⟩
  have hZ2_eq_Z1 : Z2 = Z1 := le_antisymm hZ2Z1 hZ1Z2
  have hXZ1 : ∀ x ∈ X, ∀ z ∈ Z1, x * z * x⁻¹ ∈ Z1 := by
    intro x hx z hz
    have hc : ⁅x, z⁆ ∈ D := hZ2D x hx z (hZ2_eq_Z1.symm ▸ hz)
    have hxz : x * z * x⁻¹ = ⁅x, z⁆ * z := by
      rw [commutatorElement_def]
      group
    rw [hxz]
    exact Z1.mul_mem (hDZ1 hc) hz
  have hFZ1 : F ≤ Z1 := by
    by_contra hnot
    obtain ⟨f0, hf0F, hf0Z1⟩ := Set.not_subset.1 hnot
    have hf0X : f0 ∈ X := hF_le_X hf0F
    let Z1X : Subgroup ↥X := Z1.subgroupOf X
    let FX : Subgroup ↥X := F.subgroupOf X
    haveI hZ1X_normal : Z1X.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZ1_le_X).2 fun x hx => by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        exact ⟨hXZ1 x hx z, fun hz => by
          have h := hXZ1 x⁻¹ (X.inv_mem hx) (x * z * x⁻¹) hz
          rwa [show x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ = z by group] at h⟩
    have hFX_normal : FX.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hF_le_X).2 hXF
    let N : Subgroup (↥X ⧸ Z1X) := FX.map (QuotientGroup.mk' Z1X)
    haveI hN_normal : N.Normal :=
      Subgroup.Normal.map hFX_normal (QuotientGroup.mk' Z1X)
        (QuotientGroup.mk'_surjective Z1X)
    have hNne : N ≠ ⊥ := by
      intro hbot
      let f0X : ↥X := ⟨f0, hf0X⟩
      have hf0FX : f0X ∈ FX := Subgroup.mem_subgroupOf.mpr hf0F
      have hmem : QuotientGroup.mk' Z1X f0X ∈ N :=
        Subgroup.mem_map_of_mem _ hf0FX
      rw [hbot] at hmem
      have hone : QuotientGroup.mk' Z1X f0X = 1 := by simpa using hmem
      have hmemZ1 : f0X ∈ Z1X := (QuotientGroup.eq_one_iff f0X).1 hone
      exact hf0Z1 (Subgroup.mem_subgroupOf.mp hmemZ1)
    have hXtypeA : IsTypeA L A ⊥ X := IsTypeA.step φ hF.typeA hφ
    obtain ⟨r, hr⟩ := hXtypeA.exists_card_eq W
    rw [Subgroup.card_bot, mul_one] at hr
    have hXp : IsPGroup 2 ↥X :=
      IsPGroup.of_card (n := 4 * r) (by rw [hr, pow_mul]; norm_num)
    haveI hNil : Group.IsNilpotent (↥X ⧸ Z1X) := (hXp.to_quotient Z1X).isNilpotent
    obtain ⟨g, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥X ⧸ Z1X) hNne)
    obtain ⟨fX, hfXFX, hfXg⟩ := Subgroup.mem_map.1 g.2.1
    have hfF : (fX : G) ∈ F := Subgroup.mem_subgroupOf.mp hfXFX
    have hfZ1 : (fX : G) ∉ Z1 := by
      intro hfZ
      have hfXZ : fX ∈ Z1X := Subgroup.mem_subgroupOf.mpr hfZ
      have hone : QuotientGroup.mk' Z1X fX = 1 := (QuotientGroup.eq_one_iff fX).2 hfXZ
      exact hgne (Subtype.ext (hfXg.symm.trans hone))
    have hbeta : ∀ x ∈ X, ⁅x, (fX : G)⁆ ∈ Z1 := by
      intro x hx
      let xX : ↥X := ⟨x, hx⟩
      have hcent : QuotientGroup.mk' Z1X xX * g = g * QuotientGroup.mk' Z1X xX :=
        Subgroup.mem_center_iff.1 g.2.2 (QuotientGroup.mk' Z1X xX)
      have hcomm : QuotientGroup.mk' Z1X ⁅xX, fX⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        simpa only [hfXg] using hcent
      have hmem : ⁅xX, fX⁆ ∈ Z1X := (QuotientGroup.eq_one_iff ⁅xX, fX⁆).1 hcomm
      simpa [commutatorElement_def] using Subgroup.mem_subgroupOf.mp hmem
    have hfZ2 : (fX : G) ∈ Z2 := ⟨hfF, hbeta⟩
    exact hfZ1 (hZ2_eq_Z1 ▸ hfZ2)
  have hZ1_eq_F : Z1 = F := le_antisymm hZ1_le_F hFZ1
  have hZ2_eq_F : Z2 = F := hZ2_eq_Z1.trans hZ1_eq_F
  have hstep4 : ∀ x ∈ X, ∀ f ∈ F, ⁅x, f⁆ ∈ D := by
    intro x hx f hf
    exact hZ2D x hx f (hZ2_eq_F.symm ▸ hf)
  have hY5 : IsTypeA L A D F := by
    have hcomm : ∀ x ∈ F ⊔ D, ∀ y ∈ F ⊔ D, x * y = y * x := by
      intro x hx y hy
      rw [hDF] at hx hy
      exact hF.comm x hx y hy
    have hsup : IsTypeA L A (⊥ ⊔ D) (F ⊔ D) := hF.typeA.sup W hDnorm hcomm
    rwa [bot_sup_eq, hDF] at hsup
  have hZ5 : IsTypeA L A ⊥ D := H.isTypeA_bot_D W W2 hD h4
  have hstep5 : ∀ x ∈ X, ∀ f ∈ F, x * f = f * x := by
    have hbil := IsTypeA.bilinear_mem W hφ hY5 hZ5 (fun x y => ⁅x, y⁆)
      (fun x hx y hy => hstep4 x hx y hy)
      (fun x hx y hy => by
        have hcomm : x * y = y * x := hF.comm x hx y hy
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
        exact Subgroup.one_mem ⊥)
      (fun x hx y hy => by
        have hcomm : x * y = y * x := (mem_centralizer_iff.1 (hXC hx) y hy).symm
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
        exact Subgroup.one_mem ⊥)
      (fun x hx x' hx' y hy => by
        have hcy : ⁅x', y⁆ ∈ D := hstep4 x' hx' y hy
        have hcx : ⁅x, y⁆ ∈ D := hstep4 x hx y hy
        have hconj : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by
          rw [show x * ⁅x', y⁆ = ⁅x', y⁆ * x from
            (mem_centralizer_iff.1 (hXC hx) _ hcy).symm]
          group
        have hkey : (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * ⁅x * x', y⁆ = 1 := by
          rw [commutatorElement_mul_left_eq_conj_mul x x' y]
          rw [hconj]
          rw [show (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * (⁅x', y⁆ * ⁅x, y⁆) = 1 by
            rw [show ⁅x', y⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x', y⁆ from
              (hD.comm _ hcx _ hcy).symm]
            group]
        rw [hkey]
        exact Subgroup.one_mem ⊥)
      (fun x hx y hy y' hy' => by
        have hcy' : ⁅x, y'⁆ ∈ D := hstep4 x hx y' hy'
        have hconj : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by
          rw [hF.comm y hy _ (hD_le_F hcy')]
          group
        have hkey : (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ * ⁅x, y * y'⁆ = 1 := by
          rw [commutatorElement_mul_right_eq_mul_conj x y y']
          rw [show ⁅x, y⁆ * y * ⁅x, y'⁆ * y⁻¹ =
            ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) by group, hconj]
          group
        rw [hkey]
        exact Subgroup.one_mem ⊥)
      (fun n hn x hx y hy => (show ⁅n * x * n⁻¹, n * y * n⁻¹⁆ = n * ⁅x, y⁆ * n⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group))
    intro x hx f hf
    exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa using hbil x hx f hf)
  have hY6 : IsTypeA L A F X := IsTypeA.step φ (IsTypeA.refl F hF.conj_mem) hφ
  have hstep6Z : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ F := by
    intro x hx y hy
    have hxmem : ⁅x, y⁆ ∈ X := commutator_mem hx hy
    refine (hφ.eq_one_iff _ hxmem).1 ?_
    rw [IsLayer.map_commutator hφ hx hy]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (W.A_comm _ (hφ.mem x hx) _ (hφ.mem y hy))
  have hstep6 : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    have hbil := IsTypeA.bilinear_mem W hφ hY6 hF.typeA (fun x y => ⁅x, y⁆)
      (fun x hx y hy => hstep6Z x hx y hy)
      (fun x hx y hy => by
        have hcomm : x * y = y * x := (hstep5 y hy x hx).symm
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
        exact Subgroup.one_mem ⊥)
      (fun x hx y hy => by
        have hcomm : x * y = y * x := hstep5 x hx y hy
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
        exact Subgroup.one_mem ⊥)
      (fun x hx x' hx' y hy => by
        have hcx'y : ⁅x', y⁆ ∈ F := hstep6Z x' hx' y hy
        have hcxy : ⁅x, y⁆ ∈ F := hstep6Z x hx y hy
        have hconj : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by
          rw [hstep5 x hx _ hcx'y]
          group
        have hkey : (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * ⁅x * x', y⁆ = 1 := by
          rw [commutatorElement_mul_left_eq_conj_mul x x' y]
          rw [hconj]
          rw [show (⁅x, y⁆ * ⁅x', y⁆)⁻¹ * (⁅x', y⁆ * ⁅x, y⁆) = 1 by
            rw [show ⁅x', y⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x', y⁆ from
              hF.comm _ hcx'y _ hcxy]
            group]
        rw [hkey]
        exact Subgroup.one_mem ⊥)
      (fun x hx y hy y' hy' => by
        have hcy' : ⁅x, y'⁆ ∈ F := hstep6Z x hx y' hy'
        have hconj : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by
          rw [hstep5 y hy _ hcy']
          group
        have hkey : (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ * ⁅x, y * y'⁆ = 1 := by
          rw [commutatorElement_mul_right_eq_mul_conj x y y']
          rw [show ⁅x, y⁆ * y * ⁅x, y'⁆ * y⁻¹ =
            ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) by group, hconj]
          group
        rw [hkey]
        exact Subgroup.one_mem ⊥)
      (fun n hn x hx y hy => (show ⁅n * x * n⁻¹, n * y * n⁻¹⁆ = n * ⁅x, y⁆ * n⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group))
    intro x hx y hy
    exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa using hbil x hx y hy)
  have hstep7 : ∀ x ∈ X, x ^ 2 = 1 → x ∈ D := by
    let Ω : Subgroup G := omega1 X hstep6
    have hVΩ : omega1 D hD.comm ≤ Ω := fun v hv => ⟨hD_le_X hv.1, hv.2⟩
    haveI hΩele : IsElementaryAbelian 2 Ω :=
      IsElementaryAbelian.two_of_forall_mul_self
        (fun a ha b hb => hstep6 a ha.1 b hb.1)
        (fun a ha => by simpa [pow_two] using ha.2)
    have htΩ : t ∈ normalizer (Ω : Set G) := by
      have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        refine ⟨hXt w hw.1, ?_⟩
        calc (t * w * t⁻¹) ^ 2 = t * w ^ 2 * t⁻¹ := by rw [sq, sq]; group
          _ = 1 := by rw [hw.2]; group
      · intro hw
        have he : t * (t * w * t⁻¹) * t⁻¹ = w := by
          rw [htinv]
          calc t * (t * w * t) * t = (t * t) * w * (t * t) := by group
            _ = w := by rw [ht2]; group
        have h2 : t * (t * w * t⁻¹) * t⁻¹ ∈ Ω := by
          refine ⟨?_, ?_⟩
          · exact hXt (t * w * t⁻¹) hw.1
          · calc (t * (t * w * t⁻¹) * t⁻¹) ^ 2
                = t * (t * w * t⁻¹) ^ 2 * t⁻¹ := by rw [sq, sq]; group
              _ = 1 := by rw [hw.2]; group
        rwa [he] at h2
    have ht2c : t ^ 2 ∈ centralizer (Ω : Set G) := by
      rw [H.sq_t]
      exact Subgroup.one_mem _
    have hΩsq := CFSG.GroupTheory.card_le_card_inf_centralizer_sq (Y := Ω) (x := t) htΩ ht2c
    have hΩA : Ω ⊓ centralizer ({t} : Set G) ≤ A := by
      intro w hw
      have hwC : w ∈ centralizer (D : Set G) := hXC hw.1.1
      have hwAa : w ∈ Aa := by
        have hmem : w ∈ centralizer (D : Set G) ⊓ centralizer ({t} : Set G) := ⟨hwC, hw.2⟩
        rwa [H.centralizer_D_inf_centralizer_t W W2 hD] at hmem
      exact W2.mem_A_of_sq_eq_one W hwAa (by simpa [pow_two] using hw.1.2)
    have hΩcard : Nat.card ↥(Ω ⊓ centralizer ({t} : Set G)) ≤ 16 := by
      calc Nat.card ↥(Ω ⊓ centralizer ({t} : Set G)) ≤ Nat.card A :=
            Subgroup.card_le_of_le hΩA
        _ = 16 := W.A_card
    have hΩle : Nat.card Ω ≤ 256 := by
      calc Nat.card Ω ≤ Nat.card ↥(Ω ⊓ centralizer ({t} : Set G)) ^ 2 := hΩsq
        _ ≤ 16 ^ 2 := Nat.pow_le_pow_left hΩcard 2
        _ = 256 := by norm_num
    have hVcard : Nat.card (omega1 D hD.comm) = 256 := by
      rw [H.card_omega1 W W2 hD (fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd)]
      norm_num
    have hΩV : Ω = omega1 D hD.comm :=
      (Subgroup.eq_of_le_of_card_ge hVΩ (by rw [hVcard]; exact hΩle)).symm
    intro x hx hx2
    have hxV : x ∈ omega1 D hD.comm := by
      rw [← hΩV]
      exact ⟨hx, hx2⟩
    exact hxV.1
  refine
    { D_le := hD_le_X
      le_centralizer := hXC
      comm := hstep6
      typeA := IsTypeA.step φ hF.typeA hφ
      conj_t_mem := hXt
      mem_of_sq_eq_one := hstep7 }

theorem ThCyc.exists_QHyp_of_step (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hstep : ∀ F : Subgroup G, ChainHyp L A D t F → ∀ Y : Subgroup G,
      Y ≤ centralizer (D : Set G) → IsPGroup 2 Y → F ≤ Y → ¬ Y ≤ F →
      ∃ (X : Subgroup G) (φ : G → G), IsLayer L A F X φ ∧ X ≤ centralizer (D : Set G) ∧
        X ≤ normalizer (F : Set G) ∧ ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    ∃ Q : Subgroup G, QHyp L A D t Q := by
  classical
  let Links : Set (Subgroup G) := {F | ChainHyp L A D t F}
  have hDlink : D ∈ Links := H.chainHyp_D W W2 hD h4
  obtain ⟨F, hF, hFmax⟩ := (Set.toFinite Links).exists_maximal ⟨D, hDlink⟩
  by_cases hmax : ∀ Y : Subgroup G,
      Y ≤ centralizer (D : Set G) → IsPGroup 2 Y → F ≤ Y → Y ≤ F
  · exact ⟨F, hF.qHyp W hmax⟩
  · push Not at hmax
    obtain ⟨Y, hYC, hYp, hFY, hYnotF⟩ := hmax
    obtain ⟨X, φ, hφ, hXC, hXF, hXt⟩ := hstep F hF Y hYC hYp hFY hYnotF
    have hX : ChainHyp L A D t X :=
      hF.of_isLayer H W W2 hD h4 hφ hXC hXF hXt
    have hle : F ≤ X := hφ.le
    have hXleF : X ≤ F := hFmax hX hle
    have hXeqF : X = F := le_antisymm hXleF hle
    have hcard := IsLayer.card_eq W hφ
    rw [hXeqF] at hcard
    have hpos : 0 < Nat.card F := Nat.card_pos
    omega

theorem ThCyc.exists_QHyp (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    ∃ Q : Subgroup G, QHyp L A D t Q :=
  H.exists_QHyp_of_step W W2 hD h4 fun _ hF _ hYC hYp hFY hYF => by
    obtain ⟨p, hpC, hpN, hpF, hfp⟩ := hF.exists_fix H W W2 hD hYC hYp hFY hYF
    obtain ⟨Ft, It, κ, hFt, hIt, hκ⟩ := hF.exists_isLayer_commutator H W W2 hD h4 hpC hpF hfp
    exact hF.exists_isLayer_of_fix H W W2 hD hFt hIt hκ hpC hpN hpF hfp

end CFSG.EvenSporadicStandard.ThStd

end
