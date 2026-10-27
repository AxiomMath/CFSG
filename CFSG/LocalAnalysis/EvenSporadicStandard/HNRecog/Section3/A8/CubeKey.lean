module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Orb2A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeSix

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem isConj_conj_iff {G : Type} [Group G] {a : G} (g x : G) :
    IsConj a (MulAut.conj g x) ↔ IsConj a x := by
  constructor
  · intro h
    refine h.trans (isConj_iff.mpr ⟨g⁻¹, ?_⟩)
    simp [MulAut.conj_apply, mul_assoc]
  · intro h
    exact h.trans (isConj_iff.mpr ⟨g, rfl⟩)

private theorem natCard_twoA_map_conj {G : Type} [Group G] (a g : G) (E : Subgroup G) :
    Nat.card {e : G // e ∈ E.map (MulAut.conj g).toMonoidHom ∧ IsConj a e} =
      Nat.card {e : G // e ∈ E ∧ IsConj a e} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv ?_).symm
  intro e
  exact and_congr
    (Subgroup.mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm
    (isConj_conj_iff g e).symm

theorem exists_mem_normalizer_conj_pair (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hA8 : Vert A8Shapes a z) {E : Subgroup G} (hE : IsElemTwo 3 E)
    (h6 : Nat.card {x : G // x ∈ E ∧ IsConj a x} = 6) {x y x' y' : G} (hxE : x ∈ E) (hyE : y ∈ E)
    (hx'E : x' ∈ E) (hy'E : y' ∈ E) (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y))
    (hx' : IsConj a x') (hy' : IsConj a y') (hxy' : IsConj a (x' * y')) :
    ∃ k ∈ Subgroup.normalizer (E : Set G), k * x * k⁻¹ = x' ∧ k * y * k⁻¹ = y' := by
  obtain ⟨g₀, hg₀x, hg₀y⟩ := exists_conj_pair hI h hF1 hF2 hx hy hxy hx' hy' hxy'
  let E₁ : Subgroup G := E.map (MulAut.conj g₀).toMonoidHom
  have hE₁ : IsElemTwo 3 E₁ :=
    isElemTwo_map (MulAut.conj g₀).toMonoidHom (MulAut.conj g₀).injective hE
  have h6₁ : Nat.card {e : G // e ∈ E₁ ∧ IsConj a e} = 6 := by
    show Nat.card {e : G // e ∈ E.map (MulAut.conj g₀).toMonoidHom ∧ IsConj a e} = 6
    rw [natCard_twoA_map_conj a g₀ E, h6]
  have hx'E₁ : x' ∈ E₁ := Subgroup.mem_map.mpr ⟨x, hxE, hg₀x⟩
  have hy'E₁ : y' ∈ E₁ := Subgroup.mem_map.mpr ⟨y, hyE, hg₀y⟩
  obtain ⟨t₂, ht₂mem, _ht₂2, _ht₂ne, hE₂, hcyc₂⟩ :=
    exists_two_four_of_cube hI h hF1 hF2 hF3 hA8 hE h6 hx'E hy'E hx' hy' hxy'
  obtain ⟨t₁, ht₁mem, _ht₁2, _ht₁ne, hE₁c, hcyc₁⟩ :=
    exists_two_four_of_cube hI h hF1 hF2 hF3 hA8 hE₁ h6₁ hx'E₁ hy'E₁ hx' hy' hxy'
  have hy'2 : y' ∈ orb2A x' x' := ⟨hx'.symm.trans hy', hx'.symm.trans hxy'⟩
  have hshape : IsShapeTwoTwoTimesA8 ↥(Gxy x' y') :=
    (hF3 x' z hx' (IsConj.refl z)).shape_2A y' hy'2
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hshape
  let s₁ : alternatingGroup (Fin 8) := φ.symm ⟨t₁, ht₁mem⟩
  let s₂ : alternatingGroup (Fin 8) := φ.symm ⟨t₂, ht₂mem⟩
  have hφs₁ : ((φ s₁ : ↥(derivedOf (Gxy x' y'))) : G) = t₁ := by
    show ((φ (φ.symm ⟨t₁, ht₁mem⟩) : ↥(derivedOf (Gxy x' y'))) : G) = t₁
    simp
  have hφs₂ : ((φ s₂ : ↥(derivedOf (Gxy x' y'))) : G) = t₂ := by
    show ((φ (φ.symm ⟨t₂, ht₂mem⟩) : ↥(derivedOf (Gxy x' y'))) : G) = t₂
    simp
  have hs₁ : (s₁ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := hcyc₁ φ s₁ hφs₁
  have hs₂ : (s₂ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := hcyc₂ φ s₂ hφs₂
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_two_two_two_two hs₁ hs₂)
  let σ : G := ((φ c : ↥(derivedOf (Gxy x' y'))) : G)
  have hσt : σ * t₁ * σ⁻¹ = t₂ := by
    have h1 : (φ c : ↥(derivedOf (Gxy x' y'))) * (φ s₁) * (φ c)⁻¹ = φ s₂ := by
      have h := congrArg φ hc
      simpa [map_mul, map_inv] using h
    have h3 := congrArg (fun u : ↥(derivedOf (Gxy x' y')) => (u : G)) h1
    show ((φ c : ↥(derivedOf (Gxy x' y'))) : G) * t₁ *
      (((φ c : ↥(derivedOf (Gxy x' y'))) : G))⁻¹ = t₂
    simpa [hφs₁, hφs₂] using h3
  have hσmem : σ ∈ Gxy x' y' := by
    show ((φ c : ↥(derivedOf (Gxy x' y'))) : G) ∈ Gxy x' y'
    exact derivedOf_le _ (φ c).2
  have hσx : σ * x' * σ⁻¹ = x' := by
    have hcomm : x' * σ = σ * x' := mem_Gx.mp (mem_Gxy.mp hσmem).1
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hσy : σ * y' * σ⁻¹ = y' := by
    have hcomm : y' * σ = σ * y' := mem_Gx.mp (mem_Gxy.mp hσmem).2
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hkx : (σ * g₀) * x * (σ * g₀)⁻¹ = x' := by
    calc (σ * g₀) * x * (σ * g₀)⁻¹ = σ * (g₀ * x * g₀⁻¹) * σ⁻¹ := by group
      _ = σ * x' * σ⁻¹ := by rw [hg₀x]
      _ = x' := hσx
  have hky : (σ * g₀) * y * (σ * g₀)⁻¹ = y' := by
    calc (σ * g₀) * y * (σ * g₀)⁻¹ = σ * (g₀ * y * g₀⁻¹) * σ⁻¹ := by group
      _ = σ * y' * σ⁻¹ := by rw [hg₀y]
      _ = y' := hσy
  have himg : (MulAut.conj σ).toMonoidHom '' ({x', y', t₁} : Set G) = {x', y', t₂} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [show (MulAut.conj σ).toMonoidHom x' = x' from hσx,
      show (MulAut.conj σ).toMonoidHom y' = y' from hσy,
      show (MulAut.conj σ).toMonoidHom t₁ = t₂ from hσt]
  have hcomp : (MulAut.conj (σ * g₀)).toMonoidHom =
      (MulAut.conj σ).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom := by
    ext u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hmap : E.map (MulAut.conj (σ * g₀)).toMonoidHom = E := by
    rw [hcomp, ← Subgroup.map_map (g := (MulAut.conj σ).toMonoidHom)
      (f := (MulAut.conj g₀).toMonoidHom)]
    show E₁.map (MulAut.conj σ).toMonoidHom = E
    rw [hE₁c, MonoidHom.map_closure, himg]
    exact hE₂.symm
  refine ⟨σ * g₀, ?_, hkx, hky⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change E.map (MulAut.conj (σ * g₀)).toMonoidHom = E
  exact hmap

end CFSG.EvenSporadicStandard.HNRecog.Section3
