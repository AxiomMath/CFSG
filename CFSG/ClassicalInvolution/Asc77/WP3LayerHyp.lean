module

public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51
public import CFSG.ClassicalInvolution.Asc77.WP3LayerConj

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Alpha

variable {X X' : Type} [Group X] [Group X']

theorem oddCoreOf_map_equiv (θ : X ≃* X') (Y : Subgroup X) :
    oddCoreOf (Y.map θ.toMonoidHom) = (oddCoreOf Y).map θ.toMonoidHom := by
  let eY : ↥Y ≃* ↥(Y.map θ.toMonoidHom) := Subgroup.equivMapOfInjective Y θ.toMonoidHom θ.injective
  have hinv : (classicalInvolutionOddCore ↥Y).map eY.toMonoidHom =
      classicalInvolutionOddCore ↥(Y.map θ.toMonoidHom) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant eY
  unfold oddCoreOf
  rw [← hinv, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_centralizer_singleton_equiv (θ : X ≃* X') (a : X) :
    (Subgroup.centralizer ({a} : Set X)).map θ.toMonoidHom =
      Subgroup.centralizer ({θ a} : Set X') := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨θ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem alphaOf_map_equiv (θ : X ≃* X') (A : Subgroup X) :
    alphaOf (A.map θ.toMonoidHom) = (alphaOf A).map θ.toMonoidHom := by
  have hOC : ∀ a : X, oddCoreOf (Subgroup.centralizer ({θ a} : Set X')) =
      (oddCoreOf (Subgroup.centralizer ({a} : Set X))).map θ.toMonoidHom := fun a => by
    rw [← map_centralizer_singleton_equiv, oddCoreOf_map_equiv]
  have hcomm : ∀ a : X, ⁅oddCoreOf (Subgroup.centralizer ({θ a} : Set X')), A.map θ.toMonoidHom⁆ =
      (⁅oddCoreOf (Subgroup.centralizer ({a} : Set X)), A⁆).map θ.toMonoidHom := fun a => by
    rw [hOC, Subgroup.map_commutator]
  have hne : ∀ a : X, θ a ≠ 1 ↔ a ≠ 1 := fun a => by
    rw [Ne, Ne, ← map_one θ, θ.injective.eq_iff]
  unfold alphaOf
  rw [Subgroup.map_sup]
  congr 1
  · refine le_antisymm (iSup₂_le fun a' ha' => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      refine iSup_le fun hne' => ?_
      have hne1 : a ≠ 1 := (hne a).mp hne'
      rw [MulEquiv.coe_toMonoidHom, hcomm a]
      exact Subgroup.map_mono (le_iSup₂_of_le a ha (le_iSup_of_le hne1 le_rfl))
    · simp only [Subgroup.map_iSup]
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun hne1 => ?_
      rw [← hcomm a]
      exact le_iSup₂_of_le (θ a) (Subgroup.mem_map_of_mem _ ha)
        (le_iSup_of_le ((hne a).mpr hne1) le_rfl)
  · ext x
    obtain ⟨y, rfl⟩ := θ.surjective x
    rw [Subgroup.mem_map_equiv]
    simp only [Subgroup.mem_iInf, MulEquiv.symm_apply_apply]
    constructor
    · intro h a ha ha1
      have h1 := h (θ a) (Subgroup.mem_map_of_mem _ ha) ((hne a).mpr ha1)
      rw [hOC] at h1
      have h2 := Subgroup.mem_map_equiv.mp h1
      rwa [MulEquiv.symm_apply_apply] at h2
    · intro h a' ha' ha1
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      have h1 := h a ha ((hne a).mp ha1)
      rw [MulEquiv.coe_toMonoidHom, hOC]
      exact Subgroup.mem_map_of_mem _ h1

end Alpha

section Induced

variable {H H' : Type} [Group H] [Group H']

theorem mem_normalizer_map_equiv (e : H ≃* H') (L : Subgroup H) (x : H) :
    e x ∈ Subgroup.normalizer ((L.map e.toMonoidHom : Subgroup H') : Set H') ↔
      x ∈ Subgroup.normalizer (L : Set H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (e y)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    rw [h1]
    simp
  · intro h y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv]
    exact h y

noncomputable def subgroupMapEquiv (e : H ≃* H') (L : Subgroup H) : ↥L ≃* ↥(L.map e.toMonoidHom) :=
  Subgroup.equivMapOfInjective L e.toMonoidHom e.injective

noncomputable def normalizerMapEquiv (e : H ≃* H') (L : Subgroup H) :
    ↥(Subgroup.normalizer (L : Set H)) ≃*
      ↥(Subgroup.normalizer ((L.map e.toMonoidHom : Subgroup H') : Set H')) where
  toFun x := ⟨e x, (mem_normalizer_map_equiv e L x).mpr x.2⟩
  invFun y := ⟨e.symm y, by
    have := (mem_normalizer_map_equiv e L (e.symm y)).mp
    rw [MulEquiv.apply_symm_apply] at this
    exact this y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])

end Induced


section InducedAut

variable {H H' : Type} [Group H] [Group H']

theorem conjOnNormalizer_normalizerMapEquiv (e : H ≃* H') (L : Subgroup H)
    (x : ↥(Subgroup.normalizer (L : Set H))) :
    conjOnNormalizer (L.map e.toMonoidHom) (normalizerMapEquiv e L x) =
      MulAut.congr (subgroupMapEquiv e L) (conjOnNormalizer L x) := by
  ext y'
  obtain ⟨y, hy, hy'⟩ := y'.2
  have hy'' : e y = (y' : H') := hy'
  have h1 : (subgroupMapEquiv e L).symm y' = ⟨y, hy⟩ := by
    apply (subgroupMapEquiv e L).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext hy''.symm
  show e (x : H) * (y' : H') * (e (x : H))⁻¹ =
    e ((x : H) * (((subgroupMapEquiv e L).symm y' : ↥L) : H) * (x : H)⁻¹)
  rw [h1, map_mul, map_mul, map_inv]
  show _ = e (x : H) * e y * (e (x : H))⁻¹
  rw [hy'']

theorem map_inducedAutOn (e : H ≃* H') (L : Subgroup H) :
    (inducedAutOn L).map (MulAut.congr (subgroupMapEquiv e L)).toMonoidHom =
      inducedAutOn (L.map e.toMonoidHom) := by
  have hcomp : (MulAut.congr (subgroupMapEquiv e L)).toMonoidHom.comp (conjOnNormalizer L) =
      (conjOnNormalizer (L.map e.toMonoidHom)).comp (normalizerMapEquiv e L).toMonoidHom := by
    ext x : 1
    exact (conjOnNormalizer_normalizerMapEquiv e L x).symm
  unfold inducedAutOn
  rw [← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (normalizerMapEquiv e L).surjective, ← MonoidHom.range_eq_map]

@[expose] noncomputable def inducedAutEquiv (e : H ≃* H') (L : Subgroup H) :
    ↥(inducedAutOn L) ≃* ↥(inducedAutOn (L.map e.toMonoidHom)) :=
  (Subgroup.equivMapOfInjective _ (MulAut.congr (subgroupMapEquiv e L)).toMonoidHom
    (MulAut.congr (subgroupMapEquiv e L)).injective).trans
    (MulEquiv.subgroupCongr (map_inducedAutOn e L))

theorem inducedAutEquiv_toInducedAutOn (e : H ≃* H') (L : Subgroup H)
    (x : ↥(Subgroup.normalizer (L : Set H))) :
    inducedAutEquiv e L (toInducedAutOn L x) =
      toInducedAutOn (L.map e.toMonoidHom) (normalizerMapEquiv e L x) :=
  Subtype.ext (conjOnNormalizer_normalizerMapEquiv e L x).symm

theorem map_normalizerMapEquiv_subgroupOf (e : H ≃* H') (L B : Subgroup H) :
    (B.subgroupOf (Subgroup.normalizer (L : Set H))).map (normalizerMapEquiv e L).toMonoidHom =
      (B.map e.toMonoidHom).subgroupOf
        (Subgroup.normalizer ((L.map e.toMonoidHom : Subgroup H') : Set H')) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem _ hx
  · intro hy
    refine ⟨(normalizerMapEquiv e L).symm y, ?_, (normalizerMapEquiv e L).apply_symm_apply y⟩
    have h1 := Subgroup.mem_map_equiv.mp hy
    exact h1

theorem inducedImage_map_equiv (e : H ≃* H') (L B : Subgroup H) :
    (inducedImage L B).map (inducedAutEquiv e L).toMonoidHom =
      inducedImage (L.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  unfold inducedImage
  rw [Subgroup.map_map]
  have hcomp : (inducedAutEquiv e L).toMonoidHom.comp (toInducedAutOn L) =
      (toInducedAutOn (L.map e.toMonoidHom)).comp (normalizerMapEquiv e L).toMonoidHom := by
    ext x : 1
    exact inducedAutEquiv_toInducedAutOn e L x
  rw [hcomp, ← Subgroup.map_map, map_normalizerMapEquiv_subgroupOf]

theorem alphaOf_inducedImage_eq_bot_iff (e : H ≃* H') (L B : Subgroup H) :
    alphaOf (inducedImage (L.map e.toMonoidHom) (B.map e.toMonoidHom)) = ⊥ ↔
      alphaOf (inducedImage L B) = ⊥ := by
  rw [← inducedImage_map_equiv, alphaOf_map_equiv]
  exact Subgroup.map_eq_bot_iff_of_injective _ (inducedAutEquiv e L).injective

end InducedAut

section Hyp51

variable {G : Type} [Group G]

theorem isComponent_map_equiv_iff {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (L : Subgroup X) : CFSG.IsComponent (L.map e.toMonoidHom) ↔ CFSG.IsComponent L := by
  have key : ∀ {X X' : Type} [Group X] [Group X'] (e : X ≃* X') (L : Subgroup X),
      CFSG.IsComponent L → CFSG.IsComponent (L.map e.toMonoidHom) := by
    intro X X' _ _ e L hL
    refine ⟨CatalogueBAlternating.quasisimple_iff_native.mpr
      (isQuasisimple_map_of_ker_le_center e.toMonoidHom
        (by rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]; exact bot_le)
        (CatalogueBAlternating.quasisimple_iff_native.mp hL.1)),
      Subgroup.IsSubnormal.map e.surjective hL.2⟩
  refine ⟨fun h => ?_, key e L⟩
  have h1 := key e.symm _ h
  have h2 : (L.map e.toMonoidHom).map e.symm.toMonoidHom = L := by
    ext x
    simp [Subgroup.mem_map]
  rwa [h2] at h1

theorem exists_map_oddQuotConj_eq (g c : G) (L' : Subgroup (OddQuot (g * c * g⁻¹))) :
    ∃ L : Subgroup (OddQuot c), L.map (oddQuotConj g c).toMonoidHom = L' := by
  refine ⟨L'.map (oddQuotConj g c).symm.toMonoidHom, ?_⟩
  ext x
  simp [Subgroup.mem_map]

theorem conjSub_zpowers (g c : G) :
    conjSub g (Subgroup.zpowers c) = Subgroup.zpowers (g * c * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

theorem movedByAll_conj (g c : G) (B : Subgroup G) (L : Subgroup (OddQuot c)) :
    MovedByAll (conjSub g B) (g * c * g⁻¹) (L.map (oddQuotConj g c).toMonoidHom) ↔
      MovedByAll B c L := by
  have hB := map_oddQuotConj_modOdd g c B
  have hZ := map_oddQuotConj_modOdd g c (Subgroup.zpowers c)
  rw [conjSub_zpowers] at hZ
  unfold MovedByAll
  rw [← hB, ← hZ]
  constructor
  · intro h x hx hxZ
    obtain ⟨y', hy', hne⟩ := h (oddQuotConj g c x) (Subgroup.mem_map_of_mem _ hx) (fun hmem =>
      hxZ (by simpa using Subgroup.mem_map_equiv.mp hmem))
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy'
    exact ⟨y, hy, fun hxy => hne (by
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
      rw [hxy])⟩
  · intro h x' hx' hx'Z
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨y, hy, hne⟩ := h x hx (fun hmem => hx'Z (Subgroup.mem_map_of_mem _ hmem))
    exact ⟨oddQuotConj g c y, Subgroup.mem_map_of_mem _ hy, fun hxy => hne
      ((oddQuotConj g c).injective (by simpa [map_mul] using hxy))⟩

theorem hyp51At_conj_mp {g c : G} {B : Subgroup G} (h : Hyp51At B c) :
    Hyp51At (conjSub g B) (g * c * g⁻¹) := by
  obtain ⟨hone, halpha⟩ := h
  refine ⟨fun L₁' L₂' h₁ h₂ m₁ m₂ => ?_, fun L' hL' hm => ?_⟩
  · obtain ⟨L₁, rfl⟩ := exists_map_oddQuotConj_eq g c L₁'
    obtain ⟨L₂, rfl⟩ := exists_map_oddQuotConj_eq g c L₂'
    rw [hone L₁ L₂ ((isComponent_map_equiv_iff _ L₁).mp h₁)
      ((isComponent_map_equiv_iff _ L₂).mp h₂) ((movedByAll_conj g c B L₁).mp m₁)
      ((movedByAll_conj g c B L₂).mp m₂)]
  · obtain ⟨L, rfl⟩ := exists_map_oddQuotConj_eq g c L'
    have h1 := halpha L ((isComponent_map_equiv_iff _ L).mp hL') ((movedByAll_conj g c B L).mp hm)
    have h2 := (alphaOf_inducedImage_eq_bot_iff (oddQuotConj g c) L (modOdd c B)).mpr h1
    rwa [map_oddQuotConj_modOdd] at h2

theorem hyp51At_conj (g c : G) (B : Subgroup G) :
    Hyp51At (conjSub g B) (g * c * g⁻¹) ↔ Hyp51At B c := by
  refine ⟨fun h => ?_, hyp51At_conj_mp⟩
  have h1 := hyp51At_conj_mp (g := g⁻¹) h
  have e1 : conjSub g⁻¹ (conjSub g B) = B := conjSub_inv_conjSub g B
  have e2 : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e1, e2] at h1

theorem hyp51At_of_normalizes {B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) {c : G} (h : Hyp51At B c) :
    Hyp51At B (g * c * g⁻¹) := by
  have := hyp51At_conj_mp (g := g) h
  rwa [conjSub_eq_of_mem_normalizer hg] at this

theorem isElemAbelian_conjSub {B : Subgroup G} (hB : IsElemAbelian 2 B) (g : G) :
    IsElemAbelian 2 (conjSub g B) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have ha := mem_conjSub_iff.mp a.2
    have hb := mem_conjSub_iff.mp b.2
    have h := DeltaClosure.comm_of_mem_elemAbelian hB ha hb
    calc (a : G) * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = b * a := by group
  · have hx' := mem_conjSub_iff.mp hx
    have h : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by rw [← pow_two]; exact hB.2 _ hx'
    rw [pow_two]
    calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h]; group

theorem hyp51_conj_mp {B : Subgroup G} (g : G) (h : Hyp51 B) : Hyp51 (conjSub g B) := by
  obtain ⟨hB, hcard, hall⟩ := h
  refine ⟨isElemAbelian_conjSub hB g, ?_, fun c' hc' hc1 => ?_⟩
  · rw [show Nat.card (conjSub g B) = Nat.card B from
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  · have hc := mem_conjSub_iff.mp hc'
    have e : c' = g * (g⁻¹ * c' * g) * g⁻¹ := by group
    rw [e]
    refine (hyp51At_conj g _ B).mpr (hall _ hc fun h1 => hc1 ?_)
    rw [e, h1]
    group

theorem hyp51_conj (g : G) (B : Subgroup G) : Hyp51 (conjSub g B) ↔ Hyp51 B := by
  refine ⟨fun h => ?_, hyp51_conj_mp g⟩
  have h1 := hyp51_conj_mp g⁻¹ h
  rwa [conjSub_inv_conjSub] at h1

theorem hyp51_of_orbitReps {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcard : Nat.card B = 8)
    {R : Set G} (hR : ∀ r ∈ R, Hyp51At B r)
    (hcover : ∀ c ∈ B, c ≠ 1 →
      ∃ r ∈ R, ∃ g ∈ Subgroup.normalizer (B : Set G), c = g * r * g⁻¹) : Hyp51 B := by
  refine ⟨hB, hcard, fun c hc hc1 => ?_⟩
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover c hc hc1
  exact hyp51At_of_normalizes hg (hR r hr)

end Hyp51

end CFSG.ClassicalInvolution.Asc77.ExactLayer
