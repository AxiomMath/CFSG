module

public import CFSG.Fischer.Classification.PartIII.R3.StarChart
public import CFSG.Fischer.Classification.Basic.Local

public section

namespace CFSG.Fischer.Classification.LocalR3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification F3

variable {G : Type} [Group G] {D : Set G} {m : ℕ}
  {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem isChart_of_localQuotient (hP : Pair G D) {e : G}
    (hi : Function.Injective (starImage D e)) (φ : LocalQuotient D e ≃* R3 f)
    (hφ : φ '' LocalImages D e = D3 f) : IsChart (φ ∘ lqMap D e) (LocalClass D e) (D3 f) := by
  have h2 := isChart_mulEquiv φ (LocalImages D e)
  rw [hφ] at h2
  exact (Pair.isChart_lqMap hP hi).comp h2

theorem exists_localQuotient_equiv_of_mem (hP : Pair G D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f) :
    ∃ φ' : LocalQuotient D e ≃* R3 f, φ' '' LocalImages D e = D3 f := by
  obtain ⟨ψ, hψD, hψe⟩ := Pair.exists_mulEquiv hP he hd
  refine ⟨(localQuotientCongr ψ hψD hψe).trans φ, ?_⟩
  rw [MulEquiv.coe_trans, Set.image_comp, localQuotientCongr_image, hφ]

theorem localClass_localClass_comm (d f₀ : G) :
    LocalClass (LocalClass D d) f₀ = LocalClass (LocalClass D f₀) d := by
  ext s
  simp only [mem_localClass]
  tauto

theorem mem_localClass_symm {d f₀ : G} (hd : d ∈ D) (h : f₀ ∈ LocalClass D d) :
    d ∈ LocalClass D f₀ :=
  ⟨hd, h.2.1.symm, h.2.2.symm⟩

theorem image_muSet_eq_sPt (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) (hna : ∃ a b : commutator G, a * b ≠ b * a) {d : G}
    (hd : d ∈ D) (hf : IsF3Form f) (hm : 7 ≤ m) (φ : LocalQuotient D d ≃* R3 f)
    (hφ : φ '' LocalImages D d = D3 f) {x : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) :
    ∃ w z, f w w = 1 ∧ IsIsoPt f w z ∧
      φ '' (starImage D d '' {p | (p : G) ∈ muSet D d x}) = sPt f z := by
  have hm4 : 4 ≤ m := by omega
  set ι : G → R3 f := φ ∘ lqMap D d with hιdef
  have hι : IsChart ι (LocalClass D d) (D3 f) :=
    isChart_of_localQuotient hP (Pair.starImage_injective_of_simple hP hZ hS hd) φ hφ
  have hM : ι '' muSet D d x = φ '' (starImage D d '' {p | (p : G) ∈ muSet D d x}) := by
    rw [hιdef, Set.image_comp, lqMap_image (muSet_subset_localClass d x)]
  rw [← hM]
  refine (isAdm_iff_eq_sPt hf hm).1 ⟨⟨hι.image_subset (muSet_subset_localClass d x), ?_⟩, ?_⟩
  swap
  · obtain ⟨s, hs⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
    exact ⟨ι s, s, hs, rfl⟩
  rintro _ ⟨f₀, hf₀, rfl⟩
  have hf₀d : f₀ ∈ LocalClass D d := hf₀.1
  have hf₀D : f₀ ∈ D := hf₀d.1
  have hdf₀ : d ∈ LocalClass D f₀ := mem_localClass_symm hd hf₀d
  have hxf₀ : x ∈ LocalClass D f₀ := mem_localClass_symm hx hf₀.2
  obtain ⟨w, hw, hwg⟩ := mem_D3_iff.1 (hι.mem hf₀d)
  obtain ⟨fw, Ψw, hfw, hΨw, -, hΨw2⟩ := exists_starChart hf (by omega) hw
  obtain ⟨φ₀, hφ₀⟩ := exists_localQuotient_equiv_of_mem hP hd hf₀D φ hφ
  set ι₀ : G → R3 f := φ₀ ∘ lqMap D f₀
  have hι₀ : IsChart ι₀ (LocalClass D f₀) (D3 f) :=
    isChart_of_localQuotient hP (Pair.starImage_injective_of_simple hP hZ hS hf₀D) φ₀ hφ₀
  obtain ⟨a, ha, hag⟩ := mem_D3_iff.1 (hι₀.mem hdf₀)
  obtain ⟨b, hb, hbg⟩ := mem_D3_iff.1 (hι₀.mem hxf₀)
  obtain ⟨fa, Ψa, hfa, hΨa, hΨa1, -⟩ := exists_starChart hf (by omega) ha
  set A := LocalClass (LocalClass D d) f₀ with hAdef
  have hα : IsChart (Ψw ∘ ι) A (D3 fw) := by
    have h := hι.localClass hf₀d
    rw [← hwg] at h
    exact h.comp hΨw
  have hα' : IsChart (Ψa ∘ ι₀) A (D3 fa) := by
    have h := hι₀.localClass hdf₀
    rw [← hag, ← localClass_localClass_comm] at h
    exact h.comp hΨa
  set B := A ∩ LocalClass D x with hBdef
  have hBA : B ⊆ A := Set.inter_subset_left
  have hB : B = muSet (LocalClass D f₀) d x := by
    ext s
    simp only [hBdef, hAdef, muSet, mem_localClass, Set.mem_inter_iff]
    tauto
  have hba : reflBar f b * reflBar f a ≠ reflBar f a * reflBar f b := by
    rw [hag, hbg]
    exact fun h => hxd ((hι₀.comm_iff x hxf₀ d hdf₀).2 h)
  obtain ⟨z', hz', hz'μ⟩ : ∃ z', IsIsoPt f a z' ∧
      muPt f a z' = muSet (D3 f) (reflBar f a) (reflBar f b) := by
    have hfam : muSet (D3 f) (reflBar f a) (reflBar f b) ∈ muFamily (D3 f) (reflBar f a) :=
      ⟨_, reflBar_mem_D3 hb, hba, rfl⟩
    rw [muFamily_D3 hf hm4 ha] at hfam
    exact hfam
  obtain ⟨z'', hz''0, hz'', hΨz''⟩ := hΨa1 z' hz'
  have hα'B : (Ψa ∘ ι₀) '' B = sPt fa z'' := by
    rw [Set.image_comp, hB, hι₀.image_muSet hdf₀ hxf₀, ← hag, ← hbg, ← hz'μ, hΨz'']
  have hne : (sPt fa z'').Nonempty := by
    rw [← hΨz'']
    obtain ⟨t, htt, hta, htz⟩ :=
      exists_norm_one_perp_isotropic hf (by omega) ha hz'.1 hz'.2.1 hz'.2.2
    exact ⟨_, _, ⟨t, htt, hta, htz, rfl⟩, rfl⟩
  obtain ⟨z₁, hz₁0, hz₁, hαB⟩ :=
    eq_sPt_of_isChart hfw hfa (by omega) (by omega) hBA hα hα' hz''0 hz'' hα'B hne
  obtain ⟨ζ, hζ, hΨζ⟩ := hΨw2 z₁ hz₁0 hz₁
  have hιB : ι '' B = muPt f w ζ := by
    have hsub1 : ι '' B ⊆ LocalClass (D3 f) (reflBar f w) := by
      rw [hwg, ← hι.image_localClass hf₀d]
      exact Set.image_mono hBA
    refine (hΨw.image_eq_image_iff hsub1 (muPt_subset_localClass hf hm4 hw ζ)).1 ?_
    rw [← Set.image_comp, hαB, hΨζ]
  have hwζ : f w ζ = 0 := by rw [hf.symm]; exact hζ.2.2
  have hu : f (w + ζ) (w + ζ) = 1 := by rw [norm_add hf, hw, hwζ, hζ.2.1]; ring
  refine ⟨reflBar f (w + ζ), reflBar_mem_D3 hu, ?_, ?_⟩
  · rw [← hwg]
    exact reflBar_add_not_commute hf hm4 hw hζ
  · rw [← hwg, muSet_eq_muPt hf hm4 hw hu, add_sub_cancel_left, ← hιB, hwg,
      ← hι.image_localClass hf₀d,
      ← hι.image_inter (muSet_subset_localClass d x) (localClass_subset _ _)]
    congr 1
    ext s
    simp only [hBdef, hAdef, muSet, mem_localClass, Set.mem_inter_iff]
    tauto

end CFSG.Fischer.Classification.LocalR3
