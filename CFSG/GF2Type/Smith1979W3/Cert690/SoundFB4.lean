module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

theorem mapsInto_iff {g : ℕ} {L : List ℕ} :
    mapsInto g L = true ↔ ∀ n ∈ L, Code.act g n ∈ L := by
  simp only [mapsInto, List.all_eq_true, List.contains_iff_mem]

theorem mapsIntoList_iff {g : ℕ} {L M : List ℕ} :
    mapsIntoList g L M = true ↔ ∀ n ∈ L, Code.act g n ∈ M := by
  simp only [mapsIntoList, List.all_eq_true, List.contains_iff_mem]

theorem pglF6Of_facts {D : PGLData} (h : pglF6Of D = true) :
    ∀ g ∈ kPGL0Gens, mapsInto g vPlusVecs = true ∧ mapsInto g vStarVecs = true := by
  simpa only [pglF6Of, List.all_eq_true, Bool.and_eq_true] using h

theorem pglF7Of_facts {D : PGLData} (h : pglF7Of D = true) :
    ∀ k ∈ D.elems.toList, k ∈ D.elems0.toList ∨
      (mapsIntoList k vPlusVecs vStarVecs = true ∧
        mapsIntoList k vStarVecs vPlusVecs = true) := by
  simp only [pglF7Of, Array.all_eq_true, Bool.and_eq_true] at h
  intro k hk
  rw [Array.mem_toList_iff] at hk
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hk
  have hk' := h i hi
  by_cases hc : D.elems0.contains D.elems[i] = true
  · left
    exact Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hc)
  · right
    rw [if_neg hc] at hk'
    exact Bool.and_eq_true_iff.mp hk'

theorem map_spanOfList_le_of_mapsInto {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} {S : List ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c)
    (hmap : ∀ n ∈ S, Code.act c n ∈ S) :
    (spanOfList S).map (g : V₀ →ₗ[ZMod 2] V₀) ≤ spanOfList S := by
  simp only [spanOfList]
  rw [Submodule.map_span, Submodule.span_le]
  rintro v ⟨w, hw, rfl⟩
  rcases hw with ⟨n, hn, rfl⟩
  rw [show (g : V₀ →ₗ[ZMod 2] V₀) (Code.vec n) = Code.vec (Code.act c n) from
    apply_vec_of_hasCode hg n]
  exact Submodule.subset_span ⟨Code.act c n, hmap n hn, rfl⟩

theorem map_spanOfList_eq_of_mapsInto {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} {S : List ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c)
    (hmap : ∀ n ∈ S, Code.act c n ∈ S) :
    (spanOfList S).map (g : V₀ →ₗ[ZMod 2] V₀) = spanOfList S := by
  refine Submodule.eq_of_le_of_finrank_eq (map_spanOfList_le_of_mapsInto hg hmap) ?_
  exact LinearEquiv.finrank_map_eq g (spanOfList S)

theorem map_VPlus_eq_of_mapsInto {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c)
    (hmap : ∀ n ∈ vPlusVecs, Code.act c n ∈ vPlusVecs) :
    VPlus.map (g : V₀ →ₗ[ZMod 2] V₀) = VPlus := by
  rw [← spanOfList_vPlus]
  exact map_spanOfList_eq_of_mapsInto hg hmap

theorem map_VStar_eq_of_mapsInto {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c)
    (hmap : ∀ n ∈ vStarVecs, Code.act c n ∈ vStarVecs) :
    VStar.map (g : V₀ →ₗ[ZMod 2] V₀) = VStar := by
  rw [← spanOfList_vStar]
  exact map_spanOfList_eq_of_mapsInto hg hmap

theorem map_VPlus_le_VStar_of_mapsInto {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c)
    (hmap : ∀ n ∈ vPlusVecs, Code.act c n ∈ vStarVecs) :
    VPlus.map (g : V₀ →ₗ[ZMod 2] V₀) ≤ VStar := by
  rw [← spanOfList_vPlus, ← spanOfList_vStar]
  simp only [spanOfList]
  rw [Submodule.map_span, Submodule.span_le]
  rintro v ⟨w, hw, rfl⟩
  rcases hw with ⟨n, hn, rfl⟩
  rw [show (g : V₀ →ₗ[ZMod 2] V₀) (Code.vec n) = Code.vec (Code.act c n) from
    apply_vec_of_hasCode hg n]
  exact Submodule.subset_span ⟨Code.act c n, hmap n hn, rfl⟩

theorem map_VStar_le_VPlus_of_mapsInto {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c)
    (hmap : ∀ n ∈ vStarVecs, Code.act c n ∈ vPlusVecs) :
    VStar.map (g : V₀ →ₗ[ZMod 2] V₀) ≤ VPlus := by
  rw [← spanOfList_vStar, ← spanOfList_vPlus]
  simp only [spanOfList]
  rw [Submodule.map_span, Submodule.span_le]
  rintro v ⟨w, hw, rfl⟩
  rcases hw with ⟨n, hn, rfl⟩
  rw [show (g : V₀ →ₗ[ZMod 2] V₀) (Code.vec n) = Code.vec (Code.act c n) from
    apply_vec_of_hasCode hg n]
  exact Submodule.subset_span ⟨Code.act c n, hmap n hn, rfl⟩

theorem KPGL0_preserves {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    (h5 : pglF5Of D = true) (h6 : pglF6Of D = true) :
    ∀ g ∈ KPGL0, VPlus.map (g : V₀ →ₗ[ZMod 2] V₀) = VPlus ∧
      VStar.map (g : V₀ →ₗ[ZMod 2] V₀) = VStar := by
  intro g hg
  change g ∈ codeSubgroup kPGL0Gens at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨m, hm, hgm⟩ := hg
    have hmaps := pglF6Of_facts h6 m hm
    exact ⟨map_VPlus_eq_of_mapsInto hgm (mapsInto_iff.mp hmaps.1),
      map_VStar_eq_of_mapsInto hgm (mapsInto_iff.mp hmaps.2)⟩
  | one => constructor <;> simp
  | mul x y _ _ hx hy =>
    exact ⟨by rw [Code.coe_mul, Submodule.map_comp, hy.1, hx.1],
      by rw [Code.coe_mul, Submodule.map_comp, hy.2, hx.2]⟩
  | inv x _ hx =>
    have hid : ((x⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) ∘ₗ
        (x : V₀ →ₗ[ZMod 2] V₀) = LinearMap.id := by
      have h := Code.coe_mul x⁻¹ x
      rw [inv_mul_cancel] at h
      simpa using h.symm
    constructor
    · have hcomp := Submodule.map_comp (x : V₀ →ₗ[ZMod 2] V₀)
        ((x⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) VPlus
      rw [hid, Submodule.map_id, hx.1] at hcomp
      exact hcomp.symm
    · have hcomp := Submodule.map_comp (x : V₀ →ₗ[ZMod 2] V₀)
        ((x⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) VStar
      rw [hid, Submodule.map_id, hx.2] at hcomp
      exact hcomp.symm

theorem map_VPlus_eq_VStar_of_not_mem {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    (hK0 : EnumCert kPGL0Gens D.elems0.toList) (h5 : pglF5Of D = true)
    (h7 : pglF7Of D = true) {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ KPGL) (hg0 : g ∉ KPGL0) :
    VPlus.map (g : V₀ →ₗ[ZMod 2] V₀) = VStar := by
  have hcode : hK.code g ∈ D.elems.toList := hK.code_mem hg
  have hnot : hK.code g ∉ D.elems0.toList := by
    intro hc
    exact hg0 (mem_KPGL0_iff_of_enum hK0 (hK.hasCode_code hg) (hK.lt _ hcode) |>.2
      (Array.mem_toList_iff.mp hc))
  have h7' := pglF7Of_facts h7 (hK.code g) hcode
  rcases h7' with hc | ⟨hplus, hstar⟩
  · exact absurd hc hnot
  · refine Submodule.eq_of_le_of_finrank_eq
      (map_VPlus_le_VStar_of_mapsInto (hK.hasCode_code hg) (mapsIntoList_iff.mp hplus)) ?_
    rw [LinearEquiv.finrank_map_eq, finrank_VPlus h5, finrank_VStar h5]

theorem map_VStar_eq_VPlus_of_not_mem {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    (hK0 : EnumCert kPGL0Gens D.elems0.toList) (h5 : pglF5Of D = true)
    (h7 : pglF7Of D = true) {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ KPGL) (hg0 : g ∉ KPGL0) :
    VStar.map (g : V₀ →ₗ[ZMod 2] V₀) = VPlus := by
  have hcode : hK.code g ∈ D.elems.toList := hK.code_mem hg
  have hnot : hK.code g ∉ D.elems0.toList := by
    intro hc
    exact hg0 (mem_KPGL0_iff_of_enum hK0 (hK.hasCode_code hg) (hK.lt _ hcode) |>.2
      (Array.mem_toList_iff.mp hc))
  have h7' := pglF7Of_facts h7 (hK.code g) hcode
  rcases h7' with hc | ⟨hplus, hstar⟩
  · exact absurd hc hnot
  · refine Submodule.eq_of_le_of_finrank_eq
      (map_VStar_le_VPlus_of_mapsInto (hK.hasCode_code hg) (mapsIntoList_iff.mp hstar)) ?_
    rw [LinearEquiv.finrank_map_eq, finrank_VStar h5, finrank_VPlus h5]

end CFSG.GF2Type.Smith1979W3.Cert690
