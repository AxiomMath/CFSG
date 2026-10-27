module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm

theorem alt6_involutions_conj_perm :
    ∀ a : Perm (Fin 6), Perm.sign a = 1 → a * a = 1 → a ≠ 1 →
      ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * (swap 0 1 * swap 2 3) * g⁻¹ = a := by
  decide +kernel

theorem alt6_involutions_conj (a b : alternatingGroup (Fin 6)) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hb1 : b ≠ 1) (hb2 : b * b = 1) : ∃ g : alternatingGroup (Fin 6), g⁻¹ * a * g = b := by
  have key : ∀ c : alternatingGroup (Fin 6), c ≠ 1 → c * c = 1 →
      ∃ g : alternatingGroup (Fin 6), g * (⟨swap 0 1 * swap 2 3, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : alternatingGroup (Fin 6)) * g⁻¹ = c := by
    intro c hc1 hc2
    have h1 : (c : Perm (Fin 6)) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have h2 : (c : Perm (Fin 6)) * (c : Perm (Fin 6)) = 1 := by
      have := congrArg Subtype.val hc2
      simpa using this
    obtain ⟨g, hg, hgc⟩ := alt6_involutions_conj_perm c (Equiv.Perm.mem_alternatingGroup.mp c.2) h2 h1
    exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩, Subtype.ext (by simpa using hgc)⟩
  obtain ⟨g₁, h₁⟩ := key a ha1 ha2
  obtain ⟨g₂, h₂⟩ := key b hb1 hb2
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  calc (g₁ * g₂⁻¹)⁻¹ * a * (g₁ * g₂⁻¹) = g₂ * (g₁⁻¹ * a * g₁) * g₂⁻¹ := by group
    _ = g₂ * (⟨swap 0 1 * swap 2 3, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : alternatingGroup (Fin 6)) * g₂⁻¹ := by
        rw [← h₁]; group
    _ = b := h₂

theorem card_involutions_dihedral_four :
    (Finset.univ.filter fun d : DihedralGroup 4 => d * d = 1 ∧ d ≠ 1).card = 5 := by
  decide

section Count

variable {G : Type*} [Group G]

theorem ncard_conjClass_inf_eq_five {K RK : Subgroup G} {z₁ z₂ s : G}
    (e : ↥K ≃* alternatingGroup (Fin 6)) (hRK : RK ≤ K) (f : ↥RK ≃* DihedralGroup 4)
    (hz₁K : z₁ ∈ K) (hz₁1 : z₁ ≠ 1) (hz₁2 : z₁ * z₁ = 1) (hz₂ : z₂ = s⁻¹ * z₁ * s) :
    {y | y ∈ conjClass z₂ ∧ y ∈ RK}.ncard = 5 := by
  have hz₂2 : z₂ * z₂ = 1 := by
    rw [hz₂]
    calc s⁻¹ * z₁ * s * (s⁻¹ * z₁ * s) = s⁻¹ * (z₁ * z₁) * s := by group
      _ = 1 := by rw [hz₁2]; group
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    apply hz₁1
    have : z₁ = s * z₂ * s⁻¹ := by rw [hz₂]; group
    rw [this, h]; group
  have hconj : ∀ y ∈ RK, y * y = 1 → y ≠ 1 → y ∈ conjClass z₂ := by
    intro y hy hy2 hy1
    let a : alternatingGroup (Fin 6) := e ⟨y, hRK hy⟩
    let b : alternatingGroup (Fin 6) := e ⟨z₁, hz₁K⟩
    have ha1 : a ≠ 1 := by
      intro h
      have : (⟨y, hRK hy⟩ : K) = 1 := e.injective (by simpa [a] using h)
      exact hy1 (congrArg Subtype.val this)
    have ha2 : a * a = 1 := by
      have : (⟨y, hRK hy⟩ : K) * ⟨y, hRK hy⟩ = 1 := Subtype.ext hy2
      show e ⟨y, hRK hy⟩ * e ⟨y, hRK hy⟩ = 1
      rw [← map_mul, this, map_one]
    have hb1 : b ≠ 1 := by
      intro h
      have : (⟨z₁, hz₁K⟩ : K) = 1 := e.injective (by simpa [b] using h)
      exact hz₁1 (congrArg Subtype.val this)
    have hb2 : b * b = 1 := by
      have : (⟨z₁, hz₁K⟩ : K) * ⟨z₁, hz₁K⟩ = 1 := Subtype.ext hz₁2
      show e ⟨z₁, hz₁K⟩ * e ⟨z₁, hz₁K⟩ = 1
      rw [← map_mul, this, map_one]
    obtain ⟨g, hg⟩ := alt6_involutions_conj b a hb1 hb2 ha1 ha2
    have hk : (e.symm g)⁻¹ * (⟨z₁, hz₁K⟩ : K) * e.symm g = ⟨y, hRK hy⟩ := by
      apply e.injective
      simpa [a, b] using hg
    have hk' : ((e.symm g : K) : G)⁻¹ * z₁ * (e.symm g : K) = y := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨s⁻¹ * (e.symm g : K), ?_⟩
    rw [← hk', hz₂]
    group
  have hI : {y | y ∈ conjClass z₂ ∧ y ∈ RK} =
      (fun d : DihedralGroup 4 => ((f.symm d : RK) : G)) '' {d | d * d = 1 ∧ d ≠ 1} := by
    ext y
    constructor
    · rintro ⟨⟨g, rfl⟩, hyR⟩
      refine ⟨f ⟨g⁻¹ * z₂ * g, hyR⟩, ⟨?_, ?_⟩, by simp⟩
      · rw [← map_mul]
        have : (⟨g⁻¹ * z₂ * g, hyR⟩ : RK) * ⟨g⁻¹ * z₂ * g, hyR⟩ = 1 := by
          apply Subtype.ext
          show g⁻¹ * z₂ * g * (g⁻¹ * z₂ * g) = 1
          calc g⁻¹ * z₂ * g * (g⁻¹ * z₂ * g) = g⁻¹ * (z₂ * z₂) * g := by group
            _ = 1 := by rw [hz₂2]; group
        rw [this, map_one]
      · intro h
        have : (⟨g⁻¹ * z₂ * g, hyR⟩ : RK) = 1 := f.injective (by simpa using h)
        apply hz₂1
        have h' := congrArg Subtype.val this
        have : z₂ = g * (g⁻¹ * z₂ * g) * g⁻¹ := by group
        rw [this]
        simpa using congrArg (fun t => g * t * g⁻¹) h'
    · rintro ⟨d, ⟨hd2, hd1⟩, rfl⟩
      have hyR : ((f.symm d : RK) : G) ∈ RK := (f.symm d).2
      refine ⟨hconj _ hyR ?_ ?_, hyR⟩
      · have : f.symm d * f.symm d = 1 := by rw [← map_mul, hd2, map_one]
        simpa using congrArg Subtype.val this
      · intro h
        apply hd1
        have : f.symm d = 1 := Subtype.ext (by simpa using h)
        simpa using congrArg f this
  have hinj : Function.Injective (fun d : DihedralGroup 4 => ((f.symm d : RK) : G)) :=
    fun a b hab => f.symm.injective (Subtype.ext hab)
  rw [hI, Set.ncard_image_of_injective _ hinj]
  have hJ : {d : DihedralGroup 4 | d * d = 1 ∧ d ≠ 1} =
      ↑(Finset.univ.filter fun d : DihedralGroup 4 => d * d = 1 ∧ d ≠ 1) := by
    ext d; simp
  rw [hJ, Set.ncard_coe_finset]
  exact card_involutions_dihedral_four

end Count

end CFSG.QuasithinUnique.DoubleA3
