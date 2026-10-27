module

public import CFSG.ClassicalInvolution.Q3.Q3ZASymFrame
public import CFSG.ClassicalInvolution.Q3.Q3ZASimil
public import CFSG.ClassicalInvolution.Q3.Q3ZAStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane form
  isHyperbolicPlane_stdPlane longBlock longBlock_injective planeGroup_stdPlane)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_frame_of_core' (c : CCore3 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ fr : C3Frame G Ω, fr.K₀ = K ∧ fr.K₁ ∈ Ω := by
  obtain ⟨l⟩ := c.nonempty_layer
  have hinj := l.injective hsingle
  obtain ⟨hK₁, -⟩ := l.plane _ (isHyperbolicPlane_stdPlane (K := GaloisField 3 1) (n := 2) 0)
  obtain ⟨hK₂, -⟩ := l.plane _ (isHyperbolicPlane_stdPlane (K := GaloisField 3 1) (n := 2) 1)
  set K₁ := (planeGroup (stdPlane (GaloisField 3 1) 2 0)).map l.Θ with hK₁def
  set K₂ := (planeGroup (stdPlane (GaloisField 3 1) 2 1)).map l.Θ with hK₂def
  have hcomm₁₂ : Commutes K₁ K₂ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, commutes_planeGroup_stdPlane x hx y hy]
  have hKK₁ : Commutes K K₁ := l.commutes_K_map _
  have hKK₂ : Commutes K K₂ := l.commutes_K_map _
  obtain ⟨g, hg⟩ := hsingle K₂ hK₂.1
  have hzg : g * z * g⁻¹ ∈ K₂ := hg ▸ conj_mem_conjSub c.hz.mem
  have hKmem : conjSub g⁻¹ K ∈ centralizingMembers Ω {z} :=
    conjSub_inv_mem_centralizingMembers c.hΩ.conjInvariant c.hK hzg hKK₂
  have hK₁mem : conjSub g⁻¹ K₁ ∈ centralizingMembers Ω {z} :=
    conjSub_inv_mem_centralizingMembers c.hΩ.conjInvariant hK₁.1 hzg hcomm₁₂
  have hKne : conjSub g⁻¹ K ≠ K := by
    intro h
    have : K = K₂ := by
      calc K = conjSub g (conjSub g⁻¹ K) := (conjSub_conjSub_inv g K).symm
        _ = conjSub g K := by rw [h]
        _ = K₂ := hg.symm
    exact ne_of_commutes_member c.hΩ c.hK hKK₂ this
  have hK₁ne : conjSub g⁻¹ K₁ ≠ K := by
    intro h
    have : K₁ = K₂ := by
      calc K₁ = conjSub g (conjSub g⁻¹ K₁) := (conjSub_conjSub_inv g K₁).symm
        _ = conjSub g K := by rw [h]
        _ = K₂ := hg.symm
    exact ne_of_commutes_member c.hΩ hK₁.1 hcomm₁₂ this
  obtain ⟨Pa, hPa, hLa⟩ := c.exists_plane_of_ne hKmem hKne
  obtain ⟨Pb, hPb, hLb⟩ := c.exists_plane_of_ne hK₁mem hK₁ne
  have hKa := l.eq_member hKmem hPa hLa
  have hKb := l.eq_member hK₁mem hPb hLb
  have horth : ∀ u ∈ Pa, ∀ v ∈ Pb, form u v = 0 := by
    refine (l.commutes_map_planeGroup_iff hinj hPa hPb).1 ?_
    rw [← hKa, ← hKb]
    exact (commutes_conjSub_iff g⁻¹).2 hKK₁
  obtain ⟨h, -, -, hh₀, hh₁⟩ := exists_hom_sp4_of_orth hPa hPb horth
  refine ⟨{
    K₀ := K
    K₁ := K₁
    K₂ := K₂
    Θ₀₁ := (MulAut.conj g).toMonoidHom.comp (l.Θ.comp (MulAut.conj h).toMonoidHom)
    Θ₁₂ := l.Θ
    inj₀₁ := (MulAut.conj g).injective.comp (hinj.comp (MulAut.conj h).injective)
    inj₁₂ := hinj
    hK₂ := hK₂.1
    blk₀₁₀ := ?_
    blk₀₁₁ := ?_
    blk₁₂₀ := rfl
    blk₁₂₁ := rfl
    comm₀₁ := ?_
    comm₁₂ := ?_ }, rfl, hK₁.1⟩
  · rw [← Subgroup.map_map, ← Subgroup.map_map, hh₀, ← hKa]
    exact conjSub_conjSub_inv g K
  · rw [← Subgroup.map_map, ← Subgroup.map_map, hh₁, ← hKb]
    exact conjSub_conjSub_inv g K₁
  · rintro _ ⟨s, rfl⟩ b hb
    have hk : g⁻¹ * b * g ∈ K := mem_conjSub_iff.1 (hg ▸ hb)
    have h1 := l.commutes_K (h * s * h⁻¹) hk
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * l.Θ (h * s * h⁻¹) * g⁻¹ * b
        = g * (l.Θ (h * s * h⁻¹) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * l.Θ (h * s * h⁻¹)) * g⁻¹ := by rw [h1]
      _ = b * (g * l.Θ (h * s * h⁻¹) * g⁻¹) := by group
  · rintro _ ⟨s, rfl⟩ b hb
    exact l.commutes_K s hb

end Frame

section Hub

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_discrepancy (fr : C3Frame G Ω) :
    ∃ α : MulAut SL(2, F3),
      ∀ x : SL(2, F3), fr.Θ₁₂ (longBlock F3 2 0 (α x)) = fr.Θ₀₁ (longBlock F3 2 1 x) := by
  have hf₁ : Function.Injective (fr.Θ₀₁.comp (longBlock F3 2 1)) :=
    fr.inj₀₁.comp (longBlock_injective 1)
  have hf₂ : Function.Injective (fr.Θ₁₂.comp (longBlock F3 2 0)) :=
    fr.inj₁₂.comp (longBlock_injective 0)
  have hr₁ : (fr.Θ₀₁.comp (longBlock F3 2 1)).range = fr.K₁ := by
    rw [← fr.blk₀₁₁, planeGroup_stdPlane]
    show (fr.Θ₀₁.comp (longBlock F3 2 1)).range = (longBlock F3 2 1).range.map fr.Θ₀₁
    rw [MonoidHom.map_range]
  have hr₂ : (fr.Θ₁₂.comp (longBlock F3 2 0)).range = fr.K₁ := by
    rw [← fr.blk₁₂₀, planeGroup_stdPlane]
    show (fr.Θ₁₂.comp (longBlock F3 2 0)).range = (longBlock F3 2 0).range.map fr.Θ₁₂
    rw [MonoidHom.map_range]
  let α : MulAut SL(2, F3) :=
    (MonoidHom.ofInjective hf₁).trans ((MulEquiv.subgroupCongr (hr₁.trans hr₂.symm)).trans
      (MonoidHom.ofInjective hf₂).symm)
  refine ⟨α, fun x => ?_⟩
  have h := MonoidHom.apply_ofInjective_symm hf₂
    (MulEquiv.subgroupCongr (hr₁.trans hr₂.symm) (MonoidHom.ofInjective hf₁ x))
  exact h

theorem exists_hubFrame (fr : C3Frame G Ω) :
    ∃ fr' : C3Frame G Ω, fr'.K₀ = fr.K₀ ∧ fr'.K₁ = fr.K₁ ∧
      ∀ x : SL(2, F3), fr'.Θ₁₂ (longBlock F3 2 0 x) = fr'.Θ₀₁ (longBlock F3 2 1 x) := by
  obtain ⟨α, hα⟩ := exists_discrepancy fr
  obtain ⟨Gl, hGl⟩ := Q3T6.Fa.sl2_aut_eq_conj_of_card_three Q3W.card_gf3 α
  obtain ⟨ν, hνbij, hν0, f, hfsurj, hν1⟩ := exists_aut_of_conj Gl
  have hν0α : ∀ x, ν (longBlock F3 2 0 x) = longBlock F3 2 0 (α x) := fun x =>
    hν0 x (α x) (congrArg Subtype.val (hGl x))
  have hmap0 : (planeGroup (stdPlane F3 2 0)).map ν = planeGroup (stdPlane F3 2 0) := by
    rw [planeGroup_stdPlane]
    show (longBlock F3 2 0).range.map ν = (longBlock F3 2 0).range
    ext w
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨α x, (hν0α x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := α.surjective y
      exact ⟨_, ⟨x, rfl⟩, hν0α x⟩
  have hmap1 : (planeGroup (stdPlane F3 2 1)).map ν = planeGroup (stdPlane F3 2 1) := by
    rw [planeGroup_stdPlane]
    show (longBlock F3 2 1).range.map ν = (longBlock F3 2 1).range
    ext w
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨f x, (hν1 x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hfsurj y
      exact ⟨_, ⟨x, rfl⟩, hν1 x⟩
  refine ⟨{ fr with
    Θ₁₂ := fr.Θ₁₂.comp ν
    inj₁₂ := fr.inj₁₂.comp hνbij.1
    blk₁₂₀ := by
      rw [← Subgroup.map_map, hmap0]
      exact fr.blk₁₂₀
    blk₁₂₁ := by
      rw [← Subgroup.map_map, hmap1]
      exact fr.blk₁₂₁
    comm₁₂ := by
      rintro _ ⟨s, rfl⟩ b hb
      exact fr.comm₁₂ _ ⟨ν s, rfl⟩ b hb }, rfl, rfl, fun x => ?_⟩
  show fr.Θ₁₂ (ν (longBlock F3 2 0 x)) = fr.Θ₀₁ (longBlock F3 2 1 x)
  rw [hν0α, hα]

end Hub

section Tri


theorem triangleExists :
    TriangleExists := by
  intro G _ _ _ K z hctx
  obtain ⟨-, hR, hshape, hO3⟩ := hctx
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_cdict hR.inClass hK hR.cls hshape
  obtain ⟨fr, hK₀, hK₁⟩ := exists_frame_of_core'
    ⟨hR.inClass, hR.setup.1, hK, hR.cls, hR.setup.2, hO3, d⟩ (fun L ⟨g, hg⟩ => ⟨g, hg.symm⟩)
  obtain ⟨fr', h₀, h₁, hhub⟩ := exists_hubFrame fr
  exact ⟨SymTri.ofFrame fr' (by rw [h₀, hK₀]; exact hK) (by rw [h₁]; exact hK₁) hhub⟩

end Tri

end CFSG.ClassicalInvolution.Q3.Q3ZA
