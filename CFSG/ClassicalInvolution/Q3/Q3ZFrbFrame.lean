module

public import CFSG.ClassicalInvolution.Q3.Q3ZFrbInj
public import CFSG.ClassicalInvolution.Q3.Q3ZFraRel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane form
  isHyperbolicPlane_stdPlane)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_frame_of_core (c : CCore3 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ fr : C3Frame G Ω, fr.K₀ = K := by
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
    comm₁₂ := ?_ }, rfl⟩
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

theorem exists_frame (hΩ : Q3.InClass3 Ω) (hex : Q3.ExactMembers3 Ω) (hK : K ∈ Ω)
    (hz : Q3.IsClassicalMember3 K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : Q3W.LocalOddThreeFree3 Ω z) (d : ShapeCDict3 Ω z) :
    ∃ fr : C3Frame G Ω, fr.K₀ = K :=
  exists_frame_of_core ⟨hΩ, hex, hK, hz, hP1, hO3, d⟩ hsingle

end Frame

section Chain


@[expose] def C3ChainInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), Q3W.RouteD3Setup K z →
      Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z →
      Q3W.LocalOddThreeFree3 (conjClass3 K) z →
      ∃ U : Fin 3 → Subgroup G, U 2 ∈ conjClass3 K ∧ (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
        (∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1)) ∧
        (∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
          (U 1))

theorem exists_frame_of_setup {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) :
    ∃ fr : C3Frame G (conjClass3 K), fr.K₀ = K := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_cdict hR.inClass hK hR.cls hshape
  exact exists_frame hR.inClass hR.setup.1 hK hR.cls
    (fun L ⟨g, hg⟩ => ⟨g, hg.symm⟩) hR.setup.2 hO3 d

theorem chain_exists_of_a2rel (h : C3A2Rel) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) :
    ∃ U : Fin 3 → Subgroup G, U 2 ∈ conjClass3 K ∧ (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1)) ∧
      (∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
        (U 1)) := by
  obtain ⟨fr, -⟩ := exists_frame_of_setup hR hshape hO3
  exact chain_of_c3A2Rel h hnab hR hshape hO3 fr

theorem c3ChainInput_of_a2rel (h : C3A2Rel) : C3ChainInput :=
  fun _ _ _ _ hnab _ _ hR hshape hO3 => chain_exists_of_a2rel h hnab hR hshape hO3

end Chain

end CFSG.ClassicalInvolution.Q3.Q3Z
