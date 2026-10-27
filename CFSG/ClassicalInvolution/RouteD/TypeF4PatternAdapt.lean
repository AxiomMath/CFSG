module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternModel
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternMain
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternB

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane longBlock shortBlock)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Normal

variable {Ω : Set (Subgroup G)} {z : G}

theorem range_normal_of_dict (d : ShapeCDict p f 3 Ω z) : d.ψ.range.Normal := by
  classical
  have hmem : ∀ L ∈ centralizingMembers Ω {z},
      locImg Ω z L ≤ Subgroup.normalizer (d.ψ.range : Set (locQuot Ω z)) := by
    intro L hL
    have hLfam : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
    rcases d.fam_cases _ hLfam with h | ⟨P, hP, hPL⟩
    · intro q hq
      apply Subgroup.centralizer_le_normalizer (d.ψ.range : Set (locQuot Ω z))
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (d.commutes q (h hq) c hc).symm
    · rw [hPL]
      exact (Subgroup.map_le_range _ _).trans Subgroup.le_normalizer
  have hlayer : locImg Ω z (locLayer Ω z) = ⊤ := by
    unfold locImg
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have h1 : locLayer Ω z = ⨆ L : ↥(centralizingMembers Ω {z}), (L : Subgroup G) := by
    simp only [locLayer, centralizingLayer, iSup_subtype']
  have hsup : locImg Ω z (locLayer Ω z) =
      ⨆ L : ↥(centralizingMembers Ω {z}), locImg Ω z (L : Subgroup G) :=
    (congrArg (locImg Ω z) h1).trans (locImg_iSup _ (fun L => le_centralizingLayer L.2))
  have hle : (⊤ : Subgroup (locQuot Ω z)) ≤
      Subgroup.normalizer (d.ψ.range : Set (locQuot Ω z)) := by
    rw [← hlayer, hsup]
    exact iSup_le fun L => hmem L L.2
  exact ⟨fun c hc g => ((Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_top g))) c).mp hc⟩

end Normal

section Adapt

variable {Ω : Set (Subgroup G)} {z : G}

theorem conjSub_mem_centralizingMembers_layer (hΩ : ConjInvariant Ω) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (y : ↥(locLayer Ω z)) :
    conjSub (y : G) L ∈ centralizingMembers Ω {z} := by
  have hyz : (y : G) * z * (y : G)⁻¹ = z := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} y.2)
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  have := centralizingMembers_conj hΩ (y : G) z
  rw [hyz] at this
  rw [this]
  exact ⟨L, hL, rfl⟩

theorem locImg_conjSub_dict (d : ShapeCDict p f 3 Ω z) {L : Subgroup G}
    {H : Subgroup (StatedSp 3 (GaloisField p f))} (hL : locImg Ω z L = H.map d.ψ)
    (y : ↥(locLayer Ω z)) {g : StatedSp 3 (GaloisField p f)} (hy : locMk Ω z y = d.ψ g) :
    locImg Ω z (conjSub (y : G) L) = (H.map (MulAut.conj g).toMonoidHom).map d.ψ := by
  rw [locImg_conjSub_layer, hL, hy, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h
  simp [MulAut.conj_apply]

end Adapt

section Main

variable [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem adaptedF4_of_partner (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z) {j : Fin 3 → Subgroup G}
    (hj0 : j 0 ∈ centralizingMembers Ω {z})
    (himg0 : locImg Ω z (j 0) =
      (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ)
    (himg1 : locImg Ω z (j 1) =
      (shortBlock (GaloisField p f) (by decide : (1 : Fin 3) ≠ 2)).range.map d.ψ)
    (himg2 : locImg Ω z (j 2) =
      (shortBlock (GaloisField p f) (by decide : (0 : Fin 3) ≠ 1)).range.map d.ψ)
    {N : Subgroup G} {t : G} (ht : IsClassicalMember p f N t)
    (hNj : ∃ W, LinearBlockStandardPair (GaloisField p f) W N (j 0))
    (htz : t * z * t⁻¹ = z) : AdaptedF4 hΩ j htz := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  have hodd : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two] at this
  have hτ : ∀ y, Gaps.locAut hΩ.conjInvariant htz (Gaps.locAut hΩ.conjInvariant htz y) = y :=
    Gaps.locAut_locAut hΩ.conjInvariant htz ht2
  have hnorm := range_normal_of_dict d
  obtain ⟨θ, hθr, hθτ⟩ := exists_chart_of_standardPair hp2 hΩ.conjInvariant ht
    (le_centralizingLayer hj0) htz hNj
  have hθ : θ.range = (longBlock (GaloisField p f) 3 2).range.map d.ψ := by
    rw [hθr, himg0]
    exact congrArg (fun H => H.map d.ψ) (Models.SymplecticPairs.planeGroup_stdPlane (2 : Fin 3))
  obtain ⟨g, hg1, hg2, hg3⟩ := SpAdapt.exists_fixed_shortRoots hodd h5 d.ψ d.ker_le hnorm
    (Gaps.locAut hΩ.conjInvariant htz) hτ θ hθ hθτ
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (d.ψ g)
  have hy' : locMk Ω z y = d.ψ g := hy
  refine ⟨(y : G), y.2, ?_, ?_, ?_⟩
  ·
    refine locImg_injOn hΩ hP1 (conjSub_mem_centralizingMembers_layer hΩ.conjInvariant hj0 y)
      hj0 ?_
    rw [locImg_conjSub_dict d himg0 y hy', himg0]
    congr 1
    have hL : planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2)) =
        (longBlock (GaloisField p f) 3 2).range := Models.SymplecticPairs.planeGroup_stdPlane 2
    rw [hL]
    exact hg1
  · intro x hx
    rw [locImg_conjSub_dict d himg1 y hy'] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    exact hg2 x₀ hx₀
  · intro x hx
    rw [locImg_conjSub_dict d himg2 y hy'] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    exact hg3 x₀ hx₀

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
