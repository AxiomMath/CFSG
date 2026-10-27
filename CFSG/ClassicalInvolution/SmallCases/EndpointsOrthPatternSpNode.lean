module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthLayerB
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpModel
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair longBlock shortBlock
  planeGroup IsHyperbolicPlane symplecticBlockStandardPair_conj
  exists_planeGroup_eq_conj_longBlock shortBlock_sup_longBlock_eq_top)
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

namespace SpLayer

variable {a : ℕ} (Λ : SpLayer p f a Ω x)

theorem exists_shortNode_of_conj [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (h01 : (0 : Fin 2) ≠ 1) (g : StatedSp 2 (GaloisField p f))
    (hMg : locImg Ω x M = ((longBlock (GaloisField p f) 2 1).range.map
      (MulAut.conj g).toMonoidHom).map Λ.ψ) :
    ∃ Us : Subgroup G, Λ.IsShortNode M Us ∧ locImg Ω x Us =
      ((shortBlock (GaloisField p f) h01).range.map (MulAut.conj g).toMonoidHom).map Λ.ψ := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  have hstd := symplecticBlockStandardPair_conj (K := GaloisField p f) (n := 2) h01 g
  have hpairX := symplecticBlockPair_map_central h5 hstd Λ.ψ Λ.ψ_ker
  set Rs : Subgroup (StatedSp 2 (GaloisField p f)) :=
    (shortBlock (GaloisField p f) h01).range.map (MulAut.conj g).toMonoidHom with hRs
  have hSperf : Rs.map Λ.ψ ≤ ⁅Rs.map Λ.ψ, Rs.map Λ.ψ⁆ :=
    (symplecticBlockPair_perfect h4 hpairX).2
  obtain ⟨A, hAperf, hAmap⟩ := exists_perfect_lift hP1 hSperf
  set Yl : Subgroup G := locLayer Ω x with hYl
  let Us : Subgroup G := A.map Yl.subtype
  have hUsimg : locImg Ω x Us = Rs.map Λ.ψ := by
    show locImg Ω x (A.map Yl.subtype) = _
    rw [locImg_map_subtype, hAmap]
  have hUsY : Us ≤ Yl := Subgroup.map_subtype_le _
  have hUsperf : Us ≤ ⁅Us, Us⁆ := by
    show A.map Yl.subtype ≤ ⁅A.map Yl.subtype, A.map Yl.subtype⁆
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAperf
  have hMY : M ≤ Yl := le_centralizingLayer hM
  have hMperf : M ≤ ⁅M, M⁆ := by
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact (commutator_eq_of_isClassicalMember hz).ge
  have hUsrange : locImg Ω x Us ≤ (Λ.D.hom Λ.i₁).range := by
    rw [hUsimg, ← Λ.ψ_range]
    exact Subgroup.map_le_range _ _
  have hsup : (longBlock (GaloisField p f) 2 1).range.map (MulAut.conj g).toMonoidHom ⊔ Rs = ⊤ := by
    rw [hRs, ← Subgroup.map_sup, sup_comm, shortBlock_sup_longBlock_eq_top, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  obtain ⟨W, hW⟩ : ∃ W, SymplecticBlockPair (GaloisField p f) W (locImg Ω x M)
      (locImg Ω x Us) := ⟨_, by rw [hMg, hUsimg]; exact hpairX⟩
  refine ⟨Us, ⟨hUsY, le_antisymm (commutator_self_le _) hUsperf, hUsrange, ?_, ?_, ?_⟩, hUsimg⟩
  · exact symplecticBlockPair_of_locImg_perfect hp2 hq hP1 hMY hUsY hMperf hUsperf hW
  · intro N hN j hj hNj
    have hNY : N ≤ Yl := le_centralizingLayer hN
    have hNperf : N ≤ ⁅N, N⁆ := by
      obtain ⟨z, hz⟩ := hΩ.classical N hN.1
      exact (commutator_eq_of_isClassicalMember hz).ge
    refine commutes_of_commutes_locImg_perfect hP1 hNY hUsY hNperf ?_
    intro u hu w hw
    exact range_commute_of_ne Λ.D hj u (hNj hu) w (hUsrange hw)
  · rw [hMg, hUsimg, ← Subgroup.map_sup, hsup, Subgroup.map_top, Λ.ψ_range]

theorem range_normal : ((Λ.D.hom Λ.i₁).range).Normal := by
  refine ⟨fun c hc g => ?_⟩
  have hg : g ∈ ⨆ i, (Λ.D.hom i).range := by rw [Λ.D.generate]; trivial
  refine Subgroup.iSup_induction (fun i => (Λ.D.hom i).range)
    (C := fun g => ∀ c ∈ (Λ.D.hom Λ.i₁).range, g * c * g⁻¹ ∈ (Λ.D.hom Λ.i₁).range) hg ?_ ?_ ?_ c hc
  · intro i y hy c hc
    by_cases hi : i = Λ.i₁
    · subst hi
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hc) (Subgroup.inv_mem _ hy)
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hc
      rw [Λ.D.commute i Λ.i₁ hi u v, mul_inv_cancel_right]
      exact ⟨v, rfl⟩
  · intro c hc
    simpa using hc
  · intro y z hy hz c hc
    have := hy _ (hz c hc)
    simpa [mul_assoc] using this

theorem exists_shortNode_centralizer [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x}) {t : G} (ht : t * x * t⁻¹ = x)
    (ht2 : t * t = 1) {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range)
    (θ : SL(2, GaloisField p f) →* locQuot Ω x) (hθ : θ.range = locImg Ω x M)
    (hθτ : ∀ s, Gaps.locAut hΩ.conjInvariant ht (θ s) = θ (diagConj2 (-1) 1 s)) :
    ∃ Us : Subgroup G, Λ.IsShortNode M Us ∧ Us ≤ Subgroup.centralizer ({t} : Set G) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  have hodd : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  set τ := Gaps.locAut hΩ.conjInvariant ht with hτdef
  have hτ : ∀ y, τ (τ y) = y := Gaps.locAut_locAut hΩ.conjInvariant ht ht2
  obtain ⟨P, hP, hMP⟩ := Λ.exists_plane_of_mem hΩ hP1 hM hMi
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (1 : Fin 2)
  let ψ' : StatedSp 2 (GaloisField p f) →* locQuot Ω x := Λ.ψ.comp (MulAut.conj g).toMonoidHom
  have hker' : ψ'.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p f)) := by
    intro y hy
    have h1 : (MulAut.conj g).toMonoidHom y ∈ Subgroup.center (StatedSp 2 (GaloisField p f)) :=
      Λ.ψ_ker hy
    have h2 := (inferInstance : (Subgroup.center (StatedSp 2 (GaloisField p f))).Normal).conj_mem
      _ h1 g⁻¹
    have e : g⁻¹ * (MulAut.conj g).toMonoidHom y * g⁻¹⁻¹ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [e] at h2
  have hrange' : ψ'.range = Λ.ψ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective,
      Subgroup.map_top]
  have hnorm' : ψ'.range.Normal := by
    rw [hrange', Λ.ψ_range]
    exact Λ.range_normal
  have hθ' : θ.range = (longBlock (GaloisField p f) 2 1).range.map ψ' := by
    rw [hθ, hMP, hg, Subgroup.map_map]
  obtain ⟨g', hg'1, hg'2⟩ := SpToral.exists_fixed_shortRoot hodd h5 ψ' hker' hnorm' τ hτ θ hθ'
    hθτ h01
  have hMg : locImg Ω x M = ((longBlock (GaloisField p f) 2 1).range.map
      (MulAut.conj (g * g')).toMonoidHom).map Λ.ψ := by
    rw [hMP, hg]
    congr 1
    calc (longBlock (GaloisField p f) 2 1).range.map (MulAut.conj g).toMonoidHom
        = ((longBlock (GaloisField p f) 2 1).range.map (MulAut.conj g').toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by rw [hg'1]
      _ = (longBlock (GaloisField p f) 2 1).range.map (MulAut.conj (g * g')).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨Us, hsn, hUsimg⟩ := Λ.exists_shortNode_of_conj hp2 hq hΩ hP1 hM h01 (g * g') hMg
  refine ⟨Us, hsn, ?_⟩
  obtain ⟨hUsY, hUsperf, -⟩ := hsn
  refine (locAut_fixed_iff_of_perfect hΩ hP1 ht hUsY hUsperf.ge).2 ?_
  intro y hy
  rw [hUsimg] at hy
  obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := hy
  have hw : g' * s * g'⁻¹ ∈ (shortBlock (GaloisField p f) h01).range.map
      (MulAut.conj g').toMonoidHom := ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have h1 := hg'2 _ hw
  have e : (MulAut.conj (g * g')).toMonoidHom s = (MulAut.conj g).toMonoidHom (g' * s * g'⁻¹) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
  show τ (Λ.ψ ((MulAut.conj (g * g')).toMonoidHom s)) = Λ.ψ ((MulAut.conj (g * g')).toMonoidHom s)
  rw [e]
  exact h1

end SpLayer

end CFSG.ClassicalInvolution.RouteD
