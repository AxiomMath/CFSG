module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter

private lemma sec5pef_isInvolution_of_orderOf_eq_two {G : Type*} [Group G] {y : G}
    (hy : orderOf y = 2) : BenderSuzuki.PFAppendixIII.IsInvolution y := by
  constructor
  · rintro rfl
    simp at hy
  · have h := pow_orderOf_eq_one y
    rwa [hy] at h

private lemma sec5pef_conj_data
    {K : Type*} [Field K] [Finite K]
    (U : Subgroup (PGL2 K)) (s w : PGL2 K) (hUc : IsCyclic U)
    (hwU : w ∉ U) (hw2 : w * w = 1)
    (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hcent : Subgroup.centralizer ({s} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w)
    {y : PGL2 K} {g : PGL2 K} (hg : g * s * g⁻¹ = y) :
    Nonempty (↥(Subgroup.centralizer ({y} : Set (PGL2 K))) ≃* DihedralGroup (Nat.card U)) ∧
    ∃ C : Subgroup (PGL2 K), C ≤ Subgroup.centralizer ({y} : Set (PGL2 K)) ∧ IsCyclic C ∧
      Nat.card C = Nat.card U ∧
      ∀ c ∈ C, Odd (orderOf c) →
        c ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  classical
  let _ : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  haveI : IsCyclic U := hUc
  have hCy : Subgroup.centralizer ({y} : Set (PGL2 K)) =
      (Subgroup.centralizer ({s} : Set (PGL2 K))).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact CFSG.Walter.centralizer_conj_eq_map g s
  have hUle : U ≤ Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    rw [hcent]
    exact le_sup_left
  have hequiv : Nonempty (↥(Subgroup.centralizer ({s} : Set (PGL2 K))) ≃*
      DihedralGroup (Nat.card U)) := by
    have h := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup U w hwU hw2 hinv
    rwa [← hcent] at h
  constructor
  · obtain ⟨e⟩ := hequiv
    let eMap : ↥(Subgroup.centralizer ({s} : Set (PGL2 K))) ≃*
        ↥((Subgroup.centralizer ({s} : Set (PGL2 K))).map
          (MulAut.conj g).toMonoidHom) :=
      (MulAut.conj g).subgroupMap _
    let eCongr : ↥(Subgroup.centralizer ({y} : Set (PGL2 K))) ≃*
        ↥((Subgroup.centralizer ({s} : Set (PGL2 K))).map
          (MulAut.conj g).toMonoidHom) :=
      MulEquiv.subgroupCongr hCy
    exact ⟨(eCongr.trans eMap.symm).trans e⟩
  · refine ⟨U.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rw [hCy]
      exact Subgroup.map_mono hUle
    · exact (MulEquiv.subgroupMap (MulAut.conj g) U).isCyclic.mp hUc
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    · intro c _ hcodd
      exact pgl2_mem_psl2Range_of_odd_orderOf hcodd

private lemma sec5pef_exists_conj_of_torus_data
    {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {s₁ s₂ : PGL2 K} (hI₁ : BenderSuzuki.PFAppendixIII.IsInvolution s₁)
    (hI₂ : BenderSuzuki.PFAppendixIII.IsInvolution s₂)
    (hnotconj : ¬ IsConj s₁ s₂) {y : PGL2 K}
    (hIy : BenderSuzuki.PFAppendixIII.IsInvolution y) :
    (∃ g : PGL2 K, g * s₁ * g⁻¹ = y) ∨ (∃ g : PGL2 K, g * s₂ * g⁻¹ = y) := by
  classical
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hnotboth_in : ¬ (s₁ ∈ J ∧ s₂ ∈ J) := by
    rintro ⟨h1, h2⟩
    obtain ⟨g, _, hg⟩ := pgl2_inner_involutions_conjugate hK hcard h1 hI₁ h2 hI₂
    exact hnotconj (isConj_iff.mpr ⟨g, hg⟩)
  have hnotboth_out : ¬ (s₁ ∉ J ∧ s₂ ∉ J) := by
    rintro ⟨h1, h2⟩
    exact hnotconj (pgl2_outer_involutions_conjugate K hK hcard hI₁ hI₂ h1 h2)
  have hcases : (s₁ ∈ J ∧ s₂ ∉ J) ∨ (s₁ ∉ J ∧ s₂ ∈ J) := by
    by_cases h1 : s₁ ∈ J <;> by_cases h2 : s₂ ∈ J
    · exact absurd ⟨h1, h2⟩ hnotboth_in
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd ⟨h1, h2⟩ hnotboth_out
  by_cases hyJ : y ∈ J
  · rcases hcases with ⟨h1, _⟩ | ⟨_, h2⟩
    · obtain ⟨g, _, hg⟩ :=
        pgl2_inner_involutions_conjugate hK hcard h1 hI₁ hyJ hIy
      exact Or.inl ⟨g, hg⟩
    · obtain ⟨g, _, hg⟩ :=
        pgl2_inner_involutions_conjugate hK hcard h2 hI₂ hyJ hIy
      exact Or.inr ⟨g, hg⟩
  · rcases hcases with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Or.inr (isConj_iff.mp (pgl2_outer_involutions_conjugate K hK hcard hI₂ hIy h2 hyJ))
    · exact Or.inl (isConj_iff.mp (pgl2_outer_involutions_conjugate K hK hcard hI₁ hIy h1 hyJ))

theorem sec5pef_pgl2_involution_centralizer
    {F : Type} [Field F] [Finite F] (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    {y : PGL2 F} (hy : orderOf y = 2) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∃ n : ℕ, (n : ℤ) = (Nat.card F : ℤ) - δ ∧
      Nonempty (↥(Subgroup.centralizer ({y} : Set (PGL2 F))) ≃* DihedralGroup n) ∧
      ∃ C : Subgroup (PGL2 F), C ≤ Subgroup.centralizer ({y} : Set (PGL2 F)) ∧ IsCyclic C ∧
        Nat.card C = n ∧
        ∀ c ∈ C, Odd (orderOf c) →
          c ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  classical
  let _ : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _hp, hpodd, _hn, hq⟩ := hK
    rw [hq]
    exact hpodd.pow
  obtain ⟨U₁, s₁, w₁, hU₁c, hU₁card, _hs₁U, hs₁2, hs₁1, hw₁U, hw₁2, hinv₁, hcent₁, _⟩ :=
    pgl2_split_torus_centralizer_data F hodd
  obtain ⟨U₂, s₂, w₂, hU₂c, hU₂card, _hs₂U, hs₂2, hs₂1, hw₂U, hw₂2, hinv₂, hcent₂, _⟩ :=
    pgl2_nonsplit_torus_centralizer_data F hodd
  have hI₁ : BenderSuzuki.PFAppendixIII.IsInvolution s₁ :=
    ⟨hs₁1, by simpa [pow_two] using hs₁2⟩
  have hI₂ : BenderSuzuki.PFAppendixIII.IsInvolution s₂ :=
    ⟨hs₂1, by simpa [pow_two] using hs₂2⟩
  have hcard₁ : Nat.card (Subgroup.centralizer ({s₁} : Set (PGL2 F))) =
      2 * (Nat.card F - 1) := by
    have h := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup U₁ w₁
      hw₁U hw₁2 hinv₁
    rw [← hcent₁] at h
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hU₁card]
  have hcard₂ : Nat.card (Subgroup.centralizer ({s₂} : Set (PGL2 F))) =
      2 * (Nat.card F + 1) := by
    have h := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup U₂ w₂
      hw₂U hw₂2 hinv₂
    rw [← hcent₂] at h
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hU₂card]
  have hne_card : Nat.card (Subgroup.centralizer ({s₁} : Set (PGL2 F))) ≠
      Nat.card (Subgroup.centralizer ({s₂} : Set (PGL2 F))) := by
    rw [hcard₁, hcard₂]
    omega
  have hnotconj : ¬ IsConj s₁ s₂ := by
    intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply hne_card
    have h := CFSG.Walter.centralizer_conj_eq_map g s₁
    rw [hg] at h
    rw [h]
    exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  have hIy : BenderSuzuki.PFAppendixIII.IsInvolution y :=
    sec5pef_isInvolution_of_orderOf_eq_two hy
  obtain hconj | hconj :=
    sec5pef_exists_conj_of_torus_data hK hcard hI₁ hI₂ hnotconj hIy
  · obtain ⟨g, hg⟩ := hconj
    have key := sec5pef_conj_data U₁ s₁ w₁ hU₁c hw₁U hw₁2 hinv₁ hcent₁ hg
    have hcast : ((Nat.card F - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.card F)]
      norm_num
    rw [hU₁card] at key
    exact ⟨1, Or.inl rfl, Nat.card F - 1, hcast, key⟩
  · obtain ⟨g, hg⟩ := hconj
    have key := sec5pef_conj_data U₂ s₂ w₂ hU₂c hw₂U hw₂2 hinv₂ hcent₂ hg
    have hcast : ((Nat.card F + 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - (-1) := by
      push_cast
      ring
    rw [hU₂card] at key
    exact ⟨-1, Or.inr rfl, Nat.card F + 1, hcast, key⟩

end CFSG.OddStandard.SmallF3.Omega
