module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactA

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem mem_of_mem_aStar (hK : K ∈ Ω) {J : Subgroup G} (hJ : J ∈ aStar Ω K) : J ∈ Ω :=
  (mem_aStar_symm hK hJ).1

theorem aStar_subset_aStar_of_mem {K' : Subgroup G} (h : K' ∈ aStar Ω K) :
    aStar Ω K' ⊆ aStar Ω K :=
  fun _ hJ => Relation.ReflTransGen.trans h hJ

theorem le_conjStab_aStar (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) {M : Subgroup G}
    (hM : M ∈ aStar Ω K) : M ≤ conjStab (aStar Ω K) :=
  fun _ hx => mem_conjStab_aStar hΩ hK hM (conjSub_eq_self_of_mem hx)

theorem omegaGen_aStar_le_conjStab (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) :
    omegaGen (aStar Ω K) ≤ conjStab (aStar Ω K) :=
  iSup₂_le fun _ hM => le_conjStab_aStar hΩ hK hM

theorem conjStab_le_normalizer_omegaGen (S : Set (Subgroup G)) :
    conjStab S ≤ Subgroup.normalizer (omegaGen S : Set G) := by
  have key : ∀ x ∈ conjStab S, conjSub x (omegaGen S) ≤ omegaGen S := by
    intro x hx
    unfold omegaGen conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun M => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hM => ?_
    exact le_omegaGen ((mem_conjStab_iff.mp hx M).mpr hM)
  intro x hx
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm (key x hx) ?_
  have h1 := conjSub_mono (n := x) (key x⁻¹ ((conjStab S).inv_mem hx))
  rwa [conjSub_conjSub_inv] at h1

theorem conjSub_mem_aStar_of_centralizer (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    {M : Subgroup G} (hM : M ∈ aStar Ω K) : conjSub c M ∈ aStar Ω K := by
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [this]
    group
  have hKc : conjSub c K ∈ aStar Ω K := by
    by_cases he : conjSub c K = K
    · rw [he]
      exact Relation.ReflTransGen.refl
    · have hz' : IsUniqueInvolution (conjSub c K) z := by
        have := hz.conj c
        rwa [hcz] at this
      exact Relation.ReflTransGen.single
        ⟨hΩ c K hK, Or.inr (Or.inr ⟨⟨hΩ c K hK, z, hz, hz'⟩, he⟩)⟩
  exact aStar_subset_aStar_of_mem hKc (aStar_conj hΩ hM c)

theorem centralizer_le_conjStab_aStar (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤ conjStab (aStar Ω K) := by
  intro c hc M
  refine ⟨fun h => ?_, fun h => conjSub_mem_aStar_of_centralizer hΩ hK hz hc h⟩
  have := conjSub_mem_aStar_of_centralizer hΩ hK hz
    ((Subgroup.centralizer ({z} : Set G)).inv_mem hc) h
  rwa [conjSub_inv_conjSub] at this

theorem aStar_eq_of_omegaGen_eq_top (hΩ : ConjInvariant Ω) (hK : K ∈ Ω)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M) (htop : omegaGen (aStar Ω K) = ⊤) :
    aStar Ω K = Ω := by
  refine Set.Subset.antisymm (fun J hJ => mem_of_mem_aStar hK hJ) fun M hM => ?_
  obtain ⟨g, rfl⟩ := htrans M hM
  have hg : g ∈ conjStab (aStar Ω K) :=
    omegaGen_aStar_le_conjStab hΩ hK (htop ▸ Subgroup.mem_top g)
  exact (mem_conjStab_iff.mp hg K).mpr Relation.ReflTransGen.refl

end CFSG.ClassicalInvolution.Asc77.T3Core
