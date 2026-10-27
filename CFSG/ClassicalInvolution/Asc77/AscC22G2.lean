module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace C22G

section Generic

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def genGroup (Ω : Set (Subgroup G)) (K : Subgroup G) (u : G) : Subgroup G :=
  (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω u

theorem le_genGroup_of_mem_twinSet {K M : Subgroup G} {u : G} (hM : M ∈ twinSet Ω K) :
    M ≤ genGroup Ω K u :=
  le_sup_of_le_left (le_iSup₂_of_le M hM le_rfl)

theorem rLayer_le_genGroup (K : Subgroup G) (u : G) : rLayer Ω u ≤ genGroup Ω K u := le_sup_right

theorem le_rLayer_of_le_centralizer {R : Subgroup G} {a : G} (hR : R ∈ RSet Ω)
    (hRa : R ≤ Subgroup.centralizer ({a} : Set G)) : R ≤ rLayer Ω a :=
  le_iSup₂_of_le R hR (le_iSup_of_le hRa le_rfl)

theorem rLayer_le_of_conj (hΩ : ConjInvariant Ω) {A : Subgroup G} {a u c : G} (hc : c ∈ A)
    (hca : c * a * c⁻¹ = u) (hA : rLayer Ω u ≤ A) : rLayer Ω a ≤ A := by
  unfold rLayer
  refine iSup₂_le fun R hR => iSup_le fun hRa => ?_
  intro r hr
  have h1 : c * r * c⁻¹ ∈ conjSub c R := conj_mem_conjSub hr
  have h2 : conjSub c R ≤ rLayer Ω u := by
    refine le_rLayer_of_le_centralizer (RSet.conj hΩ hR c) ?_
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp (hRa hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hca]
    calc x * (c * a * c⁻¹) = c * ((c⁻¹ * x * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by rw [hx']
      _ = c * a * c⁻¹ * x := by group
  have h3 : c * r * c⁻¹ ∈ A := hA (h2 h1)
  have h4 : c⁻¹ * (c * r * c⁻¹) * c ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hc) h3) hc
  have e : c⁻¹ * (c * r * c⁻¹) * c = r := by group
  rwa [e] at h4

theorem conjSub_mem_twinSet (hΩ : ConjInvariant Ω) {K J : Subgroup G} {z w y : G}
    (hz : IsUniqueInvolution K z) (hJ : J ∈ Ω) (hw : IsUniqueInvolution J w)
    (hyw : y * z * y⁻¹ = w) : conjSub y⁻¹ J ∈ twinSet Ω K := by
  refine ⟨hΩ y⁻¹ J hJ, z, hz, ?_⟩
  have := hw.conj y⁻¹
  have e : y⁻¹ * w * y⁻¹⁻¹ = z := by rw [← hyw]; group
  rwa [e] at this

theorem le_genGroup_of_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} {z w y u : G}
    (hz : IsUniqueInvolution K z) (hJ : J ∈ Ω) (hw : IsUniqueInvolution J w)
    (hy : y ∈ genGroup Ω K u) (hyw : y * z * y⁻¹ = w) : J ≤ genGroup Ω K u := by
  have hM : conjSub y⁻¹ J ∈ twinSet Ω K := conjSub_mem_twinSet hΩ hz hJ hw hyw
  have hMA : conjSub y⁻¹ J ≤ genGroup Ω K u := le_genGroup_of_mem_twinSet hM
  intro x hx
  have h1 : y⁻¹ * x * y⁻¹⁻¹ ∈ conjSub y⁻¹ J := conj_mem_conjSub hx
  have h2 := hMA h1
  have h3 : y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ ∈ genGroup Ω K u :=
    (genGroup Ω K u).mul_mem ((genGroup Ω K u).mul_mem hy h2) ((genGroup Ω K u).inv_mem hy)
  have e : y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = x := by group
  rwa [e] at h3

end Generic

end C22G

end CFSG.ClassicalInvolution.Asc77
