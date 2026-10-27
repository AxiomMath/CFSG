module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrProp
public import CFSG.ClassicalInvolution.Q3.TL4OddBadW
public import CFSG.ClassicalInvolution.Asc77.AscT7FA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace LinkDisc

section Propagation

variable {G : Type} [Group G] [Finite G]

theorem normal_alphaOf_of_edges {K J : Subgroup G} {z u : G}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) (hc : DConnected (CoreAssembly.conjClass K))
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr (CoreAssembly.conjClass K) K)
    (hconst : ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, ∀ l : G, IsUniqueInvolution L l →
      alphaOf (Subgroup.closure ({l, z} : Set G)) =
        alphaOf (Subgroup.closure ({u, z} : Set G))) :
    (alphaOf (Subgroup.closure ({u, z} : Set G))).Normal := by
  have hcl := hΩ.conjInvariant
  have hval : ∀ (g : G) {L : Subgroup G},
      L ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub g K) → ∀ l : G,
        IsUniqueInvolution L l →
          alphaOf (Subgroup.closure ({l, g * z * g⁻¹} : Set G)) =
            conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) := by
    intro g L hL l hl
    have h1 := omegaNbr_conj hcl hL g⁻¹
    rw [conjSub_inv_conjSub] at h1
    have hl' : g * (g⁻¹ * l * g⁻¹⁻¹) * g⁻¹ = l := by group
    have e : Subgroup.closure ({l, g * z * g⁻¹} : Set G) =
        conjSub g (Subgroup.closure ({g⁻¹ * l * g⁻¹⁻¹, z} : Set G)) := by
      rw [T7A.conjSub_closure_pair, hl']
    rw [e, alphaOf_conjSub, hconst _ h1 _ (hl.conj g⁻¹)]
  have hedge : ∀ g g' : G,
      conjSub g' K ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub g K) →
        conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
          conjSub g' (alphaOf (Subgroup.closure ({u, z} : Set G))) := by
    intro g g' h
    have h' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ ⟨g, rfl⟩ ⟨g', rfl⟩ h
    rw [← hval g h _ (hz.conj g'), ← hval g' h' _ (hz.conj g), Set.pair_comm]
  have hreach : ∀ L ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = L ∧
      conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := by
    intro L hL
    have hp := hc _ (CoreAssembly.mem_conjClass_self K) _ hL
    clear hL
    induction hp with
    | refl => exact ⟨1, conjSub_one _, conjSub_one _⟩
    | @tail B C _ hBC ih =>
      obtain ⟨g, rfl, hgα⟩ := ih
      obtain ⟨⟨g', hg'⟩, hadj⟩ := hBC
      subst hg'
      refine ⟨g', rfl, ?_⟩
      rcases hadj with h1 | h2
      · rw [← hedge g g' h1, hgα]
      · rw [hedge g' g h2, hgα]
  have hall : ∀ g : G, conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
    intro g
    obtain ⟨g₁, hg₁, hg₁α⟩ := hreach _ (hcl g J hJ.1)
    have hJg := omegaNbr_conj hcl hJ g
    rw [← hg₁] at hJg
    rw [hedge g g₁ hJg, hg₁α]
  refine ⟨fun x hx g => ?_⟩
  rw [← hall g]
  exact Generic.conj_mem_conjSub hx

end Propagation

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem alphaOf_eq_of_edge (hL : TightLargeHypR r n Y R S t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J)
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (hB2 : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
        secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t M)
    {u : Y} (hu : IsUniqueInvolution J u) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ l : Y,
      IsUniqueInvolution L l →
        alphaOf (Subgroup.closure ({l, t} : Set Y)) =
          alphaOf (Subgroup.closure ({u, t} : Set Y)) := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have hO : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
    rw [Set.pair_comm]
    exact (oddCoreOf_layerY_le hΩ.conjInvariant).trans
      (oddCoreOf_centralizer_le_normalizer_alphaOf hu.sq ht.ne_one ctu)
  obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM.1
  have hmtu : m = t * u := hbad M hM hMJ u m hu hm
  have hEm : Subgroup.closure ({m, t} : Set Y) = Subgroup.closure ({u, t} : Set Y) := by
    rw [hmtu, ctu, closure_tz_pair, Set.pair_comm]
  have hO' : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({m, t} : Set Y)) : Set Y) := by
    rw [hEm]
    exact hO
  intro L hL' l hl
  rcases hB2 L hL' with e | e
  · exact AlphaFr.alphaOf_eq_of_secImg_conj hL hJ hL' hu hl hO (g := 1) (Subgroup.one_mem _)
      (by rw [map_one, conjSub_one, e])
  · rw [← hEm]
    exact AlphaFr.alphaOf_eq_of_secImg_conj hL hM hL' hm hl hO' (g := 1) (Subgroup.one_mem _)
      (by rw [map_one, conjSub_one, e])

end Cit3

end LinkDisc

end CFSG.ClassicalInvolution.Q3.TL4
