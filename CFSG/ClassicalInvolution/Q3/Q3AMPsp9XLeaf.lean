module

public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XVertex
public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Defs


@[expose] def PspLayersWC9 : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' →
      ∀ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G), BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃ →
        PspNbhdL4 Ω K z → PspNbhdL4 Ω J t → PspNbhdL4 Ω K' (z * t) →
          ∃ L₁ L₂ : Subgroup G,
            IsSectionMember 3 2 (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₁ z ∧
              IsSectionMember 3 2 (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₂ t ∧
                WeakClosureAt (t₁ * t₂ * t₃) L₁ ∧ NormalizesImageAt (t₁ * t₂ * t₃) t L₁

end Defs

section Route


theorem pspVertexSLeaf9_of_layersWC (hL : PspLayersWC9) : PspVertexSLeaf9 := by
  intro hI9 G _ _ _ Ω K J S R T W z t K' hb9 hset t₁ t₂ t₃ R₁ R₂ R₃ hax hK hJ hK'
  obtain ⟨L₁, L₂, h₁, h₂, hwc, hnorm⟩ :=
    hL hI9 G Ω K J S R T W z t K' hb9 hset t₁ t₂ t₃ R₁ R₂ R₃ hax hK hJ hK'
  have hbad := hset.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  have hs2 := hax.s_mul_self
  have hcz : z * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z := hax.s_comm₁.eq
  have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
  have hindep : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z, t} : Set G) := hax.s_not_mem_pair
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun h1 => hindep (h1 ▸ Subgroup.one_mem _)
  have hzB : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hsz : z ≠ t₁ * t₂ * t₃ := fun e => hindep (e ▸ hzB)
  have hst : t ≠ t₁ * t₂ * t₃ := fun e => hindep (e ▸ htB)
  have helem := T8T.isElemAbelian_closure_three hz2 ht2 hs2 hzt hcz hct
  have h8 := T8T.natCard_closure_three hz2 ht2 hs2 hzt hcz hct hstd.hz.ne_one hstd.ht.ne_one hne
    hs1 hindep
  exact hyp51At_of_layers_wc hbad.nonabelian (hb9 2 (by norm_num)) (by norm_num) (by norm_num)
    helem h8 hs1 hstd.hz.ne_one hstd.ht.ne_one hne hsz hst h₁ h₂ hwc hnorm

end Route

end CFSG.ClassicalInvolution.Q3.Q3AM
