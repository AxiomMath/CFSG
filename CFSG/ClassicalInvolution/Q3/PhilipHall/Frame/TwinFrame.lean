module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7F0
public import CFSG.ClassicalInvolution.SmallCases.A7Q1

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

namespace TwinFrame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def frameSet (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {B | ∃ (K K' J : Subgroup G) (z u t : G), TwinFrameData Ω K K' z u J t ∧
    B = Subgroup.closure ({z, u, t} : Set G)}

theorem closure_mem_frameSet {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) : Subgroup.closure ({z, u, t} : Set G) ∈ frameSet Ω :=
  ⟨K, K', J, z, u, t, h, rfl⟩

theorem frameData_conj [Finite G] (hΩ : ConjInvariant Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) (g : G) :
    TwinFrameData Ω (conjSub g K) (conjSub g K') (g * z * g⁻¹) (g * u * g⁻¹) (conjSub g J)
      (g * t * g⁻¹) := by
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b hab => by simpa using hab
  have hK'c := twinSet_conj hΩ h.hK' g
  refine ⟨hΩ g K h.mem, h.hz.conj g, hK'c, fun e => h.hne (conjSub_injective g e), ?_, ?_, ?_,
    fun e => h.huz (hinj _ _ e), ?_, h.ht.conj g, ?_⟩
  · have := conj_mem_conjSub (n := g) h.hu
    rwa [T7A.conjSub_sup_eq] at this
  · calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [h.hu2]; group
  · intro e
    exact h.hu1 (hinj _ _ (by rw [e]; group))
  · refine ⟨hΩ g J h.hJ.1, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ hL g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have := omegaNbr_conj hΩ (h.hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  · calc (g * t * g⁻¹) * (g * u * g⁻¹) = g * (t * u) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [h.htu]
      _ = (g * u * g⁻¹) * (g * t * g⁻¹) := by group

theorem map_conj_closure_three (g a b c : G) :
    (Subgroup.closure ({a, b, c} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹, g * c * g⁻¹} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

theorem frameSet_conj [Finite G] (hΩ : ConjInvariant Ω) {B : Subgroup G} (hB : B ∈ frameSet Ω)
    (g : G) : B.map (MulAut.conj g).toMonoidHom ∈ frameSet Ω := by
  obtain ⟨K, K', J, z, u, t, h, rfl⟩ := hB
  exact ⟨_, _, _, _, _, _, frameData_conj hΩ h g, map_conj_closure_three g z u t⟩

theorem z_mem (z u t : G) : z ∈ Subgroup.closure ({z, u, t} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem u_mem (z u t : G) : u ∈ Subgroup.closure ({z, u, t} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem t_mem (z u t : G) : t ∈ Subgroup.closure ({z, u, t} : Set G) :=
  Subgroup.subset_closure (by simp)

section Shape

variable [Finite G]

theorem shape_of_frameData (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) :
    IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) ∧
      Nat.card (Subgroup.closure ({z, u, t} : Set G)) = 8 :=
  ⟨Hat2A7S.twinFrame_isElemAbelian hΩ h, Hat2A7S.twinFrame_natCard_eight hΩ h⟩

end Shape

section FourGroups

variable [Finite G]

theorem closure_zu_mem {K K' J : Subgroup G} {z u t : G} (h : TwinFrameData Ω K K' z u J t) :
    Subgroup.closure ({z, u} : Set G) ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, u, t} : Set G)) := by
  refine ⟨Subgroup.closure_mono ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp
  · rw [Balance.Bootstrap.card_closure_pair_eq_four h.hz.sq h.hu2 h.hz.ne_one h.hu1
      (Ne.symm h.huz) h.comm_zu]
    norm_num

theorem closure_zt_mem (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) :
    Subgroup.closure ({z, t} : Set G) ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, u, t} : Set G)) := by
  refine ⟨Subgroup.closure_mono ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp
  · rw [Balance.Bootstrap.card_closure_pair_eq_four h.hz.sq h.ht.sq h.hz.ne_one h.ht.ne_one
      (Ne.symm h.t_ne_z) (A7Q.Gen.comm_zt hΩ h)]
    norm_num

end FourGroups

end TwinFrame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
