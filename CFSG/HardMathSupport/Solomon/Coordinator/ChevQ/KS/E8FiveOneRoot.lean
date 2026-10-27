module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneSylow
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSplit
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
public import CFSG.RankThree.Lattice.SteinbergBIGenUnipotent

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh

set_option linter.unusedSectionVars false

section Group

variable {G : Type*} [Group G]

theorem map_conj_eq_of_forall (U E : Subgroup G) (h : ∀ x ∈ E, ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    ∀ x ∈ E, U.map (MulAut.conj x).toMonoidHom = U := by
  intro x hx
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact h x hx u hu
  · intro u hu
    refine ⟨x⁻¹ * u * x, ?_, ?_⟩
    · have := h x⁻¹ (inv_mem hx) u hu
      simpa using this
    · show x * (x⁻¹ * u * x) * x⁻¹ = u
      group

theorem normalizesRGroup_of_conj (r : ℕ) (E : Subgroup G) (c : G)
    (h : NormalizesRGroup r (E.map (MulAut.conj c).toMonoidHom)) : NormalizesRGroup r E := by
  obtain ⟨U, hU1, hUp, hUn⟩ := h
  refine ⟨U.map (MulAut.conj c⁻¹).toMonoidHom, ?_, hUp.map _, ?_⟩
  · intro hbot
    apply hU1
    have h2 := congrArg (fun V : Subgroup G => V.map (MulAut.conj c).toMonoidHom) hbot
    simp only [Subgroup.map_map, Subgroup.map_bot] at h2
    have : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rwa [this, Subgroup.map_id] at h2
  · apply map_conj_eq_of_forall
    intro x hx u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hcx : c * x * c⁻¹ ∈ E.map (MulAut.conj c).toMonoidHom := ⟨x, hx, rfl⟩
    have h3 : (c * x * c⁻¹) * v * (c * x * c⁻¹)⁻¹ ∈ U := by
      have := hUn _ hcx
      rw [← this]
      exact ⟨v, hv, rfl⟩
    refine ⟨(c * x * c⁻¹) * v * (c * x * c⁻¹)⁻¹, h3, ?_⟩
    show c⁻¹ * ((c * x * c⁻¹) * v * (c * x * c⁻¹)⁻¹) * c⁻¹⁻¹ = x * (c⁻¹ * v * c⁻¹⁻¹) * x⁻¹
    group

end Group

section Root


variable (K : Type) [Field K] [Finite K]

@[expose] def rootGrp (β : Fin Tag.E8.rank → ℤ) : Subgroup (adjointGroup Tag.E8 K) :=
  (rootSubgroup Tag.E8 K β).subgroupOf (adjointGroup Tag.E8 K)

variable {K}

theorem normalizesRGroup_of_fixed_root {E : Subgroup (adjointGroup Tag.E8 K)}
    (hE : ∀ x ∈ E, x ∈ monomialN K) {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β)
    (hfix : ∀ (x : adjointGroup Tag.E8 K) (hx : x ∈ E), rhoN K ⟨x, hE x hx⟩ • β = β) :
    NormalizesRGroup (ringChar K) E := by
  refine ⟨rootGrp K β, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : (⟨pinnedX Tag.E8 K β 1, pinnedX_mem_adjointGroup β 1⟩ :
        adjointGroup Tag.E8 K) ∈ rootGrp K β := by
      rw [rootGrp, Subgroup.mem_subgroupOf]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h0 : pinnedX Tag.E8 K β (1 : K) = pinnedX Tag.E8 K β 0 := by
      have := congrArg Subtype.val hmem
      rw [pinnedX_zero]
      exact this
    exact one_ne_zero (pinnedX_injective Tag.E8 K β h0)
  · intro u
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hu : ((u : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ rootSubgroup Tag.E8 K β := u.2
    have := e8Split_pow_ringChar Tag.E8 β hu
    simpa using this
  · apply map_conj_eq_of_forall
    intro x hx u hu
    have hu' : (u : ModGL Tag.E8 K) ∈ rootSubgroup Tag.E8 K β := hu
    have hxm : ((x : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ monomialSubgroup Tag.E8 K := hE x hx
    have h1 :=
      CFSG.RankThree.Lattice.GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup
        (k := K) hxm hβ
    have hrho : weylQuotientHom Tag.E8 K ⟨(x : ModGL Tag.E8 K), hxm⟩ • β = β := hfix x hx
    rw [hrho] at h1
    have h2 : ((x * u * x⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈
        (rootSubgroup Tag.E8 K β).map (MulAut.conj (x : ModGL Tag.E8 K)).toMonoidHom := by
      refine ⟨u, hu', ?_⟩
      simp [MulAut.conj_apply]
    rw [h1] at h2
    exact h2

end Root

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
