module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG

open Subgroup

variable {X Y : Type*} [Group X] [Group Y]

theorem map_pCore_eq_of_surjective_of_isPGroup_ker {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    (pCore p X).map f = pCore p Y := by
  refine le_antisymm ?_ ?_
  · exact le_sSup ⟨(pCore_normal (p := p) (G := X)).map f hf, (pCore_isPGroup (p := p)).map f⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := hf y
    have hx : x ∈ (pCore p Y).comap f := hy
    have hcomap : IsPGroup p ↥((pCore p Y).comap f) :=
      IsPGroup.comap_of_ker_isPGroup (pCore_isPGroup (p := p) (G := Y)) f hker
    have hnorm : ((pCore p Y).comap f).Normal := (pCore_normal (p := p) (G := Y)).comap f
    exact Subgroup.mem_map.mpr ⟨x, le_sSup (s := {K : Subgroup X | K.Normal ∧ IsPGroup p K})
      ⟨hnorm, hcomap⟩ hx, rfl⟩

theorem nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    Nonempty ((X ⧸ pCore p X) ≃* (Y ⧸ pCore p Y)) := by
  have hmap := map_pCore_eq_of_surjective_of_isPGroup_ker f hf hker
  have hle : pCore p X ≤ (pCore p Y).comap f := by
    intro x hx
    rw [Subgroup.mem_comap, ← hmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  let F : (X ⧸ pCore p X) →* (Y ⧸ pCore p Y) :=
    QuotientGroup.map (pCore p X) (pCore p Y) f hle
  have hFsurj : Function.Surjective F :=
    QuotientGroup.map_surjective_of_surjective _ _ f
      (fun y => by
        obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨x, rfl⟩ := hf z
        exact ⟨x, rfl⟩) hle
  have hkerF : F.ker = ⊥ := by
    rw [QuotientGroup.ker_map, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    have hfx : f x ∈ pCore p Y := hx
    rw [← hmap] at hfx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hfx
    have hmem : a⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hax]
      simp
    have hk : f.ker ≤ pCore p X := le_sSup ⟨f.normal_ker, hker⟩
    have hax' : a⁻¹ * x ∈ pCore p X := hk hmem
    have h := (pCore p X).mul_mem ha hax'
    simpa [mul_assoc] using h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hkerF).trans
    QuotientGroup.quotientBot).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)⟩

theorem pCore_ne_bot_of_surjective_of_isPGroup_ker {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker) (hY : pCore p Y ≠ ⊥) :
    pCore p X ≠ ⊥ := by
  intro hX
  apply hY
  rw [← map_pCore_eq_of_surjective_of_isPGroup_ker f hf hker, hX, Subgroup.map_bot]

theorem perfectResidual_subtype_subgroupOf {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (hKL : K ≤ L) :
    ((CFSG.perfectResidual ↥K).map K.subtype).subgroupOf L =
      (CFSG.perfectResidual ↥(K.subgroupOf L)).map (K.subgroupOf L).subtype := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr ((Subgroup.map_subtype_le _).trans hKL)]
  have h := SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map L.subtype (K.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hKL] at h
  exact h.symm

end CFSG
