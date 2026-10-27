module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingOrbitKernel
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

open MulAction

theorem equivariantSubgroup_eq_centralizer {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) :
    equivariantSubgroup P Ω = Subgroup.centralizer (P : Set (Equiv.Perm Ω)) := by
  have hrange : Set.range (MulAction.toPermHom P Ω) = (P : Set (Equiv.Perm Ω)) := by
    ext c
    constructor
    · rintro ⟨g, rfl⟩
      exact g.property
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
  unfold equivariantSubgroup
  rw [hrange]

@[expose] def equivariantNormalizerInclusion {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) :
    equivariantSubgroup P Ω →* Subgroup.normalizer (P : Set (Equiv.Perm Ω)) where
  toFun c := ⟨c.val, Subgroup.centralizer_le_normalizer _
    (equivariantSubgroup_eq_centralizer P ▸ c.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def normalizerOrbitKernel {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Subgroup.normalizer (P : Set (Equiv.Perm Ω))) :=
  (orbitKernel P Ω).map (equivariantNormalizerInclusion P)

theorem normalizerOrbitKernel_eq {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) :
    normalizerOrbitKernel P =
      (Subgroup.centralizer (P : Set (Equiv.Perm Ω))).subgroupOf
        (Subgroup.normalizer (P : Set (Equiv.Perm Ω))) ⊓
      (CFSG.FiveTransitive.NormalizerOrbitHom.toPermHom (Y := Ω) P).ker := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨equivariantSubgroup_eq_centralizer P ▸ d.property, ?_⟩
    apply Equiv.ext
    intro o
    induction o using Quotient.inductionOn with
    | h x => exact (mem_orbitKernel d).mp hd x
  · rintro ⟨hc, hkernel⟩
    let d : equivariantSubgroup P Ω :=
      ⟨c.val, (equivariantSubgroup_eq_centralizer P).symm ▸ hc⟩
    refine ⟨d, ?_, rfl⟩
    apply (mem_orbitKernel d).mpr
    intro x
    exact Equiv.congr_fun hkernel (Quotient.mk'' x)

theorem normalizerOrbitKernel_normal {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) :
    (normalizerOrbitKernel P).Normal := by
  rw [normalizerOrbitKernel_eq]
  infer_instance

theorem normalizerOrbitKernel_isPGroup {Ω : Type*} [Finite Ω]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup p P) :
    IsPGroup p (normalizerOrbitKernel P) :=
  (orbitKernel_isPGroup p hP).map (equivariantNormalizerInclusion P)

theorem normalizerOrbitKernelExtension_mem {Ω : Type*} (P : Subgroup (Equiv.Perm Ω))
    (o : orbitRel.Quotient P Ω) (u : equivariantSubgroup P o.orbit) :
    equivariantNormalizerInclusion P (orbitKernelExtension o u).val ∈
      normalizerOrbitKernel P :=
  Subgroup.mem_map_of_mem _ (orbitKernelExtension o u).property

theorem normalizerOrbitKernel_centralizer_preserves {Ω : Type*} [Finite Ω]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup p P)
    (c : Subgroup.normalizer (P : Set (Equiv.Perm Ω)))
    (hc : c ∈ Subgroup.centralizer (normalizerOrbitKernel P : Set _))
    (o : orbitRel.Quotient P Ω) [Nontrivial o.orbit] (x : Ω) (hx : x ∈ o.orbit) :
    c.val x ∈ o.orbit := by
  let : Nontrivial (equivariantSubgroup P o.orbit) :=
    transitive_equivariant_nontrivial p hP ⟨x, hx⟩
  obtain ⟨u, hu⟩ := exists_ne (1 : equivariantSubgroup P o.orbit)
  let v := equivariantNormalizerInclusion P (orbitKernelExtension o u).val
  have hcomm := Subgroup.mem_centralizer_iff.mp hc v
    (normalizerOrbitKernelExtension_mem P o u)
  have happly := congrArg (fun d : Subgroup.normalizer (P : Set (Equiv.Perm Ω)) => d.val x)
    hcomm
  change (orbitKernelExtension o u).val.val (c.val x) =
    c.val ((orbitKernelExtension o u).val.val x) at happly
  by_contra houtside
  rw [orbitKernelExtension_apply_not_mem o u _ houtside,
    orbitKernelExtension_apply_mem o u x hx] at happly
  have hfix := c.val.injective happly
  exact equivariant_nonidentity_fixedPointFree u hu ⟨x, hx⟩ (Subtype.ext hfix.symm)

theorem normalizer_pComponent_equivariant {Ω : Type*} [Finite Ω]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup p P)
    (L : Subgroup (Subgroup.normalizer (P : Set (Equiv.Perm Ω))))
    (hL : CFSG.IsPComponent p L) :
    ∀ c : L, c.val.val ∈ equivariantSubgroup P Ω := by
  let N := Subgroup.normalizer (P : Set (Equiv.Perm Ω))
  have hc := pComponent_le_centralizer_normal_p p L (P.subgroupOf N) hL hP.comap_subtype
  intro c
  rw [equivariantSubgroup_eq_centralizer]
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  have hcomm := Subgroup.mem_centralizer_iff.mp (hc c.property)
    (⟨g, P.le_normalizer hg⟩ : N) hg
  exact congrArg Subtype.val hcomm

theorem normalizer_pComponent_fixedSupport {Ω : Type*} [Finite Ω]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup p P)
    (L : Subgroup (Subgroup.normalizer (P : Set (Equiv.Perm Ω))))
    (hL : CFSG.IsPComponent p L) :
    ∀ (c : L) (x : Ω), x ∉ MulAction.fixedPoints P Ω → c.val.val x = x := by
  let N := Subgroup.normalizer (P : Set (Equiv.Perm Ω))
  let : (normalizerOrbitKernel P).Normal := normalizerOrbitKernel_normal P
  have hcentral := pComponent_le_centralizer_normal_p p L (normalizerOrbitKernel P) hL
    (normalizerOrbitKernel_isPGroup p P hP)
  let : Group.IsPerfect L := pComponent_perfect hL
  intro c x hx
  let o : orbitRel.Quotient P Ω := Quotient.mk'' x
  have hxo : x ∈ o.orbit := orbitRel.Quotient.mem_orbit.mpr rfl
  have hnot : ¬∀ g : P, g • x = x := fun h => hx (MulAction.mem_fixedPoints.mpr h)
  obtain ⟨g, hg⟩ := not_forall.mp hnot
  let : Nontrivial o.orbit := nontrivial_of_ne
    (⟨g • x, o.mapsTo_smul_orbit g hxo⟩ : o.orbit) ⟨x, hxo⟩
    (fun h => hg (congrArg Subtype.val h))
  have hpreserves : ∀ d : L, ∀ y : Ω, d.val.val y ∈ o.orbit ↔ y ∈ o.orbit := by
    intro d y
    constructor
    · intro hy
      have hinv := normalizerOrbitKernel_centralizer_preserves p P hP d.val⁻¹
        (hcentral (L.inv_mem d.property)) o (d.val.val y) hy
      change d.val.val.symm (d.val.val y) ∈ o.orbit at hinv
      simpa only [Equiv.symm_apply_apply] using hinv
    · exact normalizerOrbitKernel_centralizer_preserves p P hP d.val
        (hcentral d.property) o y
  let f : L →* equivariantSubgroup P o.orbit :=
    { toFun d := ⟨d.val.val.subtypePerm (hpreserves d), by
        apply (mem_equivariantSubgroup _).mpr
        intro a y
        apply Subtype.ext
        exact (mem_equivariantSubgroup _).mp (normalizer_pComponent_equivariant p P hP L hL d)
          a y.val⟩
      map_one' := Subtype.ext (Equiv.ext fun _ => rfl)
      map_mul' _ _ := Subtype.ext (Equiv.ext fun _ => rfl) }
  let : Group.IsNilpotent (equivariantSubgroup P o.orbit) :=
    (transitive_equivariant_isPGroup p hP ⟨x, hxo⟩).isNilpotent
  have hf : f = 1 := SolvableKernelContainment.hom_eq_one f
  exact congrArg (fun d : equivariantSubgroup P o.orbit => (d.val ⟨x, hxo⟩).val)
    (DFunLike.congr_fun hf c)

end CFSG.ComponentClassification.CatalogueBAlternating
