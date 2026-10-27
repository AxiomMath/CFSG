module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingEquivariant

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

open MulAction

@[expose] def equivariantOrbitHom (P Ω : Type*) [Group P] [MulAction P Ω] :
    equivariantSubgroup P Ω →* Equiv.Perm (MulAction.orbitRel.Quotient P Ω) where
  toFun c :=
    { toFun := Quotient.map' c.val (by
        intro x y h
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
        exact MulAction.mem_orbit_iff.mpr ⟨g,
          ((mem_equivariantSubgroup c.val).mp c.property g y).symm.trans
            (congrArg c.val hg)⟩)
      invFun := Quotient.map' c.val.symm (by
        intro x y h
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
        exact MulAction.mem_orbit_iff.mpr ⟨g,
          ((mem_equivariantSubgroup (c⁻¹).val).mp (c⁻¹).property g y).symm.trans
            (congrArg c.val.symm hg)⟩)
      left_inv o := Quotient.inductionOn' o (fun x => congrArg Quotient.mk''
        (c.val.symm_apply_apply x))
      right_inv o := Quotient.inductionOn' o (fun x => congrArg Quotient.mk''
        (c.val.apply_symm_apply x)) }
  map_one' := Equiv.ext fun o => Quotient.inductionOn' o (fun _ => rfl)
  map_mul' _ _ := Equiv.ext fun o => Quotient.inductionOn' o (fun _ => rfl)

theorem equivariantOrbitHom_mk {P Ω : Type*} [Group P] [MulAction P Ω]
    (c : equivariantSubgroup P Ω) (x : Ω) :
    equivariantOrbitHom P Ω c (Quotient.mk'' x) = Quotient.mk'' (c.val x) := rfl

@[expose] def orbitKernel (P Ω : Type*) [Group P] [MulAction P Ω] :
    Subgroup (equivariantSubgroup P Ω) := (equivariantOrbitHom P Ω).ker

theorem mem_orbitKernel {P Ω : Type*} [Group P] [MulAction P Ω]
    (c : equivariantSubgroup P Ω) : c ∈ orbitKernel P Ω ↔
      ∀ x : Ω, (Quotient.mk'' (c.val x) : orbitRel.Quotient P Ω) = Quotient.mk'' x := by
  change equivariantOrbitHom P Ω c = 1 ↔ _
  constructor
  · intro hc x
    exact Equiv.congr_fun hc (Quotient.mk'' x)
  · intro hc
    apply Equiv.ext
    intro o
    exact Quotient.inductionOn' o hc

theorem orbitKernel_normal (P Ω : Type*) [Group P] [MulAction P Ω] :
    (orbitKernel P Ω).Normal := inferInstanceAs (equivariantOrbitHom P Ω).ker.Normal

theorem orbitKernel_preserves {P Ω : Type*} [Group P] [MulAction P Ω]
    (c : orbitKernel P Ω) (o : orbitRel.Quotient P Ω) (x : Ω) :
    c.val.val x ∈ o.orbit ↔ x ∈ o.orbit := by
  rw [orbitRel.Quotient.mem_orbit, orbitRel.Quotient.mem_orbit,
    (mem_orbitKernel c.val).mp c.property]

@[expose] def orbitKernelRestriction (P Ω : Type*) [Group P] [MulAction P Ω] :
    orbitKernel P Ω →* ((o : orbitRel.Quotient P Ω) → equivariantSubgroup P o.orbit) where
  toFun c o := ⟨c.val.val.subtypePerm (orbitKernel_preserves c o), by
    apply (mem_equivariantSubgroup _).mpr
    intro g x
    apply Subtype.ext
    exact (mem_equivariantSubgroup c.val.val).mp c.val.property g x.val⟩
  map_one' := by
    funext o
    apply Subtype.ext
    exact Equiv.ext (fun _ => rfl)
  map_mul' _ _ := by
    funext o
    apply Subtype.ext
    exact Equiv.ext (fun _ => rfl)

theorem orbitKernelRestriction_injective {P Ω : Type*} [Group P] [MulAction P Ω] :
    Function.Injective (orbitKernelRestriction P Ω) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let o : orbitRel.Quotient P Ω := Quotient.mk'' x
  let y : o.orbit := ⟨x, orbitRel.Quotient.mem_orbit.mpr rfl⟩
  exact congrArg (fun f => (f o).val y |>.val) h

theorem finite_pi_isPGroup {ι : Type*} [Finite ι] {H : ι → Type*}
    [∀ i, Group (H i)] [∀ i, Finite (H i)] (p : ℕ) [Fact p.Prime]
    (h : ∀ i, IsPGroup p (H i)) : IsPGroup p ((i : ι) → H i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose n hn using fun i => (h i).exists_card_eq
  apply IsPGroup.of_card (n := ∑ i, n i)
  rw [Nat.card_pi]
  simp_rw [hn]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem orbitKernel_isPGroup {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω]
    [Finite Ω] (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P) :
    IsPGroup p (orbitKernel P Ω) := by
  have hfactors : ∀ o : orbitRel.Quotient P Ω, IsPGroup p (equivariantSubgroup P o.orbit) := by
    intro o
    obtain ⟨x, hx⟩ := o.nonempty_orbit
    exact transitive_equivariant_isPGroup p hP ⟨x, hx⟩
  exact (finite_pi_isPGroup p hfactors).of_injective (orbitKernelRestriction P Ω)
    orbitKernelRestriction_injective

theorem orbit_ofSubtype_equivariant {P Ω : Type*} [Group P] [MulAction P Ω]
    (o : orbitRel.Quotient P Ω) (u : equivariantSubgroup P o.orbit) :
    @Equiv.Perm.ofSubtype Ω (· ∈ o.orbit) (Classical.decPred _) u.val ∈
      equivariantSubgroup P Ω := by
  classical
  apply (mem_equivariantSubgroup _).mpr
  intro g x
  by_cases hx : x ∈ o.orbit
  · have hgx := orbitRel.Quotient.mapsTo_smul_orbit g o hx
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx,
      Equiv.Perm.ofSubtype_apply_of_mem _ hgx]
    exact congrArg Subtype.val
      ((mem_equivariantSubgroup u.val).mp u.property g ⟨x, hx⟩)
  · have hgx : g • x ∉ o.orbit := by
      intro h
      have := orbitRel.Quotient.mapsTo_smul_orbit g⁻¹ o h
      exact hx (by simpa only [inv_smul_smul] using this)
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx,
      Equiv.Perm.ofSubtype_apply_of_not_mem _ hgx]

@[expose] noncomputable def orbitKernelExtension {P Ω : Type*} [Group P]
    [MulAction P Ω] (o : orbitRel.Quotient P Ω)
    (u : equivariantSubgroup P o.orbit) : orbitKernel P Ω := by
  classical
  refine ⟨⟨Equiv.Perm.ofSubtype u.val, orbit_ofSubtype_equivariant o u⟩, ?_⟩
  apply (mem_orbitKernel _).mpr
  intro x
  by_cases hx : x ∈ o.orbit
  · change Quotient.mk'' (Equiv.Perm.ofSubtype u.val x) = _
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    exact (orbitRel.Quotient.mem_orbit.mp (u.val ⟨x, hx⟩).property).trans
      (orbitRel.Quotient.mem_orbit.mp hx).symm
  · exact congrArg Quotient.mk'' (Equiv.Perm.ofSubtype_apply_of_not_mem u.val hx)

theorem orbitKernelExtension_apply_mem {P Ω : Type*} [Group P] [MulAction P Ω]
    (o : orbitRel.Quotient P Ω) (u : equivariantSubgroup P o.orbit)
    (x : Ω) (hx : x ∈ o.orbit) :
    (orbitKernelExtension o u).val.val x = (u.val ⟨x, hx⟩).val := by
  classical
  exact Equiv.Perm.ofSubtype_apply_of_mem u.val hx

theorem orbitKernelExtension_apply_not_mem {P Ω : Type*} [Group P] [MulAction P Ω]
    (o : orbitRel.Quotient P Ω) (u : equivariantSubgroup P o.orbit)
    (x : Ω) (hx : x ∉ o.orbit) :
    (orbitKernelExtension o u).val.val x = x := by
  classical
  exact Equiv.Perm.ofSubtype_apply_of_not_mem u.val hx

theorem orbit_nontrivial_of_no_fixedPoints {P Ω : Type*} [Group P] [MulAction P Ω]
    (hfixed : MulAction.fixedPoints P Ω = ∅) (o : orbitRel.Quotient P Ω) :
    Nontrivial o.orbit := by
  obtain ⟨x, hx⟩ := o.nonempty_orbit
  have hnot : ¬∀ g : P, g • x = x := by
    intro h
    have hm := MulAction.mem_fixedPoints.mpr h
    rw [hfixed] at hm
    exact hm
  obtain ⟨g, hg⟩ := not_forall.mp hnot
  exact nontrivial_of_ne (⟨g • x, o.mapsTo_smul_orbit g hx⟩ : o.orbit) ⟨x, hx⟩
    (fun h => hg (congrArg Subtype.val h))

theorem orbitKernel_centralizer_le {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω]
    [Finite Ω] (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P)
    (hfixed : MulAction.fixedPoints P Ω = ∅) :
    Subgroup.centralizer (orbitKernel P Ω : Set (equivariantSubgroup P Ω)) ≤
      orbitKernel P Ω := by
  intro c hc
  apply (mem_orbitKernel c).mpr
  intro x
  let o : orbitRel.Quotient P Ω := Quotient.mk'' x
  have hx : x ∈ o.orbit := orbitRel.Quotient.mem_orbit.mpr rfl
  let : Nontrivial o.orbit := orbit_nontrivial_of_no_fixedPoints hfixed o
  let : Nontrivial (equivariantSubgroup P o.orbit) :=
    transitive_equivariant_nontrivial p hP ⟨x, hx⟩
  obtain ⟨u, hu⟩ := exists_ne (1 : equivariantSubgroup P o.orbit)
  let v := orbitKernelExtension o u
  have hcomm := Subgroup.mem_centralizer_iff.mp hc v.val v.property
  have happly := congrArg (fun d : equivariantSubgroup P Ω => d.val x) hcomm
  change v.val.val (c.val x) = c.val (v.val.val x) at happly
  by_contra hmove
  have houtside : c.val x ∉ o.orbit := by
    intro h
    exact hmove (orbitRel.Quotient.mem_orbit.mp h)
  rw [orbitKernelExtension_apply_not_mem o u _ houtside,
    orbitKernelExtension_apply_mem o u x hx] at happly
  have hfix := c.val.injective happly
  exact equivariant_nonidentity_fixedPointFree u hu ⟨x, hx⟩
    (Subtype.ext hfix.symm)

theorem fixedFree_equivariant_kernel {P Ω : Type*} [Group P] [Finite P]
    [MulAction P Ω] [Finite Ω] (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P)
    (hfixed : MulAction.fixedPoints P Ω = ∅) :
    (orbitKernel P Ω).Normal ∧ IsPGroup p (orbitKernel P Ω) ∧
      Subgroup.centralizer (orbitKernel P Ω : Set (equivariantSubgroup P Ω)) ≤
        orbitKernel P Ω :=
  ⟨orbitKernel_normal P Ω, orbitKernel_isPGroup p hP,
    orbitKernel_centralizer_le p hP hfixed⟩

end CFSG.ComponentClassification.CatalogueBAlternating
