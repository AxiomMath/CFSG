module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

structure DihedralFusionChain (S : Subgroup G) (k : ℕ) where
  subgroups : Fin (k + 1) → Subgroup G
  supports : Fin k → Subgroup G
  automorphisms : (i : Fin k) → MulAut (supports i)
  subgroup_le : ∀ i, subgroups i ≤ S
  support_le : ∀ i, supports i ≤ S
  domain_le : ∀ i, subgroups i.castSucc ≤ supports i
  image_eq : ∀ i,
    (((subgroups i.castSucc).subgroupOf (supports i)).map
      (automorphisms i).toMonoidHom).map (supports i).subtype = subgroups i.succ
  realized : ∀ i, ∃ h : G,
    ((supports i = S ∧ h ∈ S) ∨
      (IsKleinFour (supports i) ∧
        h ∈ Subgroup.normalizer (supports i : Set G))) ∧
    ∀ x : supports i, (automorphisms i x : G) = h⁻¹ * (x : G) * h

theorem support_automorphism_image_eq_rightConjugate
    {Q T : Subgroup G} (hQT : Q ≤ T) (a : MulAut T) (h : G)
    (ha : ∀ x : T, (a x : G) = h⁻¹ * (x : G) * h) :
    ((Q.subgroupOf T).map a.toMonoidHom).map T.subtype = rightConjugate Q h := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨z, hz, by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.subtype_apply] using
        (ha z).symm⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let yT : T := ⟨y, hQT hy⟩
    refine Subgroup.mem_map.mpr ⟨a yT, Subgroup.mem_map.mpr ⟨yT, hy, rfl⟩, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.subtype_apply] using ha yT

namespace DihedralFusionChain

variable {S : Subgroup G} {k : ℕ} (c : DihedralFusionChain S k)

@[expose] def step (i : Fin k) : c.subgroups i.castSucc →* c.subgroups i.succ where
  toFun x := ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩, by
    rw [← c.image_eq i]
    exact Subgroup.mem_map.mpr
      ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩,
        Subgroup.mem_map.mpr ⟨⟨x, c.domain_le i x.property⟩, x.property, rfl⟩, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G)) (map_one (c.automorphisms i))
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G))
      (map_mul (c.automorphisms i) ⟨x, c.domain_le i x.property⟩
        ⟨y, c.domain_le i y.property⟩)

theorem step_coe (i : Fin k) (x : c.subgroups i.castSucc) :
    (c.step i x : G) =
      (c.automorphisms i ⟨x, c.domain_le i x.property⟩ : G) := rfl

@[expose] def prefixMap : (i : Fin (k + 1)) → c.subgroups 0 →* c.subgroups i :=
  Fin.induction (MonoidHom.id _) (fun i f => (c.step i).comp f)

theorem prefix_zero (x : c.subgroups 0) : c.prefixMap 0 x = x := by
  simp only [prefixMap, Fin.induction_zero, MonoidHom.id_apply]

theorem prefix_succ (i : Fin k) (x : c.subgroups 0) :
    c.prefixMap i.succ x = c.step i (c.prefixMap i.castSucc x) := by
  simp only [prefixMap, Fin.induction_succ, MonoidHom.comp_apply]

@[expose] def composite : c.subgroups 0 →* c.subgroups (Fin.last k) :=
  c.prefixMap (Fin.last k)

theorem composite_empty (c : DihedralFusionChain S 0) (x : c.subgroups 0) :
    (c.composite x : G) = x := by
  exact congrArg Subtype.val (c.prefix_zero x)

theorem prefix_coe_eq
    (prefixes : Fin (k + 1) → G) (actors : Fin k → G)
    (hfirst : prefixes 0 = 1)
    (hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i)
    (ha : ∀ i, ∀ x : c.supports i,
      (c.automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i) :
    ∀ i, ∀ x : c.subgroups 0,
      (c.prefixMap i x : G) = (prefixes i)⁻¹ * (x : G) * prefixes i := by
  intro i
  refine Fin.induction ?_ (fun j ih => ?_) i
  · intro x
    rw [hfirst, c.prefix_zero]
    simp only [inv_one, one_mul, mul_one]
  · intro x
    rw [c.prefix_succ, c.step_coe, ha, ih, hstep]
    group

theorem subgroups_eq_rightConjugate
    (prefixes : Fin (k + 1) → G) (actors : Fin k → G)
    (hfirst : prefixes 0 = 1)
    (hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i)
    (ha : ∀ i, ∀ x : c.supports i,
      (c.automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i) :
    ∀ i, c.subgroups i = rightConjugate (c.subgroups 0) (prefixes i) := by
  intro i
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp only [hfirst, rightConjugate, inv_one, Subgroup.conjBy_one]
  · rw [← c.image_eq j,
      support_automorphism_image_eq_rightConjugate (c.domain_le j)
        (c.automorphisms j) (actors j) (ha j), ih, hstep]
    simp only [rightConjugate, mul_inv_rev, Subgroup.conjBy_mul]

theorem exists_realizing_element :
    ∃ g : G, c.subgroups (Fin.last k) = rightConjugate (c.subgroups 0) g ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g := by
  classical
  choose actors _hallowed ha using c.realized
  let prefixes : Fin (k + 1) → G :=
    Fin.induction 1 (fun i g => g * actors i)
  have hfirst : prefixes 0 = 1 := Fin.induction_zero _ _
  have hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i :=
    fun i => Fin.induction_succ _ _ i
  refine ⟨prefixes (Fin.last k),
    c.subgroups_eq_rightConjugate prefixes actors hfirst hstep ha (Fin.last k), ?_⟩
  exact c.prefix_coe_eq prefixes actors hfirst hstep ha (Fin.last k)

end DihedralFusionChain

end CFSG.GorensteinWalter
