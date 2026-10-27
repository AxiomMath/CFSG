module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Certificates

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def schreierElement (b : X) (t : MulAction.orbit G b → G)
    (x : MulAction.orbit G b) (s : G) : G :=
  (t (s • x))⁻¹ * s * t x

@[expose] def schreierGeneratorSet (b : X) (S : Set G)
    (t : MulAction.orbit G b → G) : Set G :=
  {u | ∃ (x : MulAction.orbit G b) (s : G),
    s ∈ S ∪ (fun g : G => g⁻¹) '' S ∧ u = schreierElement b t x s}

theorem schreierElement_mul (b : X) (t : MulAction.orbit G b → G)
    (x : MulAction.orbit G b) (g h : G) :
    schreierElement b t x (g * h) =
      schreierElement b t (h • x) g * schreierElement b t x h := by
  simp only [schreierElement, mul_smul]
  group

theorem schreierElement_mem_stabilizer (b : X) (t : MulAction.orbit G b → G)
    (ht : ∀ x, t x • b = (x : X)) (x : MulAction.orbit G b) (s : G) :
    schreierElement b t x s ∈ MulAction.stabilizer G b := by
  apply MulAction.mem_stabilizer_iff.2
  rw [schreierElement, mul_smul, mul_smul, ht x]
  change (t (s • x))⁻¹ • ((s • x : MulAction.orbit G b) : X) = b
  rw [← ht (s • x), inv_smul_smul]

theorem schreierElement_mem_closure (b : X) (S : Set G)
    (t : MulAction.orbit G b → G) (g : G) (hg : g ∈ Subgroup.closure S)
    (x : MulAction.orbit G b) :
    schreierElement b t x g ∈ Subgroup.closure (schreierGeneratorSet b S t) := by
  let U := Subgroup.closure (schreierGeneratorSet b S t)
  refine Subgroup.closure_induction_left
    (p := fun g _ => ∀ x : MulAction.orbit G b, schreierElement b t x g ∈ U)
    ?_ ?_ ?_ hg x
  · intro y
    simp [schreierElement]
  · intro s hs h _ ih y
    rw [schreierElement_mul]
    exact U.mul_mem (Subgroup.subset_closure ⟨h • y, s, Or.inl hs, rfl⟩) (ih y)
  · intro s hs h _ ih y
    rw [schreierElement_mul]
    exact U.mul_mem
      (Subgroup.subset_closure ⟨h • y, s⁻¹, Or.inr ⟨s, hs, rfl⟩, rfl⟩) (ih y)

theorem schreier_stabilizer_generators (b : X) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (t : MulAction.orbit G b → G)
    (ht : ∀ x, t x • b = (x : X))
    (ht1 : t ⟨b, MulAction.mem_orbit_self b⟩ = 1) :
    Subgroup.closure (schreierGeneratorSet b S t) = MulAction.stabilizer G b := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨x, s, _, rfl⟩
    exact schreierElement_mem_stabilizer b t ht x s
  · intro g hg
    have hgen : g ∈ Subgroup.closure S := by
      rw [hS]
      exact Subgroup.mem_top g
    have hroot : g • (⟨b, MulAction.mem_orbit_self b⟩ : MulAction.orbit G b) =
        ⟨b, MulAction.mem_orbit_self b⟩ :=
      Subtype.ext (MulAction.mem_stabilizer_iff.1 hg)
    simpa only [schreierElement, hroot, ht1, inv_one, one_mul, mul_one] using
      schreierElement_mem_closure b S t g hgen ⟨b, MulAction.mem_orbit_self b⟩

theorem schreier_stabilizer_generators_subgroup (H : Subgroup G) (b : X)
    (S : Set H) (hS : Subgroup.closure S = ⊤) (t : MulAction.orbit H b → H)
    (ht : ∀ x, t x • b = (x : X))
    (ht1 : t ⟨b, MulAction.mem_orbit_self b⟩ = 1) :
    Subgroup.closure (H.subtype '' schreierGeneratorSet b S t) =
      H ⊓ MulAction.stabilizer G b := by
  rw [← MonoidHom.map_closure, schreier_stabilizer_generators b S hS t ht ht1]
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, hh⟩
  · rintro ⟨hg, hb⟩
    exact ⟨⟨g, hg⟩, hb, rfl⟩

theorem schreier_subtype_generators_generate (S : Set G) :
    Subgroup.closure ((Subgroup.closure S).subtype ⁻¹' S) = ⊤ := by
  apply Subgroup.map_subtype_inj.1
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  congr 1
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hg
    exact ⟨⟨g, Subgroup.subset_closure hg⟩, hg, rfl⟩

theorem schreier_generated_stabilizer_generators (b : X) (S : Set G)
    (t : MulAction.orbit (Subgroup.closure S) b → Subgroup.closure S)
    (ht : ∀ x, t x • b = (x : X))
    (ht1 : t ⟨b, MulAction.mem_orbit_self b⟩ = 1) :
    Subgroup.closure ((Subgroup.closure S).subtype ''
      schreierGeneratorSet b ((Subgroup.closure S).subtype ⁻¹' S) t) =
        Subgroup.closure S ⊓ MulAction.stabilizer G b :=
  schreier_stabilizer_generators_subgroup (Subgroup.closure S) b
    ((Subgroup.closure S).subtype ⁻¹' S) (schreier_subtype_generators_generate S) t ht ht1

end CFSG.Certificates
