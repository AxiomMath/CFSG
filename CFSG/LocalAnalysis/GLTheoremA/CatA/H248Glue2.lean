module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open
open scoped commutatorElement

instance centerCommGroup (E : Type) [Group E] : CommGroup (Subgroup.center E) :=
  { (inferInstance : Group (Subgroup.center E)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1) }

theorem eq_one_of_hom_to_comm {E A : Type} [Group E] [CommGroup A] (hperf : commutator E = ⊤)
    (f : E →* A) (x : E) : f x = 1 := by
  have hker : commutator E ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hx : x ∈ commutator E := by rw [hperf]; exact Subgroup.mem_top x
  exact (MonoidHom.mem_ker).mp (hker hx)

theorem center_eq_comap_of_perfect {E F : Type} [Group E] [Group F] (φ : E →* F)
    (hφ : Function.Surjective φ) (hperf : commutator E = ⊤)
    (hker : ∀ x : E, φ x = 1 → x ∈ Subgroup.center E) :
    Subgroup.center E = (Subgroup.center F).comap φ := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    rw [Subgroup.mem_center_iff] at hx
    intro y
    obtain ⟨e, rfl⟩ := hφ y
    rw [← map_mul, ← map_mul, hx e]
  · intro hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff] at hx
    have hcen : ∀ e : E, ⁅x, e⁆ ∈ Subgroup.center E := by
      intro e
      apply hker
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hx (φ e)).symm
    let ψ : E →* Subgroup.center E :=
      { toFun := fun e => ⟨⁅x, e⁆, hcen e⟩
        map_one' := by
          apply Subtype.ext
          simp [commutatorElement_def]
        map_mul' := by
          intro a b
          apply Subtype.ext
          have hc : x * b * x⁻¹ * b⁻¹ ∈ Subgroup.center E := hcen b
          have hcomm := Subgroup.mem_center_iff.mp hc a
          show ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
          calc x * (a * b) * x⁻¹ * (a * b)⁻¹
              = (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
            _ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by rw [hcomm]; group }
    have hall : ∀ e : E, ⁅x, e⁆ = 1 := by
      intro e
      have h2 : ψ e = 1 := eq_one_of_hom_to_comm hperf ψ e
      exact congrArg Subtype.val h2
    exact Subgroup.mem_center_iff.mpr (fun g => (commutatorElement_eq_one_iff_mul_comm.mp (hall g)).symm)

theorem map_center_le {E : Type} [Group E] (α : E ≃* E) :
    Subgroup.map α.toMonoidHom (Subgroup.center E) ≤ Subgroup.center E := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := α.surjective g
  have hz' := Subgroup.mem_center_iff.mp hz g'
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, hz']

theorem map_center_eq {E : Type} [Group E] (α : E ≃* E) :
    Subgroup.map α.toMonoidHom (Subgroup.center E) = Subgroup.center E := by
  apply le_antisymm (map_center_le α)
  intro y hy
  have h1 : α.symm y ∈ Subgroup.center E :=
    map_center_le α.symm (Subgroup.mem_map_of_mem _ hy)
  exact ⟨α.symm y, h1, by simp⟩

def centerQuotAut {E : Type} [Group E] (α : E ≃* E) :
    (E ⧸ Subgroup.center E) ≃* (E ⧸ Subgroup.center E) :=
  QuotientGroup.congr (Subgroup.center E) (Subgroup.center E) α (map_center_eq α)

theorem centerQuotAut_mk {E : Type} [Group E] (α : E ≃* E) (x : E) :
    centerQuotAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  QuotientGroup.congr_mk _ _ α (map_center_eq α) x

def centerQuotAutHom (E : Type) [Group E] : MulAut E →* MulAut (E ⧸ Subgroup.center E) where
  toFun α := centerQuotAut α
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.one_apply]
    exact centerQuotAut_mk (1 : MulAut E) x
  map_mul' := by
    intro α β
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.mul_apply]
    show centerQuotAut (α * β) (QuotientGroup.mk x) = centerQuotAut α (centerQuotAut β (QuotientGroup.mk x))
    rw [centerQuotAut_mk, centerQuotAut_mk, centerQuotAut_mk, MulAut.mul_apply]

theorem centerQuotAutHom_injective (E : Type) [Group E] (hperf : commutator E = ⊤) :
    Function.Injective (centerQuotAutHom E) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hmem : ∀ y : E, y⁻¹ * α y ∈ Subgroup.center E := by
    intro y
    have h1 : centerQuotAut α (QuotientGroup.mk y) = QuotientGroup.mk y := by
      have := congrArg (fun f : MulAut (E ⧸ Subgroup.center E) => f (QuotientGroup.mk y)) hα
      exact this
    rw [centerQuotAut_mk] at h1
    exact QuotientGroup.eq.mp h1.symm
  let g : E →* Subgroup.center E :=
    { toFun := fun y => ⟨y⁻¹ * α y, hmem y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        have hc : y⁻¹ * α y ∈ Subgroup.center E := hmem y
        have hcomm := Subgroup.mem_center_iff.mp hc z
        have key : z⁻¹ * (y⁻¹ * α y) * z = y⁻¹ * α y := by
          rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
        show (y * z)⁻¹ * α (y * z) = (y⁻¹ * α y) * (z⁻¹ * α z)
        rw [map_mul]
        calc (y * z)⁻¹ * (α y * α z) = z⁻¹ * (y⁻¹ * α y) * α z := by group
          _ = z⁻¹ * (y⁻¹ * α y) * (z * (z⁻¹ * α z)) := by group
          _ = (z⁻¹ * (y⁻¹ * α y) * z) * (z⁻¹ * α z) := by group
          _ = (y⁻¹ * α y) * (z⁻¹ * α z) := by rw [key] }
  ext y
  have h3 : g y = 1 := eq_one_of_hom_to_comm hperf g y
  have h4 : y⁻¹ * α y = 1 := congrArg Subtype.val h3
  have h5 : α y = y := by
    have := congrArg (fun t => y * t) h4
    simpa using this
  simpa using h5

def mulAutConjHom {S T : Type} [Group S] [Group T] (e : S ≃* T) : MulAut S →* MulAut T where
  toFun α := e.symm.trans (α.trans e)
  map_one' := by
    ext t
    simp
  map_mul' := by
    intro α β
    ext t
    simp

theorem mulAutConjHom_injective {S T : Type} [Group S] [Group T] (e : S ≃* T) :
    Function.Injective (mulAutConjHom e) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  ext s
  have h1 := congrArg (fun f : MulAut T => f (e s)) hα
  simp [mulAutConjHom] at h1
  simpa using h1

theorem exists_elemAbelian_mulAut_of_perfect {E T : Type} [Group E] [Group T]
    (hperf : commutator E = ⊤) (e : (E ⧸ Subgroup.center E) ≃* T) {p : ℕ}
    (A : Subgroup (MulAut E)) (hA : CFSG.Open.IsElemAbelian p A) :
    ∃ A' : Subgroup (MulAut T), CFSG.Open.IsElemAbelian p A' ∧ Nat.card A' = Nat.card A := by
  let F : MulAut E →* MulAut T := (mulAutConjHom e).comp (centerQuotAutHom E)
  have hF : Function.Injective F := by
    intro a b hab
    exact centerQuotAutHom_injective E hperf (mulAutConjHom_injective e hab)
  refine ⟨A.map F, isElemAbelian_map F hF hA, ?_⟩
  exact (Nat.card_congr (Subgroup.equivMapOfInjective A F hF).toEquiv).symm

end CFSG.LocalAnalysis.GLTheoremA.H248
