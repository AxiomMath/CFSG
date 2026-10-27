module

public import CFSG.Assembly.OddCoreBalance

public section

namespace CFSG.Assembly.Dichotomy

variable {G X : Type*} [Group G] [Group X]

@[expose] def involutionOddCore (a : G) : Subgroup G :=
  (oddCore (Subgroup.centralizer ({a} : Set G))).map
    (Subgroup.centralizer ({a} : Set G)).subtype

@[expose] def oddCoreSpan (A : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), involutionOddCore a

@[simp] theorem oddCoreSpan_bot : oddCoreSpan (⊥ : Subgroup G) = ⊥ := by
  apply bot_unique
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_
  exact False.elim (hne (Subgroup.mem_bot.mp ha))

theorem involutionOddCore_le_span (A : Subgroup G) {a : G} (ha : a ∈ A) (hne : a ≠ 1) :
    involutionOddCore a ≤ oddCoreSpan A :=
  le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le hne le_rfl))

theorem oddCoreSpan_mono {A B : Subgroup G} (hBA : B ≤ A) :
    oddCoreSpan B ≤ oddCoreSpan A := by
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hne => ?_
  exact involutionOddCore_le_span A (hBA hb) hne

private theorem centralizer_singleton_map (e : G ≃* X) (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp hx

theorem involutionOddCore_map (e : G ≃* X) (a : G) :
    (involutionOddCore a).map e.toMonoidHom = involutionOddCore (e a) := by
  let C := Subgroup.centralizer ({a} : Set G)
  let D := Subgroup.centralizer ({e a} : Set X)
  let f : C ≃* D := (e.subgroupMap C).trans
    (MulEquiv.subgroupCongr (centralizer_singleton_map e a))
  have hf : D.subtype.comp f.toMonoidHom = e.toMonoidHom.comp C.subtype := by
    ext x
    rfl
  have hcore : (oddCore C).map f.toMonoidHom = oddCore D := by
    rw [oddCore_eq_pPrimeCore, oddCore_eq_pPrimeCore]
    exact CFSG.pPrimeCore_map_iso 2 f
  change ((oddCore C).map C.subtype).map e.toMonoidHom = (oddCore D).map D.subtype
  rw [Subgroup.map_map, ← hf, ← Subgroup.map_map, hcore]

theorem oddCoreSpan_map (e : G ≃* X) (A : Subgroup G) :
    (oddCoreSpan A).map e.toMonoidHom = oddCoreSpan (A.map e.toMonoidHom) := by
  simp only [oddCoreSpan, Subgroup.map_iSup, involutionOddCore_map]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_
    exact le_iSup_of_le (e a)
      (le_iSup_of_le (Subgroup.mem_map_of_mem e.toMonoidHom ha)
        (le_iSup_of_le (fun h => hne (e.injective (by simpa using h))) le_rfl))
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun hne => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact le_iSup_of_le a (le_iSup_of_le ha
      (le_iSup_of_le (fun h => hne (by rw [h, map_one])) le_rfl))

theorem oddCoreSpan_conj (A : Subgroup G) (g : G) :
    oddCoreSpan (A.map (MulAut.conj g⁻¹).toMonoidHom) =
      (oddCoreSpan A).map (MulAut.conj g⁻¹).toMonoidHom :=
  (oddCoreSpan_map (MulAut.conj g⁻¹) A).symm

theorem normalizer_le_oddCoreSpan_normalizer (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (oddCoreSpan A : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have heq := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  simpa only [MulEquiv.toMonoidHom_eq_coe, heq] using oddCoreSpan_map (MulAut.conj g) A

end CFSG.Assembly.Dichotomy
