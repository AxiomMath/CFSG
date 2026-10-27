module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModRep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModWeyl
public import CFSG.Quasithin.Background.SmithCurtisChevType

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

abbrev Idx26 : Type := {i : Ix // i ≠ i14}

instance : Nonempty Idx26 := ⟨⟨i0, by decide⟩⟩

@[expose] def jFun (w : Idx26 → K) : Ix → K := fun i =>
  if h : i = i14 then w ⟨i12, by decide⟩ + w ⟨i13, by decide⟩ else w ⟨i, h⟩

@[expose] def jExt : (Idx26 → K) →ₗ[K] (Fin e6Data.d →₀ K) where
  toFun w := Finsupp.equivFunOnFinite.symm (jFun K w)
  map_add' v w := by
    refine Finsupp.ext fun i => ?_
    by_cases h : i = i14 <;> simp [jFun, h] <;> ring
  map_smul' c w := by
    refine Finsupp.ext fun i => ?_
    by_cases h : i = i14 <;> simp [jFun, h] <;> ring

@[expose] def pRes : (Fin e6Data.d →₀ K) →ₗ[K] (Idx26 → K) where
  toFun v i := v i.1
  map_add' v w := rfl
  map_smul' c v := rfl

theorem pRes_jExt (w : Idx26 → K) : pRes K (jExt K w) = w := by
  funext i
  change jFun K w i.1 = w i
  simp [jFun, i.2]

theorem jExt_injective : Function.Injective (jExt K) :=
  Function.LeftInverse.injective (pRes_jExt K)

theorem fT_jExt (w : Idx26 → K) : fT K (jExt K w) = 0 := by
  rw [fT_eq]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  change jFun K w i12 + jFun K w i13 + jFun K w i14 = 0
  have h12 : i12 ≠ i14 := by decide
  have h13 : i13 ≠ i14 := by decide
  simp only [jFun, h12, h13, dite_false, dite_true]
  linear_combination (w ⟨i12, h12⟩ + w ⟨i13, h13⟩) * h2

theorem jExt_pRes (v : Fin e6Data.d →₀ K) (hv : fT K v = 0) : jExt K (pRes K v) = v := by
  refine Finsupp.ext fun i => ?_
  rw [fT_eq] at hv
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  change jFun K (pRes K v) i = v i
  by_cases h : i = i14
  · subst h
    simp only [jFun, dite_true]
    change v i12 + v i13 = v i14
    linear_combination hv - v i14 * h2
  · simp only [jFun, h, dite_false]
    rfl

theorem fT_endo_f4Embed (θ : adjointGroup Tag.F4 K ≃* adjointGroup Tag.F4 K)
    (g : adjointGroup Tag.F4 K) (v : Fin e6Data.d →₀ K) :
    fT K (e6Data_valid.endo K (f4Embed K θ g) v) = fT K v :=
  fT_endo e6Data_valid (f4Embed_mem K θ g) v

@[expose] def m26Rep : Representation K (adjointGroup Tag.F4 K) (Idx26 → K) where
  toFun g := pRes K ∘ₗ (e6Data_valid.endo K (f4Embed K (idF4 K) g)) ∘ₗ jExt K
  map_one' := LinearMap.ext fun w => by
    simp only [map_one, MinData.Valid.endo_one, LinearMap.comp_apply, Module.End.one_apply,
      pRes_jExt, Module.End.one_eq_id, LinearMap.id_apply]
  map_mul' g h := LinearMap.ext fun w => by
    simp only [map_mul, MinData.Valid.endo_mul, LinearMap.comp_apply, Module.End.mul_apply]
    rw [jExt_pRes K _ (by rw [fT_endo_f4Embed, fT_jExt])]

theorem m26Rep_apply (g : adjointGroup Tag.F4 K) (w : Idx26 → K) :
    m26Rep K g w = pRes K (e6Data_valid.endo K (f4Embed K (idF4 K) g) (jExt K w)) := rfl

theorem jExt_m26Rep (g : adjointGroup Tag.F4 K) (w : Idx26 → K) :
    jExt K (m26Rep K g w) = e6Data_valid.endo K (f4Embed K (idF4 K) g) (jExt K w) := by
  rw [m26Rep_apply, jExt_pRes K _ (by rw [fT_endo_f4Embed, fT_jExt])]

@[expose] def y26 : Idx26 → K := pRes K (Finsupp.single i0 1)

theorem jExt_y26 : jExt K (y26 K) = Finsupp.single i0 (1 : K) :=
  jExt_pRes K _ (fT_single_i0 K)

theorem y26_ne_zero : y26 K ≠ 0 := fun h => by
  have := jExt_y26 K
  rw [h, map_zero] at this
  have h2 := congrArg (fun v : Fin e6Data.d →₀ K => v i0) this
  simp at h2

theorem m26Rep_fixed_smul {x : Idx26 → K}
    (hx : ∀ (j : Fin Tag.F4.rank) (c : K), m26Rep K (xC Tag.F4 K j c) x = x) :
    ∃ c : K, x = c • y26 K := by
  have h1 : ∀ (j : Fin Tag.F4.rank) (c : K),
      e6Data_valid.endo K (f4Embed K (idF4 K) (xC Tag.F4 K j c)) (jExt K x) = jExt K x := by
    intro j c
    rw [← jExt_m26Rep, hx j c]
  obtain ⟨c, hc⟩ := eq_smul_i0_of_fixed K (jExt K x) (fT_jExt K x) h1
  refine ⟨c, jExt_injective K ?_⟩
  rw [hc, map_smul, jExt_y26]

theorem orbitSpan_m26 : orbitSpan (m26Rep K) (y26 K) = ⊤ := by
  have h0 : Finsupp.single i0 (1 : K) ∈ (orbitSpan (m26Rep K) (y26 K)).map (jExt K) :=
    ⟨y26 K, mem_orbitSpan_self _ _, jExt_y26 K⟩
  have hstep : ∀ k < 72, ∀ u ∈ (orbitSpan (m26Rep K) (y26 K)).map (jExt K),
      e6Data_valid.endo K (gen e6Data_valid K (e6root k) 1) u - u ∈
        (orbitSpan (m26Rep K) (y26 K)).map (jExt K) := by
    intro k hk u hu
    obtain ⟨w, hw, rfl⟩ := hu
    have hemb := f4Embed_symm_apply K
      ⟨gen e6Data_valid K (e6root k) 1, gen_mem_F4in27 _ _ (isRoot_e6root hk) 1⟩
    set a : adjointGroup Tag.F4 K := f4in27Equiv K
      ⟨gen e6Data_valid K (e6root k) 1, gen_mem_F4in27 _ _ (isRoot_e6root hk) 1⟩ with ha
    have hst := orbitSpan_stable (m26Rep K) (y26 K) a hw
    refine ⟨m26Rep K a w - w, Submodule.sub_mem _ hst hw, ?_⟩
    rw [map_sub, jExt_m26Rep, hemb]
  have hker := ker_le_of_closed K _ h0 hstep
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨w1, hw1, h1⟩ := hker (LinearMap.mem_ker.2 (fT_jExt K w))
  rwa [← jExt_injective K h1]

theorem isSimpleRep_m26 : IsSimpleRep (m26Rep K) :=
  (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').isSimpleRep_of_fixU (p := 2) (m26Rep K)
    (y := y26 K)
    (fun x hx => m26Rep_fixed_smul K fun j c =>
      hx (xC Tag.F4 K j c) ((chevDatum Tag.F4 K 2 exists_weyl_neg_F4').X_le j
        (xC_mem_X (hw := exists_weyl_neg_F4') j c)))
    (orbitSpan_m26 K)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
