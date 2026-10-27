module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Sound
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8TorusTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Rec
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Alg

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def flOf (f : Fin 4 → ZMod 5) : List ℤ := List.ofFn fun i => ((f i).val : ℤ)

@[expose] def pv (f : Fin 4 → ZMod 5) : Fin 4 :=
  ⟨pivot5 (flOf f) % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] def keyV (f g : Fin 4 → ZMod 5) : Fin 4 → ZMod 5 := g - g (pv f) • f

instance normF_decidable (f : Fin 4 → ZMod 5) : Decidable (NormF f) := by
  unfold NormF
  infer_instance

theorem normF_pivot_aux : ∀ a b c d : ZMod 5, NormF ![a, b, c, d] →
    ![a, b, c, d] = 0 ∨ ![a, b, c, d] (pv ![a, b, c, d]) = 1 := by
  decide +kernel

theorem normF_pivot {f : Fin 4 → ZMod 5} (hN : NormF f) : f = 0 ∨ f (pv f) = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ZMod 5, f = ![a, b, c, d] :=
    ⟨f 0, f 1, f 2, f 3, by funext i; fin_cases i <;> rfl⟩
  exact normF_pivot_aux a b c d hN

theorem flOf_mem_allF5_aux : ∀ a b c d : ZMod 5, NormF ![a, b, c, d] →
    flOf ![a, b, c, d] ∈ allF5 := by
  decide +kernel

theorem flOf_mem_allF5 {f : Fin 4 → ZMod 5} (hN : NormF f) : flOf f ∈ allF5 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ZMod 5, f = ![a, b, c, d] :=
    ⟨f 0, f 1, f 2, f 3, by funext i; fin_cases i <;> rfl⟩
  exact flOf_mem_allF5_aux a b c d hN

theorem length_flOf (f : Fin 4 → ZMod 5) : (flOf f).length = 4 := by
  simp [flOf]

theorem getElem_flOf (g : Fin 4 → ZMod 5) {k : ℕ} (hk : k < (flOf g).length) :
    (flOf g)[k] = ((g ⟨k, by simpa [length_flOf] using hk⟩).val : ℤ) := by
  simp only [flOf, List.getElem_ofFn]

theorem getD_flOf (g : Fin 4 → ZMod 5) (i : Fin 4) : (flOf g).getD i 0 = ((g i).val : ℤ) := by
  have h : (i : ℕ) < (flOf g).length := by rw [length_flOf]; exact i.2
  rw [List.getD_eq_getElem _ _ h, getElem_flOf]

theorem flOf_injective : Function.Injective flOf := by
  intro f g h
  funext i
  have h1 := congrArg (fun l : List ℤ => l.getD i 0) h
  simp only [getD_flOf] at h1
  exact ZMod.val_injective 5 (by exact_mod_cast h1)

theorem flOf_zero : flOf (0 : Fin 4 → ZMod 5) = List.replicate 4 0 := by
  simp [flOf, List.ofFn_const]

theorem pivot5_lt_four (f : Fin 4 → ZMod 5) : pivot5 (flOf f) < 4 := by
  unfold pivot5
  rw [length_flOf]
  cases hfd : (List.range 4).find? fun i => (flOf f).getD i 0 != 0 with
  | none => simp
  | some i =>
    have := List.mem_of_find?_eq_some hfd
    simpa using this

theorem pv_val (f : Fin 4 → ZMod 5) : ((pv f : Fin 4) : ℕ) = pivot5 (flOf f) :=
  Nat.mod_eq_of_lt (pivot5_lt_four f)

theorem val_keyV (f g : Fin 4 → ZMod 5) (i : Fin 4) :
    ((keyV f g i).val : ℤ) =
      (((g i).val : ℤ) - ((g (pv f)).val : ℤ) * ((f i).val : ℤ)) % 5 := by
  have h : keyV f g i =
      ((((g i).val : ℤ) - ((g (pv f)).val : ℤ) * ((f i).val : ℤ) : ℤ) : ZMod 5) := by
    simp [keyV]
  rw [h, ZMod.val_intCast] <;> rfl

theorem key5_flOf (f g : Fin 4 → ZMod 5) : key5 (flOf f) (flOf g) = flOf (keyV f g) := by
  refine List.ext_getElem (by simp [key5, length_flOf]) fun k h1 h2 => ?_
  have hk : k < 4 := by simpa [length_flOf] using h2
  have hp : (flOf g).getD (pivot5 (flOf f)) 0 = ((g (pv f)).val : ℤ) := by
    rw [← getD_flOf g (pv f), pv_val]
  simp only [key5, List.getElem_zipWith, hp]
  rw [getElem_flOf g, getElem_flOf f, getElem_flOf (keyV f g)]
  exact (val_keyV f g ⟨k, hk⟩).symm

theorem ofFn_getD_eq5 {n : ℕ} {b : List ℤ} (hb : b.length = n) :
    List.ofFn (fun i : Fin n => b.getD i 0) = b := by
  refine List.ext_getElem (by simp [hb]) fun k h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

theorem rr5_ofFn8 (v : Fin 8 → ℤ) : rr5 (List.ofFn v) = flOf (rrv v) := by
  have hlen : ∀ k, k < 4 → (e5Rows.getD k []).length = 8 := by decide
  refine List.ext_getElem (by simp [rr5, e5Rows, length_flOf]) fun k h1 h2 => ?_
  have hk : k < 4 := by simpa [length_flOf] using h2
  have hk' : k < e5Rows.length := by simpa [e5Rows] using hk
  have hdot : dotZ (e5Rows.getD k []) (List.ofFn v) =
      ∑ j : Fin 8, (e5Rows.getD k []).getD j 0 * v j := by
    have h := dotZ_ofFn (fun j : Fin 8 => (e5Rows.getD k []).getD j 0) v
    rwa [ofFn_getD_eq5 (hlen k hk)] at h
  have hrrv : rrv v ⟨k, hk⟩ =
      ((∑ j : Fin 8, (e5Rows.getD k []).getD j 0 * v j : ℤ) : ZMod 5) := by
    simp [rrv, pairZ, E5]
  have hL : (rr5 (List.ofFn v))[k] = (∑ j : Fin 8, (e5Rows.getD k []).getD j 0 * v j) % 5 := by
    simp only [rr5, List.getElem_map]
    rw [← hdot, List.getD_eq_getElem _ _ hk']
  refine hL.trans ?_
  rw [getElem_flOf]
  show _ = ((rrv v ⟨k, hk⟩).val : ℤ)
  rw [hrrv, ZMod.val_intCast] <;> rfl

theorem rr5_ofFn (v : Fin Tag.E8.rank → ℤ) : rr5 (List.ofFn v) = flOf (rrv v) := rr5_ofFn8 v

theorem fib5_ofFn (f : Fin 4 → ZMod 5) (v : Fin Tag.E8.rank → ℤ) :
    fib5 (flOf f) (List.ofFn v) = flOf (keyV f (rrv v)) := by
  rw [fib5, rr5_ofFn, key5_flOf]

theorem keyV_eq_zero_iff {f g : Fin 4 → ZMod 5} (hfp : f = 0 ∨ f (pv f) = 1) :
    keyV f g = 0 ↔ ∃ t : ZMod 5, g = t • f := by
  constructor
  · intro h
    refine ⟨g (pv f), ?_⟩
    have : g - g (pv f) • f = 0 := h
    exact sub_eq_zero.1 this
  · rintro ⟨t, rfl⟩
    rcases hfp with rfl | hp
    · simp [keyV]
    · funext i
      simp [keyV, hp]

theorem keyV_eq_iff {f g g' : Fin 4 → ZMod 5} (hfp : f = 0 ∨ f (pv f) = 1) :
    keyV f g = keyV f g' ↔ ∃ t : ZMod 5, g' = g + t • f := by
  constructor
  · intro h
    refine ⟨g' (pv f) - g (pv f), ?_⟩
    funext i
    have := congrFun h i
    simp only [keyV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -this
  · rintro ⟨t, rfl⟩
    rcases hfp with rfl | hp
    · simp [keyV]
    · funext i
      simp [keyV, hp]
      ring

section Family

variable {L : Type} [Field L]

abbrev famIdx (f : Fin 4 → ZMod 5) : Type := {c : Fin 4 → ZMod 5 // f ⬝ᵥ c = 0}

@[expose] def famPar (ζ : Lˣ) (f : Fin 4 → ZMod 5) : famIdx f → Fin Tag.E8.rank → Lˣ :=
  fun c => torV5 ζ (xc c.1)

theorem rootChar_famPar {ζ : Lˣ} (h5 : ζ ^ 5 = 1) {f : Fin 4 → ZMod 5} (c : famIdx f)
    (v : Fin Tag.E8.rank → ℤ) : rootChar (famPar ζ f c) v = chiZ ζ (c.1 ⬝ᵥ rrv v) := by
  rw [famPar, rootChar_torV5 h5]
  exact congrArg (chiZ ζ) (pairZ_xc c.1 v)


theorem familyKernel_famPar {ζ : Lˣ} (hζ : orderOf ζ = 5) {f : Fin 4 → ZMod 5} (hN : NormF f) :
    familyKernel (famPar ζ f) = famK' (flOf f) := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hfp : f = 0 ∨ f (pv f) = 1 := normF_pivot hN
  have hfp' : f = 0 ∨ ∃ p, f p = 1 := hfp.imp id fun h => ⟨_, h⟩
  ext γ
  constructor
  · rintro ⟨hγ, hall⟩
    refine ⟨hγ, ?_⟩
    rw [fib5_ofFn, ← flOf_zero]
    congr 1
    refine (keyV_eq_zero_iff hfp).2 ?_
    refine (perp_iff f (rrv γ) hfp').1 fun c hc => ?_
    have h1 := hall ⟨c, hc⟩
    rw [rootChar_famPar h5] at h1
    have h2 : c ⬝ᵥ rrv γ = 0 :=
      chiZ_injective hζ (h1.trans (chiZ_zero ζ).symm)
    rw [dotProduct_comm]
    exact h2
  · rintro ⟨hγ, hf⟩
    refine ⟨hγ, fun c => ?_⟩
    rw [fib5_ofFn, ← flOf_zero] at hf
    have h0 : keyV f (rrv γ) = 0 := flOf_injective hf
    obtain ⟨t, ht⟩ := (keyV_eq_zero_iff hfp).1 h0
    rw [rootChar_famPar h5]
    have : c.1 ⬝ᵥ rrv γ = 0 := by
      rw [ht, dotProduct_smul, dotProduct_comm, c.2, smul_zero]
    rw [this, chiZ_zero]

theorem familyStabilizer_famPar_subset {ζ : Lˣ} (hζ : orderOf ζ = 5) {f : Fin 4 → ZMod 5}
    (hN : NormF f) : familyStabilizer (famPar ζ f) ⊆ famS' (flOf f) := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hfp : f = 0 ∨ f (pv f) = 1 := normF_pivot hN
  have hfp' : f = 0 ∨ ∃ p, f p = 1 := hfp.imp id fun h => ⟨_, h⟩
  intro u hu i
  rw [fib5_ofFn, fib5_ofFn]
  congr 1
  refine (keyV_eq_iff hfp).2 ?_
  have hperp : ∀ c : Fin 4 → ZMod 5, f ⬝ᵥ c = 0 →
      (rrv (u • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) -
        rrv (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) ⬝ᵥ c = 0 := by
    intro c hc
    have h1 := hu ⟨c, hc⟩ (Pi.single i 1)
    rw [rootChar_famPar h5, rootChar_famPar h5] at h1
    have h2 : c ⬝ᵥ rrv (u • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) =
        c ⬝ᵥ rrv (Pi.single i 1 : Fin Tag.E8.rank → ℤ) := chiZ_injective hζ h1
    rw [sub_dotProduct, dotProduct_comm _ c, dotProduct_comm _ c, h2, sub_self]
  obtain ⟨t, ht⟩ := (perp_iff f _ hfp').1 hperp
  exact ⟨-t, eq_add_neg_smul_of_sub_eq ht⟩

end Family

section LeafData

variable {L : Type} [Field L]

@[expose] def LeafD1 {ι : Type} (a : ι → Fin Tag.E8.rank → Lˣ) : Prop :=
  familyKernel a = ∅ ∧ ∀ u ∈ familyStabilizer a, u = 1

@[expose] def LeafD2 {ι : Type} (a : ι → Fin Tag.E8.rank → Lˣ) : Prop :=
  ∃ α : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 α ∧
    familyKernel a = {α, -α, e8PhiFourWeyl • α, -(e8PhiFourWeyl • α)} ∧
    ∀ u ∈ familyStabilizer a, u = 1 ∨ u = rootReflection α ∨
      u = rootReflection (e8PhiFourWeyl • α) ∨
      u = rootReflection α * rootReflection (e8PhiFourWeyl • α)

theorem matVecL_ofFn (v : Fin Tag.E8.rank → ℤ) :
    matVecL e8FourMat (List.ofFn v) = List.ofFn (e8PhiFourWeyl • v) := by
  have hr : Tag.E8.rank = 8 := rfl
  have hrow : ∀ k, k < 8 → (e8FourMat.getD k []).length = 8 := by decide
  have hlenM : e8FourMat.length = 8 := by decide
  refine List.ext_getElem ?_ fun k h1 h2 => ?_
  · simp only [matVecL, List.length_map, List.length_ofFn, hlenM]
    exact hr.symm
  · have hk : k < 8 := by
      have h := h1
      simp only [matVecL, List.length_map, hlenM] at h
      exact h
    have hkr : k < Tag.E8.rank := hk
    have hk8 : k < e8FourMat.length := by rw [hlenM]; exact hk
    have hrowk : (e8FourMat.getD k []).length = Tag.E8.rank := hrow k hk
    have hd : dotZ (e8FourMat.getD k []) (List.ofFn v) =
        ∑ j : Fin Tag.E8.rank, (e8FourMat.getD k []).getD j 0 * v j := by
      have h := dotZ_ofFn (fun j : Fin Tag.E8.rank => (e8FourMat.getD k []).getD j 0) v
      rwa [ofFn_getD_eq5 hrowk] at h
    have hRHS : (List.ofFn (e8PhiFourWeyl • v))[k]'h2 = (e8M *ᵥ v) ⟨k, hkr⟩ :=
      (List.getElem_ofFn h2).trans (congrFun (smul_e8PhiFourWeyl v) ⟨k, hkr⟩)
    have hLHS : (matVecL e8FourMat (List.ofFn v))[k]'h1 =
        dotZ (e8FourMat.getD k []) (List.ofFn v) := by
      simp only [matVecL, List.getElem_map]
      rw [List.getD_eq_getElem _ _ hk8]
    refine hLHS.trans (hd.trans (Eq.trans ?_ hRHS.symm))
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => rfl

theorem leafData_of_normF {ζ : Lˣ} (hζ : orderOf ζ = 5) {f : Fin 4 → ZMod 5} (hN : NormF f) :
    LeafD1 (famPar ζ f) ∨ LeafD2 (famPar ζ f) := by
  have hOK : famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
      ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat (flOf f) = true :=
    List.all_eq_true.1 famOK5_all _ (flOf_mem_allF5 hN)
  have hker := familyKernel_famPar hζ hN
  have hsub := familyStabilizer_famPar_subset hζ hN
  rcases famData_of_famOK5 (flOf f) hOK with ⟨hK0, hS1⟩ | ⟨α, β, hα, hβ, hβl, hK, hS⟩
  · left
    exact ⟨hker.trans hK0, fun u hu => hS1 u (hsub hu)⟩
  · right
    have hβw : β = e8PhiFourWeyl • α := by
      apply List.ofFn_injective
      rw [hβl, matVecL_ofFn]
    refine ⟨α, hα, ?_, fun u hu => ?_⟩
    · rw [hker, hK, hβw]
    · have h := hS u (hsub hu)
      rwa [hβw] at h

end LeafData

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
