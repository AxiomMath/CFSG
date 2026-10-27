module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

section PowMat

variable {k : Type*} [Field k] {d : ℕ}

@[expose] def powMat (B : Matrix (Fin d) (Fin d) k) (m : ℕ) :
    Matrix (Fin m → Fin d) (Fin m → Fin d) k :=
  fun x' x => ∏ i, B (x' i) (x i)

theorem powMat_mul (B C : Matrix (Fin d) (Fin d) k) (m : ℕ) :
    powMat (B * C) m = powMat B m * powMat C m := by
  ext x'' x
  simp only [powMat, Matrix.mul_apply]
  have := Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin d)))
    (fun i b => B (x'' i) b * C b (x i))
  simp only [Fintype.piFinset_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

@[expose] def coeffMonomial {G : Type*} (A : G → Matrix (Fin d) (Fin d) k) {m : ℕ}
    (p q : Fin m → Fin d) : G → k :=
  fun g => ∏ s, A g (p s) (q s)

end PowMat


section Interp

variable {k : Type*} [Field k] {d : ℕ} {G : Type*} [Fintype G] [DecidableEq G]

@[expose] def monSpan (A : G → Matrix (Fin d) (Fin d) k) : Submodule k (G → k) :=
  Submodule.span k {f | ∃ (m : ℕ) (_ : m < Fintype.card G) (p q : Fin m → Fin d),
    f = coeffMonomial A p q}

omit [DecidableEq G] in
theorem prod_coeffCoord_mem_monSpan (A : G → Matrix (Fin d) (Fin d) k) (T : Finset G)
    (hT : T.card < Fintype.card G) (i j : G → Fin d) :
    (fun g' => ∏ x ∈ T, A g' (i x) (j x)) ∈ monSpan A := by
  refine Submodule.subset_span ⟨T.card, hT, fun s => i ((T.equivFin.symm s : T) : G),
    fun s => j ((T.equivFin.symm s : T) : G), ?_⟩
  funext g'
  simp only [coeffMonomial]
  rw [← Finset.prod_coe_sort T]
  exact Fintype.prod_equiv T.equivFin (fun x : T => A g' (i x) (j x))
    (fun s : Fin T.card => A g' (i (T.equivFin.symm s)) (j (T.equivFin.symm s)))
    (fun x => by simp)

theorem delta_mem_monSpan (hd : 0 < d) (A : G → Matrix (Fin d) (Fin d) k)
    (hA : Function.Injective A) (g : G) : (Pi.single g 1 : G → k) ∈ monSpan A := by
  have hex : ∀ x : G, x ≠ g → ∃ ij : Fin d × Fin d, A g ij.1 ij.2 ≠ A x ij.1 ij.2 := by
    intro x hx
    by_contra hc
    push Not at hc
    exact hx (hA (Matrix.ext fun i j => (hc (i, j)).symm))
  choose ij hij using hex
  let S : Finset G := Finset.univ.erase g
  let i : G → Fin d := fun x => if h : x = g then ⟨0, hd⟩ else (ij x h).1
  let j : G → Fin d := fun x => if h : x = g then ⟨0, hd⟩ else (ij x h).2
  have hne : ∀ x ∈ S, A g (i x) (j x) - A x (i x) (j x) ≠ 0 := by
    intro x hx
    have hxg : x ≠ g := Finset.ne_of_mem_erase hx
    simp only [i, j, hxg, dite_false]
    exact sub_ne_zero.mpr (hij x hxg)
  let a : G → k := fun x => (A g (i x) (j x) - A x (i x) (j x))⁻¹
  let b : G → k := fun x => - (A x (i x) (j x)) * a x
  have hprod : (Pi.single g 1 : G → k) =
      ∏ x ∈ S, ((a x) • (fun g' => A g' (i x) (j x)) + b x • (1 : G → k)) := by
    funext g'
    rw [Finset.prod_apply]
    by_cases hg : g' = g
    · subst hg
      rw [Pi.single_eq_same]
      symm
      refine Finset.prod_eq_one fun x hx => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one, b, a]
      have := hne x hx
      field_simp
      ring
    · rw [Pi.single_eq_of_ne hg]
      symm
      refine Finset.prod_eq_zero (i := g') (Finset.mem_erase.mpr ⟨hg, Finset.mem_univ _⟩) ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one, b]
      ring
  rw [hprod, Finset.prod_add]
  refine Submodule.sum_mem _ fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.mp hT
  have hcard : T.card < Fintype.card G := by
    have h1 : T.card ≤ S.card := Finset.card_le_card hTS
    have h2 : S.card = Fintype.card G - 1 := by
      simp [S, Finset.card_erase_of_mem]
    have h3 : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨g⟩
    omega
  have hmon := prod_coeffCoord_mem_monSpan A T hcard i j
  have : (∏ x ∈ T, a x • (fun g' => A g' (i x) (j x))) * ∏ x ∈ S \ T, b x • (1 : G → k) =
      ((∏ x ∈ T, a x) * ∏ x ∈ S \ T, b x) • (fun g' => ∏ x ∈ T, A g' (i x) (j x)) := by
    funext g'
    simp only [Finset.prod_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.one_apply, mul_one,
      Finset.prod_mul_distrib]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ hmon

end Interp


section Coeff

variable {k : Type*} [Field k] {d : ℕ} {G : Type*} [Group G]
variable {E : Type*} [AddCommGroup E] [Module k E]

@[expose] def regularToModule [Fintype G] (σ : Representation k G E) (e : E) : (G → k) →ₗ[k] E where
  toFun f := ∑ g, f g • σ g⁻¹ e
  map_add' f f' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_smul]

theorem regularToModule_translate [Fintype G] (σ : Representation k G E) (e : E) (h : G)
    (f : G → k) : regularToModule σ e (fun g => f (g * h)) = σ h (regularToModule σ e f) := by
  simp only [regularToModule, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  refine (Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_)
  simp only [Equiv.coe_mulRight, mul_inv_rev]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem regularToModule_single [Fintype G] [DecidableEq G] (σ : Representation k G E) (e : E)
    (g : G) : regularToModule σ e (Pi.single g 1) = σ g⁻¹ e := by
  simp [regularToModule, Pi.single_apply]

@[expose] def coeffMap (A : G →* Matrix (Fin d) (Fin d) k) (m : ℕ) (p : Fin m → Fin d) :
    ((Fin m → Fin d) → k) →ₗ[k] (G → k) where
  toFun f := fun g => ((powMat (A g) m).mulVec f) p
  map_add' f f' := by funext g; simp [Matrix.mulVec_add]
  map_smul' c f := by funext g; simp [Matrix.mulVec_smul]

theorem coeffMap_translate (A : G →* Matrix (Fin d) (Fin d) k) (m : ℕ) (p : Fin m → Fin d)
    (h : G) (f : (Fin m → Fin d) → k) :
    coeffMap A m p ((powMat (A h) m).mulVec f) = fun g => coeffMap A m p f (g * h) := by
  funext g
  simp only [coeffMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_mulVec, ← powMat_mul, map_mul]

theorem coeffMap_single [DecidableEq G] (A : G →* Matrix (Fin d) (Fin d) k) (m : ℕ)
    (p q : Fin m → Fin d) :
    coeffMap A m p (Pi.single q 1) = coeffMonomial A p q := by
  funext g
  simp [coeffMap, coeffMonomial, powMat]

end Coeff

section Main

variable {k : Type*} [Field k] {d : ℕ} {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {E : Type*} [AddCommGroup E] [Module k E]

theorem faithful_tensor_power (hd : 0 < d) (A : G →* Matrix (Fin d) (Fin d) k)
    (hA : Function.Injective A) (σ : Representation k G E) (hσ : σ.IsIrreducible) :
    ∃ m : ℕ, m < Fintype.card G ∧ ∃ f : ((Fin m → Fin d) → k) →ₗ[k] E, Function.Surjective f ∧
      ∀ g v, f ((powMat (A g) m).mulVec v) = σ g (f v) := by
  obtain ⟨hnt, hirr⟩ := (isIrreducible_iff σ).mp hσ
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  let ι := Σ m : Fin (Fintype.card G), (Fin m → Fin d)
  let ψ := regularToModule σ e
  let T : Submodule k E := ⨆ mp : ι, LinearMap.range (ψ.comp (coeffMap A mp.1 mp.2))
  have heT : e ∈ T := by
    have h1 : ψ (Pi.single 1 1) = e := by
      show regularToModule σ e (Pi.single 1 1) = e
      rw [regularToModule_single]; simp
    rw [← h1]
    have hmem : ∀ f ∈ monSpan (⇑A), ψ f ∈ T := by
      intro f hf
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
      · rintro f ⟨m, hm, p, q, rfl⟩
        have : ψ (coeffMonomial (⇑A) p q) ∈ LinearMap.range (ψ.comp (coeffMap A m p)) :=
          ⟨Pi.single q 1, by simp [coeffMap_single]⟩
        exact Submodule.mem_iSup_of_mem (⟨⟨m, hm⟩, p⟩ : ι) this
      · simp
      · intro x y _ _ hx hy; rw [map_add]; exact T.add_mem hx hy
      · intro c x _ hx; rw [map_smul]; exact T.smul_mem c hx
    exact hmem _ (delta_mem_monSpan hd (⇑A) hA 1)
  have hTne : T ≠ ⊥ := fun h => he ((Submodule.mem_bot k).mp (h ▸ heT))
  obtain ⟨mp, hmp⟩ : ∃ mp : ι, LinearMap.range (ψ.comp (coeffMap A mp.1 mp.2)) ≠ ⊥ := by
    by_contra hc
    push Not at hc
    exact hTne (iSup_eq_bot.mpr hc)
  have hequi : ∀ g v, (ψ.comp (coeffMap A mp.1 mp.2)) ((powMat (A g) mp.1).mulVec v) =
      σ g ((ψ.comp (coeffMap A mp.1 mp.2)) v) := by
    intro g v
    simp only [LinearMap.comp_apply]
    rw [coeffMap_translate]
    exact regularToModule_translate σ e g _
  have hinv : ∀ g, ∀ u ∈ LinearMap.range (ψ.comp (coeffMap A mp.1 mp.2)),
      σ g u ∈ LinearMap.range (ψ.comp (coeffMap A mp.1 mp.2)) := by
    intro g u hu
    obtain ⟨v, rfl⟩ := hu
    exact ⟨(powMat (A g) mp.1).mulVec v, hequi g v⟩
  refine ⟨mp.1, mp.1.2, ψ.comp (coeffMap A mp.1 mp.2), ?_, hequi⟩
  rw [← LinearMap.range_eq_top]
  rcases hirr _ hinv with h | h
  · exact absurd h hmp
  · exact h

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules
