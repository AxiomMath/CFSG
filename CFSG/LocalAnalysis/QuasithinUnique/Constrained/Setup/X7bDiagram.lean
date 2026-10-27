module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra TensorProduct
open Matrix CFSG.Semidihedral.Principal Representation
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem rank_map_algebraMap_le {K L : Type} [Field K] [Field L] [Algebra K L] {m n : Type}
    [Fintype m] [Fintype n] (B : Matrix m n K) :
    (B.map (algebraMap K L)).rank ≤ B.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  set W : Submodule K (m → K) := Submodule.span K (Set.range B.col) with hW
  let φ : (m → K) →ₗ[K] (m → L) :=
    { toFun := fun v i => algebraMap K L (v i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp [Algebra.smul_def] }
  let bW := Module.finBasis K W
  let s : Finset (m → L) := Finset.univ.image (fun l => φ (bW l : m → K))
  have hsub : Submodule.span L (Set.range (B.map (algebraMap K L)).col) ≤
      Submodule.span L (s : Set (m → L)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : B.col j ∈ W := Submodule.subset_span ⟨j, rfl⟩
    have hrepr := bW.sum_repr ⟨B.col j, hj⟩
    have hcol : B.col j = ∑ l, bW.repr ⟨B.col j, hj⟩ l • (bW l : m → K) := by
      have := congrArg (fun x : W => (x : m → K)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    have himg : (B.map (algebraMap K L)).col j = φ (B.col j) := by
      ext i; rfl
    rw [himg, hcol, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)))
  calc Module.finrank L (Submodule.span L (Set.range (B.map (algebraMap K L)).col))
      ≤ Module.finrank L (Submodule.span L (s : Set (m → L))) := Submodule.finrank_mono hsub
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Module.finrank K W := by simp

section Perfect

variable {k G : Type} [Field k] [Group G]

theorem trivial_of_trivial_factors (hG : Group.IsPerfect G) {V : Type} [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ : Representation k G V)
    (h : ∀ (E : Type) [AddCommGroup E] [Module k E] [Module.Finite k E]
      (σ : Representation k G E), σ.IsIrreducible → 0 < repMultiplicity ρ σ →
        ∀ g v, σ g v = v) : ∀ g, ρ g = 1 := by
  have key := rep_induction (k := k) (G := G)
    (fun {V} _ _ _ ρ => (∀ (E : Type) [AddCommGroup E] [Module k E] [Module.Finite k E]
      (σ : Representation k G E), σ.IsIrreducible → 0 < repMultiplicity ρ σ →
        ∀ g v, σ g v = v) → ∀ g, ρ g = 1)
    (fun {V} _ _ _ ρ hsub _ g => by
      have h1 : Subsingleton V := hsub
      exact LinearMap.ext fun v => Subsingleton.elim _ _)
    (fun {V} _ _ _ ρ hirr hρ g => by
      have hpos : 0 < repMultiplicity ρ ρ := by
        rw [repMultiplicity_of_isIrreducible hirr ρ]
        have : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
        simp [this]
      refine LinearMap.ext fun v => ?_
      exact hρ V ρ hirr hpos g v)
    (fun {V} _ _ _ ρ W hW1 hW2 hρ => by
      have hWt : ∀ g, W.toRepresentation g = 1 := hW1 (fun E _ _ _ σ hσ hpos => hρ E σ hσ (by
        rw [repMultiplicity_sub_quot ρ W σ]
        omega))
      have hQt : ∀ g, W.quotient g = 1 := hW2 (fun E _ _ _ σ hσ hpos => hρ E σ hσ (by
        rw [repMultiplicity_sub_quot ρ W σ]
        omega))
      have hmem : ∀ g v, ρ g v - v ∈ W.toSubmodule := fun g v => by
        have h1 : W.quotient g (W.toSubmodule.mkQ v) = W.toSubmodule.mkQ v := by
          rw [hQt g]
          rfl
        have h2 : W.toSubmodule.mkQ (ρ g v) = W.toSubmodule.mkQ v := h1
        exact (Submodule.Quotient.eq W.toSubmodule).mp h2
      have hfix : ∀ g, ∀ w ∈ W.toSubmodule, ρ g w = w := fun g w hw => by
        have := congrArg (fun T : W.toSubmodule →ₗ[k] W.toSubmodule => (T ⟨w, hw⟩ : V)) (hWt g)
        exact this
      have hprod : ∀ g h : G, (ρ g - 1) * (ρ h - 1) = 0 := fun g h => by
        refine LinearMap.ext fun v => ?_
        have h1 : ρ g (ρ h v - v) = ρ h v - v := hfix g _ (hmem h v)
        show (ρ g - 1) ((ρ h - 1) v) = 0
        simp only [LinearMap.sub_apply, Module.End.one_apply] at h1 ⊢
        rw [h1, sub_self]
      have hmul : ∀ g h : G, ρ (g * h) - 1 = (ρ g - 1) + (ρ h - 1) := fun g h => by
        have e : ρ g * ρ h - 1 - ((ρ g - 1) + (ρ h - 1)) = (ρ g - 1) * (ρ h - 1) := by
          simp only [mul_sub, sub_mul, mul_one, one_mul]
          abel
        rw [hprod g h] at e
        rw [map_mul]
        exact sub_eq_zero.mp e
      let Φ : G →* Multiplicative (V →ₗ[k] V) :=
        { toFun := fun g => Multiplicative.ofAdd (ρ g - 1)
          map_one' := by simp
          map_mul' := fun g h => by
            show Multiplicative.ofAdd (ρ (g * h) - 1) =
              Multiplicative.ofAdd (ρ g - 1) * Multiplicative.ofAdd (ρ h - 1)
            rw [hmul g h]
            rfl }
      have hker : (⊤ : Subgroup G) ≤ Φ.ker := by
        rw [← hG.commutator_eq_top, commutator_def]
        refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
        rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
        simp
      intro g
      have := hker (Subgroup.mem_top g)
      rw [MonoidHom.mem_ker] at this
      have h0 : ρ g - 1 = 0 := by
        have := congrArg Multiplicative.toAdd this
        simpa [Φ] using this
      exact sub_eq_zero.mp h0)
  exact fun g => key _ ρ rfl h g

end Perfect

section Shift

open CFSG.QuasithinUnique.Setup.X7 (matRep MatIso matIso_of_reindex)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]

@[expose] def shiftSet (f s : ℕ) (A : Finset ℕ) : Finset ℕ := A.image fun i => (i + s) % (2 * f)

theorem shiftSet_subset {f : ℕ} (hf : 1 ≤ f) (s : ℕ) (A : Finset ℕ) :
    shiftSet f s A ⊆ Finset.range (2 * f) := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))

theorem shiftSet_injOn {f : ℕ} (s : ℕ) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    Set.InjOn (fun i => (i + s) % (2 * f)) (A : Set ℕ) := by
  intro a ha b hb hab
  have ha' := Finset.mem_range.mp (hA ha)
  have hb' := Finset.mem_range.mp (hA hb)
  have h1 : (a + s) % (2 * f) = (b + s) % (2 * f) := hab
  have h2 : a % (2 * f) = b % (2 * f) := Nat.ModEq.add_right_cancel' s h1
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2

theorem shiftSet_card {f : ℕ} (s : ℕ) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    (shiftSet f s A).card = A.card :=
  Finset.card_image_of_injOn (shiftSet_injOn s hA)

theorem shiftSet_shiftSet (f s t : ℕ) (A : Finset ℕ) :
    shiftSet f s (shiftSet f t A) = shiftSet f (t + s) A := by
  unfold shiftSet
  rw [Finset.image_image]
  refine Finset.image_congr fun i _ => ?_
  show ((i + t) % (2 * f) + s) % (2 * f) = (i + (t + s)) % (2 * f)
  rw [Nat.mod_add_mod, add_assoc]

theorem shiftSet_zero {f : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    shiftSet f 0 A = A := by
  unfold shiftSet
  conv_rhs => rw [← Finset.image_id (s := A)]
  refine Finset.image_congr fun i hi => ?_
  have := Finset.mem_range.mp (hA hi)
  simp [Nat.mod_eq_of_lt this]

theorem shiftSet_mod {f : ℕ} (s : ℕ) (A : Finset ℕ) :
    shiftSet f (s % (2 * f)) A = shiftSet f s A := by
  unfold shiftSet
  refine Finset.image_congr fun i _ => ?_
  show (i + s % (2 * f)) % (2 * f) = (i + s) % (2 * f)
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

omit [Fintype F] in
theorem natRepS_comp_pow [Finite F] (i s : ℕ) (g : antiSp F) :
    natRepS (F := F) k i ((minorAut F ^ s) g) = natRepS (F := F) k (i + s) g := by
  rw [natRepS_apply, natRepS_apply, pow_add, MulAut.mul_apply]

variable {f : ℕ}

theorem tensorRepS_comp_shift_aux (hF : Fintype.card F = 2 ^ f) (i s : ℕ) (g : antiSp F) :
    natRepS (F := F) k ((i + s) % (2 * f)) g = natRepS (F := F) k i ((minorAut F ^ s) g) := by
  rw [natRepS_comp_pow, ← natRepS_mod (k := k) hF]

theorem tensorRepS_comp_shift (hF : Fintype.card F = 2 ^ f) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (s : ℕ) :
    Nonempty (Representation.Equiv
      (matRep ((tensorRepS (F := F) k A).comp (minorAut F ^ s).toMonoidHom))
      (matRep (tensorRepS (F := F) k (shiftSet f s A)))) := by
  classical
  have hinj : Function.Injective (fun i : ↥A => (⟨(i.1 + s) % (2 * f),
      Finset.mem_image_of_mem _ i.2⟩ : ↥(shiftSet f s A))) := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (shiftSet_injOn s hA a.2 b.2 this)
  have hsurj : Function.Surjective (fun i : ↥A => (⟨(i.1 + s) % (2 * f),
      Finset.mem_image_of_mem _ i.2⟩ : ↥(shiftSet f s A))) := by
    rintro ⟨j, hj⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨⟨i, hi⟩, rfl⟩
  let e₀ : ↥A ≃ ↥(shiftSet f s A) := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  let e : (↥A → Fin 4) ≃ (↥(shiftSet f s A) → Fin 4) := Equiv.arrowCongr e₀ (Equiv.refl _)
  exact (matIso_of_reindex (R := (tensorRepS (F := F) k A).comp (minorAut F ^ s).toMonoidHom)
    (R' := tensorRepS (F := F) k (shiftSet f s A)) e (fun g x' x => by
      rw [tensorRepS_apply]
      show ∏ j : ↥(shiftSet f s A), natRepS (F := F) k j g ((e x') j) ((e x) j) =
        tensorRepS (F := F) k A ((minorAut F ^ s) g) x' x
      rw [tensorRepS_apply]
      refine (Fintype.prod_equiv e₀ _ _ (fun i => ?_)).symm
      simp only [e, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
        Equiv.symm_apply_apply]
      show natRepS (F := F) k i ((minorAut F ^ s) g) (x' i) (x i) =
        natRepS (F := F) k ((i.1 + s) % (2 * f)) g (x' i) (x i)
      rw [tensorRepS_comp_shift_aux k hF])).equiv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype F] in
theorem matMap_frob_tensorRepS [Finite F] (A : Finset ℕ) :
    CFSG.QuasithinUnique.Setup.X7.matMap (frobeniusEquiv F 2 : F →+* F)
        (tensorRepS (F := F) F A) =
      (tensorRepS (F := F) F A).comp (minorAut F ^ 2).toMonoidHom := by
  refine MonoidHom.ext fun g => ?_
  ext x' x
  simp only [CFSG.QuasithinUnique.Setup.X7.matMap_apply, Matrix.map_apply, tensorRepS_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := natRepS_add_two' F (i : ℕ) g
  have h2 : natRepS (F := F) F (i : ℕ) ((minorAut F ^ 2) g) = natRepS (F := F) F (i + 2) g := by
    rw [natRepS_comp_pow]
  rw [h2, h]
  simp [frobeniusEquiv_apply, frobenius_def]

section Mult

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap)

theorem minorAut_pow_two_mul (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) :
    minorAut F ^ (2 * f) = 1 := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have := pow_orderOf_eq_one (minorAut F)
  rwa [orderOf_minorAut hf hcard] at this

theorem mult_shift_two (hF : Fintype.card F = 2 ^ f) (PF : antiSp F →* Matrix ι ι F)
    (hτ : matMap (frobeniusEquiv F 2 : F →+* F) PF = PF) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) :
    repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F (shiftSet f 2 A))) =
      repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F A)) := by
  obtain ⟨e⟩ := tensorRepS_comp_shift (F := F) F hF hA 2
  rw [← repMultiplicity_congr_right (matRep PF) e, ← matMap_frob_tensorRepS]
  have := repMultiplicity_matMap (frobeniusEquiv F 2) PF (tensorRepS (F := F) F A)
  rw [hτ] at this
  exact this

theorem mult_shift_pow (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (PF : antiSp F →* Matrix ι ι F)
    (j : ℕ) (hj : j ≤ 2 * f)
    (e : Representation.Equiv (matRep PF) ((matRep PF).comp (minorAut F ^ j).toMonoidHom))
    {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F (shiftSet f (2 * f - j) A))) =
      repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F A)) := by
  obtain ⟨e'⟩ := tensorRepS_comp_shift (F := F) F hF hA (2 * f - j)
  let α : antiSp F →* antiSp F := (minorAut F ^ j).toMonoidHom
  have hα : Function.Surjective α := (minorAut F ^ j).surjective
  let σ : Representation F (antiSp F) ((↥A → Fin 4) → F) :=
    (matRep (tensorRepS (F := F) F A)).comp (minorAut F ^ (2 * f - j)).toMonoidHom
  have hσα : σ.comp α = matRep (tensorRepS (F := F) F A) := by
    refine MonoidHom.ext fun g => ?_
    show matRep (tensorRepS (F := F) F A) ((minorAut F ^ (2 * f - j)) ((minorAut F ^ j) g)) =
      matRep (tensorRepS (F := F) F A) g
    rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hj, minorAut_pow_two_mul hF hf]
    rfl
  have key := repMultiplicity_comp_surjective α hα (matRep PF) σ
  rw [hσα] at key
  have e2 := repMultiplicity_congr_left e (matRep (tensorRepS (F := F) F A))
  have e3 := repMultiplicity_congr_right (matRep PF) e'
  have e4 : repMultiplicity (matRep PF) σ = repMultiplicity (matRep PF)
      (matRep ((tensorRepS (F := F) F A).comp (minorAut F ^ (2 * f - j)).toMonoidHom)) := rfl
  rw [← e3, ← e4, ← key, ← e2]

end Mult

end Shift

section Orbit

variable {f : ℕ}

theorem invariant_all_shifts (hf : 1 ≤ f) (m : Finset ℕ → ℕ)
    (h2 : ∀ A, A ⊆ Finset.range (2 * f) → m (shiftSet f 2 A) = m A) (s₀ : ℕ)
    (hodd : s₀ % 2 = 1) (hs₀ : s₀ < 2 * f)
    (h0 : ∀ A, A ⊆ Finset.range (2 * f) → m (shiftSet f s₀ A) = m A) :
    ∀ (s : ℕ) (A : Finset ℕ), A ⊆ Finset.range (2 * f) → m (shiftSet f s A) = m A := by
  have h2n : ∀ (n : ℕ) (A : Finset ℕ), A ⊆ Finset.range (2 * f) → m (shiftSet f (2 * n) A) = m A := by
    intro n
    induction n with
    | zero => intro A hA; rw [Nat.mul_zero, shiftSet_zero hA]
    | succ n ih =>
      intro A hA
      have e : shiftSet f (2 * (n + 1)) A = shiftSet f 2 (shiftSet f (2 * n) A) := by
        rw [shiftSet_shiftSet]
        congr 1
      rw [e, h2 _ (shiftSet_subset hf _ A), ih A hA]
  have h1 : ∀ A, A ⊆ Finset.range (2 * f) → m (shiftSet f 1 A) = m A := by
    intro A hA
    obtain ⟨c, hc⟩ : ∃ c, s₀ = 2 * c + 1 := ⟨s₀ / 2, by omega⟩
    have hcf : c < f := by omega
    have e : shiftSet f 1 A = shiftSet f s₀ (shiftSet f (2 * (f - c)) A) := by
      rw [shiftSet_shiftSet, ← shiftSet_mod (f := f) (2 * (f - c) + s₀) A]
      have : (2 * (f - c) + s₀) % (2 * f) = 1 := by
        have : 2 * (f - c) + s₀ = 2 * f + 1 := by omega
        rw [this, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [this]
    rw [e, h0 _ (shiftSet_subset hf _ A), h2n _ A hA]
  intro s
  induction s with
  | zero => intro A hA; rw [shiftSet_zero hA]
  | succ s ih =>
    intro A hA
    have e : shiftSet f (s + 1) A = shiftSet f 1 (shiftSet f s A) := by
      rw [shiftSet_shiftSet]
    rw [e, h1 _ (shiftSet_subset hf _ A), ih A hA]

@[expose] def orbitSet (f : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  (Finset.range (2 * f)).image fun s => shiftSet f s A

theorem mem_orbitSet {B A : Finset ℕ} : B ∈ orbitSet f A ↔ ∃ s < 2 * f, shiftSet f s A = B := by
  simp [orbitSet]

theorem orbit_card_mul (hf : 1 ≤ f) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f))
    (hne : A.Nonempty) : 2 * f ≤ (orbitSet f A).card * A.card := by
  have hcover : Finset.range (2 * f) ⊆ (orbitSet f A).biUnion id := by
    intro x hx
    obtain ⟨a, ha⟩ := hne
    have hx' := Finset.mem_range.mp hx
    have ha' := Finset.mem_range.mp (hA ha)
    rw [Finset.mem_biUnion]
    refine ⟨shiftSet f ((x + 2 * f - a) % (2 * f)) A, mem_orbitSet.mpr ⟨_, Nat.mod_lt _ (by omega),
      rfl⟩, ?_⟩
    rw [shiftSet_mod]
    simp only [id, shiftSet, Finset.mem_image]
    refine ⟨a, ha, ?_⟩
    have : a + (x + 2 * f - a) = x + 2 * f := by omega
    rw [this, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hx'
  calc 2 * f = (Finset.range (2 * f)).card := (Finset.card_range _).symm
    _ ≤ ((orbitSet f A).biUnion id).card := Finset.card_le_card hcover
    _ ≤ ∑ B ∈ orbitSet f A, (id B).card := Finset.card_biUnion_le
    _ = (orbitSet f A).card * A.card := by
      rw [Finset.sum_congr rfl (g := fun _ => A.card)]
      · simp
      · intro B hB
        obtain ⟨s, -, rfl⟩ := mem_orbitSet.mp hB
        exact shiftSet_card s hA

end Orbit

section Ranks

theorem rank_map_ringHom_le {K L : Type} [Field K] [Field L] (φ : K →+* L) {m n : Type}
    [Fintype m] [Fintype n] (B : Matrix m n K) : (B.map φ).rank ≤ B.rank := by
  let _ : Algebra K L := φ.toAlgebra
  exact rank_map_algebraMap_le (L := L) B

theorem rank_map_ringEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) {m n : Type}
    [Fintype m] [Fintype n] (B : Matrix m n K) : (B.map e).rank = B.rank := by
  refine le_antisymm (rank_map_ringHom_le (e : K →+* L) B) ?_
  have h := rank_map_ringHom_le (e.symm : L →+* K) (B.map e)
  have h2 : (B.map e).map (e.symm : L →+* K) = B := by
    ext i j
    simp
  rwa [h2] at h

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

omit [Fintype F] in
theorem rank_natRepS_eq [Finite F] (i : ℕ) (z : antiSp F) :
    (natRepS (F := F) F i z - 1).rank =
      (glMat (((minorAut F ^ i) z : antiSp F) : GL (Fin 4) F) - 1).rank := by
  rw [natRepS_apply]
  congr 2

omit [Fintype F] in
theorem rank_natRepS_add_two [Finite F] (i : ℕ) (z : antiSp F) :
    (natRepS (F := F) F (i + 2) z - 1).rank = (natRepS (F := F) F i z - 1).rank := by
  rw [natRepS_add_two' F i z]
  have : (natRepS (F := F) F i z).map (fun x => x ^ 2) - 1 =
      (natRepS (F := F) F i z - 1).map (frobeniusEquiv F 2) := by
    ext a b
    by_cases h : a = b <;> simp [h, frobenius_def, CharTwo.sub_eq_add, CharTwo.add_sq]
  rw [this]
  exact rank_map_ringEquiv (frobeniusEquiv F 2) _

omit [Fintype F] in
theorem rank_natRepS_parity [Finite F] (z : antiSp F) (i : ℕ) :
    (natRepS (F := F) F i z - 1).rank = if i % 2 = 0 then rk0 z else rk1 z := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 =>
      rw [rank_natRepS_eq]
      simp [rk0]
    | 1 =>
      rw [rank_natRepS_eq]
      simp [rk1, minorAut_apply]
    | i + 2 =>
      rw [rank_natRepS_add_two, ih i (by omega)]
      simp only [Nat.add_mod_right]

omit [CharP F 2] [Fintype F] in
theorem fixedCodim_matRep {ι k : Type} [Field k] [Fintype ι] [DecidableEq ι] {G : Type} [Group G]
    (R : G →* Matrix ι ι k) (z : G) :
    Module.finrank k (ι → k) -
      Module.finrank k (repFixedSpace (CFSG.QuasithinUnique.Setup.X7.matRep R) {z}) =
        (R z - 1).rank := by
  have hker : repFixedSpace (CFSG.QuasithinUnique.Setup.X7.matRep R) {z} =
      LinearMap.ker (Matrix.mulVecLin (R z - 1)) := by
    ext v
    simp only [mem_repFixedSpace, Set.mem_singleton_iff, forall_eq, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    rfl
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (R z - 1))
  rw [hker]
  unfold Matrix.rank
  simp only [Module.finrank_fintype_fun_eq_card] at h ⊢
  omega

end Ranks

section Label

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap matRep_apply)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem exists_nonempty_label (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (hG : Group.IsPerfect (antiSp F)) (PF : antiSp F →* Matrix ι ι F) (hnt : ∃ g, PF g ≠ 1) :
    ∃ A : Finset ℕ, A ⊆ Finset.range (2 * f) ∧ A.Nonempty ∧
      0 < repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F A)) := by
  by_contra hcon
  have hcon' : ∀ A : Finset ℕ, A ⊆ Finset.range (2 * f) → A.Nonempty →
      ¬ 0 < repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F A)) :=
    fun A hA hne hpos => hcon ⟨A, hA, hne, hpos⟩
  have htriv := trivial_of_trivial_factors (k := F) hG (matRep PF)
    (fun E _ _ _ σ hσ hpos g v => by
      obtain ⟨⟨A, ⟨hA, ⟨e⟩⟩, -⟩, h2⟩ :=
        split_simple_module_production (F := F) (k := F) hF hf σ hσ
      have hmult : repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F A)) =
          repMultiplicity (matRep PF) σ := repMultiplicity_congr_right _ e
      by_cases hne : A.Nonempty
      · exact absurd (hmult ▸ hpos) (hcon' A hA hne)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        exact ((h2 A hA ⟨e⟩).2.mp hne) g v)
  obtain ⟨g, hg⟩ := hnt
  apply hg
  have h1 : matRep PF g = 1 := htriv g
  ext a b
  have := congrArg (fun T : (ι → F) →ₗ[F] (ι → F) => T (Pi.single b 1) a) h1
  simpa [matRep_apply, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using
    this

theorem sum_rank_le (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (PF : antiSp F →* Matrix ι ι F)
    (z : antiSp F) (O : Finset (Finset ℕ))
    (hO : ∀ B ∈ O, B ⊆ Finset.range (2 * f) ∧
      0 < repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F B))) :
    ∑ B ∈ O, (tensorRepS (F := F) F B z - 1).rank ≤ (PF z - 1).rank := by
  classical
  have key := sum_repMultiplicity_mul_fixedCodim_le (k := F) (matRep PF) {z} (ι := ↥O)
    (fun t => (↥(t : Finset ℕ) → Fin 4) → F) (fun t => matRep (tensorRepS (F := F) F t))
    (fun t t' h => Subtype.ext
      ((tensorRepS_absolutely_irreducible_and_distinct (k := F) hF hf).2 t (hO t t.2).1 t'
        (hO t' t'.2).1 h))
  have hc : ∀ t : ↥O, Module.finrank F ((↥(t : Finset ℕ) → Fin 4) → F) -
      Module.finrank F (repFixedSpace (matRep (tensorRepS (F := F) F t)) {z}) =
        (tensorRepS (F := F) F t z - 1).rank := fun t => fixedCodim_matRep _ z
  simp only [hc] at key
  rw [fixedCodim_matRep PF z] at key
  refine le_trans ?_ key
  rw [← Finset.sum_coe_sort O]
  refine Finset.sum_le_sum fun t _ => ?_
  have := (hO t t.2).2
  exact Nat.le_mul_of_pos_left _ this

end Label

section Arith

theorem four_mul_le_four_pow {m : ℕ} (hm : 1 ≤ m) : 4 * m ≤ 4 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem six_mul_add_two_pow_le {m : ℕ} (hm : 2 ≤ m) : 6 * m + 2 ^ m ≤ 4 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ, pow_succ 4 m]
    omega

theorem sum_range_two_mul_ite (x y c : ℕ) :
    ∑ i ∈ Finset.range (2 * c), (if i % 2 = 0 then x else y) = c * (x + y) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * c) % 2 = 0 := by omega
    have h2 : (2 * c + 1) % 2 = 1 := by omega
    simp only [h1, h2]
    simp
    ring

end Arith

section OrbitRank

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap matRep_apply MatIso)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem card_of_mem_orbitSet {A B : Finset ℕ} (hA : A ⊆ Finset.range (2 * f))
    (hB : B ∈ orbitSet f A) : B.card = A.card := by
  obtain ⟨s, -, rfl⟩ := mem_orbitSet.mp hB
  exact shiftSet_card s hA

theorem sum_orbit_rank_ge (hf : 1 ≤ f) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f))
    (hm : 2 ≤ A.card) {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    3 * (2 * f) ≤ ∑ B ∈ orbitSet f A, (tensorRepS (F := F) F B z - 1).rank := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hO : ∀ B ∈ orbitSet f A, 3 * A.card ≤ (tensorRepS (F := F) F B z - 1).rank := by
    intro B hB
    have hc := card_of_mem_orbitSet hA hB
    have h1 := rank_tensorRepS_sub_one_ge F B hz hz1
    have h2 := six_mul_add_two_pow_le hm
    rw [hc] at h1
    omega
  calc 3 * (2 * f) ≤ 3 * ((orbitSet f A).card * A.card) :=
        Nat.mul_le_mul_left _ (orbit_card_mul hf hA hne)
    _ = ∑ _B ∈ orbitSet f A, 3 * A.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring
    _ ≤ ∑ B ∈ orbitSet f A, (tensorRepS (F := F) F B z - 1).rank := Finset.sum_le_sum hO

theorem sum_orbit_rank_two (hf : 1 ≤ f) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f))
    (hne : A.Nonempty) {z : antiSp F} (hz : z * z = 1) (h0 : rk0 z = 2) (h1 : rk1 z = 2) :
    4 * f ≤ ∑ B ∈ orbitSet f A, (tensorRepS (F := F) F B z - 1).rank := by
  have hO : ∀ B ∈ orbitSet f A, 2 * A.card ≤ (tensorRepS (F := F) F B z - 1).rank := by
    intro B hB
    have hc := card_of_mem_orbitSet hA hB
    have hBne : B.Nonempty := Finset.card_pos.mp (by rw [hc]; exact Finset.card_pos.mpr hne)
    obtain ⟨i, hi⟩ := hBne
    have hri : (natRepS (F := F) F i z - 1).rank = 2 := by
      rw [rank_natRepS_parity]
      split_ifs
      · exact h0
      · exact h1
    have h2 := rank_tensorRepS_sub_one_of_rank_two F B hz hi hri
    have h3 := four_mul_le_four_pow (m := A.card) (Finset.card_pos.mpr hne)
    rw [h2, hc]
    omega
  calc 4 * f = 2 * (2 * f) := by ring
    _ ≤ 2 * ((orbitSet f A).card * A.card) := Nat.mul_le_mul_left _ (orbit_card_mul hf hA hne)
    _ = ∑ _B ∈ orbitSet f A, 2 * A.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring
    _ ≤ ∑ B ∈ orbitSet f A, (tensorRepS (F := F) F B z - 1).rank := Finset.sum_le_sum hO

theorem singleton_mem_orbitSet (hf : 1 ≤ f) {a i : ℕ} (ha : a < 2 * f) (hi : i < 2 * f) :
    ({i} : Finset ℕ) ∈ orbitSet f {a} := by
  refine mem_orbitSet.mpr ⟨(i + 2 * f - a) % (2 * f), Nat.mod_lt _ (by omega), ?_⟩
  rw [shiftSet_mod]
  simp only [shiftSet, Finset.image_singleton, Finset.singleton_inj]
  have : a + (i + 2 * f - a) = i + 2 * f := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hi

theorem rank_tensorRepS_singleton {z : antiSp F} (hz : z * z = 1) (i : ℕ) :
    (tensorRepS (F := F) F {i} z - 1).rank = (natRepS (F := F) F i z - 1).rank := by
  have h1 := rank_tensorRepS_sub_one F ({i} : Finset ℕ) hz
  have h2 := rank_natRepS_sub_one_le F hz i
  rw [Finset.prod_coe_sort ({i} : Finset ℕ)
    (fun j => 4 - 2 * (natRepS (F := F) F j z - 1).rank), Finset.prod_singleton,
    Finset.card_singleton, pow_one] at h1
  omega

theorem sum_singletons_rank {z : antiSp F} (hz : z * z = 1) :
    ∑ B ∈ (Finset.range (2 * f)).image (fun i => ({i} : Finset ℕ)),
        (tensorRepS (F := F) F B z - 1).rank = f * (rk0 z + rk1 z) := by
  rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
  simp only [rank_tensorRepS_singleton hz, rank_natRepS_parity]
  exact sum_range_two_mul_ite _ _ f

end OrbitRank

section Matrix

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap matRep_apply MatIso)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem antiSp_isPerfect (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) :
    Group.IsPerfect (antiSp F) := by
  have h4 : 4 ≤ Fintype.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by simpa using h4)
  have := CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 F (Or.inl ⟨s, hs⟩)
  exact Group.IsPerfect.ofSurjective (f := (antiSpEquiv F).symm.toMonoidHom)
    (antiSpEquiv F).symm.surjective

theorem rank_lower_bound_matrix (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (PF : antiSp F →* Matrix ι ι F) (hτ : matMap (frobeniusEquiv F 2 : F →+* F) PF = PF)
    (hnt : ∃ g, PF g ≠ 1) {j : ℕ} (hjodd : j % 2 = 1) (hj : j < 2 * f) {P Q : Matrix ι ι F}
    (hiso : MatIso PF (PF.comp (minorAut F ^ j).toMonoidHom) P Q) {z : antiSp F}
    (hz : z * z = 1) (hz1 : z ≠ 1) :
    3 * f ≤ (PF z - 1).rank ∧ (rk0 z = 2 → rk1 z = 2 → 4 * f ≤ (PF z - 1).rank) := by
  have hf1 : 1 ≤ f := by omega
  obtain ⟨A, hA, hne, hpos⟩ := exists_nonempty_label hF hf1 (antiSp_isPerfect hF hf) PF hnt
  obtain ⟨e⟩ := hiso.equiv
  let m : Finset ℕ → ℕ := fun B =>
    repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F B))
  have hm2 : ∀ B, B ⊆ Finset.range (2 * f) → m (shiftSet f 2 B) = m B := fun B hB =>
    mult_shift_two hF PF hτ hB
  have hs₀ : (2 * f - j) % 2 = 1 := by omega
  have hs₀' : 2 * f - j < 2 * f := by omega
  have hm0 : ∀ B, B ⊆ Finset.range (2 * f) → m (shiftSet f (2 * f - j) B) = m B := fun B hB =>
    mult_shift_pow hF hf1 PF j hj.le e hB
  have hinv := invariant_all_shifts hf1 m hm2 (2 * f - j) hs₀ hs₀' hm0
  have hOpos : ∀ B ∈ orbitSet f A, B ⊆ Finset.range (2 * f) ∧ 0 < m B := by
    intro B hB
    obtain ⟨s, -, rfl⟩ := mem_orbitSet.mp hB
    exact ⟨shiftSet_subset hf1 s A, by rw [hinv s A hA]; exact hpos⟩
  have hsum := sum_rank_le hF hf1 PF z (orbitSet f A) hOpos
  refine ⟨?_, fun h0 h1 => le_trans (sum_orbit_rank_two hf1 hA hne hz h0 h1) hsum⟩
  by_cases hm : 2 ≤ A.card
  · have := sum_orbit_rank_ge hf1 hA hm hz hz1
    omega
  · have hA1 : A.card = 1 := by
      have := Finset.card_pos.mpr hne
      omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA1
    have ha := Finset.mem_range.mp (hA (Finset.mem_singleton_self a))
    have hO' : ∀ B ∈ (Finset.range (2 * f)).image (fun i => ({i} : Finset ℕ)),
        B ⊆ Finset.range (2 * f) ∧ 0 < m B := by
      intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact hOpos _ (singleton_mem_orbitSet hf1 ha (Finset.mem_range.mp hi))
    have hsum' := sum_rank_le hF hf1 PF z _ hO'
    rw [sum_singletons_rank hz] at hsum'
    have h3 : 3 ≤ rk0 z + rk1 z := by
      rcases involution_rank_pair hz hz1 with h | h | h <;> omega
    calc 3 * f = f * 3 := by ring
      _ ≤ f * (rk0 z + rk1 z) := Nat.mul_le_mul_left _ h3
      _ ≤ (PF z - 1).rank := hsum'

end Matrix

section Final

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap matMap_apply MatIso)

@[expose] def repLinEquiv {k G : Type} [Field k] [Group G] {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem repLinEquiv_apply {k G : Type} [Field k] [Group G] {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g : G) (v : V) : repLinEquiv ρ g v = ρ g v :=
  rfl

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem binary_diagram_stable_modules_have_large_inner_involution_ranks
    (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f) {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] (π : Representation (ZMod 2) (antiSp F) M) (hπ : ∃ g, π g ≠ 1)
    (b : M ≃ₗ[ZMod 2] M) (h : antiSp F) {j : ℕ} (hjodd : j % 2 = 1) (hj : j < 2 * f)
    (hb : ∀ (g : antiSp F) (w : M), b (π g (b.symm w)) = π (h * (minorAut F ^ j) g * h⁻¹) w)
    {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    3 * f ≤ Module.finrank (ZMod 2) (LinearMap.range (π z - 1)) ∧
      (rk0 z = 2 → rk1 z = 2 →
        4 * f ≤ Module.finrank (ZMod 2) (LinearMap.range (π z - 1))) := by
  classical
  let n := Module.finrank (ZMod 2) M
  let bas : Module.Basis (Fin n) (ZMod 2) M := Module.finBasis (ZMod 2) M
  let α : antiSp F →* antiSp F := (minorAut F ^ j).toMonoidHom
  have hb' : ∀ (g : antiSp F) (v : M), b (π g v) = π (h * α g * h⁻¹) (b v) := fun g v => by
    have := hb g (b v)
    rwa [LinearEquiv.symm_apply_apply] at this
  let u : M ≃ₗ[ZMod 2] M := b.trans (repLinEquiv π h⁻¹)
  let E : Representation.Equiv π (π.comp α) := Representation.Equiv.mk u (fun g => by
    refine LinearMap.ext fun v => ?_
    show π h⁻¹ (b (π g v)) = π (α g) (π h⁻¹ (b v))
    rw [hb' g v, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group)
  obtain ⟨U, U', hU⟩ := CFSG.QuasithinUnique.Setup.X7.MatIso.exists_of_equiv
    ((matRepEquiv π bas).symm.trans (E.trans (matRepEquiv (π.comp α) bas)))
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let PF : antiSp F →* Matrix (Fin n) (Fin n) F := matMap φ (toMatRep π bas)
  have hφ : (frobeniusEquiv F 2 : F →+* F).comp φ = φ := RingHom.ext_zmod _ _
  have hτ : matMap (frobeniusEquiv F 2 : F →+* F) PF = PF := by
    refine MonoidHom.ext fun g => ?_
    show ((toMatRep π bas g).map φ).map (frobeniusEquiv F 2 : F →+* F) = (toMatRep π bas g).map φ
    rw [Matrix.map_map]
    congr 1
    funext x
    exact RingHom.congr_fun hφ x
  have hnt : ∃ g, PF g ≠ 1 := by
    obtain ⟨g, hg⟩ := hπ
    refine ⟨g, fun hPF => hg ?_⟩
    have h1 : (toMatRep π bas g).map φ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map φ := by
      rw [Matrix.map_one φ (map_zero φ) (map_one φ)]
      exact hPF
    have h2 := Matrix.map_injective φ.injective h1
    have h3 : LinearMap.toMatrix bas bas (π g) = LinearMap.toMatrix bas bas 1 := by
      rw [LinearMap.toMatrix_one]
      exact h2
    exact (LinearMap.toMatrix bas bas).injective h3
  have hiso : MatIso PF (PF.comp α) (U.map φ) (U'.map φ) := hU.map φ
  obtain ⟨h1, h2⟩ := rank_lower_bound_matrix hF hf PF hτ hnt hjodd hj hiso hz hz1
  have hrank : (PF z - 1).rank ≤ Module.finrank (ZMod 2) (LinearMap.range (π z - 1)) := by
    have e1 : PF z - 1 = (toMatRep π bas z - 1).map φ := by
      ext a b
      by_cases hab : a = b <;> simp [PF, matMap_apply, hab]
    have e2 : (toMatRep π bas z - 1).rank =
        Module.finrank (ZMod 2) (LinearMap.range (π z - 1)) := by
      have e3 : toMatRep π bas z - 1 = LinearMap.toMatrix bas bas (π z - 1) := by
        rw [map_sub, LinearMap.toMatrix_one]
        rfl
      rw [e3, Matrix.rank_eq_finrank_range_toLin _ bas bas, Matrix.toLin_toMatrix]
    rw [← e2, e1]
    exact rank_map_ringHom_le φ _
  exact ⟨h1.trans hrank, fun a b => (h2 a b).trans hrank⟩

end Final

end CFSG.QuasithinUnique.Setup.X7b
