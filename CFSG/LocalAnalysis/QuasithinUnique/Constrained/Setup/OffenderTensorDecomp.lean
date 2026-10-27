module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open Module TensorProduct

universe u v

section Decomp

variable {F : Type u} [Field F] {W : Type u} [AddCommGroup W] [Module F W]

@[expose] def invSubmodule (L : Subgroup (W ≃ₗ[F] W)) (U : Submodule F W)
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) : Submodule (spanAlg L) W where
  carrier := U
  add_mem' := U.add_mem
  zero_mem' := U.zero_mem
  smul_mem' := by
    rintro ⟨r, hr⟩ u hu
    show r u ∈ U
    induction hr using Algebra.adjoin_induction generalizing u with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact hU l l.2 u hu
    | algebraMap c =>
      simpa using U.smul_mem c hu
    | add x y _ _ hx hy =>
      rw [LinearMap.add_apply]
      exact U.add_mem (hx hu) (hy hu)
    | mul x y _ _ hx hy =>
      rw [Module.End.mul_apply]
      exact hx (hy hu)

theorem exists_simple_submodule (L : Subgroup (W ≃ₗ[F] W)) [Nontrivial W] [Finite W] :
    ∃ I : Submodule (spanAlg L) W, IsSimpleModule (spanAlg L) I := by
  have : IsAtomic (Submodule (spanAlg L) W) := inferInstance
  obtain ⟨I, hI⟩ := IsAtomic.exists_atom (Submodule (spanAlg L) W)
  exact ⟨I, isSimpleModule_iff_isAtom.2 hI⟩

end Decomp

section Decomp2

variable {F : Type u} [Field F] {W : Type u} [AddCommGroup W] [Module F W]

@[expose] def commLinear (L : Subgroup (W ≃ₗ[F] W)) (k : W ≃ₗ[F] W)
    (hk : ∀ l ∈ L, ∀ w, k (l w) = l (k w)) : W →ₗ[spanAlg L] W where
  toFun := k
  map_add' := map_add k
  map_smul' := by
    rintro ⟨r, hr⟩ w
    exact comm_spanAlg (f := (k : Module.End F W)) hk hr w

@[expose] def stabSet (S : Set W) : Subgroup (W ≃ₗ[F] W) where
  carrier := {g | ∀ u, g u ∈ S ↔ u ∈ S}
  one_mem' := fun u => Iff.rfl
  mul_mem' := fun {a b} ha hb u => by
    show a (b u) ∈ S ↔ u ∈ S
    rw [ha, hb]
  inv_mem' := fun {a} ha u => by
    have h := ha (a⁻¹ u)
    have h2 : a (a⁻¹ u) = u := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [h2] at h
    exact h.symm

@[expose] def transOf (L K : Subgroup (W ≃ₗ[F] W)) (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x) (k : K) :
    W →ₗ[spanAlg L] W :=
  commLinear L k.1 (fun l hl w => (congrArg (fun T : W ≃ₗ[F] W => T w) (hLK l hl k.1 k.2)).symm)

theorem transOf_apply (L K : Subgroup (W ≃ₗ[F] W)) (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x)
    (k : K) (w : W) : transOf L K hLK k w = k.1 w := rfl

theorem le_stabSet_of_invariant (G : Subgroup (W ≃ₗ[F] W)) (S : Set W)
    (hG : ∀ g ∈ G, ∀ u ∈ S, g u ∈ S) : G ≤ stabSet S := by
  intro g hg u
  refine ⟨fun h => ?_, hG g hg u⟩
  have := hG g⁻¹ (G.inv_mem hg) (g u) h
  rwa [gl_inv_apply_apply] at this

theorem iSup_translates_eq_top (L K : Subgroup (W ≃ₗ[F] W))
    (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x) (hirr : IsIrrAct (L ⊔ K))
    (I : Submodule (spanAlg L) W) (hI : I ≠ ⊥) :
    ⨆ k : K, I.map (transOf L K hLK k) = ⊤ := by
  obtain ⟨S, hS⟩ : ∃ S : Submodule (spanAlg L) W, S = ⨆ k : K, I.map (transOf L K hLK k) :=
    ⟨_, rfl⟩
  rw [← hS]
  have hK : ∀ k : K, ∀ u ∈ S, k.1 u ∈ S := by
    intro k u hu
    have : S.map (transOf L K hLK k) ≤ S := by
      rw [hS, Submodule.map_iSup]
      refine iSup_le fun k' => ?_
      rw [← Submodule.map_comp]
      have : (transOf L K hLK k) ∘ₗ (transOf L K hLK k') = transOf L K hLK (k * k') := by
        ext w; rfl
      rw [this]
      exact le_iSup (fun k'' : K => I.map (transOf L K hLK k'')) (k * k')
    exact this ⟨u, hu, rfl⟩
  have hL : ∀ l ∈ L, ∀ u ∈ S, l u ∈ S := fun l hl u hu =>
    S.smul_mem (⟨l, mem_spanAlg_of_mem hl⟩ : spanAlg L) hu
  have hLst : L ≤ stabSet (S : Set W) := le_stabSet_of_invariant L _ hL
  have hKst : K ≤ stabSet (S : Set W) := le_stabSet_of_invariant K _ (fun g hg u hu => hK ⟨g, hg⟩ u hu)
  have hH : ∀ h ∈ L ⊔ K, ∀ u ∈ S.restrictScalars F, h u ∈ S.restrictScalars F := fun h hh u hu =>
    (sup_le hLst hKst hh u).2 hu
  rcases hirr _ hH with h | h
  · exfalso
    apply hI
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S := by
      rw [hS]
      refine Submodule.mem_iSup_of_mem (1 : K) ⟨x, hx, rfl⟩
    have : x ∈ S.restrictScalars F := hxS
    rw [h] at this
    exact this
  · rw [eq_top_iff]
    intro x _
    have : x ∈ S.restrictScalars F := by rw [h]; trivial
    exact this

theorem exists_pi_equiv [Nontrivial W] [Finite W] (L K : Subgroup (W ≃ₗ[F] W))
    (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x) (hirr : IsIrrAct (L ⊔ K))
    (I : Submodule (spanAlg L) W) [hIs : IsSimpleModule (spanAlg L) I] :
    ∃ (n : ℕ), 0 < n ∧ Nonempty (W ≃ₗ[spanAlg L] (Fin n → I)) := by
  have hI : I ≠ ⊥ := by
    intro h
    have := hIs.nontrivial
    rw [h] at this
    exact not_nontrivial _ this
  have htop := iSup_translates_eq_top L K hLK hirr I hI
  have hle : isotypicComponent (spanAlg L) W I = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le fun k => Submodule.map_le_isotypicComponent I (transOf L K hLK k)
  have hss : IsSemisimpleModule (spanAlg L) W := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top ?_
    rw [eq_top_iff, ← hle]
    refine sSup_le fun m hm => le_sSup ?_
    obtain ⟨e⟩ := hm
    exact IsSimpleModule.congr (R := spanAlg L) (M := m) (N := I) e
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top hle
  have : Module.Finite (spanAlg L) W := Module.Finite.of_finite
  obtain ⟨n, ⟨Θ⟩⟩ := hiso.linearEquiv_fun
  refine ⟨n, ?_, ⟨Θ⟩⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exfalso
    subst h
    have : Subsingleton W := Θ.toEquiv.subsingleton
    exact not_nontrivial_iff_subsingleton.2 this inferInstance
  · exact h

end Decomp2

section PiComm

variable {R M : Type*} [Ring R] [AddCommMonoid M] [Module R M] {n : ℕ}

@[expose] def piMap (ε : Module.End R M) : (Fin n → M) →ₗ[R] (Fin n → M) :=
  LinearMap.pi fun i => ε ∘ₗ LinearMap.proj i

theorem piMap_apply (ε : Module.End R M) (x : Fin n → M) (i : Fin n) : piMap ε x i = ε (x i) := rfl

theorem piMap_comm (hcomm : ∀ a b : Module.End R M, a * b = b * a) (ε : Module.End R M)
    (Φ : (Fin n → M) →ₗ[R] (Fin n → M)) (x : Fin n → M) :
    piMap ε (Φ x) = Φ (piMap ε x) := by
  have key : (piMap ε : (Fin n → M) →ₗ[R] (Fin n → M)) ∘ₗ Φ = Φ ∘ₗ piMap ε := by
    refine LinearMap.pi_ext fun j y => ?_
    refine funext fun i => ?_
    have hψ := congrArg (fun T : Module.End R M => T y)
      (hcomm ε (LinearMap.proj i ∘ₗ Φ ∘ₗ LinearMap.single R (fun _ => M) j))
    simp only [Module.End.mul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single] at hψ
    have h2 : piMap ε (Pi.single j y : Fin n → M) = Pi.single j (ε y) := by
      ext l
      by_cases hl : l = j
      · subst hl; simp [piMap_apply]
      · simp [piMap_apply, hl]
    show ε ((Φ (Pi.single j y)) i) = (Φ (piMap ε (Pi.single j y))) i
    rw [h2]
    exact hψ
  exact congrArg (fun T : (Fin n → M) →ₗ[R] (Fin n → M) => T x) key

end PiComm

section Decomp3

variable {F : Type u} [Field F] {W : Type u} [AddCommGroup W] [Module F W]

@[expose] def commutantSubgroup (f : Module.End F W) : Subgroup (W ≃ₗ[F] W) where
  carrier := {h | ∀ w, f (h w) = h (f w)}
  one_mem' := fun w => rfl
  mul_mem' := fun {a b} ha hb w => by
    show f (a (b w)) = a (b (f w))
    rw [ha, hb]
  inv_mem' := fun {a} ha w => by
    have h1 := ha (a⁻¹ w)
    have h2 : a (a⁻¹ w) = w := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [h2] at h1
    have h3 : a⁻¹ (f w) = a⁻¹ (a (f (a⁻¹ w))) := by rw [← h1]
    rw [h3]
    exact (gl_inv_apply_apply a _).symm

theorem endomorphism_scalar (L K : Subgroup (W ≃ₗ[F] W))
    (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x)
    (hend : ∀ f : Module.End F W, (∀ h ∈ L ⊔ K, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w)
    (I : Submodule (spanAlg L) W) {n : ℕ} (hn : 0 < n) (Θ : W ≃ₗ[spanAlg L] (Fin n → I))
    (hcomm : ∀ a b : Module.End (spanAlg L) I, a * b = b * a)
    (ε : Module.End (spanAlg L) I) : ∃ c : F, ∀ x : I, ε x = c • x := by
  let εt : W →ₗ[spanAlg L] W := Θ.symm.toLinearMap ∘ₗ piMap ε ∘ₗ Θ.toLinearMap
  let εF : Module.End F W := εt.restrictScalars F
  have hεF : ∀ w, εF w = Θ.symm (piMap ε (Θ w)) := fun w => rfl
  have hL : L ≤ commutantSubgroup εF := by
    intro l hl w
    show εF (l w) = l (εF w)
    exact εt.map_smul (⟨l, mem_spanAlg_of_mem hl⟩ : spanAlg L) w
  have hK : K ≤ commutantSubgroup εF := by
    intro k hk w
    show εF (k w) = k (εF w)
    have h1 : Θ (k w) = (Θ.toLinearMap ∘ₗ transOf L K hLK ⟨k, hk⟩ ∘ₗ Θ.symm.toLinearMap) (Θ w) := by
      simp [transOf_apply]
    rw [hεF, hεF, h1, piMap_comm hcomm ε (Θ.toLinearMap ∘ₗ transOf L K hLK ⟨k, hk⟩ ∘ₗ Θ.symm.toLinearMap)]
    simp [transOf_apply]
  obtain ⟨c, hc⟩ := hend εF (fun h hh => sup_le hL hK hh)
  refine ⟨c, fun x => ?_⟩
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 := hc (Θ.symm (Pi.single i₀ x))
  rw [hεF, LinearEquiv.apply_symm_apply] at h1
  have h2 := congrArg Θ h1
  rw [LinearEquiv.apply_symm_apply] at h2
  have h3 : Θ (c • Θ.symm (Pi.single i₀ x)) = c • (Pi.single i₀ x : Fin n → I) := by
    rw [← algebraMap_smul (spanAlg L) c (Θ.symm (Pi.single i₀ x)), map_smul, algebraMap_smul,
      LinearEquiv.apply_symm_apply]
  rw [h3] at h2
  have h4 := congrFun h2 i₀
  simpa [piMap_apply] using h4

end Decomp3


section Slice

variable {F : Type*} [Field F] {P Q : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q]
  [Module F Q]

@[expose] noncomputable def sliceL (ψ : P →ₗ[F] F) : P ⊗[F] Q →ₗ[F] Q :=
  (TensorProduct.lid F Q).toLinearMap ∘ₗ LinearMap.rTensor Q ψ

theorem sliceL_tmul (ψ : P →ₗ[F] F) (p : P) (q : Q) : sliceL ψ (p ⊗ₜ[F] q) = ψ p • q := by
  simp [sliceL]

theorem sliceL_rTensor (ψ : P →ₗ[F] F) (a : Module.End F P) (u : P ⊗[F] Q) :
    sliceL ψ (LinearMap.rTensor Q a u) = sliceL (ψ ∘ₗ a) u := by
  induction u with
  | tmul p q => simp [sliceL_tmul]
  | add x y hx hy => simp [hx, hy]

theorem sliceL_lTensor (ψ : P →ₗ[F] F) (b : Module.End F Q) (u : P ⊗[F] Q) :
    sliceL ψ (LinearMap.lTensor P b u) = b (sliceL ψ u) := by
  induction u with
  | tmul p q => simp [sliceL_tmul]
  | add x y hx hy => simp [hx, hy]

theorem rTensor_smulRight (ψ : P →ₗ[F] F) (x : P) (u : P ⊗[F] Q) :
    LinearMap.rTensor Q (ψ.smulRight x) u = x ⊗ₜ[F] sliceL ψ u := by
  induction u with
  | tmul p q => simp [sliceL_tmul, TensorProduct.smul_tmul]
  | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]

theorem exists_dual_one [Nontrivial P] : ∃ (p : P) (ψ : P →ₗ[F] F), ψ p = 1 := by
  obtain ⟨e, he⟩ := exists_ne (0 : P)
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_ne_zero F he
  exact ⟨e, (φ₀ e)⁻¹ • φ₀, by simp [hφ₀]⟩

theorem eq_lTensor_of_commute_rTensor (p₀ : P) (ψ₀ : P →ₗ[F] F) (h₀ : ψ₀ p₀ = 1)
    (T : Module.End F (P ⊗[F] Q))
    (hT : ∀ (a : Module.End F P) (u : P ⊗[F] Q),
      T (LinearMap.rTensor Q a u) = LinearMap.rTensor Q a (T u)) :
    T = LinearMap.lTensor P (sliceL ψ₀ ∘ₗ T ∘ₗ TensorProduct.mk F P Q p₀) := by
  refine TensorProduct.ext' fun x q => ?_
  have h1 : x ⊗ₜ[F] q = LinearMap.rTensor Q (ψ₀.smulRight x) (p₀ ⊗ₜ[F] q) := by
    simp [h₀]
  have h2 : T (x ⊗ₜ[F] q) = x ⊗ₜ[F] sliceL ψ₀ (T (p₀ ⊗ₜ[F] q)) := by
    rw [h1, hT, rTensor_smulRight]
  rw [h2]
  simp

theorem lTensor_injective' [Nontrivial P] :
    Function.Injective (fun S : Module.End F Q => LinearMap.lTensor P S) := by
  obtain ⟨p₀, ψ₀, h₀⟩ := exists_dual_one (P := P) (F := F)
  intro S₁ S₂ h
  refine LinearMap.ext fun q => ?_
  have := congrArg (fun T : Module.End F (P ⊗[F] Q) => sliceL ψ₀ (T (p₀ ⊗ₜ[F] q))) h
  simpa [sliceL_tmul, h₀] using this

end Slice

section Density

variable {F R M : Type*} [Field F] [Ring R] [AddCommGroup M] [Module F M] [Module R M]

theorem exists_smul_eq_of_scalar_endo [IsSemisimpleModule R M] [Finite M]
    (hscal : ∀ ε : Module.End R M, ∃ c : F, ∀ x, ε x = c • x) (g : M →ₗ[F] M) :
    ∃ r : R, ∀ x, r • x = g x := by
  classical
  have : Fintype M := Fintype.ofFinite M
  let g' : Module.End (Module.End R M) M :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun d x => by
        obtain ⟨c, hc⟩ := hscal d
        show g (d x) = d (g x)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density g' Finset.univ
  exact ⟨r, fun x => (hr x (Finset.mem_univ x)).symm⟩

end Density



section Act

variable {F : Type u} [Field F] {W : Type u} [AddCommGroup W] [Module F W]

@[expose] def actLin (L : Subgroup (W ≃ₗ[F] W)) (I : Submodule (spanAlg L) W) (l : L) :
    I →ₗ[F] I where
  toFun x := ⟨(l : W ≃ₗ[F] W) x,
    I.smul_mem (⟨((l : W ≃ₗ[F] W) : W →ₗ[F] W), mem_spanAlg_of_mem l.2⟩ : spanAlg L) x.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

theorem actLin_apply (L : Subgroup (W ≃ₗ[F] W)) (I : Submodule (spanAlg L) W) (l : L) (x : I) :
    ((actLin L I l x : I) : W) = (l : W ≃ₗ[F] W) x := rfl

@[expose] noncomputable def actHom (L : Subgroup (W ≃ₗ[F] W)) (I : Submodule (spanAlg L) W) :
    L →* (I ≃ₗ[F] I) where
  toFun l := LinearEquiv.ofLinearMap (actLin L I l) (actLin L I l⁻¹)
    (LinearMap.ext fun x => Subtype.ext (by
      simp only [LinearMap.comp_apply, actLin_apply, Subgroup.coe_inv, LinearMap.id_apply]
      exact gl_apply_inv_apply _ _))
    (LinearMap.ext fun x => Subtype.ext (by
      simp only [LinearMap.comp_apply, actLin_apply, Subgroup.coe_inv, LinearMap.id_apply]
      exact gl_inv_apply_apply _ _))
  map_one' := LinearEquiv.ext fun x => Subtype.ext rfl
  map_mul' a b := LinearEquiv.ext fun x => Subtype.ext rfl

theorem actHom_apply (L : Subgroup (W ≃ₗ[F] W)) (I : Submodule (spanAlg L) W) (l : L) (x : I) :
    ((actHom L I l x : I) : W) = (l : W ≃ₗ[F] W) x := rfl

theorem mem_spanAlg_of_mem_span {L : Subgroup (W ≃ₗ[F] W)} {x : Module.End F W}
    (hx : x ∈ Submodule.span F (Set.range (toEnd L))) : x ∈ spanAlg L := by
  rw [← Subalgebra.mem_toSubmodule, spanAlg_toSubmodule]; exact hx

theorem endomorphism_comm_of_simple {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] [Finite M] : ∀ a b : Module.End R M, a * b = b * a := by
  classical
  have : Finite (Module.End R M) :=
    Finite.of_injective (fun f : Module.End R M => (f : M → M)) DFunLike.coe_injective
  let _ : Field (Module.End R M) := littleWedderburn _
  intro a b
  exact mul_comm a b

theorem endomorphism_comm [Finite W] (L : Subgroup (W ≃ₗ[F] W)) (I : Submodule (spanAlg L) W)
    [IsSimpleModule (spanAlg L) I] : ∀ a b : Module.End (spanAlg L) I, a * b = b * a :=
  endomorphism_comm_of_simple (R := spanAlg L) (M := I)

end Act

theorem piScalarRight_symm_comp {F : Type*} [Field F] {P : Type*} [AddCommGroup P] [Module F P]
    {n : ℕ} (f : P →ₗ[F] P) (y : Fin n → P) :
    (TensorProduct.piScalarRight F F P (Fin n)).symm (fun i => f (y i)) =
      LinearMap.rTensor (Fin n → F) f ((TensorProduct.piScalarRight F F P (Fin n)).symm y) := by
  conv_lhs => rw [show (fun i => f (y i)) = ∑ i, (Pi.single i (f (y i)) : Fin n → P) from
    (Finset.univ_sum_single _).symm]
  conv_rhs => rw [show y = ∑ i, (Pi.single i (y i) : Fin n → P) from
    (Finset.univ_sum_single _).symm]
  simp [map_sum, TensorProduct.piScalarRight_symm_single, LinearMap.rTensor_tmul]



section SecondAction

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
  {P Q : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]

theorem exists_second_action [Nontrivial P] (e : W ≃ₗ[F] P ⊗[F] Q) {G : Type*} [Group G]
    (ρ : G →* (P ≃ₗ[F] P)) (φ : G →* (W ≃ₗ[F] W))
    (he : ∀ g w, e (φ g w) = LinearMap.rTensor Q ((ρ g : P ≃ₗ[F] P) : P →ₗ[F] P) (e w))
    (hspan : Submodule.span F (Set.range fun g : G => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    (K : Subgroup (W ≃ₗ[F] W)) (hK : ∀ g, ∀ k ∈ K, φ g * k = k * φ g) :
    ∃ σ : K →* (Q ≃ₗ[F] Q), ∀ (k : K) w, e ((k : W ≃ₗ[F] W) w) =
      LinearMap.lTensor P ((σ k : Q ≃ₗ[F] Q) : Q →ₗ[F] Q) (e w) := by
  obtain ⟨p₀, ψ₀, h₀⟩ := exists_dual_one (P := P) (F := F)
  let T : K → Module.End F (P ⊗[F] Q) := fun k =>
    e.toLinearMap ∘ₗ ((k : W ≃ₗ[F] W) : W →ₗ[F] W) ∘ₗ e.symm.toLinearMap
  have hT_apply : ∀ (k : K) (w : W), T k (e w) = e ((k : W ≃ₗ[F] W) w) := by
    intro k w; simp [T]
  have hT_comm : ∀ (k : K) (a : Module.End F P) (u : P ⊗[F] Q),
      T k (LinearMap.rTensor Q a u) = LinearMap.rTensor Q a (T k u) := by
    intro k a u
    have hsub : ∀ a ∈ Submodule.span F
        (Set.range fun g : G => ((ρ g : P ≃ₗ[F] P) : Module.End F P)),
        ∀ u, T k (LinearMap.rTensor Q a u) = LinearMap.rTensor Q a (T k u) := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨g, rfl⟩ := ha
        intro u
        obtain ⟨w, rfl⟩ := e.surjective u
        rw [← he g w, hT_apply, hT_apply, ← he g ((k : W ≃ₗ[F] W) w)]
        congr 1
        exact (congrArg (fun x : W ≃ₗ[F] W => x w) (hK g k k.2)).symm
      | zero => intro u; simp
      | add a b _ _ ha hb =>
        intro u
        simp only [LinearMap.rTensor_add, LinearMap.add_apply, map_add, ha u, hb u]
      | smul c a _ ha =>
        intro u
        simp only [LinearMap.rTensor_smul, LinearMap.smul_apply, map_smul, ha u]
    rw [hspan] at hsub
    exact hsub a Submodule.mem_top u
  let S : K → Module.End F Q := fun k => sliceL ψ₀ ∘ₗ T k ∘ₗ TensorProduct.mk F P Q p₀
  have hS : ∀ k : K, T k = LinearMap.lTensor P (S k) := fun k =>
    eq_lTensor_of_commute_rTensor p₀ ψ₀ h₀ (T k) (hT_comm k)
  have hT_mul : ∀ k k' : K, T (k * k') = T k * T k' := by
    intro k k'
    refine LinearMap.ext fun u => ?_
    obtain ⟨w, rfl⟩ := e.surjective u
    rw [Module.End.mul_apply, hT_apply, hT_apply, hT_apply]
    rfl
  have hT_one : T 1 = 1 := by
    refine LinearMap.ext fun u => ?_
    obtain ⟨w, rfl⟩ := e.surjective u
    rw [Module.End.one_apply, hT_apply]
    rfl
  have hS_mul : ∀ k k' : K, S (k * k') = S k * S k' := by
    intro k k'
    refine lTensor_injective' (P := P) (F := F) ?_
    show LinearMap.lTensor P (S (k * k')) = LinearMap.lTensor P (S k * S k')
    rw [← hS, LinearMap.lTensor_mul, ← hS, ← hS, hT_mul]
  have hS_one : S 1 = 1 := by
    refine lTensor_injective' (P := P) (F := F) ?_
    show LinearMap.lTensor P (S 1) = LinearMap.lTensor P (LinearMap.id)
    rw [← hS, LinearMap.lTensor_id, hT_one]
    rfl
  let σ : K →* (Q ≃ₗ[F] Q) :=
    { toFun := fun k => LinearEquiv.ofLinearMap (S k) (S k⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← hS_mul, mul_inv_cancel, hS_one]; rfl)
        (by rw [← Module.End.mul_eq_comp, ← hS_mul, inv_mul_cancel, hS_one]; rfl)
      map_one' := LinearEquiv.ext fun x => by
        show S 1 x = x
        rw [hS_one]; rfl
      map_mul' := fun a b => LinearEquiv.ext fun x => by
        show S (a * b) x = S a (S b x)
        rw [hS_mul]; rfl }
  refine ⟨σ, fun k w => ?_⟩
  rw [← hT_apply, hS k]
  rfl

end SecondAction

section Split

variable {F : Type u} [Field F] {W : Type u} [AddCommGroup W] [Module F W]

theorem first_factor_split [Finite F] [Nontrivial W] [Finite W] (L K : Subgroup (W ≃ₗ[F] W))
    (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x) (hirr : IsIrrAct (L ⊔ K))
    (hend : ∀ f : Module.End F W, (∀ h ∈ L ⊔ K, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module F P) (Q : Type u) (_ : AddCommGroup Q)
      (_ : Module F Q) (ρ : L →* (P ≃ₗ[F] P)) (e : W ≃ₗ[F] P ⊗[F] Q),
      Nontrivial P ∧ Nontrivial Q ∧ Finite P ∧ Finite Q ∧
      (∀ l : L, ∀ w, e ((l : W ≃ₗ[F] W) w) =
        LinearMap.rTensor Q ((ρ l : P ≃ₗ[F] P) : P →ₗ[F] P) (e w)) ∧
      Submodule.span F (Set.range fun l : L => ((ρ l : P ≃ₗ[F] P) : Module.End F P)) = ⊤ := by
  classical
  obtain ⟨I, hI⟩ := exists_simple_submodule L
  obtain ⟨n, hn, ⟨Θ⟩⟩ := exists_pi_equiv L K hLK hirr I
  have hcomm := endomorphism_comm L I
  have hscal := endomorphism_scalar L K hLK hend I hn Θ hcomm
  have hIn : Nontrivial I := hI.nontrivial
  let e : W ≃ₗ[F] ↥I ⊗[F] (Fin n → F) :=
    (Θ.restrictScalars F).trans (TensorProduct.piScalarRight F F ↥I (Fin n)).symm
  have he_l : ∀ l : L, ∀ w, e ((l : W ≃ₗ[F] W) w) =
      LinearMap.rTensor (Fin n → F) ((actHom L I l : I ≃ₗ[F] I) : I →ₗ[F] I) (e w) := by
    intro l w
    have h := Θ.map_smul (⟨((l : W ≃ₗ[F] W) : W →ₗ[F] W), mem_spanAlg_of_mem l.2⟩ : spanAlg L) w
    have h2 : Θ ((l : W ≃ₗ[F] W) w) = fun i => actHom L I l (Θ w i) := by
      funext i
      exact Subtype.ext (congrArg Subtype.val (congrFun h i))
    show (TensorProduct.piScalarRight F F ↥I (Fin n)).symm (Θ ((l : W ≃ₗ[F] W) w)) =
      LinearMap.rTensor (Fin n → F) ((actHom L I l : I ≃ₗ[F] I) : I →ₗ[F] I)
        ((TensorProduct.piScalarRight F F ↥I (Fin n)).symm (Θ w))
    rw [h2]
    exact piScalarRight_symm_comp ((actHom L I l : I ≃ₗ[F] I) : I →ₗ[F] I) (Θ w)
  have hspan : Submodule.span F
      (Set.range fun l : L => ((actHom L I l : I ≃ₗ[F] I) : Module.End F I)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨r, hr⟩ := exists_smul_eq_of_scalar_endo (R := spanAlg L) (M := I) hscal g
    let ℓ₀ : spanAlg L → Module.End F I := fun a =>
      { toFun := fun x => a • x
        map_add' := fun x y => smul_add a x y
        map_smul' := fun c x => smul_comm a c x }
    let ℓ : spanAlg L →ₗ[F] Module.End F I :=
      { toFun := ℓ₀
        map_add' := fun a b => LinearMap.ext fun x => add_smul a b x
        map_smul' := fun c a => LinearMap.ext fun x => smul_assoc c a x }
    have hg : g = ℓ r := LinearMap.ext fun x => (hr x).symm
    have key : ∀ x (hxs : x ∈ Submodule.span F (Set.range (toEnd L))) (hx : x ∈ spanAlg L),
        ℓ ⟨x, hx⟩ ∈ Submodule.span F
          (Set.range fun l : L => ((actHom L I l : I ≃ₗ[F] I) : Module.End F I)) := by
      intro x hxs
      induction hxs using Submodule.span_induction with
      | mem x hx' =>
        obtain ⟨l, rfl⟩ := hx'
        intro hx
        refine Submodule.subset_span ⟨l, ?_⟩
        refine LinearMap.ext fun y => Subtype.ext ?_
        rfl
      | zero =>
        intro hx
        have : (⟨0, hx⟩ : spanAlg L) = 0 := rfl
        rw [this, map_zero]
        exact Submodule.zero_mem _
      | add x y hx hy ihx ihy =>
        intro hxy
        have e1 : (⟨x + y, hxy⟩ : spanAlg L) =
            ⟨x, mem_spanAlg_of_mem_span hx⟩ + ⟨y, mem_spanAlg_of_mem_span hy⟩ := rfl
        rw [e1, map_add]
        exact Submodule.add_mem _ (ihx _) (ihy _)
      | smul c x hx ihx =>
        intro hcx
        have e1 : (⟨c • x, hcx⟩ : spanAlg L) = c • (⟨x, mem_spanAlg_of_mem_span hx⟩ : spanAlg L) :=
          rfl
        rw [e1, map_smul]
        exact Submodule.smul_mem _ _ (ihx _)
    have hr' : (r : Module.End F W) ∈ Submodule.span F (Set.range (toEnd L)) := by
      rw [← spanAlg_toSubmodule]; exact r.2
    rw [hg]
    exact key r hr' r.2
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨↥I, inferInstance, inferInstance, Fin n → F, inferInstance, inferInstance, actHom L I, e,
    hIn, inferInstance, inferInstance, inferInstance, he_l, hspan⟩

theorem two_factor_split [Finite F] [Nontrivial W] [Finite W] (L K : Subgroup (W ≃ₗ[F] W))
    (hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x) (hirr : IsIrrAct (L ⊔ K))
    (hend : ∀ f : Module.End F W, (∀ h ∈ L ⊔ K, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module F P) (Q : Type u) (_ : AddCommGroup Q)
      (_ : Module F Q) (ρ : L →* (P ≃ₗ[F] P)) (σ : K →* (Q ≃ₗ[F] Q)) (e : W ≃ₗ[F] P ⊗[F] Q),
      Nontrivial P ∧ Nontrivial Q ∧ Finite P ∧ Finite Q ∧
      (∀ l : L, ∀ w, e ((l : W ≃ₗ[F] W) w) =
        LinearMap.rTensor Q ((ρ l : P ≃ₗ[F] P) : P →ₗ[F] P) (e w)) ∧
      (∀ k : K, ∀ w, e ((k : W ≃ₗ[F] W) w) =
        LinearMap.lTensor P ((σ k : Q ≃ₗ[F] Q) : Q →ₗ[F] Q) (e w)) ∧
      Submodule.span F (Set.range fun l : L => ((ρ l : P ≃ₗ[F] P) : Module.End F P)) = ⊤ := by
  obtain ⟨P, _, _, Q, _, _, ρ, e, hP, hQ, hPf, hQf, he, hspan⟩ :=
    first_factor_split L K hLK hirr hend
  obtain ⟨σ, hσ⟩ := exists_second_action e ρ L.subtype he hspan K
    (fun g k hk => hLK g g.2 k hk)
  exact ⟨P, inferInstance, inferInstance, Q, inferInstance, inferInstance, ρ, σ, e, hP, hQ, hPf,
    hQf, he, hσ, hspan⟩

end Split



section Cons

variable {F : Type*} [Field F] {s : ℕ} (V : Fin (s+1) → Type*) [∀ i, AddCommGroup (V i)]
  [∀ i, Module F (V i)]

noncomputable def consMulti (v : V 0) :
    MultilinearMap F (fun j : Fin s => V j.succ) (⨂[F] i, V i) where
  toFun m' := PiTensorProduct.tprod F (Fin.cons v m' : ∀ i, V i)
  map_update_add' := by
    intro inst m' j x y
    obtain rfl : inst = instDecidableEqFin s := Subsingleton.elim _ _
    rw [Fin.cons_update (α := V) v m' j (x + y), Fin.cons_update (α := V) v m' j x,
      Fin.cons_update (α := V) v m' j y]
    exact (PiTensorProduct.tprod F : MultilinearMap F V _).map_update_add _ _ _ _
  map_update_smul' := by
    intro inst m' j c x
    obtain rfl : inst = instDecidableEqFin s := Subsingleton.elim _ _
    rw [Fin.cons_update (α := V) v m' j (c • x), Fin.cons_update (α := V) v m' j x]
    exact (PiTensorProduct.tprod F : MultilinearMap F V _).map_update_smul _ _ _ _

noncomputable def consMultiLin :
    V 0 →ₗ[F] MultilinearMap F (fun j : Fin s => V j.succ) (⨂[F] i, V i) where
  toFun := consMulti V
  map_add' v₁ v₂ := by
    refine MultilinearMap.ext fun m' => ?_
    show PiTensorProduct.tprod F (Fin.cons (v₁ + v₂) m' : ∀ i, V i) =
      PiTensorProduct.tprod F (Fin.cons v₁ m' : ∀ i, V i) +
        PiTensorProduct.tprod F (Fin.cons v₂ m' : ∀ i, V i)
    have h := (PiTensorProduct.tprod F : MultilinearMap F V _).map_update_add
      (Fin.cons v₁ m' : ∀ i, V i) 0 v₁ v₂
    rw [Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero] at h
    exact h
  map_smul' c v := by
    refine MultilinearMap.ext fun m' => ?_
    show PiTensorProduct.tprod F (Fin.cons (c • v) m' : ∀ i, V i) =
      c • PiTensorProduct.tprod F (Fin.cons v m' : ∀ i, V i)
    have h := (PiTensorProduct.tprod F : MultilinearMap F V _).map_update_smul
      (Fin.cons v m' : ∀ i, V i) 0 c v
    rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
    exact h

noncomputable def consInv : V 0 ⊗[F] (⨂[F] j : Fin s, V j.succ) →ₗ[F] ⨂[F] i, V i :=
  TensorProduct.lift
    ((PiTensorProduct.lift (R := F) (s := fun j : Fin s => V j.succ)
      (E := ⨂[F] i, V i)).toLinearMap ∘ₗ consMultiLin V)

theorem consInv_tmul (v : V 0) (m' : ∀ j : Fin s, V j.succ) :
    consInv V (v ⊗ₜ[F] PiTensorProduct.tprod F m') =
      PiTensorProduct.tprod F (Fin.cons v m' : ∀ i, V i) := by
  unfold consInv
  rw [TensorProduct.lift.tmul]
  simp [consMultiLin, consMulti]

noncomputable def fwdMulti : MultilinearMap F V (V 0 ⊗[F] (⨂[F] j : Fin s, V j.succ)) where
  toFun m := m 0 ⊗ₜ[F] PiTensorProduct.tprod F (Fin.tail m)
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin (s + 1) := Subsingleton.elim _ _
    induction i using Fin.cases with
    | zero => simp only [Function.update_self, Fin.tail_update_zero, TensorProduct.add_tmul]
    | succ j =>
      have h0 : ∀ z, Function.update m j.succ z 0 = m 0 := fun z =>
        Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
      simp only [h0, Fin.tail_update_succ]
      rw [(PiTensorProduct.tprod F : MultilinearMap F (fun j : Fin s => V j.succ) _).map_update_add,
        TensorProduct.tmul_add]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin (s + 1) := Subsingleton.elim _ _
    induction i using Fin.cases with
    | zero => simp only [Function.update_self, Fin.tail_update_zero, TensorProduct.smul_tmul']
    | succ j =>
      have h0 : ∀ z, Function.update m j.succ z 0 = m 0 := fun z =>
        Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
      simp only [h0, Fin.tail_update_succ]
      rw [(PiTensorProduct.tprod F : MultilinearMap F (fun j : Fin s => V j.succ) _).map_update_smul,
        TensorProduct.tmul_smul]

noncomputable def consFwd : (⨂[F] i, V i) →ₗ[F] V 0 ⊗[F] (⨂[F] j : Fin s, V j.succ) :=
  PiTensorProduct.lift (fwdMulti V)

theorem consFwd_tprod (m : ∀ i, V i) :
    consFwd V (PiTensorProduct.tprod F m) =
      m 0 ⊗ₜ[F] PiTensorProduct.tprod F (Fin.tail m) := by
  unfold consFwd
  rw [PiTensorProduct.lift.tprod]
  rfl

@[expose] noncomputable def tensorConsEquiv :
    (⨂[F] i, V i) ≃ₗ[F] V 0 ⊗[F] (⨂[F] j : Fin s, V j.succ) :=
  LinearEquiv.ofLinearMap (consFwd V) (consInv V)
    (by
      refine TensorProduct.ext' fun v t => ?_
      induction t using PiTensorProduct.induction_on with
      | smul_tprod a m' =>
        rw [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.tmul_smul, map_smul,
          consInv_tmul, map_smul, consFwd_tprod]
        simp [Fin.tail_cons]
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add, map_add]
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy ⊢
        rw [hx, hy])
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        consFwd_tprod, consInv_tmul]
      rw [Fin.cons_self_tail])

theorem tensorConsEquiv_tprod (m : ∀ i, V i) :
    tensorConsEquiv V (PiTensorProduct.tprod F m) =
      m 0 ⊗ₜ[F] PiTensorProduct.tprod F (Fin.tail m) :=
  consFwd_tprod V m

theorem tensorConsEquiv_symm_tmul (v : V 0) (m' : ∀ j : Fin s, V j.succ) :
    (tensorConsEquiv V).symm (v ⊗ₜ[F] PiTensorProduct.tprod F m') =
      PiTensorProduct.tprod F (Fin.cons v m' : ∀ i, V i) :=
  consInv_tmul V v m'

theorem tensorConsEquiv_factorEnd_zero (f : Module.End F (V 0)) (x : ⨂[F] i, V i) :
    tensorConsEquiv V (factorEnd 0 f x) =
      LinearMap.rTensor (⨂[F] j : Fin s, V j.succ) f (tensorConsEquiv V x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul]
    rw [factorEnd_tprod, tensorConsEquiv_tprod, tensorConsEquiv_tprod, LinearMap.rTensor_tmul,
      Function.update_self, Fin.tail_update_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem tensorConsEquiv_factorEnd_succ (j : Fin s) (g : Module.End F (V j.succ))
    (x : ⨂[F] i, V i) :
    tensorConsEquiv V (factorEnd j.succ g x) =
      LinearMap.lTensor (V 0) (factorEnd (V := fun i : Fin s => V i.succ) j g)
        (tensorConsEquiv V x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul]
    rw [factorEnd_tprod, tensorConsEquiv_tprod, tensorConsEquiv_tprod, LinearMap.lTensor_tmul,
      factorEnd_tprod, Fin.tail_update_succ]
    rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end Cons



section SliceSub

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
  {P Q : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]

@[expose] noncomputable def sliceSub (e : W ≃ₗ[F] P ⊗[F] Q) (U' : Submodule F Q) : Submodule F W :=
  ⨅ ψ : P →ₗ[F] F, U'.comap (sliceL ψ ∘ₗ e.toLinearMap)

theorem mem_sliceSub (e : W ≃ₗ[F] P ⊗[F] Q) (U' : Submodule F Q) (w : W) :
    w ∈ sliceSub e U' ↔ ∀ ψ : P →ₗ[F] F, sliceL ψ (e w) ∈ U' := by
  simp [sliceSub, Submodule.mem_iInf]

theorem eq_bot_or_top_of_sliceSub [Nontrivial P] (e : W ≃ₗ[F] P ⊗[F] Q) (U' : Submodule F Q)
    (h : sliceSub e U' = ⊥ ∨ sliceSub e U' = ⊤) : U' = ⊥ ∨ U' = ⊤ := by
  obtain ⟨p₀, ψ₀, h₀⟩ := exists_dual_one (P := P) (F := F)
  rcases h with h | h
  · left
    rw [eq_bot_iff]
    intro q hq
    have hw : e.symm (p₀ ⊗ₜ[F] q) ∈ sliceSub e U' := by
      rw [mem_sliceSub]
      intro ψ
      rw [LinearEquiv.apply_symm_apply, sliceL_tmul]
      exact U'.smul_mem _ hq
    rw [h, Submodule.mem_bot] at hw
    have h2 : p₀ ⊗ₜ[F] q = 0 := by
      have := congrArg e hw
      simpa using this
    have h3 : q = sliceL ψ₀ (p₀ ⊗ₜ[F] q) := by simp [sliceL_tmul, h₀]
    rw [h2, map_zero] at h3
    rw [h3]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro q _
    have hw : e.symm (p₀ ⊗ₜ[F] q) ∈ sliceSub e U' := by rw [h]; trivial
    rw [mem_sliceSub] at hw
    have := hw ψ₀
    rw [LinearEquiv.apply_symm_apply, sliceL_tmul, h₀, one_smul] at this
    exact this

theorem second_factor_scalar [Nontrivial P] (e : W ≃ₗ[F] P ⊗[F] Q) (f : Module.End F Q) (c : F)
    (h : ∀ w, e.symm (LinearMap.lTensor P f (e w)) = c • w) : ∀ q, f q = c • q := by
  have h1 : LinearMap.lTensor P f = LinearMap.lTensor P (c • (1 : Module.End F Q)) := by
    refine LinearMap.ext fun u => ?_
    have := congrArg e (h (e.symm u))
    simp only [LinearEquiv.apply_symm_apply, map_smul] at this
    have h1' : LinearMap.lTensor P (1 : Module.End F Q) = LinearMap.id := LinearMap.lTensor_id P Q
    rw [this, LinearMap.lTensor_smul, LinearMap.smul_apply, h1']
    rfl
  have h2 := lTensor_injective' (P := P) h1
  intro q
  rw [h2]
  simp

end SliceSub

section ConsStep

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] {s : ℕ}
  (V : Fin (s+1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
  {Q : Type*} [AddCommGroup Q] [Module F Q]

@[expose] noncomputable def consEquiv (e₁ : W ≃ₗ[F] V 0 ⊗[F] Q)
    (e' : Q ≃ₗ[F] ⨂[F] j : Fin s, V j.succ) : W ≃ₗ[F] ⨂[F] i, V i :=
  e₁.trans ((LinearEquiv.lTensor (V 0) e').trans (tensorConsEquiv V).symm)

theorem consEquiv_zero (e₁ : W ≃ₗ[F] V 0 ⊗[F] Q) (e' : Q ≃ₗ[F] ⨂[F] j : Fin s, V j.succ)
    (a : W ≃ₗ[F] W) (f : Module.End F (V 0))
    (h : ∀ w, e₁ (a w) = LinearMap.rTensor Q f (e₁ w)) (w : W) :
    consEquiv V e₁ e' (a w) = factorEnd 0 f (consEquiv V e₁ e' w) := by
  have hc : ∀ z, factorEnd 0 f ((tensorConsEquiv V).symm z) =
      (tensorConsEquiv V).symm (LinearMap.rTensor _ f z) := by
    intro z
    apply (tensorConsEquiv V).injective
    rw [tensorConsEquiv_factorEnd_zero, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  show (tensorConsEquiv V).symm (LinearEquiv.lTensor (V 0) e' (e₁ (a w))) =
    factorEnd 0 f ((tensorConsEquiv V).symm (LinearEquiv.lTensor (V 0) e' (e₁ w)))
  rw [hc, h]
  congr 1
  have key : ∀ u : V 0 ⊗[F] Q, LinearEquiv.lTensor (V 0) e' (LinearMap.rTensor Q f u) =
      LinearMap.rTensor (⨂[F] j : Fin s, V j.succ) f (LinearEquiv.lTensor (V 0) e' u) := by
    intro u
    induction u with
    | tmul p q => simp
    | add x y hx hy => simp [hx, hy]
  exact key _

theorem consEquiv_succ (e₁ : W ≃ₗ[F] V 0 ⊗[F] Q) (e' : Q ≃ₗ[F] ⨂[F] j : Fin s, V j.succ)
    (a : W ≃ₗ[F] W) (τ : Module.End F Q) (j : Fin s) (g : Module.End F (V j.succ))
    (h1 : ∀ w, e₁ (a w) = LinearMap.lTensor (V 0) τ (e₁ w))
    (h2 : ∀ q, e' (τ q) = factorEnd (V := fun i : Fin s => V i.succ) j g (e' q)) (w : W) :
    consEquiv V e₁ e' (a w) = factorEnd j.succ g (consEquiv V e₁ e' w) := by
  have hc : ∀ z, factorEnd j.succ g ((tensorConsEquiv V).symm z) =
      (tensorConsEquiv V).symm
        (LinearMap.lTensor (V 0) (factorEnd (V := fun i : Fin s => V i.succ) j g) z) := by
    intro z
    apply (tensorConsEquiv V).injective
    rw [tensorConsEquiv_factorEnd_succ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  show (tensorConsEquiv V).symm (LinearEquiv.lTensor (V 0) e' (e₁ (a w))) =
    factorEnd j.succ g ((tensorConsEquiv V).symm (LinearEquiv.lTensor (V 0) e' (e₁ w)))
  rw [hc, h1]
  congr 1
  have key : ∀ u : V 0 ⊗[F] Q, LinearEquiv.lTensor (V 0) e' (LinearMap.lTensor (V 0) τ u) =
      LinearMap.lTensor (V 0) (factorEnd (V := fun i : Fin s => V i.succ) j g)
        (LinearEquiv.lTensor (V 0) e' u) := by
    intro u
    induction u with
    | tmul p q => simp [h2]
    | add x y hx hy => simp [hx, hy]
  exact key _

end ConsStep



section Step

variable {F : Type u} [Field F]

theorem lTensor_rTensor_apply {P Q : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q]
    [Module F Q] (f : Module.End F Q) (a : Module.End F P) (u : P ⊗[F] Q) :
    LinearMap.lTensor P f (LinearMap.rTensor Q a u) =
      LinearMap.rTensor Q a (LinearMap.lTensor P f u) := by
  induction u with
  | tmul p q => simp
  | add x y hx hy => simp [hx, hy]

theorem lTensor_lTensor_apply {P Q : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q]
    [Module F Q] (f τ : Module.End F Q) (hf : ∀ q, f (τ q) = τ (f q)) (u : P ⊗[F] Q) :
    LinearMap.lTensor P f (LinearMap.lTensor P τ u) =
      LinearMap.lTensor P τ (LinearMap.lTensor P f u) := by
  induction u with
  | tmul p q => simp [hf]
  | add x y hx hy => simp [hx, hy]

theorem step_data [Finite F] {s : ℕ} {W : Type u} [AddCommGroup W] [Module F W] [Nontrivial W]
    [Finite W] (G : Fin (s+1) → Type u) [∀ i, Group (G i)] (φ : ∀ i, G i →* (W ≃ₗ[F] W))
    (hcomm : ∀ i j, i ≠ j → ∀ x y, φ i x * φ j y = φ j y * φ i x)
    (hirr : ∀ U : Submodule F W, (∀ i (g : G i), ∀ u ∈ U, φ i g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hend : ∀ f : Module.End F W, (∀ i (g : G i), ∀ w, f (φ i g w) = φ i g (f w)) →
      ∃ c : F, ∀ w, f w = c • w) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module F P) (Q : Type u) (_ : AddCommGroup Q)
      (_ : Module F Q) (ρ₀ : G 0 →* (P ≃ₗ[F] P)) (σ : ∀ j : Fin s, G j.succ →* (Q ≃ₗ[F] Q))
      (e₁ : W ≃ₗ[F] P ⊗[F] Q),
      Nontrivial P ∧ Nontrivial Q ∧ Finite P ∧ Finite Q ∧
      (∀ g w, e₁ (φ 0 g w) = LinearMap.rTensor Q ((ρ₀ g : P ≃ₗ[F] P) : P →ₗ[F] P) (e₁ w)) ∧
      (∀ (j : Fin s) (g : G j.succ) w, e₁ (φ j.succ g w) =
        LinearMap.lTensor P ((σ j g : Q ≃ₗ[F] Q) : Q →ₗ[F] Q) (e₁ w)) ∧
      Submodule.span F (Set.range fun g : G 0 => ((ρ₀ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤ ∧
      (∀ i j, i ≠ j → ∀ x y, σ i x * σ j y = σ j y * σ i x) ∧
      (∀ U : Submodule F Q, (∀ (j : Fin s) (g : G j.succ), ∀ u ∈ U, σ j g u ∈ U) →
        U = ⊥ ∨ U = ⊤) ∧
      (∀ f : Module.End F Q, (∀ (j : Fin s) (g : G j.succ), ∀ q, f (σ j g q) = σ j g (f q)) →
        ∃ c : F, ∀ q, f q = c • q) := by
  classical
  let L : Subgroup (W ≃ₗ[F] W) := (φ 0).range
  let K : Subgroup (W ≃ₗ[F] W) := Subgroup.centralizer (L : Set (W ≃ₗ[F] W))
  have hLK : ∀ x ∈ L, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy x hx
  have hφK : ∀ (j : Fin s) (g : G j.succ), φ j.succ g ∈ K := by
    intro j g
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact hcomm 0 j.succ (Fin.succ_ne_zero j).symm x g
  have hirrLK : IsIrrAct (L ⊔ K) := by
    intro U hU
    refine hirr U ?_
    intro i
    induction i using Fin.cases with
    | zero => intro g u hu; exact hU (φ 0 g) (Subgroup.mem_sup_left ⟨g, rfl⟩) u hu
    | succ j => intro g u hu; exact hU (φ j.succ g) (Subgroup.mem_sup_right (hφK j g)) u hu
  have hendLK : ∀ f : Module.End F W, (∀ h ∈ L ⊔ K, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w := by
    intro f hf
    refine hend f ?_
    intro i
    induction i using Fin.cases with
    | zero => intro g w; exact hf (φ 0 g) (Subgroup.mem_sup_left ⟨g, rfl⟩) w
    | succ j => intro g w; exact hf (φ j.succ g) (Subgroup.mem_sup_right (hφK j g)) w
  obtain ⟨P, _, _, Q, _, _, ρ, σ', e, hP, hQ, hPf, hQf, heL, heK, hspan⟩ :=
    two_factor_split L K hLK hirrLK hendLK
  let ρ₀ : G 0 →* (P ≃ₗ[F] P) := ρ.comp (φ 0).rangeRestrict
  let σ : ∀ j : Fin s, G j.succ →* (Q ≃ₗ[F] Q) := fun j =>
    σ'.comp ((φ j.succ).codRestrict K (hφK j))
  have h0 : ∀ g w, e (φ 0 g w) =
      LinearMap.rTensor Q ((ρ₀ g : P ≃ₗ[F] P) : P →ₗ[F] P) (e w) :=
    fun g w => heL ⟨φ 0 g, g, rfl⟩ w
  have hs : ∀ (j : Fin s) (g : G j.succ) w, e (φ j.succ g w) =
      LinearMap.lTensor P ((σ j g : Q ≃ₗ[F] Q) : Q →ₗ[F] Q) (e w) :=
    fun j g w => heK ⟨φ j.succ g, hφK j g⟩ w
  have hspan₀ : Submodule.span F
      (Set.range fun g : G 0 => ((ρ₀ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤ := by
    have : (Set.range fun g : G 0 => ((ρ₀ g : P ≃ₗ[F] P) : Module.End F P)) =
        Set.range fun l : L => ((ρ l : P ≃ₗ[F] P) : Module.End F P) := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩; exact ⟨(φ 0).rangeRestrict g, rfl⟩
      · rintro ⟨l, rfl⟩
        obtain ⟨g, hg⟩ := (φ 0).rangeRestrict_surjective l
        exact ⟨g, by simp [ρ₀, hg]⟩
    rw [this]; exact hspan
  have hcomm' : ∀ i j, i ≠ j → ∀ x y, σ i x * σ j y = σ j y * σ i x := by
    intro i j hij x y
    show σ' ⟨φ i.succ x, hφK i x⟩ * σ' ⟨φ j.succ y, hφK j y⟩ =
      σ' ⟨φ j.succ y, hφK j y⟩ * σ' ⟨φ i.succ x, hφK i x⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) x y)
  have hirr' : ∀ U : Submodule F Q, (∀ (j : Fin s) (g : G j.succ), ∀ u ∈ U, σ j g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U' hU'
    apply eq_bot_or_top_of_sliceSub e U'
    apply hirr
    intro i
    induction i using Fin.cases with
    | zero =>
      intro g w hw
      rw [mem_sliceSub] at hw ⊢
      intro ψ
      rw [h0, sliceL_rTensor]
      exact hw _
    | succ j =>
      intro g w hw
      rw [mem_sliceSub] at hw ⊢
      intro ψ
      rw [hs, sliceL_lTensor]
      exact hU' j g _ (hw ψ)
  have hend' : ∀ f : Module.End F Q,
      (∀ (j : Fin s) (g : G j.succ), ∀ q, f (σ j g q) = σ j g (f q)) →
      ∃ c : F, ∀ q, f q = c • q := by
    intro f hf
    let TW : Module.End F W := e.symm.toLinearMap ∘ₗ LinearMap.lTensor P f ∘ₗ e.toLinearMap
    have hTW : ∀ i (g : G i) w, TW (φ i g w) = φ i g (TW w) := by
      intro i
      induction i using Fin.cases with
      | zero =>
        intro g w
        apply e.injective
        show e (e.symm (LinearMap.lTensor P f (e (φ 0 g w)))) =
          e (φ 0 g (e.symm (LinearMap.lTensor P f (e w))))
        rw [LinearEquiv.apply_symm_apply, h0, h0, LinearEquiv.apply_symm_apply,
          lTensor_rTensor_apply]
      | succ j =>
        intro g w
        apply e.injective
        show e (e.symm (LinearMap.lTensor P f (e (φ j.succ g w)))) =
          e (φ j.succ g (e.symm (LinearMap.lTensor P f (e w))))
        rw [LinearEquiv.apply_symm_apply, hs, hs, LinearEquiv.apply_symm_apply,
          lTensor_lTensor_apply f _ (hf j g)]
    obtain ⟨c, hc⟩ := hend TW hTW
    exact ⟨c, second_factor_scalar e f c hc⟩
  exact ⟨P, inferInstance, inferInstance, Q, inferInstance, inferInstance, ρ₀, σ, e, hP, hQ, hPf,
    hQf, h0, hs, hspan₀, hcomm', hirr', hend'⟩

end Step



section Core

variable {F : Type u} [Field F]

theorem tensor_decomposition_core [Finite F] : ∀ (s : ℕ) {W : Type u} [AddCommGroup W]
    [Module F W] [Nontrivial W] [Finite W] (G : Fin s → Type u) [∀ i, Group (G i)]
    (φ : ∀ i, G i →* (W ≃ₗ[F] W)),
    (∀ i j, i ≠ j → ∀ x y, φ i x * φ j y = φ j y * φ i x) →
    (∀ U : Submodule F W, (∀ i (g : G i), ∀ u ∈ U, φ i g u ∈ U) → U = ⊥ ∨ U = ⊤) →
    (∀ f : Module.End F W, (∀ i (g : G i), ∀ w, f (φ i g w) = φ i g (f w)) →
      ∃ c : F, ∀ w, f w = c • w) →
    ∃ (V : Fin s → Type u) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module F (V i))
      (ρ : ∀ i, G i →* (V i ≃ₗ[F] V i)) (e : W ≃ₗ[F] ⨂[F] i, V i),
      (∀ i, Nontrivial (V i)) ∧ (∀ i, Finite (V i)) ∧
      (∀ i (g : G i) w, e (φ i g w) =
        factorEnd i ((ρ i g : V i ≃ₗ[F] V i) : Module.End F (V i)) (e w)) ∧
      (∀ i, Submodule.span F
        (Set.range fun g : G i => ((ρ i g : V i ≃ₗ[F] V i) : Module.End F (V i))) = ⊤) := by
  intro s
  induction s with
  | zero =>
    intro W _ _ _ _ G _ φ hcomm hirr hend
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    have htop : (Submodule.span F {w₀} : Submodule F W) = ⊤ := by
      rcases hirr (Submodule.span F {w₀}) (fun i => i.elim0) with h | h
      · exfalso
        apply hw₀
        have hmem : w₀ ∈ Submodule.span F {w₀} := Submodule.subset_span rfl
        rw [h] at hmem
        exact (Submodule.mem_bot F).1 hmem
      · exact h
    let ψ : F ≃ₗ[F] W := LinearEquiv.ofBijective (LinearMap.toSpanSingleton F W w₀)
      ⟨smul_left_injective F hw₀, fun w => by
        have : w ∈ Submodule.span F {w₀} := by rw [htop]; trivial
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
        exact ⟨a, ha⟩⟩
    let V0 : Fin 0 → Type u := fun i => i.elim0
    let iV0 : ∀ i, AddCommGroup (V0 i) := fun i => i.elim0
    let mV0 : ∀ i, Module F (V0 i) := fun i => i.elim0
    exact ⟨V0, iV0, mV0, fun i => i.elim0,
      ψ.symm.trans (PiTensorProduct.isEmptyEquiv (R := F) (s := V0) (Fin 0)).symm,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ s ih =>
    intro W _ _ _ _ G _ φ hcomm hirr hend
    obtain ⟨P, iP, mP, Q, iQ, mQ, ρ₀, σ, e₁, hP, hQ, hPf, hQf, h0, hs, hspan₀, hcomm', hirr',
      hend'⟩ := step_data G φ hcomm hirr hend
    have := hQ
    have := hQf
    obtain ⟨V', iV, mV, ρ', e', hn', hf', heq', hspan'⟩ :=
      ih (W := Q) (fun j => G j.succ) σ hcomm' hirr' hend'
    let V : Fin (s+1) → Type u := Fin.cons (α := fun _ => Type u) P V'
    let iV' : ∀ i, AddCommGroup (V i) := fun i =>
      Fin.cases (motive := fun i => AddCommGroup (V i)) iP iV i
    let mV' : ∀ i, @Module F (V i) _ (iV' i).toAddCommMonoid := fun i =>
      Fin.cases (motive := fun i => @Module F (V i) _ (iV' i).toAddCommMonoid) mP mV i
    let ρ'' : ∀ i, G i →* (@LinearEquiv F F _ _ (RingHom.id F) (RingHom.id F) _ _ (V i) (V i)
        (iV' i).toAddCommMonoid (iV' i).toAddCommMonoid (mV' i) (mV' i)) := fun i =>
      Fin.cases (motive := fun i => G i →* (@LinearEquiv F F _ _ (RingHom.id F) (RingHom.id F) _ _
        (V i) (V i) (iV' i).toAddCommMonoid (iV' i).toAddCommMonoid (mV' i) (mV' i)))
        ρ₀ ρ' i
    let _ := iV'
    let _ := mV'
    refine ⟨V, iV', mV', ρ'', consEquiv V e₁ e', ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact hP
      | succ j => exact hn' j
    · intro i
      induction i using Fin.cases with
      | zero => exact hPf
      | succ j => exact hf' j
    · intro i
      induction i using Fin.cases with
      | zero => intro g w; exact consEquiv_zero V e₁ e' (φ 0 g) _ (h0 g) w
      | succ j =>
        intro g w
        exact consEquiv_succ V e₁ e' (φ j.succ g) _ j _ (hs j g) (heq' j g) w
    · intro i
      induction i using Fin.cases with
      | zero => exact hspan₀
      | succ j => exact hspan' j

end Core



section SpanIff

variable {F : Type*} [Field F] {W X V : Type*} [AddCommGroup W] [Module F W] [AddCommGroup X]
  [Module F X] [AddCommGroup V] [Module F V]

theorem mem_span_iff_of_equivariant {G : Type*} [Group G] (φ : G →* (W ≃ₗ[F] W))
    (ρ : G →* (V ≃ₗ[F] V)) (e : W ≃ₗ[F] X) (Ψ : Module.End F V →ₗ[F] Module.End F X)
    (heq : ∀ g w, e (φ g w) = Ψ (ρ g : Module.End F V) (e w))
    (hspan : Submodule.span F (Set.range fun g => (ρ g : Module.End F V)) = ⊤)
    (T : Module.End F W) :
    T ∈ Submodule.span F (Set.range fun g => ((φ g : W ≃ₗ[F] W) : Module.End F W)) ↔
      ∃ f : Module.End F V, ∀ w, e (T w) = Ψ f (e w) := by
  have h2 : ∀ T ∈ Submodule.span F (Set.range fun g => ((φ g : W ≃ₗ[F] W) : Module.End F W)),
      ∃ f : Module.End F V, ∀ w, e (T w) = Ψ f (e w) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨ρ g, fun w => heq g w⟩
    | zero => exact ⟨0, fun w => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨f₁, h₁⟩ := hx
      obtain ⟨f₂, h₂⟩ := hy
      exact ⟨f₁ + f₂, fun w => by simp [h₁ w, h₂ w]⟩
    | smul c x _ hx =>
      obtain ⟨f₁, h₁⟩ := hx
      exact ⟨c • f₁, fun w => by simp [h₁ w]⟩
  have h1 : ∀ f ∈ Submodule.span F (Set.range fun g => (ρ g : Module.End F V)),
      ∃ T ∈ Submodule.span F (Set.range fun g => ((φ g : W ≃ₗ[F] W) : Module.End F W)),
        ∀ w, e (T w) = Ψ f (e w) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, fun w => heq g w⟩
    | zero => exact ⟨0, Submodule.zero_mem _, fun w => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, hT₁, h₁⟩ := hx
      obtain ⟨T₂, hT₂, h₂⟩ := hy
      exact ⟨T₁ + T₂, Submodule.add_mem _ hT₁ hT₂, fun w => by simp [h₁ w, h₂ w]⟩
    | smul c x _ hx =>
      obtain ⟨T₁, hT₁, h₁⟩ := hx
      exact ⟨c • T₁, Submodule.smul_mem _ _ hT₁, fun w => by simp [h₁ w]⟩
  refine ⟨h2 T, fun ⟨f, hf⟩ => ?_⟩
  obtain ⟨T', hT', hT'f⟩ := h1 f (by rw [hspan]; trivial)
  have : T = T' := LinearMap.ext fun w => e.injective (by rw [hf w, hT'f w])
  rw [this]
  exact hT'

end SpanIff

section Final

variable {F : Type u} [Field F]

theorem commuting_factors_absolutely_irreducible_tensor_decomposition [Finite F]
    {W : Type u} [AddCommGroup W] [Module F W] [Nontrivial W] [Finite W] {s : ℕ}
    (L : Fin s → Subgroup (W ≃ₗ[F] W))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hirr : IsIrrAct (⨆ i, L i))
    (hend : ∀ f : Module.End F W, (∀ h ∈ ⨆ i, L i, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w) :
    ∃ (V : Fin s → Type u) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module F (V i))
      (ρ : ∀ i, L i →* (V i ≃ₗ[F] V i)) (e : W ≃ₗ[F] ⨂[F] i, V i),
      (∀ i, Nontrivial (V i)) ∧ (∀ i, Module.Finite F (V i)) ∧
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i, ∀ l : L i, ∀ w, e ((l : W ≃ₗ[F] W) w) =
        factorEnd i ((ρ i l : V i ≃ₗ[F] V i) : Module.End F (V i)) (e w)) ∧
      (∀ i, Submodule.span F
        (Set.range fun l : L i => ((ρ i l : V i ≃ₗ[F] V i) : Module.End F (V i))) = ⊤) ∧
      (∀ i, ∀ (E : Type v) (_ : Field E) (_ : Algebra F E) (U : Submodule E (E ⊗[F] V i)),
        (∀ l : L i, ∀ u ∈ U,
          (LinearMap.baseChange E ((ρ i l : V i ≃ₗ[F] V i) : V i →ₗ[F] V i)) u ∈ U) →
          U = ⊥ ∨ U = ⊤) ∧
      (∀ i, Group.IsPerfect (L i) → Nontrivial (L i) → 2 ≤ Module.finrank F (V i)) ∧
      (∀ i, ∀ T : Module.End F W,
        T ∈ Submodule.span F (Set.range fun l : L i => ((l : W ≃ₗ[F] W) : Module.End F W)) ↔
          ∃ f : Module.End F (V i), ∀ w, e (T w) = factorEnd i f (e w)) := by
  have hcomm' : ∀ i j, i ≠ j → ∀ (x : L i) (y : L j),
      (L i).subtype x * (L j).subtype y = (L j).subtype y * (L i).subtype x :=
    fun i j hij x y => hcomm i j hij x x.2 y y.2
  have hirr' : ∀ U : Submodule F W, (∀ i (g : L i), ∀ u ∈ U, (L i).subtype g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hirr U ?_
    have hst : ⨆ i, L i ≤ stabSet (U : Set W) :=
      iSup_le fun i => le_stabSet_of_invariant (L i) (U : Set W)
        (fun g hg u hu => hU i ⟨g, hg⟩ u hu)
    intro h hh u hu
    exact (hst hh u).2 hu
  have hend' : ∀ f : Module.End F W,
      (∀ i (g : L i), ∀ w, f ((L i).subtype g w) = (L i).subtype g (f w)) →
      ∃ c : F, ∀ w, f w = c • w := by
    intro f hf
    refine hend f ?_
    have hst : ⨆ i, L i ≤ commutantSubgroup f :=
      iSup_le fun i g hg w => hf i ⟨g, hg⟩ w
    intro h hh w
    exact hst hh w
  obtain ⟨V, iV, mV, ρ, e, hn, hfin, heq, hspan⟩ :=
    tensor_decomposition_core s (fun i => L i) (fun i => (L i).subtype) hcomm' hirr' hend'
  have hmf : ∀ i, Module.Finite F (V i) := fun i => by
    have := hfin i
    exact Module.Finite.of_finite
  have hinj : ∀ i, Function.Injective (ρ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h1 := heq i g w
    rw [hg] at h1
    have h2 : e ((g : W ≃ₗ[F] W) w) = e w := by
      rw [show (L i).subtype g w = (g : W ≃ₗ[F] W) w from rfl] at h1
      rw [h1]
      have : (((1 : V i ≃ₗ[F] V i) : V i ≃ₗ[F] V i) : Module.End F (V i)) = 1 := rfl
      rw [this, factorEnd_one]
      rfl
    exact e.injective h2
  refine ⟨V, iV, mV, ρ, e, hn, hmf, hinj, heq, hspan, ?_, ?_, ?_⟩
  · intro i E _ _ U hU
    have := hmf i
    refine eq_bot_or_top_of_invariant U ?_
    intro f
    have hf : f ∈ Submodule.span F
        (Set.range fun l : L i => ((ρ i l : V i ≃ₗ[F] V i) : Module.End F (V i))) := by
      rw [hspan i]; trivial
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact fun u hu => hU l u hu
    | zero => intro u hu; simp
    | add x y _ _ hx hy =>
      intro u hu
      rw [LinearMap.baseChange_add]
      exact U.add_mem (hx u hu) (hy u hu)
    | smul c x _ hx =>
      intro u hu
      rw [LinearMap.baseChange_smul]
      have := U.smul_mem (algebraMap F E c) (hx u hu)
      simpa [algebraMap_smul] using this
  · intro i hperf hnt
    by_contra hlt
    have := hmf i
    have hpos : 0 < Module.finrank F (V i) := Module.finrank_pos
    have h1 : Module.finrank F (V i) = 1 := by omega
    have hker : (ρ i).ker = ⊤ := by
      rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (linearEquiv_comm_of_finrank_one h1 _ _)
    obtain ⟨x, hx⟩ := exists_ne (1 : L i)
    apply hx
    apply hinj i
    rw [map_one]
    exact MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top x)
  · intro i T
    exact mem_span_iff_of_equivariant (L i).subtype (ρ i) e (factorAlgHom (F := F) (V := V) i).toLinearMap
      (fun g w => heq i g w) (hspan i) T

end Final

end CFSG.QuasithinUnique.Setup.Offender
