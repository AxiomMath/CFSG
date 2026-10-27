module

public import CFSG.HardMathSupport.GuralnickMalle.CyclicTwoDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInvolution
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open scoped TensorProduct

variable {K : Type*} [Field K] [CharP K 2]
variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

noncomputable def wedgeInlInr (a : A) (b : B) : ⋀[K]^2 (A × B) :=
  exteriorPower.ιMulti K 2 ![LinearMap.inl K A B a, LinearMap.inr K A B b]

lemma wedgeInlInr_coe (a : A) (b : B) :
    (wedgeInlInr (K := K) a b : ExteriorAlgebra K (A × B)) =
      ExteriorAlgebra.ι K (LinearMap.inl K A B a) *
        ExteriorAlgebra.ι K (LinearMap.inr K A B b) := by
  rw [wedgeInlInr, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

lemma wedgeInlInr_add_left (a₁ a₂ : A) (b : B) :
    wedgeInlInr (K := K) (a₁ + a₂) b =
      wedgeInlInr (K := K) a₁ b + wedgeInlInr (K := K) a₂ b := by
  apply Subtype.ext
  simp only [Submodule.coe_add]
  rw [wedgeInlInr_coe, wedgeInlInr_coe, wedgeInlInr_coe]
  simp only [map_add, add_mul]

lemma wedgeInlInr_smul_left (c : K) (a : A) (b : B) :
    wedgeInlInr (K := K) (c • a) b = c • wedgeInlInr (K := K) a b := by
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [wedgeInlInr_coe, wedgeInlInr_coe]
  simp only [map_smul, smul_mul_assoc]

lemma wedgeInlInr_add_right (a : A) (b₁ b₂ : B) :
    wedgeInlInr (K := K) a (b₁ + b₂) =
      wedgeInlInr (K := K) a b₁ + wedgeInlInr (K := K) a b₂ := by
  apply Subtype.ext
  simp only [Submodule.coe_add]
  rw [wedgeInlInr_coe, wedgeInlInr_coe, wedgeInlInr_coe]
  simp only [map_add, mul_add]

lemma wedgeInlInr_smul_right (c : K) (a : A) (b : B) :
    wedgeInlInr (K := K) a (c • b) = c • wedgeInlInr (K := K) a b := by
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [wedgeInlInr_coe, wedgeInlInr_coe]
  simp only [map_smul, mul_smul_comm]

noncomputable def wedgeCross : A ⊗[K] B →ₗ[K] ⋀[K]^2 (A × B) :=
  TensorProduct.lift
    (LinearMap.mk₂ K (fun a b => wedgeInlInr (K := K) a b)
      wedgeInlInr_add_left wedgeInlInr_smul_left wedgeInlInr_add_right wedgeInlInr_smul_right)

@[simp]
lemma wedgeCross_tmul (a : A) (b : B) :
    wedgeCross (K := K) (a ⊗ₜ[K] b) = wedgeInlInr (K := K) a b := by
  rw [wedgeCross, TensorProduct.lift.tmul]
  rfl

theorem add_self_eq_zero_of_char_two {V : Type*} [AddCommGroup V] [Module K V]
    (v : V) : v + v = 0 := by
  have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rwa [two_smul] at h2

noncomputable def exteriorProdMap :
    ((⋀[K]^2 A) × (A ⊗[K] B)) × (⋀[K]^2 B) →ₗ[K] ⋀[K]^2 (A × B) :=
  ((exteriorPower.map 2 (LinearMap.inl K A B)).coprod (wedgeCross (K := K))).coprod
    (exteriorPower.map 2 (LinearMap.inr K A B))

@[simp]
lemma exteriorProdMap_apply (x : ⋀[K]^2 A) (y : A ⊗[K] B) (z : ⋀[K]^2 B) :
    exteriorProdMap (K := K) ((x, y), z) =
      exteriorPower.map 2 (LinearMap.inl K A B) x + wedgeCross (K := K) y +
        exteriorPower.map 2 (LinearMap.inr K A B) z := by
  simp [exteriorProdMap, LinearMap.coprod_apply, add_assoc]

theorem finrank_ker_prodMap_sub_one {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] V) (g : W →ₗ[K] W) :
    finrank K (LinearMap.ker (f.prodMap g - 1)) =
      finrank K (LinearMap.ker (f - 1)) + finrank K (LinearMap.ker (g - 1)) := by
  have hker : LinearMap.ker (f.prodMap g - 1) = (LinearMap.ker (f - 1)).prod (LinearMap.ker (g - 1)) := by
    ext z
    simp only [LinearMap.mem_ker, Submodule.mem_prod, LinearMap.sub_apply, LinearMap.prodMap_apply,
      Module.End.one_apply, Prod.mk_sub_mk, sub_eq_zero]
    exact Prod.ext_iff
  rw [hker, LinearEquiv.finrank_eq (Submodule.prodEquiv _ _), Module.finrank_prod]

noncomputable def blockJ : K × K →ₗ[K] K × K :=
  LinearMap.prod (LinearMap.fst K K K) ((LinearMap.fst K K K) + (LinearMap.snd K K K))

@[simp]
lemma blockJ_apply (p q : K) : blockJ (K := K) (p, q) = (p, p + q) := by
  simp [blockJ]

noncomputable def blockJFixedEquiv : K ≃ₗ[K] LinearMap.ker (blockJ (K := K) - 1) where
  toFun q := ⟨(0, q), by
    simp [LinearMap.mem_ker, blockJ]⟩
  invFun z := z.1.2
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp
  left_inv q := rfl
  right_inv z := by
    obtain ⟨⟨p, q⟩, hz⟩ := z
    have hz' : blockJ (K := K) (p, q) = (p, q) := by
      simpa [LinearMap.mem_ker, sub_eq_zero] using hz
    have h : p + q = q := congrArg Prod.snd hz'
    have hp : p = 0 := by
      have h2 : p + q = 0 + q := by simpa using h
      exact add_right_cancel h2
    subst hp
    exact Subtype.ext (Prod.ext rfl rfl)

noncomputable def submodulePiEquiv {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] (p : ∀ i, Submodule K (M i)) :
    (Submodule.pi Set.univ p) ≃ₗ[K] (∀ i, p i) where
  toFun z i := ⟨z.1 i, z.2 i trivial⟩
  invFun z := ⟨fun i => (z i).1, fun i _ => (z i).2⟩
  map_add' x y := by ext i <;> rfl
  map_smul' c x := by ext i <;> rfl
  left_inv z := by ext i <;> rfl
  right_inv z := by ext i <;> rfl

theorem finrank_ker_piMap_sub_one {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]
    (f : ∀ i, M i →ₗ[K] M i) :
    finrank K (LinearMap.ker (LinearMap.piMap f - 1)) =
      ∑ i, finrank K (LinearMap.ker (f i - 1)) := by
  have hker : LinearMap.ker (LinearMap.piMap f - 1) =
      Submodule.pi Set.univ (fun i => LinearMap.ker (f i - 1)) := by
    ext z
    simp only [LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ, forall_true_left,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [funext_iff]
    simp only [LinearMap.piMap, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_proj]
  rw [hker, LinearEquiv.finrank_eq (submodulePiEquiv (K := K) (fun i => LinearMap.ker (f i - 1))),
    Module.finrank_pi_fintype]

noncomputable def blockAction {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) : W × W →ₗ[K] W × W :=
  LinearMap.prod (S.comp (LinearMap.fst K W W)) ((S.comp (LinearMap.fst K W W)) + (S.comp (LinearMap.snd K W W)))

@[simp]
theorem blockAction_apply {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) (u v : W) : blockAction S (u, v) = (S u, S u + S v) := by
  simp [blockAction]

noncomputable def tensorBlockEquiv (W : Type*) [AddCommGroup W] [Module K W] :
    (K × K) ⊗[K] W ≃ₗ[K] W × W :=
  (TensorProduct.prodLeft K K K K W).trans
    ((TensorProduct.lid K W).prodCongr (TensorProduct.lid K W))

@[simp]
theorem tensorBlockEquiv_tmul {W : Type*} [AddCommGroup W] [Module K W]
    (p q : K) (w : W) :
    tensorBlockEquiv W ((p, q) ⊗ₜ[K] w) = (p • w, q • w) := by
  simp [tensorBlockEquiv]

theorem tensorBlockEquiv_map {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) (x : (K × K) ⊗[K] W) :
    tensorBlockEquiv W (TensorProduct.map (blockJ (K := K)) S x) =
      blockAction S (tensorBlockEquiv W x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
    obtain ⟨p, q⟩ := p
    simp [blockJ, blockAction, add_smul, smul_add]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma blockAction_fixed_iff {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) (hS : S.comp S = 1) (u v : W) :
    blockAction S (u, v) = (u, v) ↔ u = (S - 1) v := by
  obtain ⟨N, hNdef⟩ : ∃ N : W →ₗ[K] W, N = S - 1 := ⟨_, rfl⟩
  have hN : N.comp N = 0 := by
    rw [hNdef]
    exact sub_one_comp_sub_one_eq_zero S hS
  have hNv : N (N v) = 0 := by
    have := congrArg (fun f : W →ₗ[K] W => f v) hN
    simpa [LinearMap.comp_apply] using this
  have hS' : S = 1 + N := by
    rw [hNdef]
    abel
  constructor
  · intro h
    have h1 : S u = u := congrArg Prod.fst h
    have h2 : S u + S v = v := congrArg Prod.snd h
    rw [h1] at h2
    have h3 : S v = u + v := by
      have h4 : S v = u + (u + S v) := by
        rw [← add_assoc, add_self_eq_zero_of_char_two (K := K) u, zero_add]
      rwa [h2] at h4
    change u = (S - 1) v
    rw [LinearMap.sub_apply, Module.End.one_apply, h3, add_sub_cancel_right]
  · intro h
    subst h
    have h1 : S (N v) = N v := by
      calc S (N v) = (1 + N) (N v) := congrArg (fun f : W →ₗ[K] W => f (N v)) hS'
        _ = N v + N (N v) := by simp
        _ = N v := by rw [hNv, add_zero]
    have h2 : S (N v) + S v = v := by
      calc S (N v) + S v = N v + (1 + N) v := by
            rw [h1, congrArg (fun f : W →ₗ[K] W => f v) hS']
        _ = N v + (v + N v) := by simp
        _ = v := by
          calc N v + (v + N v) = v + (N v + N v) := by abel
            _ = v := by rw [add_self_eq_zero_of_char_two (K := K) (N v), add_zero]
    refine Prod.ext ?_ ?_
    · rw [← hNdef]
      change S (N v) = N v
      exact h1
    · rw [← hNdef]
      change S (N v) + S v = v
      exact h2

noncomputable def blockActionKerEquiv {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    W ≃ₗ[K] LinearMap.ker (blockAction S - 1) where
  toFun w := ⟨((S - 1) w, w), by
    rw [LinearMap.mem_ker]
    simpa [LinearMap.sub_apply, sub_eq_zero] using
      (blockAction_fixed_iff S hS ((S - 1) w) w).mpr rfl⟩
  invFun z := z.1.2
  map_add' x y := by
    ext <;> simp [map_add]
  map_smul' c x := by
    ext <;> simp
  left_inv w := rfl
  right_inv z := by
    obtain ⟨⟨u, v⟩, hz⟩ := z
    have hz' : blockAction S (u, v) = (u, v) := by
      simpa [LinearMap.sub_apply, sub_eq_zero] using hz
    have huv : u = (S - 1) v := (blockAction_fixed_iff S hS u v).mp hz'
    subst huv
    exact Subtype.ext rfl

theorem finrank_ker_blockAction {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    finrank K (LinearMap.ker (blockAction S - 1)) = finrank K W := by
  rw [← LinearEquiv.finrank_eq (blockActionKerEquiv S hS)]

theorem finrank_ker_blockJ_tensor {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    finrank K (LinearMap.ker (TensorProduct.map (blockJ (K := K)) S - 1)) =
      finrank K W := by
  have h := CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining
    (tensorBlockEquiv W) (TensorProduct.map (blockJ (K := K)) S) (blockAction S)
    (fun x => tensorBlockEquiv_map S x)
  rw [← h, finrank_ker_blockAction S hS]

lemma piLeft_tmul {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    {W : Type*} [AddCommGroup W] [Module K W] (m : ∀ i, M i) (w : W) :
    TensorProduct.piLeft K W M (m ⊗ₜ[K] w) = fun i => m i ⊗ₜ[K] w := by
  simp only [TensorProduct.piLeft, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  ext i
  simp [TensorProduct.comm_tmul]

theorem finrank_ker_tensor_one_left {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) :
    finrank K (LinearMap.ker (TensorProduct.map (1 : K →ₗ[K] K) S - 1)) =
      finrank K (LinearMap.ker (S - 1)) := by
  have h : ∀ x, TensorProduct.lid K W (TensorProduct.map (1 : K →ₗ[K] K) S x) = S (TensorProduct.lid K W x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r w => simp
    | add x y hx hy => simp [map_add, hx, hy]
  exact (CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining
    (TensorProduct.lid K W) (TensorProduct.map (1 : K →ₗ[K] K) S) S h).symm

lemma piLeft_map_piMap {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : ∀ i, M i →ₗ[K] M i) (S : W →ₗ[K] W) (x : (∀ i, M i) ⊗[K] W) :
    TensorProduct.piLeft K W M (TensorProduct.map (LinearMap.piMap f) S x) =
      LinearMap.piMap (fun i => TensorProduct.map (f i) S) (TensorProduct.piLeft K W M x) := by
  induction x using TensorProduct.induction_on with
  | zero => ext i; simp [LinearMap.piMap]
  | tmul m w =>
    simp only [TensorProduct.map_tmul, piLeft_tmul, LinearMap.piMap, LinearMap.pi_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finrank_ker_tensor_piMap {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : ∀ i, M i →ₗ[K] M i) (S : W →ₗ[K] W) :
    finrank K (LinearMap.ker (TensorProduct.map (LinearMap.piMap f) S - 1)) =
      ∑ i, finrank K (LinearMap.ker (TensorProduct.map (f i) S - 1)) := by
  let e := TensorProduct.piLeft K W M
  have h := CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining e
    (TensorProduct.map (LinearMap.piMap f) S)
    (LinearMap.piMap (fun i => TensorProduct.map (f i) S))
    (fun x => piLeft_map_piMap f S x)
  rw [← h]
  exact finrank_ker_piMap_sub_one (fun i => TensorProduct.map (f i) S)

theorem one_eq_piMap_one (a : ℕ) :
    (1 : (Fin a → K) →ₗ[K] (Fin a → K)) =
      LinearMap.piMap (fun _ : Fin a => (1 : K →ₗ[K] K)) := by
  ext x i
  simp [LinearMap.piMap]

theorem one_add_stdN_eq_prodMap (a b : ℕ) :
    (1 + stdN (K := K) a b :
        ((Fin a → K) × (Fin b → K × K)) →ₗ[K] ((Fin a → K) × (Fin b → K × K))) =
      (1 : (Fin a → K) →ₗ[K] (Fin a → K)).prodMap
        (LinearMap.piMap (fun _ : Fin b => blockJ (K := K))) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, y⟩ := z
  rw [one_add_stdN_apply]
  refine Prod.ext rfl ?_
  funext i
  simp [LinearMap.prodMap_apply, LinearMap.piMap, blockJ]

theorem prodLeft_map_prodMap {A B W : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup W] [Module K W]
    (f : A →ₗ[K] A) (g : B →ₗ[K] B) (S : W →ₗ[K] W) (x : (A × B) ⊗[K] W) :
    TensorProduct.prodLeft K K A B W (TensorProduct.map (f.prodMap g) S x) =
      (TensorProduct.map f S).prodMap (TensorProduct.map g S)
        (TensorProduct.prodLeft K K A B W x) := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul p w =>
    obtain ⟨a, b⟩ := p
    simp [LinearMap.prodMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finrank_fixed_tensor_model {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (a b : ℕ) (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    finrank K (LinearMap.ker (TensorProduct.map (1 + stdN (K := K) a b) S - 1)) =
      a * finrank K (LinearMap.ker (S - 1)) + b * finrank K W := by
  rw [one_add_stdN_eq_prodMap]
  let e := TensorProduct.prodLeft K K (Fin a → K) (Fin b → K × K) W
  have h := CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining e
    (TensorProduct.map ((1 : (Fin a → K) →ₗ[K] (Fin a → K)).prodMap
      (LinearMap.piMap (fun _ : Fin b => blockJ (K := K)))) S)
    ((TensorProduct.map (1 : (Fin a → K) →ₗ[K] (Fin a → K)) S).prodMap
      (TensorProduct.map (LinearMap.piMap (fun _ : Fin b => blockJ (K := K))) S))
    (fun x => prodLeft_map_prodMap _ _ S x)
  rw [← h, finrank_ker_prodMap_sub_one]
  have hA : finrank K (LinearMap.ker
      (TensorProduct.map (1 : (Fin a → K) →ₗ[K] (Fin a → K)) S - 1)) =
      a * finrank K (LinearMap.ker (S - 1)) := by
    rw [one_eq_piMap_one, finrank_ker_tensor_piMap]
    simp only [finrank_ker_tensor_one_left]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  have hB : finrank K (LinearMap.ker
      (TensorProduct.map (LinearMap.piMap (fun _ : Fin b => blockJ (K := K))) S - 1)) =
      b * finrank K W := by
    rw [finrank_ker_tensor_piMap]
    have hsum : (∑ i : Fin b, finrank K (LinearMap.ker
        (TensorProduct.map (blockJ (K := K) : K × K →ₗ[K] K × K) S - 1))) =
        b * finrank K W := by
      simp [finrank_ker_blockJ_tensor S hS]
    exact hsum
  rw [hA, hB]

theorem finrank_ker_tensorMap_congr {V V' W W' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (T : V →ₗ[K] V) (S : W →ₗ[K] W) (T' : V' →ₗ[K] V') (S' : W' →ₗ[K] W')
    (hT : ∀ v, eV (T v) = T' (eV v)) (hS : ∀ w, eW (S w) = S' (eW w)) :
    finrank K (LinearMap.ker (TensorProduct.map T S - 1)) =
      finrank K (LinearMap.ker (TensorProduct.map T' S' - 1)) := by
  let Φ : (V ⊗[K] W) ≃ₗ[K] (V' ⊗[K] W') := TensorProduct.congr eV eW
  have h : ∀ x, Φ (TensorProduct.map T S x) = TensorProduct.map T' S' (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [Φ, TensorProduct.congr_tmul, TensorProduct.map_tmul, hT, hS]
    | add x y hx hy => simp [map_add, hx, hy]
  exact (CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining
    Φ (TensorProduct.map T S) (TensorProduct.map T' S') h).symm

theorem finrank_le_two_mul_finrank_ker_sub_one {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    finrank K W ≤ 2 * finrank K (LinearMap.ker (S - 1)) := by
  let N : W →ₗ[K] W := S - 1
  have hN : N.comp N = 0 := by simpa [N] using sub_one_comp_sub_one_eq_zero S hS
  have hle : N.range ≤ N.ker := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have h := congrArg (fun f : W →ₗ[K] W => f x) hN
    simpa [LinearMap.comp_apply] using h
  have hmono : finrank K N.range ≤ finrank K N.ker := Submodule.finrank_mono hle
  have hsum := LinearMap.finrank_range_add_finrank_ker N
  have hker : finrank K N.ker = finrank K (LinearMap.ker (S - 1)) := rfl
  omega

theorem finrank_fixed_tensor_le {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : V →ₗ[K] V) (hT : T.comp T = 1) (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) ≤
      min (Module.finrank K V * Module.finrank K (LinearMap.ker (S - 1)))
          (Module.finrank K (LinearMap.ker (T - 1)) * Module.finrank K W) ∧
      Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) ≤
        (Module.finrank K V - Module.finrank K (LinearMap.ker (T - 1))) *
          (Module.finrank K W - Module.finrank K (LinearMap.ker (S - 1))) +
        Module.finrank K (LinearMap.ker (T - 1)) * Module.finrank K (LinearMap.ker (S - 1)) := by
  classical
  obtain ⟨a, b, e, he⟩ := exists_decomposition_involution T hT
  set TM : ((Fin a → K) × (Fin b → K × K)) →ₗ[K] ((Fin a → K) × (Fin b → K × K)) :=
    1 + stdN (K := K) a b with hTM_def
  have hTM : ∀ v, e (T v) = TM (e v) := by
    intro v
    rw [he v, hTM_def, one_add_stdN_apply]
  have hD : Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) =
      Module.finrank K (LinearMap.ker (TensorProduct.map TM S - 1)) :=
    finrank_ker_tensorMap_congr e (LinearEquiv.refl K W) T S TM S hTM (fun w => rfl)
  have hModel := finrank_fixed_tensor_model (K := K) a b S hS
  have hD' : Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) =
      a * Module.finrank K (LinearMap.ker (S - 1)) + b * Module.finrank K W := by
    rw [hD, hModel]
  set n := Module.finrank K V with hn_def
  set z := Module.finrank K (LinearMap.ker (T - 1)) with hz_def
  set m := Module.finrank K W with hm_def
  set y := Module.finrank K (LinearMap.ker (S - 1)) with hy_def
  have hn : n = a + 2 * b := by
    rw [hn_def]
    exact finrank_eq_add_two_mul e
  have hz : z = a + b := by
    rw [hz_def]
    exact finrank_fixed_eq T e he
  have hy_le_m : y ≤ m := by
    rw [hy_def, hm_def]
    exact Submodule.finrank_le _
  have hm_le : m ≤ 2 * y := by
    rw [hm_def, hy_def]
    exact finrank_le_two_mul_finrank_ker_sub_one S hS
  have hbound1 : Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) ≤ n * y := by
    rw [hD', hn, hy_def]
    have hb : b * Module.finrank K W ≤ b * (2 * y) := Nat.mul_le_mul_left b hm_le
    have h1 : a * y + b * Module.finrank K W ≤ a * y + b * (2 * y) :=
      Nat.add_le_add_left hb _
    calc a * y + b * Module.finrank K W ≤ a * y + b * (2 * y) := h1
      _ = (a + 2 * b) * y := by ring
  have hboundz : Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) ≤ z * m := by
    rw [hD', hz, hm_def]
    have hy' : Module.finrank K (LinearMap.ker (S - 1)) ≤ m := by
      rw [hy_def] at hy_le_m
      exact hy_le_m
    have h1 : a * Module.finrank K (LinearMap.ker (S - 1)) ≤ a * m :=
      Nat.mul_le_mul_left a hy'
    calc a * Module.finrank K (LinearMap.ker (S - 1)) + b * m ≤ a * m + b * m :=
          Nat.add_le_add_right h1 _
      _ = (a + b) * m := by ring
  have hEq : Module.finrank K (LinearMap.ker (TensorProduct.map T S - 1)) =
      (n - z) * (m - y) + z * y := by
    have hnz : n - z = b := by
      rw [hn, hz]
      omega
    rw [hD', hnz, hz]
    rw [Nat.mul_sub_left_distrib, Nat.add_mul]
    have hby : b * y ≤ b * m := Nat.mul_le_mul_left b hy_le_m
    have h1 : (b * m - b * y) + (a * y + b * y) = ((b * m - b * y) + b * y) + a * y := by
      ac_rfl
    rw [h1, Nat.sub_add_cancel hby, Nat.add_comm]
  exact ⟨le_min hbound1 hboundz, le_of_eq hEq⟩

end CFSG.HardMathSupport.GuralnickMalle
