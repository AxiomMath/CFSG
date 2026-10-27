module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bGamma
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.QuasithinUnique.Setup.X7 CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section ShiftNat

@[expose] def shiftNat (f i : ℕ) : ℕ := (i + f) % (2 * f)

theorem shiftNat_lt {f : ℕ} (hf : 1 ≤ f) (i : ℕ) : shiftNat f i < 2 * f :=
  Nat.mod_lt _ (by omega)

theorem shiftNat_shiftNat {f : ℕ} {i : ℕ} (hi : i < 2 * f) :
    shiftNat f (shiftNat f i) = i := by
  unfold shiftNat
  rcases lt_or_ge (i + f) (2 * f) with h | h
  · rw [Nat.mod_eq_of_lt h, show i + f + f = i + 2 * f by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · have h1 : (i + f) % (2 * f) = i - f := by
      rw [show i + f = (i - f) + 2 * f by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, show i - f + f = i by omega, Nat.mod_eq_of_lt hi]

theorem shiftNat_ne_self {f : ℕ} (hf : 1 ≤ f) {i : ℕ} (hi : i < 2 * f) : shiftNat f i ≠ i := by
  intro h
  have h2 : shiftNat f (shiftNat f i) = i := shiftNat_shiftNat hi
  unfold shiftNat at h
  rcases lt_or_ge (i + f) (2 * f) with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at h
    omega
  · have h1 : (i + f) % (2 * f) = i - f := by
      rw [show i + f = (i - f) + 2 * f by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1] at h
    omega

end ShiftNat

section FlipMat

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

variable {A : Finset ℕ} (hf : 1 ≤ f) (hA : A ⊆ Finset.range (2 * f)) (hsh : shiftSet f f A = A)

include hsh in
@[expose] def shiftFun (i : ↥A) : ↥A :=
  ⟨shiftNat f i, by
    have h : shiftNat f i ∈ shiftSet f f A := Finset.mem_image_of_mem _ i.2
    rwa [hsh] at h⟩

include hA in
theorem shiftFun_involutive : Function.Involutive (shiftFun hsh) := fun i =>
  Subtype.ext (shiftNat_shiftNat (Finset.mem_range.mp (hA i.2)))

include hf hA in
theorem shiftFun_ne_self (i : ↥A) : shiftFun hsh i ≠ i := fun h =>
  shiftNat_ne_self hf (Finset.mem_range.mp (hA i.2)) (congrArg Subtype.val h)

include hA in
@[expose] def shiftEquiv : Equiv.Perm ↥A := (shiftFun_involutive hA hsh).toPerm _

include hA in
theorem shiftEquiv_apply (i : ↥A) : shiftEquiv hA hsh i = shiftFun hsh i := rfl

include hA in
theorem shiftEquiv_symm : (shiftEquiv hA hsh).symm = shiftEquiv hA hsh :=
  Function.Involutive.toPerm_symm (shiftFun_involutive hA hsh)

include hA in
@[expose] def flipEquiv : (↥A → Fin 4) ≃ (↥A → Fin 4) :=
  Equiv.arrowCongr (shiftEquiv hA hsh) (Equiv.refl (Fin 4))

include hA in
theorem flipEquiv_apply (x : ↥A → Fin 4) (i : ↥A) : flipEquiv hA hsh x i = x (shiftFun hsh i) := by
  simp only [flipEquiv, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
    shiftEquiv_symm]
  rfl

include hA in
theorem flipEquiv_symm : (flipEquiv hA hsh).symm = flipEquiv hA hsh := by
  simp only [flipEquiv, Equiv.arrowCongr_symm, shiftEquiv_symm, Equiv.refl_symm]

include hA in
theorem flipEquiv_flipEquiv (x : ↥A → Fin 4) : flipEquiv hA hsh (flipEquiv hA hsh x) = x := by
  funext i
  rw [flipEquiv_apply, flipEquiv_apply]
  exact congrArg x (shiftFun_involutive hA hsh i)

include hA in
theorem flip_matIso (hF : Fintype.card F = 2 ^ f) :
    MatIso ((tensorRepS (F := F) F A).comp (minorAut F ^ f).toMonoidHom)
      (tensorRepS (F := F) F A) (permMat F (flipEquiv hA hsh)) (permMat F (flipEquiv hA hsh).symm) := by
  refine matIso_of_reindex (flipEquiv hA hsh) (fun g x' x => ?_)
  rw [tensorRepS_apply]
  show ∏ j : ↥A, natRepS (F := F) F j g ((flipEquiv hA hsh x') j) ((flipEquiv hA hsh x) j) =
    tensorRepS (F := F) F A ((minorAut F ^ f) g) x' x
  rw [tensorRepS_apply]
  refine (Fintype.prod_equiv (shiftEquiv hA hsh) _ _ (fun i => ?_)).symm
  rw [shiftEquiv_apply, flipEquiv_apply, flipEquiv_apply, shiftFun_involutive hA hsh i]
  show natRepS (F := F) F i ((minorAut F ^ f) g) (x' i) (x i) =
    natRepS (F := F) F (shiftNat f i) g (x' i) (x i)
  rw [← tensorRepS_comp_shift_aux F hF i f g]
  rfl

end FlipMat

section Schur

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem schur_tensorRepS (hF : Fintype.card F = 2 ^ f) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (C : Matrix (↥A → Fin 4) (↥A → Fin 4) F)
    (hC : ∀ g, C * tensorRepS (F := F) F A g = tensorRepS (F := F) F A g * C) :
    ∃ c : F, C = c • (1 : Matrix (↥A → Fin 4) (↥A → Fin 4) F) := by
  obtain ⟨-, hirr, hfix, -⟩ := squarefree_tensor_fixed_line_and_character (F := F) F hF hA
  have hv : hwS F A ∈ fixedSub (matRep (tensorRepS (F := F) F A)) (upperUniSp F) := by
    rw [hfix]
    exact Submodule.mem_span_singleton_self _
  have hmem : C.mulVec (hwS F A) ∈ fixedSub (matRep (tensorRepS (F := F) F A)) (upperUniSp F) := by
    intro u hu
    have h1 : (tensorRepS (F := F) F A u).mulVec (hwS F A) = hwS F A := hv u hu
    show (tensorRepS (F := F) F A u).mulVec (C.mulVec (hwS F A)) = C.mulVec (hwS F A)
    rw [Matrix.mulVec_mulVec, ← hC u, ← Matrix.mulVec_mulVec, h1]
  rw [hfix] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_⟩
  set D : Matrix (↥A → Fin 4) (↥A → Fin 4) F := C - c • 1 with hDdef
  have hD : ∀ g, D * tensorRepS (F := F) F A g = tensorRepS (F := F) F A g * D := fun g => by
    rw [hDdef, Matrix.sub_mul, Matrix.mul_sub, hC g]
    simp
  have hDv : D.mulVec (hwS F A) = 0 := by
    rw [hDdef, Matrix.sub_mulVec, ← hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  let K : Subrepresentation (matRep (tensorRepS (F := F) F A)) :=
    ⟨LinearMap.ker (Matrix.mulVecLin D), fun g v hv => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      show D.mulVec ((tensorRepS (F := F) F A g).mulVec v) = 0
      rw [Matrix.mulVec_mulVec, hD g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]⟩
  rcases hirr.eq_bot_or_eq_top K with hK | hK
  · exfalso
    have h1 : hwS F A ∈ K.toSubmodule := by
      show hwS F A ∈ LinearMap.ker (Matrix.mulVecLin D)
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hDv
    have h2 : K.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hK
    rw [h2, Submodule.mem_bot] at h1
    exact hwS_ne_zero F A h1
  · have hall : ∀ v, D.mulVec v = 0 := fun v => by
      have h1 : v ∈ K.toSubmodule := by
        rw [show K.toSubmodule = ⊤ from congrArg Subrepresentation.toSubmodule hK]
        trivial
      have h2 : v ∈ LinearMap.ker (Matrix.mulVecLin D) := h1
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    have hD0 : D = 0 := by
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this
    exact sub_eq_zero.mp hD0

end Schur

section FlipRank

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem flip_rank_ge (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (hne : A.Nonempty)
    (S : Matrix (↥A → Fin 4) (↥A → Fin 4) F) (hSS : S * S = 1)
    (hS : ∀ g, S * tensorRepS (F := F) F A g =
      tensorRepS (F := F) F A ((minorAut F ^ f) g) * S) : 6 ≤ (S - 1).rank := by
  have hsh : shiftSet f f A = A := by
    have hiso : MatIso (tensorRepS (F := F) F A)
        ((tensorRepS (F := F) F A).comp (minorAut F ^ f).toMonoidHom) S S := ⟨hSS, hSS, hS⟩
    obtain ⟨e1⟩ := hiso.equiv
    obtain ⟨e2⟩ := tensorRepS_comp_shift (F := F) F hF hA f
    exact ((tensorRepS_absolutely_irreducible_and_distinct (k := F) hF hf).2 A hA (shiftSet f f A)
      (shiftSet_subset hf f A) ⟨e1.trans e2⟩).symm
  set e := flipEquiv hA hsh with he
  have hMat := flip_matIso hA hsh hF
  have hee : e.symm = e := flipEquiv_symm hA hsh
  rw [← he, hee] at hMat
  set P := permMat F e with hP
  have hP2 : P * P = 1 := hMat.mul_inv
  have hPT : ∀ g, P * tensorRepS (F := F) F A ((minorAut F ^ f) g) = tensorRepS (F := F) F A g * P :=
    fun g => hMat.comm g
  have hC : ∀ g, (P * S) * tensorRepS (F := F) F A g = tensorRepS (F := F) F A g * (P * S) := by
    intro g
    rw [Matrix.mul_assoc, hS g, ← Matrix.mul_assoc, hPT g, Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := schur_tensorRepS hF hA (P * S) hC
  have hSP : S = c • P := by
    calc S = (P * P) * S := by rw [hP2, Matrix.one_mul]
      _ = P * (P * S) := by rw [Matrix.mul_assoc]
      _ = c • P := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  have hcc : c * c = 1 := by
    have h1 : S * S = (c * c) • (1 : Matrix (↥A → Fin 4) (↥A → Fin 4) F) := by
      rw [hSP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP2]
    rw [hSS] at h1
    have h2 := congrFun (congrFun h1 (fun _ => 0)) (fun _ => 0)
    simpa using h2.symm
  have hc1 : c = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h : (c + 1) * (c + 1) = 0 := by linear_combination hcc + (c + 1) * h2
    have := mul_self_eq_zero.mp h
    exact CharTwo.add_eq_zero.mp this
  rw [hc1, one_smul] at hSP
  subst hSP
  have hperm : e * e = 1 := Equiv.ext fun x => flipEquiv_flipEquiv hA hsh x
  have hrank : (P - 1).rank * 2 + Fintype.card {x : ↥A → Fin 4 // e x = x} =
      Fintype.card (↥A → Fin 4) := rank_permMat_sub_one (k := F) e hperm
  obtain ⟨i₀, hi₀⟩ := hne
  let i₁ : ↥A := ⟨i₀, hi₀⟩
  let j₁ : ↥A := shiftFun hsh i₁
  have hij : j₁ ≠ i₁ := shiftFun_ne_self hf hA hsh i₁
  let xc : {p : Fin 4 × Fin 4 // p.1 ≠ p.2} → (↥A → Fin 4) := fun c i =>
    if i = i₁ then c.1.1 else if i = j₁ then c.1.2 else 0
  have hxc1 : ∀ c, xc c i₁ = c.1.1 := fun c => by simp [xc]
  have hxc2 : ∀ c, xc c j₁ = c.1.2 := fun c => by simp [xc, hij]
  have hmoved : ∀ c, e (xc c) ≠ xc c := fun c h => by
    have h1 := congrFun h i₁
    rw [he, flipEquiv_apply, hxc1] at h1
    exact c.2 (by rw [← h1, ← hxc2 c])
  let f₀ : {p : Fin 4 × Fin 4 // p.1 ≠ p.2} → {x : ↥A → Fin 4 // e x ≠ x} :=
    fun c => ⟨xc c, hmoved c⟩
  have hinj : Function.Injective f₀ := fun c c' h => by
    have h' : xc c = xc c' := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext
    · rw [← hxc1 c, ← hxc1 c', h']
    · rw [← hxc2 c, ← hxc2 c', h']
  have h12 : 12 ≤ Fintype.card {x : ↥A → Fin 4 // e x ≠ x} := by
    have := Fintype.card_le_of_injective f₀ hinj
    have hc12 : Fintype.card {p : Fin 4 × Fin 4 // p.1 ≠ p.2} = 12 := by decide
    omega
  have hcompl : Fintype.card {x : ↥A → Fin 4 // e x ≠ x} =
      Fintype.card (↥A → Fin 4) - Fintype.card {x : ↥A → Fin 4 // e x = x} :=
    Fintype.card_subtype_compl (fun x : ↥A → Fin 4 => e x = x)
  have hle : Fintype.card {x : ↥A → Fin 4 // e x = x} ≤ Fintype.card (↥A → Fin 4) :=
    Fintype.card_subtype_le (fun x : ↥A → Fin 4 => e x = x)
  omega

end FlipRank

section Atoms

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal Representation

variable {k G : Type} [Field k] [Group G] {V : Type} [AddCommGroup V] [Module k V]

theorem exists_isAtom_subrep [Module.Finite k V] (ρ : Representation k G V) [Nontrivial V] :
    ∃ U : Subrepresentation ρ, IsAtom U := by
  have hA : IsArtinian k[G] ρ.asModule := isArtinian_of_finiteDimensional k
  have : Nontrivial ρ.asModule := (Equiv.nontrivial_congr ρ.asModuleEquiv.toEquiv).mpr inferInstance
  have : Nontrivial (Submodule k[G] ρ.asModule) := (Submodule.nontrivial_iff k[G]).mpr inferInstance
  obtain ⟨N, hN, -⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Submodule k[G] ρ.asModule)).resolve_left
    top_ne_bot
  exact ⟨Subrepresentation.subrepresentationSubmoduleOrderIso.symm N,
    (OrderIso.isAtom_iff _ _).mpr hN⟩

theorem isIrreducible_of_isAtom (ρ : Representation k G V) (U : Subrepresentation ρ)
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · intro h
    apply hU.1
    apply Subrepresentation.toSubmodule_injective
    show U.toSubmodule = ⊥
    rw [_root_.eq_bot_iff]
    intro u hu
    have h1 : (⟨u, hu⟩ : U.toSubmodule) ∈ (⊤ : Subrepresentation U.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1
    have h2 : (⟨u, hu⟩ : U.toSubmodule) = 0 := (Submodule.mem_bot k).mp h1
    exact (Submodule.mem_bot k).mpr (congrArg Subtype.val h2)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
      rintro g v ⟨w, hw, rfl⟩
      exact ⟨U.toRepresentation g w, S.apply_mem_toSubmodule g hw, rfl⟩⟩
    have hS'U : S' ≤ U := by
      rintro v ⟨w, -, rfl⟩
      exact w.2
    rcases hU.le_iff.mp hS'U with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊥
      rw [_root_.eq_bot_iff]
      intro w hw
      have h1 : (w : V) ∈ S'.toSubmodule := ⟨w, hw, rfl⟩
      rw [h] at h1
      have h2 : (w : V) = 0 := (Submodule.mem_bot k).mp h1
      exact (Submodule.mem_bot k).mpr (Subtype.ext h2)
    · right
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊤
      rw [eq_top_iff]
      intro w _
      have h1 : (w : V) ∈ S'.toSubmodule := by
        rw [h]
        exact w.2
      obtain ⟨y, hy, hyw⟩ := h1
      have : y = w := Subtype.ext hyw
      rwa [← this]

end Atoms

section Irreducible

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal Representation

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem irreducible_case (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {W : Type} [AddCommGroup W] [Module F W] [Module.Finite F W]
    (ρ' : Representation F (antiSp F) W) (s' : W ≃ₗ[F] W) (hss : ∀ w, s' (s' w) = w)
    (hs : ∀ g w, s' (ρ' g w) = ρ' ((minorAut F ^ f) g) (s' w))
    (hirr : GSIrreducible ρ' s') (hW : Nontrivial W) (hnt : ∃ g, ρ' g ≠ 1) :
    4 ≤ Module.finrank F W - Module.finrank F (LinearMap.ker (s'.toLinearMap - 1)) := by
  set τ : MulAut (antiSp F) := minorAut F ^ f with hτdef
  have hττ : ∀ g, τ (τ g) = g := by
    intro g
    have h := minorAut_pow_two_mul hF hf
    show (minorAut F ^ f) ((minorAut F ^ f) g) = g
    rw [← MulAut.mul_apply, ← pow_add, ← two_mul, h]
    rfl
  have hs2 : ∀ g w, ρ' g (s' w) = s' (ρ' (τ g) w) := fun g w => by
    have := hs (τ g) w
    rw [hττ] at this
    exact this.symm
  obtain ⟨Ur, hUr⟩ := exists_isAtom_subrep ρ'
  set U : Submodule F W := Ur.toSubmodule with hUdef
  have hUne : U ≠ ⊥ := fun h => hUr.1 (Subrepresentation.toSubmodule_injective h)
  have hUG : ∀ g, ∀ u ∈ U, ρ' g u ∈ U := fun g u hu => Ur.apply_mem_toSubmodule g hu
  set sU : Submodule F W := U.map s'.toLinearMap with hsUdef
  have hsU : ∀ u ∈ U, s' u ∈ sU := fun u hu => ⟨u, hu, rfl⟩
  have hsUG : ∀ g, ∀ y ∈ sU, ρ' g y ∈ sU := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨ρ' (τ g) u, hUG _ u hu, (hs2 g u).symm⟩
  have hsUs : ∀ y ∈ sU, s' y ∈ U := by
    rintro _ ⟨u, hu, rfl⟩
    show s' (s' u) ∈ U
    rw [hss]
    exact hu
  have hsupG : ∀ g, ∀ w ∈ U ⊔ sU, ρ' g w ∈ U ⊔ sU := by
    intro g w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    exact Submodule.add_mem_sup (hUG g y hy) (hsUG g z hz)
  have hsups : ∀ w ∈ U ⊔ sU, s' w ∈ U ⊔ sU := by
    intro w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, add_comm]
    exact Submodule.add_mem_sup (hsUs z hz) (hsU y hy)
  have htop : U ⊔ sU = ⊤ := by
    rcases hirr (U ⊔ sU) hsupG hsups with h | h
    · exfalso
      apply hUne
      rw [_root_.eq_bot_iff, ← h]
      exact le_sup_left
    · exact h
  have hrn : ∀ D : W →ₗ[F] W, Module.finrank F (LinearMap.range D) +
      Module.finrank F (LinearMap.ker D) = Module.finrank F W :=
    fun D => LinearMap.finrank_range_add_finrank_ker D
  by_cases hcase : sU = U
  ·
    have hUtop : U = ⊤ := by rw [← htop, hcase, sup_idem]
    have hUr_top : Ur = ⊤ := Subrepresentation.toSubmodule_injective hUtop
    have hρirr : ρ'.IsIrreducible := by
      have : IsAtom (⊤ : Subrepresentation ρ') := hUr_top ▸ hUr
      exact isSimpleOrder_iff_isAtom_top.mpr this
    obtain ⟨⟨A, ⟨hA, ⟨e⟩⟩, -⟩, hclass⟩ :=
      split_simple_module_production (F := F) (k := F) hF hf ρ' hρirr
    obtain ⟨-, hAempty⟩ := hclass A hA ⟨e⟩
    have hAne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hA0
      obtain ⟨g, hg⟩ := hnt
      exact hg (LinearMap.ext fun v => hAempty.mp hA0 g v)
    let eL : ((↥A → Fin 4) → F) ≃ₗ[F] W := e.toLinearEquiv
    have heint : ∀ g v, eL (matRep (tensorRepS (F := F) F A) g v) = ρ' g (eL v) :=
      fun g v => IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
    have heint' : ∀ g w, eL.symm (ρ' g w) = matRep (tensorRepS (F := F) F A) g (eL.symm w) :=
      fun g w => by
        apply eL.injective
        rw [heint, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    let S₀ : ((↥A → Fin 4) → F) →ₗ[F] ((↥A → Fin 4) → F) :=
      eL.symm.toLinearMap ∘ₗ s'.toLinearMap ∘ₗ eL.toLinearMap
    have hS₀apply : ∀ v, S₀ v = eL.symm (s' (eL v)) := fun v => rfl
    have hS₀S₀ : ∀ v, S₀ (S₀ v) = v := fun v => by
      rw [hS₀apply, hS₀apply, LinearEquiv.apply_symm_apply, hss, LinearEquiv.symm_apply_apply]
    have hS₀T : ∀ g v, S₀ (matRep (tensorRepS (F := F) F A) g v) =
        matRep (tensorRepS (F := F) F A) (τ g) (S₀ v) := fun g v => by
      rw [hS₀apply, hS₀apply, heint, hs, heint']
    let S : Matrix (↥A → Fin 4) (↥A → Fin 4) F := LinearMap.toMatrix' S₀
    have hSS : S * S = 1 := by
      rw [← LinearMap.toMatrix'_comp, show S₀ ∘ₗ S₀ = LinearMap.id from LinearMap.ext hS₀S₀,
        LinearMap.toMatrix'_id]
    have hST : ∀ g, S * tensorRepS (F := F) F A g = tensorRepS (F := F) F A (τ g) * S := by
      intro g
      have h1 : S₀ ∘ₗ Matrix.mulVecLin (tensorRepS (F := F) F A g) =
          Matrix.mulVecLin (tensorRepS (F := F) F A (τ g)) ∘ₗ S₀ :=
        LinearMap.ext fun v => hS₀T g v
      have hT : ∀ M : Matrix (↥A → Fin 4) (↥A → Fin 4) F,
          LinearMap.toMatrix' (Matrix.mulVecLin M) = M := fun M => by
        rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      have h2 := congrArg LinearMap.toMatrix' h1
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, hT] at h2
      exact h2
    have h6 := flip_rank_ge hF hf hA hAne S hSS hST
    have hrank : (S - 1).rank = Module.finrank F (LinearMap.range (s'.toLinearMap - 1)) := by
      have h1 : Matrix.mulVecLin (S - 1) =
          eL.symm.toLinearMap ∘ₗ (s'.toLinearMap - 1) ∘ₗ eL.toLinearMap := by
        have : Matrix.mulVecLin (S - 1) = S₀ - LinearMap.id := by
          rw [← Matrix.toLin'_apply', map_sub, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
        rw [this]
        refine LinearMap.ext fun v => ?_
        simp [hS₀apply]
      unfold Matrix.rank
      rw [h1, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range eL)]
      exact LinearEquiv.finrank_map_eq eL.symm _
    have := hrn (s'.toLinearMap - 1)
    omega
  ·
    have hinter : U ⊓ sU = ⊥ := by
      let Ui : Subrepresentation ρ' := ⟨U ⊓ sU, fun g v hv => ⟨hUG g v hv.1, hsUG g v hv.2⟩⟩
      have hle : Ui ≤ Ur := fun v hv => hv.1
      rcases hUr.le_iff.mp hle with h | h
      · exact congrArg Subrepresentation.toSubmodule h
      · exfalso
        have h1 : U ≤ sU := fun u hu => by
          have : u ∈ Ui.toSubmodule := by rw [h]; exact hu
          exact this.2
        have hfin : Module.finrank F sU = Module.finrank F U := LinearEquiv.finrank_map_eq s' U
        exact hcase (Submodule.eq_of_le_of_finrank_eq h1 hfin.symm).symm
    set D : W →ₗ[F] W := s'.toLinearMap - 1 with hD
    have hDinj : ∀ u ∈ U, D u = 0 → u = 0 := by
      intro u hu hDu
      have h1 : s' u = u := by
        have : s' u - u = 0 := hDu
        exact sub_eq_zero.mp this
      have hu' : u ∈ sU := ⟨u, hu, h1⟩
      have : u ∈ U ⊓ sU := ⟨hu, hu'⟩
      rw [hinter] at this
      exact (Submodule.mem_bot F).mp this
    have hrank : Module.finrank F U ≤ Module.finrank F (LinearMap.range D) := by
      have hinj : Function.Injective (D.domRestrict U) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro a ha
        have ha' : D a = 0 := ha
        exact Subtype.ext (hDinj a a.2 ha')
      have h1 := LinearMap.finrank_range_of_inj hinj
      have h2 : LinearMap.range (D.domRestrict U) ≤ LinearMap.range D := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      rw [← h1]
      exact Submodule.finrank_mono h2
    have hdimU : 4 ≤ Module.finrank F U := by
      have hirrU := isIrreducible_of_isAtom ρ' Ur hUr
      obtain ⟨⟨A, ⟨hA, ⟨e⟩⟩, -⟩, hclass⟩ :=
        split_simple_module_production (F := F) (k := F) hF hf Ur.toRepresentation hirrU
      obtain ⟨hdim, hAempty⟩ := hclass A hA ⟨e⟩
      have hAne : A ≠ ∅ := by
        intro hA0
        have htriv := hAempty.mp hA0
        obtain ⟨g, hg⟩ := hnt
        apply hg
        refine LinearMap.ext fun w => ?_
        have hw : w ∈ U ⊔ sU := by rw [htop]; trivial
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
        obtain ⟨u, hu, rfl⟩ := hz
        have hy' : ρ' g y = y := congrArg Subtype.val (htriv g ⟨y, hy⟩)
        have hu' : ρ' (τ g) u = u := congrArg Subtype.val (htriv (τ g) ⟨u, hu⟩)
        have hz' : ρ' g (s' u) = s' u := by rw [hs2 g u, hu']
        show ρ' g (y + s' u) = y + s' u
        rw [map_add, hy', hz']
      have hcard : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAne)
      rw [hdim]
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ A.card := Nat.pow_le_pow_right (by norm_num) hcard
    have := hrn D
    omega

end Irreducible

section Node26Matrix

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

omit [CharP F 2] [Fintype F] in
theorem eq_one_of_mulVecLin_eq_one (M : Matrix ι ι F) (h : Matrix.mulVecLin M = 1) : M = 1 := by
  ext a b
  have := congrArg (fun T : (ι → F) →ₗ[F] (ι → F) => T (Pi.single b 1) a) h
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem matrix_displacement_ge_four (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (PF : antiSp F →* Matrix ι ι F) (hnt : ∃ g, PF g ≠ 1) (A : Matrix ι ι F) (hAA : A * A = 1)
    (hA : ∀ g, A * PF g = PF ((minorAut F ^ f) g) * A) : 4 ≤ (A - 1).rank := by
  have hf1 : 1 ≤ f := by omega
  let s : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.ofLinearMap (Matrix.mulVecLin A)
    (Matrix.mulVecLin A) (by rw [← Matrix.mulVecLin_mul, hAA, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, hAA, Matrix.mulVecLin_one])
  have hss : ∀ v, s (s v) = v := fun v => by
    show A.mulVec (A.mulVec v) = v
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hs : ∀ g v, s (matRep PF g v) = matRep PF ((minorAut F ^ f) g) (s v) := fun g v => by
    show A.mulVec ((PF g).mulVec v) = (PF ((minorAut F ^ f) g)).mulVec (A.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA g]
  have hnt' : ∃ g, matRep PF g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    exact ⟨g, fun h => hg (eq_one_of_mulVecLin_eq_one _ h)⟩
  have key := gamma_reduction (antiSp_isPerfect hF hf) (minorAut F ^ f) 4
    (fun {W} _ _ _ ρ' s' hss' hs' hirr hW hnt'' => irreducible_case hF hf1 ρ' s' hss' hs' hirr hW
      hnt'') (matRep PF) s hss hs hnt'
  have hD : s.toLinearMap - 1 = Matrix.mulVecLin (A - 1) := by
    refine LinearMap.ext fun v => ?_
    simp [s]
  rw [hD] at key
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (A - 1))
  unfold Matrix.rank
  rw [Module.finrank_fintype_fun_eq_card] at *
  omega

end Node26Matrix

section Node26

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.QuasithinUnique.Setup.X7 (matMap matMap_apply)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem outer_involutions_have_binary_displacement_at_least_four (hf : 2 ≤ f)
    (hF : Fintype.card F = 2 ^ f) {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] (π : Representation (ZMod 2) (antiSp F) M)
    (hπ : Function.Injective π) (a : M ≃ₗ[ZMod 2] M) (ha : orderOf a = 2)
    (α : MulAut (antiSp F)) (hα : α ∉ inner (antiSp F))
    (hnorm : ∀ (g : antiSp F) (w : M), a (π g (a.symm w)) = π (α g) w) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  have haa : a * a = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  have hinv : ∀ w, a (a w) = w := fun w => by
    have := congrArg (fun e : M ≃ₗ[ZMod 2] M => e w) haa
    exact this
  have hsymm : ∀ w, a.symm w = a w := fun w => (a.symm_apply_eq).mpr (hinv w).symm
  have hnorm' : ∀ (g : antiSp F) (v : M), a (π g v) = π (α g) (a v) := fun g v => by
    have := hnorm g (a v)
    rwa [LinearEquiv.symm_apply_apply] at this
  have hstar : ∀ (g : antiSp F) (v : M), π (α g) v = a (π g (a v)) := fun g v => by
    have := hnorm' g (a v)
    rw [hinv] at this
    exact this.symm
  have hαα : α * α = 1 := by
    refine MulEquiv.ext fun g => ?_
    show α (α g) = g
    apply hπ
    refine LinearMap.ext fun w => ?_
    show π (α (α g)) w = π g w
    rw [hstar (α g) w, hstar g (a w), hinv, hinv]
  have hK : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨c, hc⟩ := outer_involution_conj hf hK α hαα hα
  set τ : MulAut (antiSp F) := minorAut F ^ f with hτ
  have hαc : ∀ g : antiSp F, α (c * g * c⁻¹) = c * τ g * c⁻¹ := fun g => by
    rw [hc]
    simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_def, MulAut.conj_symm_apply]
    group
  let πc : Representation (ZMod 2) (antiSp F) M := π.comp (MulAut.conj c).toMonoidHom
  have hπc : Function.Injective πc := hπ.comp (MulAut.conj c).injective
  have hπc_apply : ∀ g, πc g = π (c * g * c⁻¹) := fun g => rfl
  have hacomm : ∀ (g : antiSp F) (v : M), a (πc g v) = πc (τ g) (a v) := fun g v => by
    rw [hπc_apply, hπc_apply, hnorm', hαc]
  have hnt : ∃ g, πc g ≠ 1 := ⟨invX F, fun h => invX_ne_one (hπc (h.trans (map_one πc).symm))⟩
  classical
  let n := Module.finrank (ZMod 2) M
  let bas : Module.Basis (Fin n) (ZMod 2) M := Module.finBasis (ZMod 2) M
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let R₂ : antiSp F →* Matrix (Fin n) (Fin n) (ZMod 2) := toMatRep πc bas
  let PF : antiSp F →* Matrix (Fin n) (Fin n) F := matMap φ R₂
  let A₂ : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.toMatrix bas bas a.toLinearMap
  let A : Matrix (Fin n) (Fin n) F := A₂.map φ
  have hA₂A₂ : A₂ * A₂ = 1 := by
    rw [← LinearMap.toMatrix_mul]
    have : a.toLinearMap * a.toLinearMap = 1 := LinearMap.ext hinv
    rw [this, LinearMap.toMatrix_one]
  have hAA : A * A = 1 := by
    show A₂.map φ * A₂.map φ = 1
    rw [← Matrix.map_mul, hA₂A₂, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hA₂ : ∀ g, A₂ * R₂ g = R₂ (τ g) * A₂ := fun g => by
    have h1 : a.toLinearMap * πc g = πc (τ g) * a.toLinearMap := LinearMap.ext (hacomm g)
    have h2 := congrArg (LinearMap.toMatrix bas bas) h1
    rwa [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul] at h2
  have hA : ∀ g, A * PF g = PF ((minorAut F ^ f) g) * A := fun g => by
    show A₂.map φ * (R₂ g).map φ = (R₂ ((minorAut F ^ f) g)).map φ * A₂.map φ
    rw [← Matrix.map_mul, ← Matrix.map_mul, hA₂ g]
  have hntF : ∃ g, PF g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun hPF => hg ?_⟩
    have h1 : (R₂ g).map φ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map φ := by
      rw [Matrix.map_one φ (map_zero φ) (map_one φ)]
      exact hPF
    have h2 := Matrix.map_injective φ.injective h1
    have h3 : LinearMap.toMatrix bas bas (πc g) = LinearMap.toMatrix bas bas 1 := by
      rw [LinearMap.toMatrix_one]
      exact h2
    exact (LinearMap.toMatrix bas bas).injective h3
  have h4 := matrix_displacement_ge_four hF hf PF hntF A hAA hA
  have hrank : (A - 1).rank ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
    have e1 : A - 1 = (A₂ - 1).map φ := by
      ext i j
      by_cases hij : i = j <;> simp [A, hij]
    have e2 : (A₂ - 1).rank = Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
      have e3 : A₂ - 1 = LinearMap.toMatrix bas bas (a.toLinearMap - 1) := by
        rw [map_sub, LinearMap.toMatrix_one]
        rfl
      rw [e3, Matrix.rank_eq_finrank_range_toLin _ bas bas, Matrix.toLin_toMatrix]
    rw [← e2, e1]
    exact rank_map_ringHom_le φ _
  omega

end Node26

end CFSG.QuasithinUnique.Setup.X7b
