module

public import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
public import CFSG.FeitThompson.Representations.AbelianPointStabilizersCharacterStabilizers
public import CFSG.FeitThompson.Representations.NormalInductionPreservesKernelSubgroup
public import CFSG.FeitThompson.Representations.ProperNormalLayerDegreeIndexMember
public import CFSG.FeitThompson.Representations.LinearCharactersSeparateElements
public import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
public import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInduction (eq_of_norm_le_of_sum_eq)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem norm_coe_monoidHom_units {X : Type*} [Group X] [Finite X] (χ : X →* ℂˣ) (x : X) :
    ‖(χ x : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card X) ?_ (Nat.card_pos (α := X)).ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']
  simp

theorem MonoidHom.eq_one_of_comp_eq_of_fixedPointFree {A M : Type*} [CommGroup A] [Finite A]
    [CommGroup M] {α : A →* A} (hα : ∀ a : A, α a = a → a = 1) {ν : A →* M}
    (h : ∀ a : A, ν (α a) = ν a) : ν = 1 := by
  set f : A → A := fun a => a⁻¹ * α a with hf
  have hinj : Function.Injective f := by
    intro a c hac
    simp only [hf] at hac
    have h1 : α (a * c⁻¹) = a * c⁻¹ := by
      rw [map_mul, map_inv]
      calc α a * (α c)⁻¹ = a * (a⁻¹ * α a) * (c * (c⁻¹ * α c))⁻¹ := by group
        _ = a * (c⁻¹ * α c) * (c * (c⁻¹ * α c))⁻¹ := by rw [hac]
        _ = a * c⁻¹ := by group
    have h2 := hα _ h1
    rwa [mul_inv_eq_one] at h2
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  ext x
  obtain ⟨a, rfl⟩ := hsurj x
  simp only [hf, map_mul, map_inv, h a]
  simp

theorem pow_fixedPointFree_of_prime {U : Type*} [Group U] {σ : MulAut U} {q d : ℕ}
    (hq : q.Prime) (hσq : σ ^ q = 1) (hfix : ∀ w : U, σ w = w → w = 1) (hd : ¬ q ∣ d)
    (w : U) (hw : (σ ^ d) w = w) : w = 1 := by
  have hqf : Fact q.Prime := ⟨hq⟩
  have hqz : NeZero q := ⟨hq.ne_zero⟩
  have hdz : (d : ZMod q) ≠ 0 := fun h => hd ((ZMod.natCast_eq_zero_iff d q).1 h)
  obtain ⟨e, he⟩ : ∃ e : ℕ, ((d * e : ℕ) : ZMod q) = 1 := by
    refine ⟨((d : ZMod q)⁻¹).val, ?_⟩
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact mul_inv_cancel₀ hdz
  have hmod : d * e % q = 1 := by
    have h1 : (d * e % q : ℕ) = (1 : ℕ) % q := by
      have := (ZMod.natCast_eq_natCast_iff' (d * e) 1 q).1 (by simpa using he)
      simpa using this
    rwa [Nat.mod_eq_of_lt hq.one_lt] at h1
  have hpow : (σ ^ (d * e)) w = w := by
    have key : ∀ m : ℕ, ((σ ^ d) ^ m) w = w := by
      intro m
      induction m with
      | zero => simp
      | succ n ih => rw [pow_succ]; simp only [MulAut.mul_apply]; rw [hw, ih]
    rw [pow_mul]
    exact key e
  have hsplit : σ ^ (d * e) = σ := by
    conv_lhs => rw [← Nat.div_add_mod (d * e) q, hmod, pow_add, pow_mul, hσq, one_pow, one_mul,
      pow_one]
  rw [hsplit] at hpow
  exact hfix w hpow

theorem eq_of_pow_comp_eq_of_fixedPointFree {A M : Type*} [CommGroup A] [Finite A] [CommGroup M]
    {τ : MulAut A} {q : ℕ} (hq : q.Prime) (hτq : τ ^ q = 1)
    (hτfix : ∀ a : A, τ a = a → a = 1) {ν : A →* M} (hν : ν ≠ 1) {i j : ℕ}
    (hi : i < q) (hj : j < q) (h : ∀ a : A, ν ((τ ^ i) a) = ν ((τ ^ j) a)) : i = j := by
  have key : ∀ m n : ℕ, n ≤ m → m < q → (∀ a : A, ν ((τ ^ m) a) = ν ((τ ^ n) a)) → m = n := by
    intro m n hnm hmq hmn
    have hd : ∀ a : A, ν ((τ ^ (m - n)) a) = ν a := by
      intro a
      have hsplit : τ ^ m = τ ^ (m - n) * τ ^ n := by
        rw [← pow_add]; congr 1; omega
      have h1 := hmn ((τ ^ n)⁻¹ a)
      rw [hsplit, MulAut.mul_apply] at h1
      simpa using h1
    by_contra hne
    have hqd : ¬ q ∣ m - n := fun hc => by
      have := Nat.le_of_dvd (by omega) hc
      omega
    exact hν (MonoidHom.eq_one_of_comp_eq_of_fixedPointFree
      (α := ((τ ^ (m - n) : MulAut A)).toMonoidHom)
      (fun a ha => pow_fixedPointFree_of_prime hq hτq hτfix hqd a ha) hd)
  rcases le_total j i with hle | hle
  · exact key i j hle hi h
  · exact (key j i hle hj fun a => (h a).symm).symm

section Induction

variable {L : Type*} [Group L] [Fintype L]

theorem indClassFun_eq_sum_of_forall_conj_mem (H : Subgroup L) (θ : H → ℂ) {z : L}
    (hmem : ∀ x : L, x⁻¹ * z * x ∈ H) :
    indClassFun H θ z = (Nat.card H : ℂ)⁻¹ * ∑ x : L, θ ⟨x⁻¹ * z * x, hmem x⟩ := by
  classical
  rw [indClassFun_apply]
  congr 1
  exact Finset.sum_congr rfl fun x _ => dif_pos (hmem x)

theorem indClassFun_apply_of_mem_center (H : Subgroup L) (θ : H → ℂ) {z : L} (hz : z ∈ H)
    (hc : z ∈ Subgroup.center L) : indClassFun H θ z = (H.index : ℂ) * θ ⟨z, hz⟩ := by
  classical
  rw [Subgroup.mem_center_iff] at hc
  have hconj : ∀ t : L, t⁻¹ * z * t = z := fun t => by
    calc t⁻¹ * z * t = t⁻¹ * (z * t) := by group
      _ = t⁻¹ * (t * z) := by rw [hc t]
      _ = z := by group
  rw [indClassFun_eq_sum_of_forall_conj_mem H θ fun t => by rw [hconj t]; exact hz]
  have key : ∀ t : L, θ ⟨t⁻¹ * z * t, by rw [hconj t]; exact hz⟩ = θ ⟨z, hz⟩ :=
    fun t => by congr 1; exact Subtype.ext (hconj t)
  rw [Finset.sum_congr rfl fun t _ => key t]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : ((Fintype.card L : ℕ) : ℂ) = (H.index : ℂ) * (Fintype.card H : ℂ) := by
    rw [← Nat.cast_mul]
    congr 1
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Subgroup.index_mul_card H]
  have hH : ((Fintype.card H : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card, hcard]
  field_simp

theorem indClassFun_apply_ne_index_of_apply_ne_one {H : Subgroup L} (χ : H →* ℂˣ) {z : L}
    (hmem : ∀ x : L, x⁻¹ * z * x ∈ H) (hz : χ ⟨z, by simpa using hmem 1⟩ ≠ 1) :
    indClassFun H (fun t => (χ t : ℂ)) z ≠ (H.index : ℂ) := by
  intro hcon
  rw [indClassFun_eq_sum_of_forall_conj_mem H _ hmem] at hcon
  have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hsum : ∑ x : L, (χ ⟨x⁻¹ * z * x, hmem x⟩ : ℂ) = ∑ _x : L, ((1 : ℝ) : ℂ) := by
    have h1 : ∑ x : L, (χ ⟨x⁻¹ * z * x, hmem x⟩ : ℂ) = (Nat.card H : ℂ) * (H.index : ℂ) := by
      field_simp at hcon
      linear_combination hcon
    rw [h1]
    simp only [Complex.ofReal_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.cast_mul, mul_comm, ← Nat.card_eq_fintype_card, Subgroup.index_mul_card]
  have hval := eq_of_norm_le_of_sum_eq
    (a := fun x : L => (χ ⟨x⁻¹ * z * x, hmem x⟩ : ℂ)) (r := 1)
    (fun x => le_of_eq (norm_coe_monoidHom_units χ _)) hsum 1
  exact hz (Units.val_injective (by simpa using hval))

theorem indClassFun_coe_mem_Irr_of_inertiaGroup_le {H : Subgroup L} [H.Normal] (χ : H →* ℂˣ)
    (hle : inertiaGroup H (fun t => (χ t : ℂ)) ≤ H) :
    indClassFun H (fun t => (χ t : ℂ)) ∈ Irr L := by
  have hχ : (fun t => (χ t : ℂ)) ∈ Irr H := SolvableNormalLayer.coe_monoidHom_units_mem_Irr χ
  exact (FreeCore.mem_Irr_indClassFun_iff H hχ).2
    (le_antisymm hle (le_inertiaGroup H (Irr_subset_classFun hχ)))

end Induction

namespace FixedFreeImage

open SemidirectProduct

instance instFintypeSemidirectProduct {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    [Fintype N] [Fintype G] : Fintype (N ⋊[φ] G) :=
  Fintype.ofEquiv (N × G) equivProd.symm

def mulAutMultiplicative {k E : Type*} [Semiring k] [AddCommGroup E] [Module k E] :
    (E ≃ₗ[k] E) →* MulAut (Multiplicative E) where
  toFun f := AddEquiv.toMultiplicative f.toAddEquiv
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

@[simp] theorem mulAutMultiplicative_apply {k E : Type*} [Semiring k] [AddCommGroup E]
    [Module k E] (f : E ≃ₗ[k] E) (x : Multiplicative E) :
    mulAutMultiplicative f x = Multiplicative.ofAdd (f (Multiplicative.toAdd x)) := (rfl)

@[simp] theorem mulAutMultiplicative_ofAdd {k E : Type*} [Semiring k] [AddCommGroup E]
    [Module k E] (f : E ≃ₗ[k] E) (v : E) :
    mulAutMultiplicative f (Multiplicative.ofAdd v) = Multiplicative.ofAdd (f v) := (rfl)

@[simp] theorem mulAutMultiplicative_symm_ofAdd {k E : Type*} [Semiring k] [AddCommGroup E]
    [Module k E] (f : E ≃ₗ[k] E) (v : E) :
    (mulAutMultiplicative f).symm (Multiplicative.ofAdd v)
      = Multiplicative.ofAdd (f.symm v) := by
  rw [MulEquiv.symm_apply_eq, mulAutMultiplicative_ofAdd]; simp

variable {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E] {U : Type*} [CommGroup U]

abbrev linAction (r : U →* (E ≃ₗ[ZMod p] E)) : U →* MulAut (Multiplicative E) :=
  mulAutMultiplicative.comp r

abbrev Semi (r : U →* (E ≃ₗ[ZMod p] E)) : Type _ := Multiplicative E ⋊[linAction r] U

variable (r : U →* (E ≃ₗ[ZMod p] E))

def kerPart : Subgroup (Semi r) := (MonoidHom.ker r).comap rightHom

theorem mem_kerPart {x : Semi r} : x ∈ kerPart r ↔ r x.right = 1 := Iff.rfl

instance : (kerPart r).Normal := Subgroup.normal_comap _

def basePart : Subgroup (Semi r) := (inl : Multiplicative E →* Semi r).range

theorem mem_basePart {x : Semi r} : x ∈ basePart r ↔ ∃ v : E, inl (Multiplicative.ofAdd v) = x :=
  Iff.rfl

theorem inl_mem_basePart (v : E) : (inl (Multiplicative.ofAdd v) : Semi r) ∈ basePart r :=
  ⟨Multiplicative.ofAdd v, rfl⟩

instance : (basePart r).Normal := by
  rw [basePart, range_inl_eq_ker_rightHom]; infer_instance

theorem basePart_le_kerPart : basePart r ≤ kerPart r := by
  rintro x ⟨v, rfl⟩
  simp [mem_kerPart]

theorem index_kerPart : (kerPart r).index = Nat.card (MonoidHom.range r) := by
  rw [kerPart, Subgroup.index_comap_of_surjective _ rightHom_surjective, Subgroup.index_ker]

def qAut (b : E ≃ₗ[ZMod p] E) (σ : MulAut U) (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) :
    MulAut (Semi r) :=
  SemidirectProduct.congr (mulAutMultiplicative b) σ fun u => by
    ext x
    simp only [MulEquiv.coe_trans, Function.comp_apply, mulAutMultiplicative_apply,
      MonoidHom.coe_comp]
    have h := congrArg (fun f : E ≃ₗ[ZMod p] E => f (b (Multiplicative.toAdd x))) (hr u)
    simp only [LinearEquiv.mul_apply] at h
    show Multiplicative.ofAdd (b (r u (Multiplicative.toAdd x)))
      = Multiplicative.ofAdd (r (σ u) (b (Multiplicative.toAdd x)))
    rw [h]
    simp

@[simp] theorem qAut_inl (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) (v : E) :
    qAut r b σ hr (inl (Multiplicative.ofAdd v)) = inl (Multiplicative.ofAdd (b v)) := by
  apply SemidirectProduct.ext <;> simp [qAut, SemidirectProduct.congr]

@[simp] theorem qAut_inr (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) (w : U) :
    qAut r b σ hr (inr w) = inr (σ w) := by
  apply SemidirectProduct.ext <;> simp [qAut, SemidirectProduct.congr]

theorem right_qAut (b : E ≃ₗ[ZMod p] E) (σ : MulAut U) (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹)
    (x : Semi r) : (qAut r b σ hr x).right = σ x.right := (rfl)

theorem qAut_mem_basePart (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) {x : Semi r} (hx : x ∈ basePart r) :
    qAut r b σ hr x ∈ basePart r := by
  obtain ⟨v, rfl⟩ := hx
  exact ⟨mulAutMultiplicative b v, by apply SemidirectProduct.ext <;> simp [qAut,
    SemidirectProduct.congr]⟩

theorem qAut_mem_kerPart (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) {x : Semi r} (hx : x ∈ kerPart r) :
    qAut r b σ hr x ∈ kerPart r := by
  rw [mem_kerPart] at hx ⊢
  rw [right_qAut, hr, hx]
  simp

theorem mem_kerPart_qAut_iff (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) (x : Semi r) :
    qAut r b σ hr x ∈ kerPart r ↔ x ∈ kerPart r := by
  rw [mem_kerPart, mem_kerPart, right_qAut, hr]
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  have := congrArg (fun f : E ≃ₗ[ZMod p] E => b⁻¹ * f * b) h
  simpa [mul_assoc] using this

theorem mem_kerPart_qAut_pow_iff (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) (n : ℕ) (x : Semi r) :
    ((qAut r b σ hr) ^ n) x ∈ kerPart r ↔ x ∈ kerPart r := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, ih, mem_kerPart_qAut_iff]

theorem qAut_pow_inr (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) (n : ℕ) (w : U) :
    ((qAut r b σ hr) ^ n) (inr w) = inr ((σ ^ n) w) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, qAut_inr, pow_succ', MulAut.mul_apply]

theorem qAut_eq (b : E ≃ₗ[ZMod p] E) (σ : MulAut U) (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹)
    (x : Semi r) :
    qAut r b σ hr x
      = inl (Multiplicative.ofAdd (b (Multiplicative.toAdd x.left))) * inr (σ x.right) := by
  conv_lhs => rw [← inl_left_mul_inr_right x]
  rw [map_mul, qAut_inr]
  congr 1
  exact qAut_inl r b σ hr (Multiplicative.toAdd x.left)

theorem left_qAut (b : E ≃ₗ[ZMod p] E) (σ : MulAut U) (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹)
    (x : Semi r) :
    (qAut r b σ hr x).left = Multiplicative.ofAdd (b (Multiplicative.toAdd x.left)) := by
  rw [qAut_eq]; simp

theorem right_mem_ker_of_mem_kerPart {x : Semi r} (hx : x ∈ kerPart r) :
    x.right ∈ MonoidHom.ker r := MonoidHom.mem_ker.2 ((mem_kerPart r).1 hx)

theorem linAction_right_eq_one {x : Semi r} (hx : x ∈ kerPart r) :
    linAction r x.right = 1 := by
  rw [mem_kerPart] at hx; simp [linAction, hx]

theorem left_mul_of_mem_kerPart {x y : Semi r} (hx : x ∈ kerPart r) :
    (x * y).left = x.left * y.left := by
  rw [mul_left, linAction_right_eq_one r hx]; rfl

instance : IsMulCommutative (kerPart r) where
  is_comm := ⟨fun x y => by
    refine Subtype.ext (SemidirectProduct.ext ?_ ?_)
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, left_mul_of_mem_kerPart r x.2,
        left_mul_of_mem_kerPart r y.2]
      exact mul_comm _ _
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_right, mul_right]
      exact mul_comm _ _⟩

def kerPartRight : kerPart r →* MonoidHom.ker r where
  toFun x := ⟨(x : Semi r).right, right_mem_ker_of_mem_kerPart r x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x _ := Subtype.ext (mul_right _ _)

@[simp] theorem coe_kerPartRight_apply (x : kerPart r) :
    ((kerPartRight r x : MonoidHom.ker r) : U) = (x : Semi r).right := (rfl)

def kerPartLeft : kerPart r →* Multiplicative E where
  toFun x := (x : Semi r).left
  map_one' := (rfl)
  map_mul' x _ := left_mul_of_mem_kerPart r x.2

@[simp] theorem kerPartLeft_apply (x : kerPart r) :
    kerPartLeft r x = (x : Semi r).left := (rfl)

def kerPartChar (lam : Multiplicative E →* ℂˣ) (ν : MonoidHom.ker r →* ℂˣ) :
    kerPart r →* ℂˣ := lam.comp (kerPartLeft r) * ν.comp (kerPartRight r)

@[simp] theorem kerPartChar_apply (lam : Multiplicative E →* ℂˣ) (ν : MonoidHom.ker r →* ℂˣ)
    (x : kerPart r) :
    kerPartChar r lam ν x = lam (kerPartLeft r x) * ν (kerPartRight r x) := (rfl)

theorem kerPartChar_inl (lam : Multiplicative E →* ℂˣ) (ν : MonoidHom.ker r →* ℂˣ) (v : E)
    (h : (inl (Multiplicative.ofAdd v) : Semi r) ∈ kerPart r) :
    kerPartChar r lam ν ⟨inl (Multiplicative.ofAdd v), h⟩ = lam (Multiplicative.ofAdd v) := by
  have hr : kerPartRight r ⟨inl (Multiplicative.ofAdd v), h⟩ = (1 : MonoidHom.ker r) :=
    Subtype.ext (by simp)
  have hl : kerPartLeft r ⟨inl (Multiplicative.ofAdd v), h⟩ = Multiplicative.ofAdd v := by simp
  rw [kerPartChar_apply, hr, hl, map_one, mul_one]

theorem kerPartChar_inr (lam : Multiplicative E →* ℂˣ) (ν : MonoidHom.ker r →* ℂˣ) (c : U)
    (hc : c ∈ MonoidHom.ker r) (h : (inr c : Semi r) ∈ kerPart r) :
    kerPartChar r lam ν ⟨inr c, h⟩ = ν ⟨c, hc⟩ := by
  have hr : kerPartRight r ⟨inr c, h⟩ = (⟨c, hc⟩ : MonoidHom.ker r) := Subtype.ext (by simp)
  have hl : kerPartLeft r ⟨inr c, h⟩ = 1 := by simp
  rw [kerPartChar_apply, hr, hl, map_one, one_mul]

theorem inv_mul_inl_mul (x : Semi r) (v : E) :
    x⁻¹ * inl (Multiplicative.ofAdd v) * x
      = inl (Multiplicative.ofAdd ((r x.right).symm v)) := by
  apply SemidirectProduct.ext
  · simp [mul_left, inv_left, linAction]
  · simp [mul_right, inv_right]

theorem conj_inl_mem_kerPart (v : E) (x : Semi r) :
    x⁻¹ * (inl (Multiplicative.ofAdd v) : Semi r) * x ∈ kerPart r := by
  rw [inv_mul_inl_mul]
  exact basePart_le_kerPart r (inl_mem_basePart r _)

theorem inr_mem_center {c : U} (hc : c ∈ MonoidHom.ker r) :
    (inr c : Semi r) ∈ Subgroup.center (Semi r) := by
  have hc' : r c = 1 := MonoidHom.mem_ker.1 hc
  rw [Subgroup.mem_center_iff]
  intro x
  refine SemidirectProduct.ext ?_ ?_
  · simp [mul_left, linAction, hc']
  · simp [mul_right, mul_comm]

theorem inr_mem_kerPart {c : U} (hc : c ∈ MonoidHom.ker r) : (inr c : Semi r) ∈ kerPart r :=
  (mem_kerPart r).2 (by simpa using MonoidHom.mem_ker.1 hc)

theorem map_mem_ker_iff (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ w : U, r (σ w) = b * r w * b⁻¹) (w : U) :
    σ w ∈ MonoidHom.ker r ↔ w ∈ MonoidHom.ker r := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hr]
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  have := congrArg (fun f : E ≃ₗ[ZMod p] E => b⁻¹ * f * b) h
  simpa [mul_assoc] using this

theorem map_ker_eq (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ w : U, r (σ w) = b * r w * b⁻¹) :
    (MonoidHom.ker r).map (σ : U →* U) = MonoidHom.ker r := by
  ext w
  simp only [Subgroup.mem_map]
  refine ⟨fun ⟨u, hu, hux⟩ => hux ▸ (map_mem_ker_iff r b σ hr u).2 hu, fun hw => ?_⟩
  exact ⟨σ.symm w, (map_mem_ker_iff r b σ hr (σ.symm w)).1 (by simpa using hw), by simp⟩

def kerAut (b : E ≃ₗ[ZMod p] E) (σ : MulAut U) (hr : ∀ w : U, r (σ w) = b * r w * b⁻¹) :
    MulAut (MonoidHom.ker r) :=
  (σ.subgroupMap (MonoidHom.ker r)).trans (MulEquiv.subgroupCongr (map_ker_eq r b σ hr))

@[simp] theorem coe_kerAut_apply (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ w : U, r (σ w) = b * r w * b⁻¹) (c : MonoidHom.ker r) :
    ((kerAut r b σ hr c : MonoidHom.ker r) : U) = σ (c : U) := (rfl)

theorem coe_kerAut_pow_apply (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ w : U, r (σ w) = b * r w * b⁻¹) (n : ℕ) (c : MonoidHom.ker r) :
    (((kerAut r b σ hr ^ n) c : MonoidHom.ker r) : U) = (σ ^ n) (c : U) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, coe_kerAut_apply, ih, pow_succ', MulAut.mul_apply]

theorem indClassFun_comp_qAut_pow [Fintype E] [Fintype U] (b : E ≃ₗ[ZMod p] E) (σ : MulAut U)
    (hr : ∀ u : U, r (σ u) = b * r u * b⁻¹) (ψ : kerPart r → ℂ) (n : ℕ) :
    indClassFun (kerPart r) ψ ∘ ((qAut r b σ hr) ^ n)
      = indClassFun (kerPart r) (fun x => ψ ⟨((qAut r b σ hr) ^ n) (x : Semi r),
          (mem_kerPart_qAut_pow_iff r b σ hr n _).2 x.2⟩) :=
  indClassFun_comp_mulEquiv ((qAut r b σ hr) ^ n)
    (fun z => (mem_kerPart_qAut_pow_iff r b σ hr n z).symm)
    (fun _ _ hy => by congr 1; exact Subtype.ext hy)

theorem exists_dual_apply_eq_one_of_comp_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E] (b : E ≃ₗ[ZMod p] E) (hbq : b ^ q = 1)
    {s : E} (hs : s ≠ 0) (hbs : b s = s) :
    ∃ l : E →ₗ[ZMod p] ZMod p, l s = 1 ∧ ∀ v : E, l (b v) = l v := by
  have hpf : Fact p.Prime := ⟨hp⟩
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hs
  have hqp : (q : ZMod p) ≠ 0 := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 ((ZMod.natCast_eq_zero_iff q p).1 h))
  set g : ℕ → E → ZMod p := fun i v => l₀ ((b ^ i : E ≃ₗ[ZMod p] E) v) with hg
  have hstep : ∀ (i : ℕ) (v : E), g i (b v) = g (i + 1) v := by
    intro i v; simp only [hg, pow_succ]; rfl
  have hqzero : ∀ v : E, g q v = g 0 v := fun v => by simp only [hg, hbq, pow_zero]
  have hgs : ∀ i : ℕ, g i s = 1 := by
    intro i
    induction i with
    | zero => simpa [hg] using hl₀
    | succ n ih =>
      have hbn : (b ^ (n + 1) : E ≃ₗ[ZMod p] E) s = (b ^ n : E ≃ₗ[ZMod p] E) (b s) := by
        rw [pow_succ]; rfl
      simp only [hg, hbn, hbs]
      simpa [hg] using ih
  set l₁ : E →ₗ[ZMod p] ZMod p :=
    ∑ i ∈ Finset.range q, l₀ ∘ₗ ((b ^ i : E ≃ₗ[ZMod p] E) : E →ₗ[ZMod p] E) with hl₁def
  have hl₁apply : ∀ v : E, l₁ v = ∑ i ∈ Finset.range q, g i v := fun v => by simp [hl₁def, hg]
  have hshift : ∀ v : E, l₁ (b v) = l₁ v := by
    intro v
    rw [hl₁apply, hl₁apply]
    have key : ∑ i ∈ Finset.range q, g (i + 1) v + g 0 v
        = ∑ i ∈ Finset.range q, g i v + g q v := by
      rw [← Finset.sum_range_succ' (fun i => g i v) q, Finset.sum_range_succ (fun i => g i v) q]
    rw [hqzero v] at key
    calc ∑ i ∈ Finset.range q, g i (b v)
        = ∑ i ∈ Finset.range q, g (i + 1) v := Finset.sum_congr rfl fun i _ => hstep i v
      _ = ∑ i ∈ Finset.range q, g i v := by linear_combination key
  refine ⟨(q : ZMod p)⁻¹ • l₁, ?_, fun v => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, hl₁apply, Finset.sum_congr rfl fun i _ => hgs i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hqp
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hshift]

noncomputable def zetaUnit (p : ℕ) [NeZero p] : ℂˣ :=
  Units.ofPowEqOne (Complex.exp (2 * Real.pi * Complex.I / p)) p
    (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).pow_eq_one (NeZero.ne p)

theorem zetaUnit_pow (p : ℕ) [NeZero p] : (zetaUnit p) ^ p = 1 := by
  apply Units.ext
  push_cast [zetaUnit, Units.val_ofPowEqOne]
  exact (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).pow_eq_one

theorem orderOf_zetaUnit (p : ℕ) [NeZero p] : orderOf (zetaUnit p) = p := by
  rw [← orderOf_units]
  exact (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).eq_orderOf.symm

noncomputable def zmodCharUnit (p : ℕ) [NeZero p] : Multiplicative (ZMod p) →* ℂˣ :=
  (AddChar.zmodChar p (zetaUnit_pow p)).toMonoidHom

theorem zmodCharUnit_apply (p : ℕ) [NeZero p] (a : ZMod p) :
    zmodCharUnit p (Multiplicative.ofAdd a) = AddChar.zmodChar p (zetaUnit_pow p) a := (rfl)

theorem zmodCharUnit_eq_one_iff (p : ℕ) [NeZero p] {a : ZMod p} :
    zmodCharUnit p (Multiplicative.ofAdd a) = 1 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  rw [zmodCharUnit_apply] at h
  have h2 : (zetaUnit p) ^ a.val = 1 := by
    rw [← AddChar.zmodChar_apply' (zetaUnit_pow p) a.val]
    simpa using h
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_zetaUnit] at hd
  have := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a)
  rwa [← ZMod.val_eq_zero]

variable [NeZero p]

noncomputable def dualChar (l : E →ₗ[ZMod p] ZMod p) : Multiplicative E →* ℂˣ :=
  (zmodCharUnit p).comp (AddMonoidHom.toMultiplicative (l : E →+ ZMod p))

theorem dualChar_apply (l : E →ₗ[ZMod p] ZMod p) (v : E) :
    dualChar l (Multiplicative.ofAdd v) = zmodCharUnit p (Multiplicative.ofAdd (l v)) := (rfl)

theorem dualChar_eq_one_iff (l : E →ₗ[ZMod p] ZMod p) (v : E) :
    dualChar l (Multiplicative.ofAdd v) = 1 ↔ l v = 0 := by
  rw [dualChar_apply, zmodCharUnit_eq_one_iff]

theorem zmodCharUnit_ofAdd_inj {a c : ZMod p}
    (h : zmodCharUnit p (Multiplicative.ofAdd a) = zmodCharUnit p (Multiplicative.ofAdd c)) :
    a = c := by
  have h5 : zmodCharUnit p (Multiplicative.ofAdd (a - c)) = 1 := by
    rw [sub_eq_add_neg, ofAdd_add, map_mul, ofAdd_neg, map_inv, h, mul_inv_cancel]
  rw [zmodCharUnit_eq_one_iff, sub_eq_zero] at h5
  exact h5

theorem dualChar_injective : Function.Injective (dualChar (p := p) (E := E)) :=
  fun l₁ l₂ h => LinearMap.ext fun v => zmodCharUnit_ofAdd_inj
    (by rw [← dualChar_apply l₁ v, ← dualChar_apply l₂ v, h])

theorem eq_zero_of_comp_eq_of_fixedFree [Fact p.Prime] [FiniteDimensional (ZMod p) E]
    (d : E ≃ₗ[ZMod p] E) (hd : ∀ v : E, d v = v → v = 0) {l : E →ₗ[ZMod p] ZMod p}
    (hfix : ∀ v : E, l (d v) = l v) : l = 0 := by
  set f : E →ₗ[ZMod p] E := (d : E →ₗ[ZMod p] E) - LinearMap.id with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    ext v
    simp only [LinearMap.mem_ker, hf, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      Submodule.mem_bot]
    exact ⟨hd v, fun h => by rw [h]; simp⟩
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hlf : ∀ v : E, l (f v) = 0 := by
    intro v
    change l (d v - v) = 0
    rw [map_sub, hfix v, sub_self]
  exact LinearMap.ext fun w => by obtain ⟨v, rfl⟩ := hsurj w; simpa using hlf v

theorem mem_ker_of_dualChar_comp_eq [Fact p.Prime] [FiniteDimensional (ZMod p) E]
    (hD : ∀ d ∈ MonoidHom.range r, d ≠ 1 → ∀ v : E, d v = v → v = 0)
    {l : E →ₗ[ZMod p] ZMod p} (hl : l ≠ 0) {w : U} (hw : ∀ v : E, l (r w v) = l v) :
    w ∈ MonoidHom.ker r := by
  by_contra hwc
  exact hl (eq_zero_of_comp_eq_of_fixedFree (r w)
    (hD (r w) ⟨w, rfl⟩ (fun h => hwc (MonoidHom.mem_ker.2 h))) hw)

theorem inertiaGroup_kerPartChar_le [Fact p.Prime] [FiniteDimensional (ZMod p) E] [NeZero p]
    (hD : ∀ d ∈ MonoidHom.range r, d ≠ 1 → ∀ v : E, d v = v → v = 0)
    {l : E →ₗ[ZMod p] ZMod p} (hl : l ≠ 0) (ν : MonoidHom.ker r →* ℂˣ) :
    inertiaGroup (kerPart r) (fun t => (kerPartChar r (dualChar l) ν t : ℂ)) ≤ kerPart r := by
  intro x hx
  rw [mem_inertiaGroup_iff_forall_conj] at hx
  have key : ∀ v : E, l ((r x.right).symm v) = l v := by
    intro v
    have hmem : (inl (Multiplicative.ofAdd v) : Semi r) ∈ kerPart r :=
      basePart_le_kerPart r (inl_mem_basePart r v)
    have hmem' : (inl (Multiplicative.ofAdd ((r x.right).symm v)) : Semi r) ∈ kerPart r :=
      basePart_le_kerPart r (inl_mem_basePart r _)
    have h := hx ⟨inl (Multiplicative.ofAdd v), hmem⟩
    have hcoe : MulAut.conjNormal x⁻¹ (⟨inl (Multiplicative.ofAdd v), hmem⟩ : kerPart r)
        = (⟨inl (Multiplicative.ofAdd ((r x.right).symm v)), hmem'⟩ : kerPart r) := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply, inv_inv]
      exact inv_mul_inl_mul r x v
    rw [hcoe, kerPartChar_inl, kerPartChar_inl] at h
    exact zmodCharUnit_ofAdd_inj (by rw [← dualChar_apply, ← dualChar_apply]; exact_mod_cast h)
  by_contra hxc
  refine hl (eq_zero_of_comp_eq_of_fixedFree (r x.right)⁻¹ ?_ key)
  intro v hv
  refine hD (r x.right) ⟨x.right, rfl⟩ (fun hc => hxc ((mem_kerPart r).2 hc)) v ?_
  have h2 : r x.right ((r x.right)⁻¹ v) = r x.right v := by rw [hv]
  simpa using h2.symm

end FixedFreeImage

open FixedFreeImage SemidirectProduct

theorem exists_moving_character_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Fintype E] [Nontrivial E]
    {U : Type} [CommGroup U] [Fintype U] (hqU : ¬ q ∣ Nat.card U)
    (b : E ≃ₗ[ZMod p] E) (hbq : b ^ q = 1) (s : E) (hs : s ≠ 0) (hbs : b s = s)
    (σ : MulAut U) (hσq : σ ^ q = 1) (hσ1 : σ ≠ 1) (hσfix : ∀ w : U, σ w = w → w = 1)
    (r : U →* (E ≃ₗ[ZMod p] E)) (hr : ∀ w : U, r (σ w) = b * r w * b⁻¹)
    (hC : MonoidHom.ker r ≠ ⊥)
    (hD : ∀ d ∈ MonoidHom.range r, d ≠ 1 → ∀ v : E, d v = v → v = 0) :
    ∃ α β : Semi r → ℂ, ∃ ψ₀ ψ₁ : kerPart r →* ℂˣ,
      α ∈ Irr (Semi r) ∧ β ∈ Irr (Semi r) ∧
      α = indClassFun (kerPart r) (fun t => (ψ₀ t : ℂ)) ∧
      β = indClassFun (kerPart r) (fun t => (ψ₁ t : ℂ)) ∧
      α 1 = (Nat.card (MonoidHom.range r) : ℂ) ∧
      β 1 = (Nat.card (MonoidHom.range r) : ℂ) ∧
      (∃ x ∈ basePart r, α x ≠ α 1) ∧ (∃ x ∈ basePart r, β x ≠ β 1) ∧
      α ∘ (qAut r b σ hr) = α ∧
      (∀ i j : ℕ, i < q → j < q → β ∘ ((qAut r b σ hr) ^ i) = β ∘ ((qAut r b σ hr) ^ j) → i = j) := by
  classical
  have hpf : Fact p.Prime := ⟨hp⟩
  have hpz : NeZero p := ⟨hp.ne_zero⟩
  have hfd : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
  obtain ⟨l, hls, hlb⟩ := exists_dual_apply_eq_one_of_comp_eq hp hq hpq b hbq hs hbs
  have hl0 : l ≠ 0 := fun h => by simp [h] at hls
  have hCnt : Nontrivial (MonoidHom.ker r) := (Subgroup.nontrivial_iff_ne_bot _).2 hC
  obtain ⟨c₀, hc₀⟩ := exists_ne (1 : MonoidHom.ker r)
  obtain ⟨ν, hνc₀⟩ := exists_monoidHom_apply_ne_one (A := MonoidHom.ker r) hc₀
  have hν : ν ≠ 1 := fun h => hνc₀ (by rw [h]; rfl)
  set ψ₀ : kerPart r →* ℂˣ := kerPartChar r (dualChar l) 1 with hψ₀
  set ψ₁ : kerPart r →* ℂˣ := kerPartChar r (dualChar l) ν with hψ₁
  set α := indClassFun (kerPart r) (fun t => (ψ₀ t : ℂ)) with hα
  set β := indClassFun (kerPart r) (fun t => (ψ₁ t : ℂ)) with hβ
  have hE : ∀ ψ : kerPart r →* ℂˣ, (∀ v : E, ∀ h, ψ ⟨inl (Multiplicative.ofAdd v), h⟩
        = dualChar l (Multiplicative.ofAdd v)) →
      indClassFun (kerPart r) (fun t => (ψ t : ℂ)) (inl (Multiplicative.ofAdd s))
        ≠ ((kerPart r).index : ℂ) := by
    intro ψ hψ
    refine indClassFun_apply_ne_index_of_apply_ne_one _ (conj_inl_mem_kerPart r s) ?_
    rw [hψ s]
    intro hcon
    rw [dualChar_eq_one_iff, hls] at hcon
    exact one_ne_zero hcon
  refine ⟨α, β, ψ₀, ψ₁,
    indClassFun_coe_mem_Irr_of_inertiaGroup_le ψ₀ (inertiaGroup_kerPartChar_le r hD hl0 1),
    indClassFun_coe_mem_Irr_of_inertiaGroup_le ψ₁ (inertiaGroup_kerPartChar_le r hD hl0 ν),
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hα, NormalInducedFamily.indClassFun_one_eq_index_mul, index_kerPart, map_one]; simp
  · rw [hβ, NormalInducedFamily.indClassFun_one_eq_index_mul, index_kerPart, map_one]; simp
  · refine ⟨inl (Multiplicative.ofAdd s), inl_mem_basePart r s, ?_⟩
    rw [hα, NormalInducedFamily.indClassFun_one_eq_index_mul, map_one, Units.val_one, mul_one]
    exact hE ψ₀ fun v h => kerPartChar_inl r _ _ v h
  · refine ⟨inl (Multiplicative.ofAdd s), inl_mem_basePart r s, ?_⟩
    rw [hβ, NormalInducedFamily.indClassFun_one_eq_index_mul, map_one, Units.val_one, mul_one]
    exact hE ψ₁ fun v h => kerPartChar_inl r _ _ v h
  · rw [hα, hψ₀]
    refine indClassFun_comp_mulEquiv (qAut r b σ hr)
      (fun z => (mem_kerPart_qAut_iff r b σ hr z).symm) fun x y hy => ?_
    rw [kerPartChar_apply, kerPartChar_apply, MonoidHom.one_apply, MonoidHom.one_apply,
      mul_one, mul_one, kerPartLeft_apply, kerPartLeft_apply]
    have h1 : (y : Semi r).left
        = Multiplicative.ofAdd (b (Multiplicative.toAdd (x : Semi r).left)) := by
      rw [hy, left_qAut]
    have h2 : (x : Semi r).left
        = Multiplicative.ofAdd (Multiplicative.toAdd (x : Semi r).left) := rfl
    rw [h1]
    conv_rhs => rw [h2]
    rw [dualChar_apply, dualChar_apply, hlb]
  · intro i j hi hj h
    set τ := kerAut r b σ hr with hτ
    have hval : ∀ c : MonoidHom.ker r, β (inr (c : U)) = (kerPart r).index * (ν c : ℂ) := by
      intro c
      rw [hβ, indClassFun_apply_of_mem_center (kerPart r) _ (inr_mem_kerPart r c.2)
        (inr_mem_center r c.2)]
      congr 1
      rw [hψ₁, kerPartChar_inr r (dualChar l) ν (c : U) c.2]
    have hidx : ((kerPart r).index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
    have hτfix : ∀ c : MonoidHom.ker r, τ c = c → c = 1 := by
      intro c hc
      have hc' : σ (c : U) = (c : U) := by
        have := congrArg (fun x : MonoidHom.ker r => (x : U)) hc
        simpa [hτ] using this
      exact Subtype.ext (hσfix _ hc')
    have hτq : τ ^ q = 1 := by
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [coe_kerAut_pow_apply, hσq]; rfl
    refine eq_of_pow_comp_eq_of_fixedPointFree hq hτq hτfix hν hi hj fun c => ?_
    have h1 := congrFun h (inr (c : U))
    simp only [Function.comp_apply, qAut_pow_inr] at h1
    rw [← coe_kerAut_pow_apply r b σ hr i c, ← coe_kerAut_pow_apply r b σ hr j c,
      hval, hval] at h1
    exact Units.val_injective (mul_left_cancel₀ hidx h1)

end CFSG.FeitThompson
