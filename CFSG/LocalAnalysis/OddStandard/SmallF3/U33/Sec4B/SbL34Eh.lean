module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

private def conjN {G : Type*} [Group G] (H N : Subgroup G)
    (hNH : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (g : ↥H) : ↥N ≃* ↥N where
  toFun n := ⟨(g : G) * (n : G) * (g : G)⁻¹, hNH (g : G) g.2 (n : G) n.2⟩
  invFun n := ⟨(g : G)⁻¹ * (n : G) * (g : G), by
    have h := hNH (g : G)⁻¹ (g⁻¹).2 (n : G) n.2
    simpa [mul_assoc] using h⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

private lemma map_conjN {G : Type*} [Group G] (H N V : Subgroup G)
    (hNH : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hVH : ∀ g ∈ H, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (g : ↥H) :
    (V.subgroupOf N).map (conjN H N hNH g) = V.subgroupOf N := by
  ext n
  constructor
  · intro hn
    rw [Subgroup.mem_map] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    simpa [conjN] using hVH (g : G) g.2 (m : G) hm
  · intro hn
    rw [Subgroup.mem_map]
    refine ⟨⟨(g : G)⁻¹ * (n : G) * (g : G), ?_⟩, ?_, ?_⟩
    · have h := hNH (g : G)⁻¹ (g⁻¹).2 (n : G) n.2
      simpa [mul_assoc] using h
    · rw [Subgroup.mem_subgroupOf]
      have h := hVH (g : G)⁻¹ (g⁻¹).2 (n : G) hn
      simpa [mul_assoc] using h
    · apply Subtype.ext
      simp [conjN, mul_assoc]

private lemma normal_subgroupOf_of_comm {G : Type*} [Group G] (N V : Subgroup G)
    (hVN : V ≤ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ V) :
    (V.subgroupOf N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ ∈ V :=
    hcomm (g : G) g.2 (n : G) (hVN hn)
  have h2 : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ * (n : G) ∈ V :=
    V.mul_mem h1 hn
  simpa [mul_assoc] using h2

theorem exists_rep {G : Type} [Group G] [Finite G] (H N V : Subgroup G) {k : ℕ}
    (hNH : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hVN : V ≤ N)
    (hVH : ∀ g ∈ H, ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ V) (hsq : ∀ a ∈ N, a * a ∈ V)
    (hcard : Nat.card N = 2 ^ k * Nat.card V) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module (ZMod 2) E) (_ : Module.Finite (ZMod 2) E)
      (ψ : ↥H →* (E ≃ₗ[ZMod 2] E)), Module.finrank (ZMod 2) E = k ∧
        ∀ g : ↥H, ψ g = 1 ↔ ∀ a ∈ N, (g : G) * a * (g : G)⁻¹ * a⁻¹ ∈ V := by
  let V' : Subgroup ↥N := V.subgroupOf N
  have hV'normal : V'.Normal := normal_subgroupOf_of_comm N V hVN hcomm
  letI : V'.Normal := hV'normal
  let Q := ↥N ⧸ V'
  have hcommQ : ∀ x y : Q, x * y = y * x := by
    intro x y
    refine Quotient.inductionOn₂' x y (fun a b => ?_)
    show ((a * b : ↥N) : Q) = ((b * a : ↥N) : Q)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv, mul_assoc] using hcomm (a : G) a.2 (b : G) b.2
  let : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcommQ }
  have hsqQ : ∀ w : Q, w * w = 1 := by
    intro w
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective w
    rw [← hs, ← QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (s * s)).mpr (hsq (s : G) s.2)]
  have htwo : ∀ w : Additive Q, 2 • w = 0 := by
    intro w
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hw : w = Additive.ofMul (s : Q) := by rw [hs]; rfl
    rw [hw, ← ofMul_pow, ← QuotientGroup.mk_pow, pow_two,
      (QuotientGroup.eq_one_iff (s * s)).mpr (hsq (s : G) s.2)]
    rfl
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (n := 2) htwo
  haveI : Finite (Additive Q) := inferInstance
  haveI : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  let φ : ↥H → (Q ≃* Q) := fun g =>
    QuotientGroup.congr V' V' (conjN H N hNH g) (map_conjN H N V hNH hVH g)
  have hmulQ : ∀ g h : ↥H, φ (g * h) = φ g * φ h := by
    intro g h
    ext q
    refine Quotient.inductionOn' q (fun n => ?_)
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      QuotientGroup.congr_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by
      show ((g : G) * (h : G)) * (n : G) * ((g : G) * (h : G))⁻¹
        = (g : G) * ((h : G) * (n : G) * (h : G)⁻¹) * (g : G)⁻¹
      group))
  let eAdd : ↥H → (Additive Q ≃+ Additive Q) := fun g =>
    { toFun := fun x => Additive.ofMul (φ g (Additive.toMul x))
      invFun := fun x => Additive.ofMul ((φ g).symm (Additive.toMul x))
      left_inv := fun x => by
        simp only [toMul_ofMul, MulEquiv.symm_apply_apply, ofMul_toMul]
      right_inv := fun x => by
        simp only [toMul_ofMul, MulEquiv.apply_symm_apply, ofMul_toMul]
      map_add' := fun x y => by
        simp only [toMul_add, map_mul, ofMul_mul] }
  let ψfun : ↥H → (Additive Q ≃ₗ[ZMod 2] Additive Q) := fun g =>
    (eAdd g).toLinearEquiv (fun c x => ZMod.map_smul (eAdd g) c x)
  have ψ_apply : ∀ (g : ↥H) (x : Additive Q), ψfun g x = Additive.ofMul (φ g x.toMul) :=
    fun g x => rfl
  have hmul : ∀ g h : ↥H, ψfun (g * h) = ψfun g * ψfun h := by
    intro g h
    ext v
    rw [LinearEquiv.mul_apply]
    apply Additive.toMul.injective
    change φ (g * h) (Additive.toMul v) = φ g (φ h (Additive.toMul v))
    rw [hmulQ, MulAut.mul_apply]
  let ψ : ↥H →* (Additive Q ≃ₗ[ZMod 2] Additive Q) := MonoidHom.mk' ψfun hmul
  have hψ_eq_one : ∀ g : ↥H, ψ g = 1 ↔ φ g = 1 := by
    intro g
    constructor
    · intro h
      ext q
      have h' := congrArg (fun f : Additive Q ≃ₗ[ZMod 2] Additive Q => f (Additive.ofMul q)) h
      change ψfun g (Additive.ofMul q) = Additive.ofMul q at h'
      rw [ψ_apply] at h'
      simpa using h'
    · intro h
      ext x
      change ψfun g x = x
      rw [ψ_apply]
      have h' : φ g x.toMul = x.toMul := by
        have := congrArg (fun f : Q ≃* Q => f x.toMul) h
        simpa using this
      rw [h']
      rfl
  have hker : ∀ g : ↥H, ψ g = 1 ↔ ∀ a ∈ N, (g : G) * a * (g : G)⁻¹ * a⁻¹ ∈ V := by
    intro g
    rw [hψ_eq_one g]
    constructor
    · intro h a ha
      let aN : ↥N := ⟨a, ha⟩
      have h1 : φ g (QuotientGroup.mk aN) = QuotientGroup.mk aN := by
        have := congrArg (fun f : Q ≃* Q => f (QuotientGroup.mk aN)) h
        simpa using this
      rw [QuotientGroup.congr_mk, QuotientGroup.eq_iff_div_mem] at h1
      rw [Subgroup.mem_subgroupOf] at h1
      simpa [aN, conjN, div_eq_mul_inv, mul_assoc] using h1
    · intro h
      ext q
      refine Quotient.inductionOn' q (fun a => ?_)
      show φ g (QuotientGroup.mk a) = QuotientGroup.mk a
      rw [QuotientGroup.congr_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      simpa [conjN, div_eq_mul_inv, mul_assoc] using h (a : G) a.2
  have hcardQ : Nat.card Q = 2 ^ k := by
    have h1 : Nat.card ↥N = Nat.card Q * Nat.card V' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup V'
    have hV'card : Nat.card V' = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
    rw [hV'card] at h1
    haveI : Nonempty ↥V := ⟨1, V.one_mem⟩
    have h2 : Nat.card Q * Nat.card V = 2 ^ k * Nat.card V := by
      rw [← h1]; exact hcard
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥V)) h2
  have hfin : Module.finrank (ZMod 2) (Additive Q) = k := by
    have hEcard : Nat.card (Additive Q) = 2 ^ Module.finrank (ZMod 2) (Additive Q) := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
      rwa [Nat.card_zmod] at h
    apply Nat.pow_right_injective (le_refl 2)
    show 2 ^ Module.finrank (ZMod 2) (Additive Q) = 2 ^ k
    rw [← hEcard, ← hcardQ]
    rfl
  exact ⟨Additive Q, inferInstance, inferInstance, inferInstance, ψ, hfin, hker⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
