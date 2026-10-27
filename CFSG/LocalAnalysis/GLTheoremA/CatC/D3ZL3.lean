module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section SemiDirect

variable {G : Type*} [Group G]

structure IsSemiDirect (P Q M : Subgroup G) : Prop where
  Q_le : Q ≤ P
  M_le : M ≤ P
  Q_norm : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q
  inf_eq : ∀ x, x ∈ Q → x ∈ M → x = 1
  decomp : ∀ x ∈ P, ∃ q ∈ Q, ∃ m ∈ M, x = q * m

namespace IsSemiDirect

variable {P Q M : Subgroup G}

theorem eq_of_mul_eq (h : IsSemiDirect P Q M) {q q' : G} {m m' : G} (hq : q ∈ Q) (hq' : q' ∈ Q)
    (hm : m ∈ M) (hm' : m' ∈ M) (e : q * m = q' * m') : q = q' ∧ m = m' := by
  have h1 : m * m'⁻¹ = q⁻¹ * q' := by
    calc m * m'⁻¹ = q⁻¹ * (q * m) * m'⁻¹ := by group
      _ = q⁻¹ * (q' * m') * m'⁻¹ := by rw [e]
      _ = q⁻¹ * q' := by group
  have h2 : q⁻¹ * q' = 1 := h.inf_eq _ (mul_mem (inv_mem hq) hq') (h1 ▸ mul_mem hm (inv_mem hm'))
  have h3 : q = q' := by
    have := congrArg (fun x => q * x) h2
    simpa using this.symm
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel e

@[expose] noncomputable def proj (_h : IsSemiDirect P Q M) (x : G) : G :=
  Classical.epsilon fun m => m ∈ M ∧ ∃ q ∈ Q, x = q * m

theorem proj_spec (h : IsSemiDirect P Q M) {x : G} (hx : x ∈ P) :
    h.proj x ∈ M ∧ ∃ q ∈ Q, x = q * h.proj x := by
  obtain ⟨q, hq, m, hm, e⟩ := h.decomp x hx
  exact Classical.epsilon_spec (p := fun m => m ∈ M ∧ ∃ q ∈ Q, x = q * m) ⟨m, hm, q, hq, e⟩

theorem proj_mem (h : IsSemiDirect P Q M) {x : G} (hx : x ∈ P) : h.proj x ∈ M := (h.proj_spec hx).1

theorem proj_eq (h : IsSemiDirect P Q M) {x q m : G} (hx : x ∈ P) (hq : q ∈ Q) (hm : m ∈ M)
    (e : x = q * m) : h.proj x = m := by
  obtain ⟨hmem, q', hq', e'⟩ := h.proj_spec hx
  exact (h.eq_of_mul_eq hq' hq hmem hm (e'.symm.trans e)).2

theorem proj_of_mem_M (h : IsSemiDirect P Q M) {m : G} (hm : m ∈ M) : h.proj m = m :=
  h.proj_eq (h.M_le hm) (one_mem Q) hm (by simp)

theorem proj_of_mem_Q (h : IsSemiDirect P Q M) {q : G} (hq : q ∈ Q) : h.proj q = 1 :=
  h.proj_eq (h.Q_le hq) hq (one_mem M) (by simp)

theorem proj_mul (h : IsSemiDirect P Q M) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    h.proj (x * y) = h.proj x * h.proj y := by
  obtain ⟨hmx, qx, hqx, ex⟩ := h.proj_spec hx
  obtain ⟨hmy, qy, hqy, ey⟩ := h.proj_spec hy
  refine h.proj_eq (mul_mem hx hy) (mul_mem hqx (h.Q_norm _ (h.M_le hmx) qy hqy)) (mul_mem hmx hmy) ?_
  calc x * y = qx * h.proj x * (qy * h.proj y) := by rw [← ex, ← ey]
    _ = _ := by group

theorem proj_inv (h : IsSemiDirect P Q M) {x : G} (hx : x ∈ P) : h.proj x⁻¹ = (h.proj x)⁻¹ := by
  have := h.proj_mul hx (inv_mem hx)
  rw [mul_inv_cancel, h.proj_of_mem_M (one_mem M)] at this
  exact (eq_inv_of_mul_eq_one_right this.symm)

theorem proj_conj (h : IsSemiDirect P Q M) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    h.proj (x * y * x⁻¹) = h.proj x * h.proj y * (h.proj x)⁻¹ := by
  rw [h.proj_mul (mul_mem hx hy) (inv_mem hx), h.proj_mul hx hy, h.proj_inv hx]

theorem proj_mem_of_mem (h : IsSemiDirect P Q M) {x : G} (hx : x ∈ P) :
    ∃ q ∈ Q, x = q * h.proj x := (h.proj_spec hx).2

theorem mul_proj_inv_mem (h : IsSemiDirect P Q M) {x : G} (hx : x ∈ P) : x * (h.proj x)⁻¹ ∈ Q := by
  obtain ⟨q, hq, e⟩ := h.proj_mem_of_mem hx
  have : x * (h.proj x)⁻¹ = q := by
    calc x * (h.proj x)⁻¹ = q * h.proj x * (h.proj x)⁻¹ := by rw [← e]
      _ = q := by group
  rw [this]; exact hq

variable (h : IsSemiDirect P Q M) (φ : G →* G)

@[expose] noncomputable def bar (x : G) : G := h.proj (φ x)

theorem bar_mem (hφP : ∀ x ∈ P, φ x ∈ P) {x : G} (hx : x ∈ P) : h.bar φ x ∈ M :=
  h.proj_mem (hφP x hx)

theorem bar_mul (hφP : ∀ x ∈ P, φ x ∈ P) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    h.bar φ (x * y) = h.bar φ x * h.bar φ y := by
  unfold bar
  rw [map_mul, h.proj_mul (hφP x hx) (hφP y hy)]

theorem bar_proj (hφP : ∀ x ∈ P, φ x ∈ P) (hφQ : ∀ q ∈ Q, φ q ∈ Q) {x : G} (hx : x ∈ P) :
    h.bar φ (h.proj x) = h.bar φ x := by
  obtain ⟨q, hq, e⟩ := h.proj_mem_of_mem hx
  have hm := h.proj_mem hx
  unfold bar
  conv_rhs => rw [e, map_mul, h.proj_mul (hφP q (h.Q_le hq)) (hφP _ (h.M_le hm)),
    h.proj_of_mem_Q (hφQ q hq), one_mul]

theorem proj_phi_proj (hφP : ∀ x ∈ P, φ x ∈ P) (hφQ : ∀ q ∈ Q, φ q ∈ Q) {x : G} (hx : x ∈ P) :
    h.proj (φ (h.proj (φ x))) = h.proj (φ (φ x)) :=
  h.bar_proj φ hφP hφQ (hφP x hx)

theorem bar_bar_bar (hφP : ∀ x ∈ P, φ x ∈ P) (hφQ : ∀ q ∈ Q, φ q ∈ Q)
    (hφ3 : ∀ m ∈ M, φ (φ (φ m)) = m) {m : G} (hm : m ∈ M) :
    h.bar φ (h.bar φ (h.bar φ m)) = m := by
  have hmP := h.M_le hm
  have h1 : h.bar φ (h.bar φ m) = h.proj (φ (φ m)) := by
    unfold bar
    exact h.proj_phi_proj φ hφP hφQ hmP
  have h2 : h.bar φ (h.bar φ (h.bar φ m)) = h.proj (φ (φ (φ m))) := by
    rw [h1]
    unfold bar
    exact h.bar_proj φ hφP hφQ (hφP _ (hφP _ hmP))
  rw [h2, hφ3 m hm, h.proj_of_mem_M hm]

theorem bar_one : h.bar φ 1 = 1 := by
  unfold bar
  rw [map_one]
  exact h.proj_of_mem_M (one_mem M)

theorem bar_inv (hφP : ∀ x ∈ P, φ x ∈ P) {x : G} (hx : x ∈ P) : h.bar φ x⁻¹ = (h.bar φ x)⁻¹ := by
  have := h.bar_mul φ hφP hx (inv_mem hx)
  rw [mul_inv_cancel, h.bar_one φ] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem bar_conj (hφP : ∀ x ∈ P, φ x ∈ P) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    h.bar φ (x * y * x⁻¹) = h.bar φ x * h.bar φ y * (h.bar φ x)⁻¹ := by
  rw [h.bar_mul φ hφP (mul_mem hx hy) (inv_mem hx), h.bar_mul φ hφP hx hy, h.bar_inv φ hφP hx]

end IsSemiDirect

end SemiDirect

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] (U : Subgroup G) [Finite U] {x : G}
    (hx : ∀ u ∈ U, x * u * x⁻¹ ∈ U) : x ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hx h hh, fun hh => ?_⟩
  let f : U → U := fun u => ⟨x * u * x⁻¹, hx u u.2⟩
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have := congrArg Subtype.val huv
    simpa [f] using this
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 hinj ⟨x * h * x⁻¹, hh⟩
  have h1 : x * (u : G) * x⁻¹ = x * h * x⁻¹ := congrArg Subtype.val hu
  have h2 : (u : G) = h := by simpa using h1
  rw [← h2]; exact u.2

end CFSG.LocalAnalysis.GLTheoremA
