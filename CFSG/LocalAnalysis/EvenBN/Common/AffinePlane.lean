module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.PlaneTranslations

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Equiv Matrix CFSG.LocalAnalysis.EvenBN.LinearThree.Plane
open scoped MatrixGroups

namespace AffinePlane

theorem perm_apply_inv_self {α : Type*} (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem perm_inv_apply_self {α : Type*} (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

section Algebra

variable {k : Type*} [Field k]

theorem sl_smul_eq (M : SL(2, k)) (v : Fin 2 → k) :
    M • v = ![M 0 0 * v 0 + M 0 1 * v 1, M 1 0 * v 0 + M 1 1 * v 1] := by
  refine vec_ext ?_ ?_ <;>
    simp [HSMul.hSMul, SMul.smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem e₁_ne_zero : (![1, 0] : Fin 2 → k) ≠ 0 := fun h => by simpa using congrFun h 0

theorem e₂_ne_zero : (![0, 1] : Fin 2 → k) ≠ 0 := fun h => by simpa using congrFun h 1

theorem e₂_not_mem_kLine : (![0, 1] : Fin 2 → k) ∉ kLine ![1, 0] := by
  rintro ⟨a, ha⟩
  simpa using congrFun ha 1

theorem eq_smul_add_smul (v : Fin 2 → k) : v = v 0 • ![1, 0] + v 1 • ![0, 1] :=
  vec_ext (by simp) (by simp)

theorem mem_kLine_of_smul_eq {M : SL(2, k)} (hM : M ≠ 1) {w : Fin 2 → k} (hw : w ≠ 0)
    (hMw : M • w = w) {y : Fin 2 → k} (hMy : M • y = y) : y ∈ kLine w := by
  by_contra hy
  apply hM
  obtain ⟨A, hA⟩ := exists_sl_smul_e₁ hw
  set N := A⁻¹ * M * A with hN
  have hNe : N • ![(1 : k), 0] = ![1, 0] := by
    rw [hN, mul_smul, mul_smul, hA, hMw, ← hA, inv_smul_smul]
  set y' := A⁻¹ • y with hy'
  have hNy : N • y' = y' := by
    rw [hN, hy', mul_smul, mul_smul, smul_inv_smul, hMy]
  have hy'1 : y' 1 ≠ 0 := by
    intro h0
    apply hy
    refine ⟨y' 0, ?_⟩
    have e : y' = y' 0 • ![1, 0] := vec_ext (by simp) (by simp [h0])
    calc y = A • y' := by rw [hy', smul_inv_smul]
      _ = A • (y' 0 • ![1, 0]) := by rw [← e]
      _ = y' 0 • w := by rw [sl_smul_smul, hA]
  have e1 := congrFun hNe 0
  have e2 := congrFun hNe 1
  have e3 := congrFun hNy 0
  rw [sl_smul_eq] at e1 e2 e3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero] at e1 e2 e3
  have hdet := N.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h01 : N 0 1 = 0 := by
    have : N 0 1 * y' 1 = 0 := by linear_combination e3 - y' 0 * e1
    exact (mul_eq_zero.mp this).resolve_right hy'1
  have h11 : N 1 1 = 1 := by
    rw [e1, h01, e2] at hdet
    linear_combination hdet
  have hN1 : N = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [e1, e2, h01, h11]
  calc M = A * N * A⁻¹ := by rw [hN]; group
    _ = 1 := by rw [hN1, mul_one, mul_inv_cancel]

theorem eq_zero_of_smul_add_smul {x y : Fin 2 → k} (hx : x ≠ 0) (hy : y ∉ kLine x) {a b : k}
    (h : a • x + b • y = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply hy
    refine ⟨-(a / b), ?_⟩
    have : b • y = -(a • x) := eq_neg_of_add_eq_zero_right h
    calc y = b⁻¹ • (b • y) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = -(a / b) • x := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  refine ⟨?_, hb⟩
  rw [hb, zero_smul, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_right hx

theorem fix_iff_of_linear_involution [CharP k 2] {N : (Fin 2 → k) → (Fin 2 → k)}
    (hadd : ∀ v w, N (v + w) = N v + N w) (hsmul : ∀ (t : k) v, N (t • v) = t • N v)
    (he : N ![1, 0] = ![1, 0]) (hinv : ∀ v, N (N v) = v) (hne : ∃ v, N v ≠ v)
    (y : Fin 2 → k) : N y = y ↔ y 1 = 0 := by
  set u := N ![0, 1] with hu
  have hform : ∀ v : Fin 2 → k, N v = ![v 0 + v 1 * u 0, v 1 * u 1] := by
    intro v
    conv_lhs => rw [eq_smul_add_smul v]
    rw [hadd, hsmul, hsmul, he, ← hu]
    refine vec_ext ?_ ?_ <;> simp
  have hNu := hinv ![0, 1]
  rw [← hu, hform u] at hNu
  have hu0 := congrFun hNu 0
  have hu1 := congrFun hNu 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu0 hu1
  have hu11 : u 1 = 1 := by
    have h2 : (u 1 + 1) ^ 2 = 0 := by
      linear_combination hu1 + (u 1 + 1) * CharTwo.two_eq_zero (R := k)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linear_combination this - CharTwo.two_eq_zero (R := k)
  have hu00 : u 0 ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hne
    apply hv
    rw [hform v, h0, hu11]
    refine vec_ext ?_ ?_ <;> simp
  rw [hform y, hu11]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    have : y 1 * u 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_right hu00
  · intro h
    refine vec_ext ?_ ?_ <;> simp [h]

end Algebra

section Plane

variable {k : Type*} [Field k]

structure SLAffine (Γ : Subgroup (Perm (Fin 2 → k))) : Prop where
  affine : ∀ γ ∈ Γ, ∀ v w, γ (v + w) + γ 0 = γ v + γ w
  trans : ∀ v : Fin 2 → k, ∃ γ ∈ Γ, γ 0 = v
  sl_mem : ∀ M : SL(2, k), slPerm M ∈ Γ
  sl_normal : ∀ δ ∈ Γ, δ 0 = 0 → ∀ M : SL(2, k), ∃ M' : SL(2, k),
    δ⁻¹ * slPerm M * δ = slPerm M'

namespace SLAffine

variable {Γ : Subgroup (Perm (Fin 2 → k))}

theorem map_add (h : SLAffine Γ) {δ : Perm (Fin 2 → k)} (hδ : δ ∈ Γ) (h0 : δ 0 = 0)
    (v w : Fin 2 → k) : δ (v + w) = δ v + δ w := by
  have := h.affine δ hδ v w
  rwa [h0, add_zero] at this

theorem inv_apply_zero {δ : Perm (Fin 2 → k)} (h0 : δ 0 = 0) : δ⁻¹ 0 = 0 :=
  Perm.inv_eq_iff_eq.mpr h0.symm

theorem exists_sl_conj (h : SLAffine Γ) {δ : Perm (Fin 2 → k)} (hδ : δ ∈ Γ) (h0 : δ 0 = 0)
    (M : SL(2, k)) : ∃ M' : SL(2, k), ∀ x, M' • δ x = δ (M • x) := by
  obtain ⟨M', hM'⟩ := h.sl_normal δ⁻¹ (inv_mem hδ) (inv_apply_zero h0) M
  refine ⟨M', fun x => ?_⟩
  have := congrArg (fun f : Perm (Fin 2 → k) => f (δ x)) hM'
  simp only [Perm.mul_apply, inv_inv, perm_inv_apply_self] at this
  exact this.symm

theorem smul_mem_kLine (h : SLAffine Γ) {δ : Perm (Fin 2 → k)} (hδ : δ ∈ Γ) (h0 : δ 0 = 0)
    {v : Fin 2 → k} (hv : v ≠ 0) (t : k) : δ (t • v) ∈ kLine (δ v) := by
  obtain ⟨A, hA⟩ := exists_sl_smul_e₁ hv
  set M := A * rootSL 1 * A⁻¹ with hM
  obtain ⟨M', hM'⟩ := h.exists_sl_conj hδ h0 M
  have hfix : ∀ s : k, M • (s • v) = s • v := by
    intro s
    rw [hM, mul_smul, mul_smul, ← hA, ← sl_smul_smul A s, inv_smul_smul,
      rootSL_smul_of_mem (smul_e₁_mem s)]
  have hM'1 : M' ≠ 1 := by
    rintro rfl
    have hfixall : ∀ x, M • x = x := fun x => δ.injective (by rw [← hM', one_smul])
    have := hfixall (A • ![0, 1])
    rw [hM, mul_smul, mul_smul, inv_smul_smul] at this
    have h1 := mem_axisLine_of_rootSL_one (smul_left_cancel A this)
    simp [axisLine] at h1
  have hδv : δ v ≠ 0 := fun h' => hv (δ.injective (h'.trans h0.symm))
  refine mem_kLine_of_smul_eq hM'1 hδv ?_ ?_
  · rw [hM']
    congr 1
    simpa using hfix 1
  · rw [hM', hfix]

theorem exists_ringHom (h : SLAffine Γ) {δ : Perm (Fin 2 → k)} (hδ : δ ∈ Γ) (h0 : δ 0 = 0) :
    ∃ σ : k →+* k, ∀ (t : k) (v : Fin 2 → k), δ (t • v) = σ t • δ v := by
  have hadd := h.map_add hδ h0
  have hδ' : δ⁻¹ ∈ Γ := inv_mem hδ
  have h0' : δ⁻¹ 0 = 0 := inv_apply_zero h0
  have hne : ∀ v, v ≠ 0 → δ v ≠ 0 := fun v hv h' => hv (δ.injective (h'.trans h0.symm))
  have hind : ∀ v w : Fin 2 → k, v ≠ 0 → w ∉ kLine v → δ w ∉ kLine (δ v) := by
    rintro v w hv hw ⟨a, ha⟩
    apply hw
    have := h.smul_mem_kLine hδ' h0' (hne v hv) a
    rwa [← ha, perm_inv_apply_self, perm_inv_apply_self] at this
  have hagree : ∀ v w : Fin 2 → k, v ≠ 0 → w ∉ kLine v → ∀ t s s' : k,
      δ (t • v) = s • δ v → δ (t • w) = s' • δ w → s = s' := by
    intro v w hv hw t s s' hs hs'
    have hvw : v + w ≠ 0 := by
      intro h'
      apply hw
      exact ⟨-1, by rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_right h'⟩
    obtain ⟨s'', hs''⟩ := h.smul_mem_kLine hδ h0 hvw t
    rw [smul_add, hadd, hadd, hs, hs'] at hs''
    have hz : (s - s'') • δ v + (s' - s'') • δ w = 0 := by
      rw [sub_smul, sub_smul, smul_add] at *
      rw [← sub_eq_zero] at hs''
      rw [← hs'']
      abel
    obtain ⟨h1, h2⟩ := eq_zero_of_smul_add_smul (hne v hv) (hind v w hv hw) hz
    linear_combination h1 - h2
  have he₁ : (![1, 0] : Fin 2 → k) ≠ 0 := e₁_ne_zero
  have hex : ∀ t : k, ∃ s : k, δ (t • ![1, 0]) = s • δ ![1, 0] :=
    fun t => h.smul_mem_kLine hδ h0 he₁ t
  choose σ hσ using hex
  have key : ∀ (t : k) (v : Fin 2 → k), δ (t • v) = σ t • δ v := by
    intro t v
    by_cases hv : v = 0
    · rw [hv, smul_zero, h0, smul_zero]
    obtain ⟨s, hs⟩ := h.smul_mem_kLine hδ h0 hv t
    rw [hs]
    congr 1
    by_cases hv1 : v ∈ kLine ![1, 0]
    · have hv2 : (![0, 1] : Fin 2 → k) ∉ kLine v := by
        rw [kLine_eq_of_mem hv1 hv]
        exact e₂_not_mem_kLine
      obtain ⟨s₂, hs₂⟩ := h.smul_mem_kLine hδ h0 e₂_ne_zero t
      rw [hagree _ _ hv hv2 t s s₂ hs hs₂]
      exact (hagree _ _ he₁ e₂_not_mem_kLine t (σ t) s₂ (hσ t) hs₂).symm
    · exact (hagree _ _ he₁ hv1 t (σ t) s (hσ t) hs).symm
  have hinj : Function.Injective fun c : k => c • δ ![1, 0] :=
    smul_left_injective k (hne _ he₁)
  refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, key⟩
  · apply hinj
    change σ 1 • δ ![1, 0] = (1 : k) • δ ![1, 0]
    rw [← key, one_smul, one_smul]
  · intro s t
    apply hinj
    change σ (s * t) • δ ![1, 0] = (σ s * σ t) • δ ![1, 0]
    rw [← key, mul_smul, key, key, smul_smul]
  · apply hinj
    change σ 0 • δ ![1, 0] = (0 : k) • δ ![1, 0]
    rw [← key, zero_smul, zero_smul, h0]
  · intro s t
    apply hinj
    change σ (s + t) • δ ![1, 0] = (σ s + σ t) • δ ![1, 0]
    rw [← key, add_smul, hadd, key, key, add_smul]

theorem ringHom_eq_of_apply_eq [Finite k] {σ σ' : k →+* k} {α : kˣ}
    (hα : ∀ x : kˣ, x ∈ Subgroup.zpowers α) (h : σ α = σ' α) : σ = σ' := by
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr (hα (Units.mk0 x hx))
  have hm' : (α : k) ^ m = x := by
    have := congrArg Units.val hm
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at this
  rw [← hm', map_pow, map_pow, h]

theorem exists_mem_apply_eq (h : SLAffine Γ) {c d : Fin 2 → k} (hcd : c ≠ d) :
    ∃ g ∈ Γ, g c = 0 ∧ g d = ![1, 0] := by
  obtain ⟨γ, hγ, hγ0⟩ := h.trans c
  have hd : γ⁻¹ d ≠ 0 := fun e => hcd (by
    rw [Perm.inv_eq_iff_eq] at e
    rw [e, hγ0])
  obtain ⟨A, hA⟩ := exists_sl_smul_e₁ hd
  refine ⟨slPerm A⁻¹ * γ⁻¹, mul_mem (h.sl_mem _) (inv_mem hγ), ?_, ?_⟩
  · rw [Perm.mul_apply, ← hγ0, perm_inv_apply_self, slPerm_apply,
      Matrix.mulVec_zero]
  · rw [Perm.mul_apply, slPerm_apply,
      show ((A⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ γ⁻¹ d = A⁻¹ • γ⁻¹ d from rfl, ← hA,
      inv_smul_smul]

variable [Fintype k] [CharP k 2]

theorem fix_line_of_mem (h : SLAffine Γ) {κ : Perm (Fin 2 → k)} (hκ : κ ∈ Γ)
    (h0 : (κ⁻¹ 0) 1 = 0) (h1 : (κ⁻¹ ![1, 0]) 1 = 0) (x : Fin 2 → k) :
    (κ⁻¹ x) 1 = 0 ↔ x 1 = 0 := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : k → Perm (Fin 2 → k), ∀ b, P b = κ * slPerm (rootSL b) * κ⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hPΓ : ∀ b, P b ∈ Γ := fun b => by
    rw [hP]
    exact mul_mem (mul_mem hκ (h.sl_mem _)) (inv_mem hκ)
  have hfix : ∀ b y, (κ⁻¹ y) 1 = 0 → P b y = y := by
    intro b y hy
    rw [hP, Perm.mul_apply, Perm.mul_apply, slPerm_apply,
      show ((rootSL b : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ κ⁻¹ y =
        rootSL b • κ⁻¹ y from rfl, rootSL_smul_of_mem hy, perm_apply_inv_self]
  have hP0 : ∀ b, P b 0 = 0 := fun b => hfix b 0 h0
  choose σ hσ using fun b => h.exists_ringHom (hPΓ b) (hP0 b)
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := kˣ)
  have hne : ∀ b, σ b (α : k) ≠ 0 := fun b => (map_ne_zero (σ b)).mpr α.ne_zero
  have hcard : Fintype.card kˣ < Fintype.card k := by
    rw [Fintype.card_units]
    have : 0 < Fintype.card k := Fintype.card_pos
    omega
  obtain ⟨b, b', hbb', hσα⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun b => Units.mk0 (σ b α) (hne b)) hcard
  have hσσ : σ b = σ b' := ringHom_eq_of_apply_eq hα (by
    have := congrArg Units.val hσα
    simpa using this)
  obtain ⟨N, hNdef⟩ : ∃ N : Perm (Fin 2 → k), N = P b' * (P b)⁻¹ := ⟨_, rfl⟩
  have hNapp : ∀ v, N v = P b' ((P b)⁻¹ v) := fun v => by rw [hNdef, Perm.mul_apply]
  have hsurj : Function.Surjective (σ b) :=
    Finite.injective_iff_surjective.mp (σ b).injective
  have hPinv : ∀ (s : k) (v : Fin 2 → k), (P b)⁻¹ (σ b s • v) = s • (P b)⁻¹ v := by
    intro s v
    rw [Perm.inv_eq_iff_eq, hσ, perm_apply_inv_self]
  have hNsmul : ∀ (t : k) (v : Fin 2 → k), N (t • v) = t • N v := by
    intro t v
    obtain ⟨s, rfl⟩ := hsurj t
    rw [hNapp, hPinv, hσ, hσσ, hNapp]
  have hNadd : ∀ v w : Fin 2 → k, N (v + w) = N v + N w := by
    intro v w
    have hb0 : (P b)⁻¹ 0 = 0 := inv_apply_zero (hP0 b)
    rw [hNapp, hNapp, hNapp, h.map_add (inv_mem (hPΓ b)) hb0, h.map_add (hPΓ b') (hP0 b')]
  obtain ⟨c, hc⟩ : ∃ c : k, c = b' - b := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact sub_ne_zero.mpr hbb'.symm
  have hNc : N = κ * slPerm (rootSL c) * κ⁻¹ := by
    have e : rootSL c = rootSL b' * (rootSL b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, ← rootSL_add, hc, sub_add_cancel]
    rw [hNdef, e, map_mul, map_inv, hP, hP]
    group
  have hNfix : ∀ y, N y = y ↔ (κ⁻¹ y) 1 = 0 := by
    intro y
    rw [hNc, Perm.mul_apply, Perm.mul_apply, slPerm_apply,
      show ((rootSL c : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ κ⁻¹ y = rootSL c • κ⁻¹ y from rfl,
      rootSL_smul]
    constructor
    · intro e
      have e' := congrArg (fun z => (κ⁻¹ z) 0) e
      simp only [perm_inv_apply_self, Matrix.cons_val_zero] at e'
      have : c * (κ⁻¹ y) 1 = 0 := by linear_combination e'
      exact (mul_eq_zero.mp this).resolve_left hc0
    · intro e
      rw [e, mul_zero, add_zero]
      conv_rhs => rw [← perm_apply_inv_self κ y]
      congr 1
      exact vec_ext (by simp) (by simp [e])
  have hNe : N ![1, 0] = ![1, 0] := (hNfix _).mpr h1
  have hNN : ∀ v, N (N v) = v := by
    intro v
    have e : slPerm (rootSL c) * slPerm (rootSL c) = 1 := by
      rw [← map_mul, ← rootSL_add, CharTwo.add_self_eq_zero, rootSL_zero, map_one]
    have : N * N = 1 := by
      calc N * N = κ * (slPerm (rootSL c) * slPerm (rootSL c)) * κ⁻¹ := by rw [hNc]; group
        _ = 1 := by rw [e, mul_one, mul_inv_cancel]
    exact congrArg (fun f : Perm (Fin 2 → k) => f v) this
  have hNne : ∃ v, N v ≠ v := by
    refine ⟨κ ![0, 1], fun e => ?_⟩
    have := (hNfix _).mp e
    rw [perm_inv_apply_self] at this
    simp at this
  rw [← hNfix, fix_iff_of_linear_involution hNadd hNsmul hNe hNN hNne]

theorem line_eq (h : SLAffine Γ) {g g' : Perm (Fin 2 → k)} (hg : g ∈ Γ) (hg' : g' ∈ Γ)
    {c d : Fin 2 → k} (hcd : c ≠ d) (hc : (g⁻¹ c) 1 = 0) (hd : (g⁻¹ d) 1 = 0)
    (hc' : (g'⁻¹ c) 1 = 0) (hd' : (g'⁻¹ d) 1 = 0) (x : Fin 2 → k) :
    (g⁻¹ x) 1 = 0 ↔ (g'⁻¹ x) 1 = 0 := by
  obtain ⟨m, hm, hmc, hmd⟩ := h.exists_mem_apply_eq hcd
  have hmc' : m⁻¹ 0 = c := by rw [Perm.inv_eq_iff_eq, hmc]
  have hmd' : m⁻¹ ![1, 0] = d := by rw [Perm.inv_eq_iff_eq, hmd]
  have key : ∀ g ∈ Γ, (g⁻¹ c) 1 = 0 → (g⁻¹ d) 1 = 0 →
      ∀ y, (g⁻¹ (m⁻¹ y)) 1 = 0 ↔ y 1 = 0 := by
    intro g hg hc hd y
    have h' := h.fix_line_of_mem (mul_mem hm hg)
      (by rw [_root_.mul_inv_rev, Perm.mul_apply, hmc']; exact hc)
      (by rw [_root_.mul_inv_rev, Perm.mul_apply, hmd']; exact hd) y
    rwa [_root_.mul_inv_rev, Perm.mul_apply] at h'
  rw [← perm_inv_apply_self m x, key g hg hc hd, key g' hg' hc' hd']

theorem line (h : SLAffine Γ) (c : k) :
    ∃ σ ∈ Γ, (∀ v ∈ axisLine k, σ v ∈ axisLine k) ∧ σ 0 = ![c, 0] := by
  have hne : (![c, 0] : Fin 2 → k) ≠ ![c + 1, 0] := fun e => by simpa using congrFun e 0
  obtain ⟨g, hg, hg0, hg1⟩ := h.exists_mem_apply_eq hne
  have hl := h.line_eq (inv_mem hg) (one_mem Γ) hne (by rw [inv_inv, hg0]; rfl)
    (by rw [inv_inv, hg1]; rfl) (by simp) (by simp)
  refine ⟨g⁻¹, inv_mem hg, fun v hv => ?_, by rw [Perm.inv_eq_iff_eq, hg0]⟩
  have := (hl (g⁻¹ v)).mp (by rw [inv_inv, perm_apply_inv_self]; exact hv)
  rw [inv_one, Perm.one_apply] at this
  exact this

theorem naturalAffine (h : SLAffine Γ) : NaturalAffine Γ :=
  ⟨h.affine, h.sl_mem, h.sl_normal, h.line⟩

theorem addRight_mem (h : SLAffine Γ) (b : Fin 2 → k) : Equiv.addRight b ∈ Γ :=
  h.naturalAffine.translations_le b

end SLAffine

end Plane

end AffinePlane

section Coset

open Subgroup AffinePlane

variable {G : Type*} [Group G] {W X K : Subgroup G} {t : G} {k : Type*} [Field k]
  [Fintype k] [CharP k 2]

theorem exists_conj_eq_mul_of_sl_transitive (ι : Multiplicative (Fin 2 → k) ≃* W)
    (hXW : X ≤ normalizer (W : Set G)) (hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W)
    (htr : ∀ w ∈ W, ∃ x ∈ X, x * t * x⁻¹ = t * w)
    (hK : K ≤ X ⊓ centralizer ({t} : Set G))
    (hnat : ∀ g ∈ K, ∃ M : SL(2, k), ∀ v : Fin 2 → k, g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
      ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hsurj : ∀ M : SL(2, k), ∃ g ∈ K, ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hKn : ∀ x ∈ X ⊓ centralizer ({t} : Set G), ∀ g ∈ K, ∃ g' ∈ K, ∀ w ∈ W,
      x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹) :
    ∀ w ∈ W, ∃ x ∈ X, x ∈ centralizer (W : Set G) ∧ x * t * x⁻¹ = t * w := by
  set ρ := cosetAction ι t hXW hXt with hρ
  have hfix : ∀ x : X, ρ x 0 = 0 → (x : G) ∈ centralizer ({t} : Set G) := by
    intro x hx0
    have hxt : (x : G) * t * (x : G)⁻¹ = t := by
      have := cosetPt_cosetAction (ι := ι) (t := t) (hXW := hXW) (hXt := hXt) x 0
      rw [← hρ, hx0, cosetPt_zero] at this
      exact this.symm
    refine mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    calc t * (x : G) = ((x : G) * t * (x : G)⁻¹) * x := by rw [hxt]
      _ = (x : G) * t := by group
  have hSL : SLAffine ρ.range := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ v w
      exact cosetAction_affine x v w
    · intro v
      obtain ⟨x, hx, hxt⟩ := htr _ (ι (Multiplicative.ofAdd v)).2
      refine ⟨ρ ⟨x, hx⟩, ⟨_, rfl⟩, cosetPt_injective (ι := ι) (t := t) ?_⟩
      rw [hρ, cosetPt_cosetAction, cosetPt_zero, hxt]
      rfl
    · intro M
      obtain ⟨g, hg, hgM⟩ := hsurj M
      exact ⟨⟨g, (hK hg).1⟩, cosetAction_eq_slPerm ι hXW hXt (hK hg).1 (hK hg).2 hgM⟩
    · rintro _ ⟨y, rfl⟩ hy0 M
      have hyt := hfix y hy0
      have hyc : (y : G)⁻¹ ∈ X ⊓ centralizer ({t} : Set G) :=
        ⟨X.inv_mem y.2, (centralizer ({t} : Set G)).inv_mem hyt⟩
      obtain ⟨g, hg, hgM⟩ := hsurj M
      obtain ⟨g', hg', hgg'⟩ := hKn _ hyc g hg
      obtain ⟨M', hM'⟩ := hnat g' hg'
      rw [inv_inv] at hgg'
      have hzX : (y : G)⁻¹ * g * y ∈ X := mul_mem (mul_mem (X.inv_mem y.2) (hK hg).1) y.2
      have hzt : (y : G)⁻¹ * g * y ∈ centralizer ({t} : Set G) :=
        mul_mem (mul_mem ((centralizer ({t} : Set G)).inv_mem hyt) (hK hg).2) hyt
      refine ⟨M', ?_⟩
      have hz : ρ ⟨(y : G)⁻¹ * g * y, hzX⟩ = slPerm M' :=
        cosetAction_eq_slPerm ι hXW hXt hzX hzt fun v => by
          rw [hgg' _ (ι (Multiplicative.ofAdd v)).2, hM']
      rw [← cosetAction_eq_slPerm ι hXW hXt (hK hg).1 (hK hg).2 hgM, ← hz, ← map_inv, ← map_mul,
        ← map_mul]
      rfl
  intro w hw
  obtain ⟨⟨x, hx⟩, hρx⟩ := hSL.addRight_mem (wCoord ι w)
  have hpt : ∀ u, x * cosetPt ι t u * x⁻¹ = cosetPt ι t (u + wCoord ι w) := by
    intro u
    have := cosetPt_cosetAction (ι := ι) (t := t) (hXW := hXW) (hXt := hXt) ⟨x, hx⟩ u
    rw [← hρ, hρx, Equiv.coe_addRight] at this
    exact this.symm
  have hxt : x * t * x⁻¹ = t * w := by
    have := hpt 0
    rw [cosetPt_zero, zero_add, cosetPt, wCoord_mem hw] at this
    exact this
  refine ⟨x, hx, mem_centralizer_iff.mpr fun w' hw' => ?_, hxt⟩
  have h1 := hpt (wCoord ι w')
  rw [cosetPt, cosetPt, ofAdd_add, map_mul, Subgroup.coe_mul, wCoord_mem hw,
    wCoord_mem hw'] at h1
  have h2 : x * (t * w') * x⁻¹ = (x * t * x⁻¹) * (x * w' * x⁻¹) := by group
  rw [h2, hxt, mul_assoc, mul_right_inj,
    CFSG.LocalAnalysis.EvenBN.LinearThree.Plane.mul_comm_of_mem ι hw' hw] at h1
  have h3 : x * w' * x⁻¹ = w' := mul_left_cancel h1
  calc w' * x = (x * w' * x⁻¹) * x := by rw [h3]
    _ = x * w' := by group

end Coset

end CFSG.LocalAnalysis.EvenBN.Common
