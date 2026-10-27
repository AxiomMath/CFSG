module

public import CFSG.Open.LocalVocabulary
import TauCeti.RepresentationTheory.Unipotent.Solvable

public section

namespace CFSG.LinearAlgebra.SchurElemAbelianTwo

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def mulSpan (N : Submodule K (V →ₗ[K] V)) (X : Submodule K V) : Submodule K V :=
  span K {v | ∃ y ∈ N, ∃ x ∈ X, y x = v}

private theorem eq_bot_of_le_mulSpan {N : Submodule K (V →ₗ[K] V)} {F : ℕ → Submodule K V}
    {m : ℕ} (hF0 : F 0 = ⊥) (hFm : F m = ⊤) (hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i)
    {X : Submodule K V} (hX : X ≤ mulSpan N X) : X = ⊥ := by
  have key : ∀ i, X ≤ F (i + 1) → X ≤ F i := by
    intro i hi
    refine hX.trans (span_le.mpr ?_)
    rintro _ ⟨y, hy, x, hx, rfl⟩
    exact hF y hy i x (hi hx)
  have hall : ∀ j, X ≤ F (m - j) := by
    intro j
    induction j with
    | zero => simp [hFm]
    | succ j ih =>
      rcases Nat.lt_or_ge j m with h | h
      · have e : m - j = (m - (j + 1)) + 1 := by omega
        rw [e] at ih
        exact key _ ih
      · have e : m - (j + 1) = m - j := by omega
        rw [e]
        exact ih
  have h0 := hall m
  rw [Nat.sub_self, hF0] at h0
  exact eq_bot_iff.mpr h0

private theorem sub_one_mem_flag {n : ℕ} (b : Basis (Fin n) K V) {T : V →ₗ[K] V}
    (hT : (LinearMap.toMatrixAlgEquiv b T).IsUpperUnitriangular) (i : ℕ) {v : V}
    (hv : v ∈ span K (b '' {j | (j : ℕ) < i + 1})) :
    (T - 1) v ∈ span K (b '' {j | (j : ℕ) < i}) := by
  obtain ⟨hTu, hTd⟩ := (Matrix.isUpperUnitriangular_def _).mp hT
  have hle : span K (b '' {j | (j : ℕ) < i + 1}) ≤
      (span K (b '' {j | (j : ℕ) < i})).comap (T - 1) := by
    rw [span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, mem_comap, Basis.mem_span_image]
    intro k hk
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hk
    simp only [Set.mem_setOf_eq] at hj ⊢
    by_contra hki
    apply hk
    have hjk : j ≤ k := by
      rw [Fin.le_iff_val_le_val]
      omega
    rcases hjk.lt_or_eq with hlt | heq
    · have h0 : LinearMap.toMatrixAlgEquiv b T k j = 0 := hTu (show id j < id k from hlt)
      rw [LinearMap.toMatrixAlgEquiv_apply] at h0
      rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, h0, Module.End.one_apply,
        Basis.repr_self, Finsupp.single_apply, if_neg hlt.ne, sub_zero]
    · subst heq
      have h1 : LinearMap.toMatrixAlgEquiv b T j j = 1 := hTd j
      rw [LinearMap.toMatrixAlgEquiv_apply] at h1
      rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, h1, Module.End.one_apply,
        Basis.repr_self, Finsupp.single_eq_same, sub_self]
  exact hle hv

private theorem commute_of_mem_span {S : Set (V →ₗ[K] V)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, Commute x y) {y z : V →ₗ[K] V} (hy : y ∈ span K S)
    (hz : z ∈ span K S) : Commute y z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    induction hz using Submodule.span_induction with
    | mem w hw => exact hS x hx w hw
    | zero => exact Commute.zero_right _
    | add a c _ _ ha hc => exact ha.add_right hc
    | smul r a _ ha => exact ha.smul_right r
  | zero => exact Commute.zero_left _
  | add a c _ _ ha hc => exact ha.add_left hc
  | smul r a _ ha => exact ha.smul_left r

private theorem eq_zero_of_forall_mem_compl {N : Submodule K (V →ₗ[K] V)}
    (hcomm : ∀ y ∈ N, ∀ z ∈ N, Commute y z) {F : ℕ → Submodule K V} {m : ℕ}
    (hF0 : F 0 = ⊥) (hFm : F m = ⊤) (hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i)
    {C : Submodule K V} (hC : IsCompl (mulSpan N ⊤) C) {y : V →ₗ[K] V} (hy : y ∈ N)
    (hyC : ∀ c ∈ C, y c = 0) : y = 0 := by
  have hX : LinearMap.range y ≤ mulSpan N (LinearMap.range y) := by
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ mulSpan N ⊤ ⊔ C := by
      rw [hC.sup_eq_top]
      trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := mem_sup.mp hv
    rw [map_add, hyC c hc, add_zero]
    clear hv
    rw [mulSpan] at hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨z, hz, x, -, rfl⟩ := hu
      have hyz : y (z x) = z (y x) := by
        have := LinearMap.congr_fun (hcomm y hy z hz).eq x
        simpa only [Module.End.mul_apply] using this
      rw [hyz]
      exact subset_span ⟨z, hz, y x, LinearMap.mem_range_self y x, rfl⟩
    | zero => simp
    | add a c _ _ ha hc =>
      rw [map_add]
      exact add_mem ha hc
    | smul r a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ha
  exact LinearMap.range_eq_bot.mp (eq_bot_of_le_mulSpan hF0 hFm hF hX)

private theorem mul_le_sq_div_four (c w : ℕ) : c * w ≤ (c + w) * (c + w) / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h : ((c * w * 4 : ℕ) : ℤ) ≤ ((c + w) * (c + w) : ℕ) := by
    push_cast
    nlinarith [sq_nonneg ((c : ℤ) - (w : ℤ))]
  exact_mod_cast h

theorem card_le_pow_of_mul_self_eq_one [Finite K] [CharP K 2] [FiniteDimensional K V]
    {A : Type*} [Group A] (ρ : Representation K A V) (hρ : Function.Injective ρ)
    (hcomm : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a * a = 1) :
    Nat.card A ≤ Nat.card K ^ (finrank K V * finrank K V / 4) := by
  classical
  have hsq : ∀ a, (ρ a - 1) * (ρ a - 1) = 0 := by
    intro a
    have h : ρ a * ρ a = 1 := by rw [← map_mul, h2, map_one]
    have htwo : (2 : V →ₗ[K] V) = 0 := by
      rw [← map_ofNat (algebraMap K (V →ₗ[K] V)) 2, CharTwo.two_eq_zero, map_zero]
    calc (ρ a - 1) * (ρ a - 1) = ρ a * ρ a - 2 * ρ a + 1 := by noncomm_ring
      _ = 2 * (1 - ρ a) := by rw [h]; noncomm_ring
      _ = 0 := by rw [htwo, zero_mul]
  obtain ⟨m, b, hb⟩ := ρ.exists_basis_isUpperUnitriangular_of_isUnipotent
    (fun a => ⟨2, by rw [pow_two]; exact hsq a⟩)
  set S : Set (V →ₗ[K] V) := Set.range fun a => ρ a - 1 with hS
  set N : Submodule K (V →ₗ[K] V) := span K S with hN
  set F : ℕ → Submodule K V := fun i => span K (b '' {j | (j : ℕ) < i}) with hFdef
  have hF0 : F 0 = ⊥ := by
    simp only [hFdef, Nat.not_lt_zero, Set.setOf_false, Set.image_empty, span_empty]
  have hFm : F m = ⊤ := by
    have : {j : Fin m | (j : ℕ) < m} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    simp only [hFdef, this, Set.image_univ, b.span_eq]
  have hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i := by
    intro y hy i v hv
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact sub_one_mem_flag b (hb a) i hv
    | zero => simp
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    have hρc : Commute (ρ a) (ρ a') := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hcomm]
    exact (hρc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hcommN : ∀ y ∈ N, ∀ z ∈ N, Commute y z := fun y hy z hz =>
    commute_of_mem_span hcommS hy hz
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (mulSpan N ⊤)
  set W := mulSpan N ⊤ with hW
  have hmemW : ∀ y ∈ N, ∀ v : V, y v ∈ W := fun y hy v =>
    subset_span ⟨y, hy, v, trivial, rfl⟩
  let Φ : N →ₗ[K] (C →ₗ[K] W) :=
    { toFun := fun y =>
        { toFun := fun c => ⟨(y : V →ₗ[K] V) c, hmemW y y.2 c⟩
          map_add' := fun c c' => Subtype.ext (map_add (y : V →ₗ[K] V) (c : V) (c' : V))
          map_smul' := fun r c => Subtype.ext (map_smul (y : V →ₗ[K] V) r (c : V)) }
      map_add' := fun y z => LinearMap.ext fun c => Subtype.ext rfl
      map_smul' := fun r y => LinearMap.ext fun c => Subtype.ext rfl }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hyC : ∀ c ∈ C, (y : V →ₗ[K] V) c = 0 := by
      intro c hc
      exact congrArg Subtype.val (LinearMap.congr_fun hy ⟨c, hc⟩)
    exact Subtype.ext (eq_zero_of_forall_mem_compl hcommN hF0 hFm hF hC y.2 hyC)
  haveI : Finite (V →ₗ[K] V) := Module.finite_of_finite K
  have hinjA : Function.Injective fun a : A => (⟨ρ a - 1, subset_span ⟨a, rfl⟩⟩ : N) := by
    intro a a' h
    apply hρ
    have := congrArg Subtype.val h
    simpa using this
  calc Nat.card A ≤ Nat.card N := Nat.card_le_card_of_injective _ hinjA
    _ = Nat.card K ^ finrank K N := Module.natCard_eq_pow_finrank
    _ ≤ Nat.card K ^ (finrank K V * finrank K V / 4) := by
      refine Nat.pow_le_pow_right Nat.card_pos ?_
      have h1 : finrank K N ≤ finrank K (C →ₗ[K] W) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
      rw [Module.finrank_linearMap] at h1
      have h2 : finrank K W + finrank K C = finrank K V :=
        Submodule.finrank_add_eq_of_isCompl hC
      rw [← h2]
      calc finrank K N ≤ finrank K C * finrank K W := h1
        _ = finrank K W * finrank K C := Nat.mul_comm _ _
        _ ≤ _ := mul_le_sq_div_four _ _

theorem card_le_pow_of_isElemAbelian_two [Finite K] [CharP K 2] {n : ℕ}
    {A : Subgroup (GL (Fin n) K)} (hA : CFSG.Open.IsElemAbelian 2 A) :
    Nat.card A ≤ Nat.card K ^ (n * n / 4) := by
  let ρ : Representation K A (Fin n → K) :=
    (MonoidHomClass.toMonoidHom (Matrix.toLinAlgEquiv' (R := K) (n := Fin n))).comp
      ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp A.subtype)
  have hρ : Function.Injective ρ := by
    intro a a' h
    apply Subtype.ext
    apply Units.ext
    exact (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective h
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have h2 : ∀ a : A, a * a = 1 := by
    intro a
    apply Subtype.ext
    have := hA.2 a a.2
    rw [pow_two] at this
    simpa using this
  have := card_le_pow_of_mul_self_eq_one ρ hρ hcomm h2
  rwa [Module.finrank_fin_fun] at this

end CFSG.LinearAlgebra.SchurElemAbelianTwo
