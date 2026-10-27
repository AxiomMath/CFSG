module

public import CFSG.LieType.SeitzGeneration.HyperIrrGroup
public import CFSG.LieType.SeitzGeneration.HyperIrrQuasi

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem stable_of_gens3 {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)}
    {a b c : SpecialLinearGroup (Fin n) F}
    (hE : E ≤ Subgroup.closure ({toPSL a, toPSL b, toPSL c} :
      Set (ProjectiveSpecialLinearGroup (Fin n) F)))
    {W : Submodule F (Fin n → F)} (ha : a ∈ stabSub W) (hb : b ∈ stabSub W)
    (hc : c ∈ stabSub W) :
    ∀ x : SpecialLinearGroup (Fin n) F, toPSL x ∈ E →
      ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
  intro x hx
  have hcl : Subgroup.closure ({a, b, c} : Set (SpecialLinearGroup (Fin n) F)) ≤ stabSub W :=
    (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl | rfl) <;> assumption)
  have hmap : (Subgroup.closure ({a, b, c} : Set (SpecialLinearGroup (Fin n) F))).map toPSL =
      Subgroup.closure {toPSL a, toPSL b, toPSL c} := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  obtain ⟨m, hm, hmx⟩ : toPSL x ∈ (Subgroup.closure
      ({a, b, c} : Set (SpecialLinearGroup (Fin n) F))).map toPSL := hmap ▸ hE hx
  have hz : m⁻¹ * x ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
    rw [mem_center_iff_toPSL_eq_one, map_mul, map_inv, hmx, inv_mul_cancel]
  have : x = m * (m⁻¹ * x) := by group
  rw [this]
  exact (stabSub W).mul_mem (hcl hm) (center_le_stabSub W hz)

theorem exists_radical_triple {p : ℕ} (hp : p.Prime) (hn : 0 < n)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) {x y : SpecialLinearGroup (Fin n) F} (hx : toPSL x ∈ E)
    (hy : toPSL y ∈ E) (hxy : x * y ≠ y * x) :
    ∃ (ζ : F) (r : SpecialLinearGroup (Fin n) F), IsPrimitiveRoot ζ p ∧
      (x : Matrix (Fin n) (Fin n) F) * y = ζ • ((y : Matrix (Fin n) (Fin n) F) * x) ∧
      toPSL r ∈ E ∧ toPSL r ≠ 1 ∧
      E ≤ Subgroup.closure ({toPSL x, toPSL y, toPSL r} :
        Set (ProjectiveSpecialLinearGroup (Fin n) F)) ∧
      (x : Matrix (Fin n) (Fin n) F) * r = r * x ∧
      (y : Matrix (Fin n) (Fin n) F) * r = r * y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hπ : Function.Surjective (toPSL (n := n) (F := F)) := QuotientGroup.mk'_surjective _
  have hcen : ∀ a b : SpecialLinearGroup (Fin n) F, toPSL a ∈ E → toPSL b ∈ E →
      ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := fun a b ha hb => by
    rw [mem_center_iff_toPSL_eq_one, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ ha _ hb)
  have hpowc : ∀ a : SpecialLinearGroup (Fin n) F, toPSL a ∈ E →
      a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := fun a ha => by
    rw [mem_center_iff_toPSL_eq_one, map_pow]; exact hexp _ ha
  obtain ⟨ζ, hζ0, hζ⟩ := exists_scalar_comm hn (hcen x y hx hy)
  obtain ⟨cx, hcx0, hcx⟩ := exists_scalar_of_mem_center hn (hpowc x hx)
  obtain ⟨cy, hcy0, hcy⟩ := exists_scalar_of_mem_center hn (hpowc y hy)
  rw [Matrix.SpecialLinearGroup.coe_pow] at hcx hcy
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hxy
    apply Subtype.ext
    simpa using hζ
  have hζp : ζ ^ p = 1 := quasi_scalar_pow_eq_one hζ hcy hcy0 (coe_ne_zero hn x)
  have hprim : IsPrimitiveRoot ζ p := isPrimitiveRoot_of_pow_eq_one_ne_one hp hζp hζ1
  have hx1 : toPSL x ≠ 1 := fun h => hxy (by
    have hz := mem_center_iff_toPSL_eq_one.2 h
    exact (Subgroup.mem_center_iff.1 hz y).symm)
  have hy1 : toPSL y ∉ Subgroup.zpowers (toPSL x) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hz : (x ^ k)⁻¹ * y ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rw [mem_center_iff_toPSL_eq_one, map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    apply hxy
    have e1 : y = x ^ k * ((x ^ k)⁻¹ * y) := by group
    rw [e1]
    calc x * (x ^ k * ((x ^ k)⁻¹ * y)) = (x * x ^ k) * ((x ^ k)⁻¹ * y) := (mul_assoc _ _ _).symm
      _ = (x ^ k * x) * ((x ^ k)⁻¹ * y) := by rw [(Commute.self_zpow x k).eq]
      _ = x ^ k * (x * ((x ^ k)⁻¹ * y)) := mul_assoc _ _ _
      _ = x ^ k * (((x ^ k)⁻¹ * y) * x) := by rw [Subgroup.mem_center_iff.1 hz x]
      _ = x ^ k * ((x ^ k)⁻¹ * y) * x := (mul_assoc _ _ _).symm
  have hcl := closure_pair_le hx hy
  have hc2 : Commute (toPSL x) (toPSL y) := hcomm _ hx _ hy
  obtain ⟨e₀, he₀E, he₀⟩ : ∃ e₀ ∈ E, e₀ ∉ Subgroup.closure
      ({toPSL x, toPSL y} : Set (ProjectiveSpecialLinearGroup (Fin n) F)) := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.closure ({toPSL x, toPSL y} :
        Set (ProjectiveSpecialLinearGroup (Fin n) F)) := fun e he => hcon e he
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_closure_pair_le hp.pos hc2 (hexp _ hx) (hexp _ hy)
    rw [hcard] at h1
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨r₀, hr₀⟩ := hπ e₀
  have hr₀E : toPSL r₀ ∈ E := hr₀ ▸ he₀E
  obtain ⟨α, hα0, hα⟩ := exists_scalar_comm hn (hcen r₀ x hr₀E hx)
  obtain ⟨β, hβ0, hβ⟩ := exists_scalar_comm hn (hcen r₀ y hr₀E hy)
  have hαp : α ^ p = 1 := quasi_scalar_pow_eq_one hα hcx hcx0 (coe_ne_zero hn r₀)
  have hβp : β ^ p = 1 := quasi_scalar_pow_eq_one hβ hcy hcy0 (coe_ne_zero hn r₀)
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, j, h1, h2⟩ := exists_adjust hprim hζ hα hβ hαp hβp hα0 hβ0
  have hrmat : ((r₀ * x ^ i * y ^ j : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (r₀ : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) ^ i *
        (y : Matrix (Fin n) (Fin n) F) ^ j := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
  have hrE : toPSL (r₀ * x ^ i * y ^ j) ∈ E := by
    rw [map_mul, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.mul_mem hr₀E (E.pow_mem hx i)) (E.pow_mem hy j)
  have hrcl : toPSL (r₀ * x ^ i * y ^ j) ∉ Subgroup.closure
      ({toPSL x, toPSL y} : Set (ProjectiveSpecialLinearGroup (Fin n) F)) := by
    intro h
    apply he₀
    have e2 : e₀ = toPSL (r₀ * x ^ i * y ^ j) * ((toPSL y) ^ j)⁻¹ * ((toPSL x) ^ i)⁻¹ := by
      rw [map_mul, map_mul, map_pow, map_pow, hr₀]; group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_closure_pair_right _ _) _)))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_closure_pair_left _ _) _))
  refine ⟨ζ, r₀ * x ^ i * y ^ j, hprim, hζ, hrE, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hrcl (h ▸ Subgroup.one_mem _)
  · exact le_closure_triple_of_independent hp hcard hx hy hrE (hexp _ hx) hx1 hy1 hrcl
  · rw [hrmat]; exact h1.symm
  · rw [hrmat]; exact h2.symm

theorem not_exists_pow_eq_of_irreducible {p : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)}
    {x y r : SpecialLinearGroup (Fin n) F}
    (hgen : E ≤ Subgroup.closure ({toPSL x, toPSL y, toPSL r} :
      Set (ProjectiveSpecialLinearGroup (Fin n) F)))
    (hxr : (x : Matrix (Fin n) (Fin n) F) * r = r * x)
    (hyr : (y : Matrix (Fin n) (Fin n) F) * r = r * y) (hr1 : toPSL r ≠ 1)
    (hirr : ∀ W : Submodule F (Fin n → F),
      (∀ z : SpecialLinearGroup (Fin n) F, toPSL z ∈ E →
        ∀ w ∈ W, (z : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : F} (hc : (r : Matrix (Fin n) (Fin n) F) ^ p = c • (1 : Matrix (Fin n) (Fin n) F)) :
    ∀ b : F, b ^ p ≠ c := by
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hc0 : c = 0 := by rw [← hb, zero_pow hp.ne_zero]
    rw [hc0, zero_smul] at hc
    have h1 := congrArg Matrix.det hc
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Matrix.det_pow, r.2, one_pow, Matrix.det_zero] at h1
    exact one_ne_zero h1
  set M₀ : Matrix (Fin n) (Fin n) F := b⁻¹ • (r : Matrix (Fin n) (Fin n) F) with hM₀
  have hM : M₀ ^ p = 1 := by
    rw [hM₀, smul_pow, hc, smul_smul, ← hb, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hb0),
      one_smul]
  obtain ⟨ξ, v, -, hv0, hMv⟩ := exists_eigenvector_of_pow_eq_one hp.pos hζ hn hM
  let W : Submodule F (Fin n → F) :=
    LinearMap.ker (Matrix.toLin' (M₀ - ξ • (1 : Matrix (Fin n) (Fin n) F)))
  have hW : ∀ w, w ∈ W ↔ M₀.mulVec w = ξ • w := fun w => by
    simp [W, LinearMap.mem_ker, Matrix.toLin'_apply, sub_eq_zero]
  have hstab : ∀ z : SpecialLinearGroup (Fin n) F,
      M₀ * (z : Matrix (Fin n) (Fin n) F) = (z : Matrix (Fin n) (Fin n) F) * M₀ →
      z ∈ stabSub W := fun z hMz w hw => by
    rw [hW] at hw ⊢
    rw [Matrix.mulVec_mulVec, hMz, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have hxW : x ∈ stabSub W := hstab x (by
    rw [hM₀, Matrix.smul_mul, Matrix.mul_smul, hxr])
  have hyW : y ∈ stabSub W := hstab y (by
    rw [hM₀, Matrix.smul_mul, Matrix.mul_smul, hyr])
  have hrW : r ∈ stabSub W := hstab r (by
    rw [hM₀, Matrix.smul_mul, Matrix.mul_smul])
  rcases hirr W (stable_of_gens3 hgen hxW hyW hrW) with h | h
  · have hvW : v ∈ W := (hW v).2 hMv
    rw [h] at hvW
    exact hv0 (by simpa using hvW)
  · have hall : ∀ w, M₀.mulVec w = ξ • w := fun w => (hW w).1 (h ▸ Submodule.mem_top)
    have hescal : M₀ = ξ • (1 : Matrix (Fin n) (Fin n) F) := by
      rw [Matrix.ext_iff_mulVec]
      intro w
      rw [hall w, Matrix.smul_mulVec, Matrix.one_mulVec]
    apply hr1
    apply mem_center_iff_toPSL_eq_one.1
    refine mem_center_of_scalar (μ := b * ξ) ?_
    rw [mul_smul, ← hescal, hM₀, smul_smul, mul_inv_cancel₀ hb0, one_smul]

end CFSG.LieType.SeitzGeneration
