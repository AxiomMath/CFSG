module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCountSU

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  {ζ : F} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution F p f ζ = -ζ)

@[expose] noncomputable def levi : SL(2, fixedSubfield F p f) →* SU (unitaryInvolution F p f) 3 :=
  (embSU (unitaryInvolution F p f)).comp (hypEquiv hζ0 hζ).toMonoidHom

theorem levi_injective : Function.Injective (levi hζ0 hζ) :=
  (embSU_injective _).comp (hypEquiv hζ0 hζ).injective

theorem range_levi : (levi hζ0 hζ).range = (embSU (unitaryInvolution F p f)).range := by
  unfold levi
  have htop : (hypEquiv hζ0 hζ).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (hypEquiv hζ0 hζ).surjective
  rw [MonoidHom.range_comp, htop, Subgroup.map_top]

section Diag

variable (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : ω ^ (p ^ f) = ω)

include hω in
theorem mat3_tSU_of_pow_eq :
    mat3 (tSU hF ω) = Matrix.diagonal ![(ω : F), 1, ((ω⁻¹ : Fˣ) : F)] := by
  have h1 : ω ^ (p ^ f - 1) = 1 := by
    have h := hω
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by have := one_le_prime_pow p f; omega⟩
    rw [hk, pow_succ'] at h
    rw [hk, Nat.add_sub_cancel]
    exact mul_eq_left.1 h
  show tMat (p ^ f) ω = _
  unfold tMat
  rw [h1, hω]
  simp

include hω in
theorem mem_fixedSubfield_unit : (ω : F) ∈ fixedSubfield F p f := by
  rw [mem_fixedSubfield, unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, hω]

include hω in
theorem mem_fixedSubfield_unit_inv : ((ω⁻¹ : Fˣ) : F) ∈ fixedSubfield F p f := by
  rw [mem_fixedSubfield, unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, inv_pow, hω]

include hω in
@[expose] noncomputable def diagSL : SL(2, fixedSubfield F p f) :=
  ⟨Matrix.diagonal ![(⟨(ω : F), mem_fixedSubfield_unit hω⟩ : fixedSubfield F p f),
      ⟨((ω⁻¹ : Fˣ) : F), mem_fixedSubfield_unit_inv hω⟩],
    by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      apply Subtype.ext
      simp⟩

include hω in
theorem coe_diagSL : ((diagSL hω : SL(2, fixedSubfield F p f)) : Matrix (Fin 2) (Fin 2) _) =
    Matrix.diagonal ![(⟨(ω : F), mem_fixedSubfield_unit hω⟩ : fixedSubfield F p f),
      ⟨((ω⁻¹ : Fˣ) : F), mem_fixedSubfield_unit_inv hω⟩] := rfl

include hF hω in
theorem levi_diagSL : levi hζ0 hζ (diagSL hω) = tSU hF ω := by
  apply mat3_injective
  rw [mat3_tSU_of_pow_eq hF hω]
  show embMat (hypMat ζ _) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embMat, hypMat, coe_diagSL]

end Diag

section Psl

@[expose] def pslMk (K : Type) [Field K] : SL(2, K) →* PSL2MatrixGroup K :=
  QuotientGroup.mk' (Subgroup.center SL(2, K))

theorem pslMk_surjective (K : Type) [Field K] : Function.Surjective (pslMk K) :=
  QuotientGroup.mk'_surjective _

theorem pslMk_eq_one_iff {K : Type} [Field K] {x : SL(2, K)} :
    pslMk K x = 1 ↔ x ∈ Subgroup.center SL(2, K) :=
  QuotientGroup.eq_one_iff x

theorem center_mul_self {K : Type} [Field K] {c : SL(2, K)} (hc : c ∈ Subgroup.center SL(2, K)) :
    c * c = 1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin, sq] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrc, ← map_mul, hr, map_one]
  rfl

theorem mem_normalizer_zpowers_of_conj_mem {G : Type*} [Group G] {a x : G}
    (h1 : x * a * x⁻¹ ∈ Subgroup.zpowers a) (h2 : x⁻¹ * a * x ∈ Subgroup.zpowers a) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 n
  · intro hy
    have : x⁻¹ * (x * y * x⁻¹) * x ∈ Subgroup.zpowers a := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← hn]
      have h3 := conj_zpow (a := x⁻¹) (b := a) (i := n)
      rw [inv_inv] at h3
      rw [← h3]
      exact Subgroup.zpow_mem _ h2 n
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem mem_normalizer_of_psl_normalizer {K : Type} [Field K] {d x : SL(2, K)} (hd : d ^ 3 = 1)
    (hx : pslMk K x ∈ Subgroup.normalizer ((Subgroup.zpowers (pslMk K d) : Subgroup _) : Set _)) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup SL(2, K)) : Set SL(2, K)) := by
  have key : ∀ y : SL(2, K), pslMk K y ∈ Subgroup.normalizer
      ((Subgroup.zpowers (pslMk K d) : Subgroup _) : Set _) → y * d * y⁻¹ ∈ Subgroup.zpowers d := by
    intro y hy
    have h1 : pslMk K (y * d * y⁻¹) ∈ Subgroup.zpowers (pslMk K d) := by
      rw [map_mul, map_mul, map_inv]
      exact ((Subgroup.mem_normalizer_iff.1 hy) (pslMk K d)).1 (Subgroup.mem_zpowers _)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hc : (d ^ n)⁻¹ * (y * d * y⁻¹) ∈ Subgroup.center SL(2, K) := by
      rw [← pslMk_eq_one_iff, map_mul, map_inv, map_zpow, hn, inv_mul_cancel]
    set c := (d ^ n)⁻¹ * (y * d * y⁻¹) with hcdef
    have hcc : c * c = 1 := center_mul_self hc
    have hcomm : (d ^ n) * c = c * (d ^ n) := Subgroup.mem_center_iff.1 hc (d ^ n)
    have he : y * d * y⁻¹ = d ^ n * c := by rw [hcdef]; group
    have h3 : (y * d * y⁻¹) ^ 3 = 1 := by
      have : (y * d * y⁻¹) ^ 3 = y * d ^ 3 * y⁻¹ := conj_pow
      rw [this, hd]; group
    have h4 : c ^ 3 = 1 := by
      rw [he, (Commute.mul_pow hcomm 3 : _)] at h3
      have : (d ^ n) ^ 3 = 1 := by
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hd, _root_.one_zpow]
      rwa [this, one_mul] at h3
    have hc1 : c = 1 := by
      calc c = c ^ 3 := by rw [pow_succ, pow_two, hcc, one_mul]
        _ = 1 := h4
    rw [he, hc1, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) n
  refine mem_normalizer_zpowers_of_conj_mem (key x hx) ?_
  have := key x⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hx)
  simpa using this

end Psl

theorem map_mem_normalizer_zpowers {G H : Type*} [Group G] [Group H] (φ : G →* H) {a x : G}
    (hx : x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    φ x ∈ Subgroup.normalizer ((Subgroup.zpowers (φ a) : Subgroup H) : Set H) := by
  have key : ∀ y ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G),
      φ y * φ a * (φ y)⁻¹ ∈ Subgroup.zpowers (φ a) := by
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
      (((Subgroup.mem_normalizer_iff.1 hy) a).1 (Subgroup.mem_zpowers a))
    rw [← map_inv, ← map_mul, ← map_mul, ← hn, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
  refine mem_normalizer_zpowers_of_conj_mem (key x hx) ?_
  have := key x⁻¹ (Subgroup.inv_mem _ hx)
  simpa using this

section Center

variable {K : Type} [Field K]

@[expose] def negOne (K : Type) [Field K] : SL(2, K) :=
  ⟨(-1 : Matrix (Fin 2) (Fin 2) K), by rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num⟩

theorem negOne_mul_self : negOne K * negOne K = 1 := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) K) * (-1) = 1
  simp

theorem negOne_ne_one (h2 : (2 : K) ≠ 0) : negOne K ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
  simp [negOne] at this
  exact h2 (by linear_combination -this)

theorem negOne_mem_center : negOne K ∈ Subgroup.center SL(2, K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  show (g : Matrix (Fin 2) (Fin 2) K) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) K)
  simp

theorem center_eq_zpowers_negOne : Subgroup.center SL(2, K) = Subgroup.zpowers (negOne K) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    rw [Fintype.card_fin, sq] at hr
    rcases mul_self_eq_one_iff.1 hr with h | h
    · have : c = 1 := by
        apply Subtype.ext
        rw [← hrc, h]
        simp
      rw [this]
      exact Subgroup.one_mem _
    · have : c = negOne K := by
        apply Subtype.ext
        rw [← hrc, h]
        show _ = (-1 : Matrix (Fin 2) (Fin 2) K)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact negOne_mem_center

theorem card_center_sl2 (h2 : (2 : K) ≠ 0) : Nat.card (Subgroup.center SL(2, K)) = 2 := by
  rw [center_eq_zpowers_negOne, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two, negOne_mul_self]) (negOne_ne_one h2)

theorem card_eq_two_mul_card_map_pslMk [Finite K] (h2 : (2 : K) ≠ 0) (W : Subgroup SL(2, K))
    (hneg : negOne K ∈ W) : Nat.card W = 2 * Nat.card (W.map (pslMk K)) := by
  set φ : W →* PSL2MatrixGroup K := (pslMk K).comp W.subtype with hφ
  have h := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = W.map (pslMk K) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = (Subgroup.center SL(2, K)).subgroupOf W := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact pslMk_eq_one_iff
  have hle : Subgroup.center SL(2, K) ≤ W := by
    rw [center_eq_zpowers_negOne, Subgroup.zpowers_le]
    exact hneg
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_center_sl2 h2] at h
  exact h.symm

end Center

section Interface

variable (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1)

include hζ0 hζ hF hω hq3

theorem diagSL_pow_three :
    (diagSL (pow_eq_self_of_orderOf_three hω hq3) : SL(2, fixedSubfield F p f)) ^ 3 = 1 := by
  apply levi_injective hζ0 hζ
  rw [map_pow, levi_diagSL hζ0 hζ hF, map_one, ← map_pow]
  have h3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  rw [h3, map_one]

theorem levi_mem_normA0_of_psl_normalizer {x : SL(2, fixedSubfield F p f)}
    (hx : pslMk (fixedSubfield F p f) x ∈ Subgroup.normalizer
      ((Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup _) : Set _)) :
    levi hζ0 hζ x ∈ normA0 hF ω := by
  have h1 := mem_normalizer_of_psl_normalizer (diagSL_pow_three hζ0 hζ hF hω hq3) hx
  have h2 := map_mem_normalizer_zpowers (levi hζ0 hζ) h1
  rwa [levi_diagSL hζ0 hζ hF] at h2

theorem normalizer_psl_le_map_comap :
    Subgroup.normalizer ((Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup _) : Set _) ≤
      ((normA0 hF ω).comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) := by
  intro xb hxb
  obtain ⟨x, rfl⟩ := pslMk_surjective _ xb
  exact ⟨x, levi_mem_normA0_of_psl_normalizer hζ0 hζ hF hω hq3 hxb, rfl⟩

theorem card_zpowers_pslMk_diagSL :
    Nat.card (Subgroup.zpowers (pslMk (fixedSubfield F p f)
      (diagSL (pow_eq_self_of_orderOf_three hω hq3)))) = 3 := by
  set d := (diagSL (pow_eq_self_of_orderOf_three hω hq3) : SL(2, fixedSubfield F p f)) with hd
  have hd3 : d ^ 3 = 1 := diagSL_pow_three hζ0 hζ hF hω hq3
  have hd1 : d ≠ 1 := by
    intro h
    have : tSU hF ω = 1 := by rw [← levi_diagSL hζ0 hζ hF (pow_eq_self_of_orderOf_three hω hq3), ← hd, h,
      map_one]
    have h4 : orderOf (tSU hF ω) = 3 := orderOf_tSU hF hω
    rw [this, orderOf_one] at h4
    omega
  have hπ1 : pslMk (fixedSubfield F p f) d ≠ 1 := by
    intro h
    have hc := pslMk_eq_one_iff.1 h
    have hcc := center_mul_self hc
    apply hd1
    calc d = d ^ 3 * (d * d)⁻¹ := by group
      _ = 1 := by rw [hd3, hcc]; group
  have hπ3 : pslMk (fixedSubfield F p f) d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hπ3 hπ1

omit hζ0 hζ hF hω hq3

end Interface

section Counts

variable (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)

include hF hp2 in
theorem levi_negOne : levi hζ0 hζ (negOne (fixedSubfield F p f)) = zSU hF := by
  apply mat3_injective
  rw [mat3_zSU hF hp2]
  show embMat (hypMat ζ _) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat, hypMat, negOne]

include hp2 in
theorem two_ne_zero_fixedSubfield : (2 : fixedSubfield F p f) ≠ 0 := by
  intro h
  have := congrArg (fun x : fixedSubfield F p f => (x : F)) h
  exact two_ne_zero_of_char_ne_two hp2 (by simpa using this)

include hF hp2 in
theorem card_inf_range_embSU_eq (W : Subgroup (SU (unitaryInvolution F p f) 3))
    (hTW : (tSU hF).range ≤ W) :
    Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) =
      2 * Nat.card ((W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f))) := by
  have h1 : Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) =
      Nat.card (W.comap (levi hζ0 hζ)) := by
    rw [← range_levi hζ0 hζ, inf_comm, ← Subgroup.map_comap_eq,
      Subgroup.card_map_of_injective (levi_injective hζ0 hζ)]
  rw [h1]
  apply card_eq_two_mul_card_map_pslMk (two_ne_zero_fixedSubfield hp2)
  show levi hζ0 hζ (negOne _) ∈ W
  rw [levi_negOne hζ0 hζ hF hp2]
  exact hTW ⟨-1, rfl⟩

include hF hp2 in
theorem card_inf_centralizer_zSU_eq (W : Subgroup (SU (unitaryInvolution F p f) 3))
    (hTW : (tSU hF).range ≤ W) :
    Nat.card (W ⊓ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) :
        Subgroup _) * (p ^ f - 1) =
      2 * Nat.card ((W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f))) *
        ((p ^ f) ^ 2 - 1) := by
  have h := card_inf_centralizer_zSU hF hp2 W hTW
  rw [card_inf_range_embSU_range_tSU hF, card_inf_range_embSU_eq hζ0 hζ hF hp2 W hTW,
    card_range_tSU hF] at h
  exact h

end Counts


end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
