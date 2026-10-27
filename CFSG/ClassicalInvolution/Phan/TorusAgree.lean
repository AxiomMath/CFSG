module

public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary

section Matrix

variable {F : Type*} [Field F] {σ : F ≃+* F}

theorem eq_zero_of_eq_mul_self_of_ne_one {a u : F} (hu : u ≠ 1) (h : a = u * a) : a = 0 := by
  by_contra ha
  exact hu (mul_right_cancel₀ ha (by rw [one_mul]; exact h.symm))

theorem exists_normOne_of_offDiag {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1)
    (hu : conjTr σ M * M = 1) (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) :
    ∃ u : normOne σ, M = Matrix.diagonal fun i => (![(u : Fˣ), (u : Fˣ)⁻¹] i : F) := by
  rw [Matrix.det_fin_two, h01, h10] at hdet
  have hab : M 0 0 * M 1 1 = 1 := by simpa using hdet
  have hu00 : σ (M 0 0) * M 0 0 = 1 := by
    have := congrFun (congrFun hu 0) 0
    simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_two, h10] using this
  let u : Fˣ := Units.mk (M 0 0) (M 1 1) hab (by rw [mul_comm]; exact hab)
  have hu' : u ∈ normOne σ := by rw [mem_normOne]; simpa [u] using hu00
  refine ⟨⟨u, hu'⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u, h01, h10]

theorem mem_range_torusTwo_of_offDiag (A : SUid σ 2)
    (h01 : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (h10 : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    A ∈ (torusTwo σ).range := by
  obtain ⟨u, hu⟩ := exists_normOne_of_offDiag A.2.1 A.2.2 h01 h10
  exact ⟨u, Subtype.ext (Units.ext (by rw [coe_torusTwo]; exact hu.symm))⟩

theorem embSUid_two_torus_comm (s t : normOne σ) :
    embSUid σ 2 (torusTwo σ s) * embSUid σ 0 (torusTwo σ t) =
      embSUid σ 0 (torusTwo σ t) * embSUid σ 2 (torusTwo σ s) := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem embSUid_zero_torus_mul_embSUid_two (hσ : ∀ c, σ (σ c) = c) (v : normOne σ)
    (A : SUid σ 2) :
    ∃ B : SUid σ 2,
      embSUid σ 0 (torusTwo σ v) * embSUid σ 2 A = embSUid σ 2 B * embSUid σ 0 (torusTwo σ v) := by
  set D : GL (Fin 2) F := diagGL ![1, (v : Fˣ)]
  have hv := v.2
  rw [mem_normOne] at hv
  have hv0 : ((v : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hD : conjTr σ (D : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp
    · simpa using hv
  refine ⟨⟨D * A * D⁻¹, conj_mem_SUid hσ hD A.2⟩, Subtype.ext (Units.ext ?_)⟩
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo, D, coe_diagGL,
    coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem embSUid_two_torus_mul_embSUid_zero (hσ : ∀ c, σ (σ c) = c) (v : normOne σ)
    (A : SUid σ 2) :
    ∃ B : SUid σ 2,
      embSUid σ 2 (torusTwo σ v) * embSUid σ 0 A = embSUid σ 0 B * embSUid σ 2 (torusTwo σ v) := by
  set D : GL (Fin 2) F := diagGL ![1, (v : Fˣ)]
  have hv := v.2
  rw [mem_normOne] at hv
  have hv0 : ((v : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hD : conjTr σ (D : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp
    · simpa using hv
  refine ⟨⟨D * A * D⁻¹, conj_mem_SUid hσ hD A.2⟩, Subtype.ext (Units.ext ?_)⟩
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo, D, coe_diagGL,
    coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> field_simp

theorem mem_range_torusTwo_of_commute_two {s : normOne σ} (hs : (s : Fˣ) ≠ 1) {A : SUid σ 2}
    (h : embSUid σ 0 A * embSUid σ 2 (torusTwo σ s) = embSUid σ 2 (torusTwo σ s) * embSUid σ 0 A) :
    A ∈ (torusTwo σ).range := by
  have h' := congrArg (fun g : SUid σ 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo] at h'
  have h12 := congrFun (congrFun h' 1) 2
  have h21 := congrFun (congrFun h' 2) 1
  simp [embPair, Matrix.mul_apply, Fin.sum_univ_three] at h12 h21
  have hs' : ((s : Fˣ) : F)⁻¹ ≠ 1 := fun h1 => hs (Units.ext (inv_eq_one.mp h1))
  exact mem_range_torusTwo_of_offDiag A (eq_zero_of_eq_mul_self_of_ne_one hs' h12)
    (eq_zero_of_eq_mul_self_of_ne_one hs' (by linear_combination -h21))

theorem mem_range_torusTwo_of_commute_zero {s : normOne σ} (hs : (s : Fˣ) ≠ 1) {A : SUid σ 2}
    (h : embSUid σ 2 A * embSUid σ 0 (torusTwo σ s) = embSUid σ 0 (torusTwo σ s) * embSUid σ 2 A) :
    A ∈ (torusTwo σ).range := by
  have h' := congrArg (fun g : SUid σ 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  simp [embPair, Matrix.mul_apply, Fin.sum_univ_three] at h01 h10
  have hs' : ((s : Fˣ) : F) ≠ 1 := fun h1 => hs (Units.ext h1)
  exact mem_range_torusTwo_of_offDiag A
    (eq_zero_of_eq_mul_self_of_ne_one hs' (by linear_combination -h01))
    (eq_zero_of_eq_mul_self_of_ne_one hs' h10)

end Matrix

section Abstract

variable {X : Type*} [Group X]

theorem le_of_centralizer_of_card_lt {M T T' A C : Subgroup X} [Finite T] (hTM : T ≤ M)
    (hAT : ∀ a ∈ A, ∀ t ∈ T, a * t = t * a) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hCM : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hT : ∀ m ∈ M, (∀ a ∈ A, a * m = m * a) → m ∈ T)
    (hcard : Nat.card (MulAut T) < Nat.card C)
    (hT' : ∀ d ∈ C, d ≠ 1 → ∀ m ∈ M, d * m = m * d → m ∈ T') : T ≤ T' := by
  have key : ∀ c ∈ C, ∀ t ∈ T, c * t * c⁻¹ ∈ T := by
    intro c hc t ht
    refine hT _ (hCM c hc t (hTM ht)) fun a ha => ?_
    have h1 : a * c = c * a := hAC a ha c hc
    have h2 : a * t = t * a := hAT a ha t ht
    have h3 : a * c⁻¹ = c⁻¹ * a := (Commute.inv_right h1).eq
    calc a * (c * t * c⁻¹) = (a * c) * t * c⁻¹ := by group
      _ = c * (a * t) * c⁻¹ := by rw [h1]; group
      _ = c * (t * a) * c⁻¹ := by rw [h2]
      _ = c * t * (a * c⁻¹) := by group
      _ = c * t * (c⁻¹ * a) := by rw [h3]
      _ = c * t * c⁻¹ * a := by group
  have hnorm : C ≤ Subgroup.normalizer (T : Set X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => key c hc t ht, fun ht => ?_⟩
    have := key c⁻¹ (C.inv_mem hc) _ ht
    simpa [mul_assoc] using this
  let φ : C →* MulAut T := T.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hφ : ¬ Function.Injective φ := fun hinj =>
    absurd (Nat.card_le_card_of_injective _ hinj) (not_le.mpr hcard)
  rw [injective_iff_map_eq_one] at hφ
  obtain ⟨x, hx⟩ := not_forall.mp hφ
  obtain ⟨hx1, hx⟩ := not_imp.mp hx
  have hxker : Subgroup.inclusion hnorm x ∈ T.normalizerMonoidHom.ker := hx1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at hxker
  intro t ht
  refine hT' (x : X) x.2 (fun h => hx (Subtype.ext h)) t (hTM ht) ?_
  exact (hxker t ht).symm

end Abstract

section Torus

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def diagTorus2 : Subgroup (Su K p f 2) :=
  (torusTwo (unitaryInvolution K p f)).range

@[expose] noncomputable def D12 : Subgroup (Su K p f 3) :=
  (diagTorus2 K p f).map (embSUid (unitaryInvolution K p f) 2)

@[expose] noncomputable def D23 : Subgroup (Su K p f 3) :=
  (diagTorus2 K p f).map (embSUid (unitaryInvolution K p f) 0)

variable {K p f}

theorem mem_diagTorus2_iff {A : Su K p f 2} :
    A ∈ diagTorus2 K p f ↔ ∃ u : normOne (unitaryInvolution K p f),
      torusTwo (unitaryInvolution K p f) u = A :=
  MonoidHom.mem_range

theorem mem_D12_iff {g : Su K p f 3} :
    g ∈ D12 K p f ↔ ∃ u : normOne (unitaryInvolution K p f),
      embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) u) = g := by
  simp only [D12, diagTorus2, Subgroup.mem_map, MonoidHom.mem_range]
  exact ⟨fun ⟨_, ⟨u, rfl⟩, h⟩ => ⟨u, h⟩, fun ⟨u, h⟩ => ⟨_, ⟨u, rfl⟩, h⟩⟩

theorem mem_D23_iff {g : Su K p f 3} :
    g ∈ D23 K p f ↔ ∃ u : normOne (unitaryInvolution K p f),
      embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) u) = g := by
  simp only [D23, diagTorus2, Subgroup.mem_map, MonoidHom.mem_range]
  exact ⟨fun ⟨_, ⟨u, rfl⟩, h⟩ => ⟨u, h⟩, fun ⟨u, h⟩ => ⟨_, ⟨u, rfl⟩, h⟩⟩

theorem D12_le_B12 : D12 K p f ≤ B12 K p f :=
  Subgroup.map_le_range _ _

theorem D23_le_B23 : D23 K p f ≤ B23 K p f :=
  Subgroup.map_le_range _ _

theorem map_D12 {X : Type*} [Group X] (θ : Su K p f 3 →* X) :
    (D12 K p f).map θ = (diagTorus2 K p f).map (θ.comp (embSUid (unitaryInvolution K p f) 2)) :=
  Subgroup.map_map _ _ _

theorem map_D23 {X : Type*} [Group X] (θ : Su K p f 3 →* X) :
    (D23 K p f).map θ = (diagTorus2 K p f).map (θ.comp (embSUid (unitaryInvolution K p f) 0)) :=
  Subgroup.map_map _ _ _

theorem D12_D23_comm {a t : Su K p f 3} (ha : a ∈ D12 K p f) (ht : t ∈ D23 K p f) :
    a * t = t * a := by
  obtain ⟨u, rfl⟩ := mem_D12_iff.mp ha
  obtain ⟨v, rfl⟩ := mem_D23_iff.mp ht
  exact embSUid_two_torus_comm u v

theorem D23_conj_mem_B12 (hK : Nat.card K = (p ^ f) ^ 2) {c m : Su K p f 3}
    (hc : c ∈ D23 K p f) (hm : m ∈ B12 K p f) : c * m * c⁻¹ ∈ B12 K p f := by
  obtain ⟨v, rfl⟩ := mem_D23_iff.mp hc
  obtain ⟨A, rfl⟩ := hm
  obtain ⟨B, hB⟩ := embSUid_zero_torus_mul_embSUid_two (unitaryInvolution_involutive hK) v A
  exact ⟨B, eq_mul_inv_iff_mul_eq.mpr hB.symm⟩

theorem D12_conj_mem_B23 (hK : Nat.card K = (p ^ f) ^ 2) {c m : Su K p f 3}
    (hc : c ∈ D12 K p f) (hm : m ∈ B23 K p f) : c * m * c⁻¹ ∈ B23 K p f := by
  obtain ⟨v, rfl⟩ := mem_D12_iff.mp hc
  obtain ⟨A, rfl⟩ := hm
  obtain ⟨B, hB⟩ := embSUid_two_torus_mul_embSUid_zero (unitaryInvolution_involutive hK) v A
  exact ⟨B, eq_mul_inv_iff_mul_eq.mpr hB.symm⟩

end Torus

section Centralizer

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem commute_of_map_commute (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (c : Fin 3) {x d : Su K p f 3}
    (hx : x ∈ (embSUid (unitaryInvolution K p f) c).range)
    (hd : d * x * d⁻¹ ∈ (embSUid (unitaryInvolution K p f) c).range)
    (h : θ x * θ d = θ d * θ x) : x * d = d * x := by
  obtain ⟨B, hB⟩ : x * d * x⁻¹ * d⁻¹ ∈ (embSUid (unitaryInvolution K p f) c).range := by
    have : x * d * x⁻¹ * d⁻¹ = x * (d * x * d⁻¹)⁻¹ := by group
    rw [this]
    exact mul_mem hx (inv_mem hd)
  have hz : x * d * x⁻¹ * d⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hB1 : B = 1 := eq_one_of_embSUid_mem_center hK c (hB ▸ hker hz)
  have hz1 : x * d * x⁻¹ * d⁻¹ = 1 := by rw [← hB, hB1, map_one]
  calc x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
    _ = d * x := by rw [hz1, one_mul]

theorem mem_diagTorus2_of_map_commute_two (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {s : normOne (unitaryInvolution K p f)}
    (hs : (s : Kˣ) ≠ 1) {A : Su K p f 2}
    (h : θ (embSUid (unitaryInvolution K p f) 0 A) *
        θ (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) s)) =
      θ (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) s)) *
        θ (embSUid (unitaryInvolution K p f) 0 A)) :
    A ∈ diagTorus2 K p f := by
  obtain ⟨B, hB⟩ := embSUid_two_torus_mul_embSUid_zero (unitaryInvolution_involutive hK) s A
  have hd : embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) s) *
      embSUid (unitaryInvolution K p f) 0 A *
      (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) s))⁻¹ ∈
        (embSUid (unitaryInvolution K p f) 0).range :=
    ⟨B, eq_mul_inv_iff_mul_eq.mpr hB.symm⟩
  exact mem_range_torusTwo_of_commute_two hs
    (commute_of_map_commute hK hker 0 ⟨A, rfl⟩ hd h)

theorem mem_diagTorus2_of_map_commute_zero (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {s : normOne (unitaryInvolution K p f)}
    (hs : (s : Kˣ) ≠ 1) {A : Su K p f 2}
    (h : θ (embSUid (unitaryInvolution K p f) 2 A) *
        θ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) s)) =
      θ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) s)) *
        θ (embSUid (unitaryInvolution K p f) 2 A)) :
    A ∈ diagTorus2 K p f := by
  obtain ⟨B, hB⟩ := embSUid_zero_torus_mul_embSUid_two (unitaryInvolution_involutive hK) s A
  have hd : embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) s) *
      embSUid (unitaryInvolution K p f) 2 A *
      (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) s))⁻¹ ∈
        (embSUid (unitaryInvolution K p f) 2).range :=
    ⟨B, eq_mul_inv_iff_mul_eq.mpr hB.symm⟩
  exact mem_range_torusTwo_of_commute_zero hs
    (commute_of_map_commute hK hker 2 ⟨A, rfl⟩ hd h)

end Centralizer

section Agree

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem exists_normOne_ne_one (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ s : normOne (unitaryInvolution K p f), (s : Kˣ) ≠ 1 := by
  obtain ⟨ω, hω, hω1⟩ := (isUnitaryInvolution_unitaryInvolution hK).exists_norm_one_ne_one
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  refine ⟨⟨Units.mk0 ω hω0, ?_⟩, fun h => hω1 ?_⟩
  · rw [mem_normOne]
    simpa using hω
  · simpa using congrArg Units.val h

theorem isCyclic_diagTorus2 : IsCyclic (diagTorus2 K p f) :=
  isCyclic_of_surjective (torusTwo (unitaryInvolution K p f)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem one_lt_card_diagTorus2 (hK : Nat.card K = (p ^ f) ^ 2) :
    1 < Nat.card (diagTorus2 K p f) := by
  obtain ⟨s, hs⟩ := exists_normOne_ne_one hK
  rw [Finite.one_lt_card_iff_nontrivial]
  refine ⟨⟨⟨_, s, rfl⟩, 1, fun h => hs ?_⟩⟩
  have h1 : torusTwo (unitaryInvolution K p f) s = torusTwo (unitaryInvolution K p f) 1 := by
    rw [map_one]
    exact congrArg Subtype.val h
  exact congrArg Subtype.val (torusTwo_injective _ h1)

theorem finite_map_subgroup {G N : Type*} [Group G] [Group N] (H : Subgroup G) (g : G →* N)
    [Finite H] : Finite (H.map g) :=
  inferInstanceAs (Finite ↥(g '' (H : Set G)))

theorem card_mulAut_lt (G : Type*) [Group G] [Finite G] [IsCyclic G] (h : 1 < Nat.card G) :
    Nat.card (MulAut G) < Nat.card G := by
  rw [IsCyclic.card_mulAut]
  exact Nat.totient_lt _ h

theorem torus_agree (hK : Nat.card K = (p ^ f) ^ 2) {θ₁ θ₂ : Su K p f 3 →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (Su K p f 3)) (h₂ : θ₂.ker ≤ Subgroup.center (Su K p f 3))
    (hM : (B23 K p f).map θ₁ = (B12 K p f).map θ₂)
    (hcomm : ∀ x ∈ (B12 K p f).map θ₁, ∀ y ∈ (B23 K p f).map θ₂, x * y = y * x) :
    (D23 K p f).map θ₁ = (D12 K p f).map θ₂ := by
  obtain ⟨s₀, hs₀⟩ := exists_normOne_ne_one hK
  have : Finite ((D23 K p f).map θ₁) := finite_map_subgroup _ _
  have : Finite ((D12 K p f).map θ₂) := finite_map_subgroup _ _
  have hcyc : IsCyclic ((D23 K p f).map θ₁) := by
    rw [map_D23]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _
      (comp_embSUid_injective hK h₁ 0))).1 isCyclic_diagTorus2
  have hcard₁ : Nat.card ((D23 K p f).map θ₁) = Nat.card (diagTorus2 K p f) := by
    rw [map_D23]
    exact Subgroup.card_map_of_injective (comp_embSUid_injective hK h₁ 0)
  have hcard₂ : Nat.card ((D23 K p f).map θ₂) = Nat.card (diagTorus2 K p f) := by
    rw [map_D23]
    exact Subgroup.card_map_of_injective (comp_embSUid_injective hK h₂ 0)
  have hcard₃ : Nat.card ((D12 K p f).map θ₂) = Nat.card (diagTorus2 K p f) := by
    rw [map_D12]
    exact Subgroup.card_map_of_injective (comp_embSUid_injective hK h₂ 2)
  have hle : (D23 K p f).map θ₁ ≤ (D12 K p f).map θ₂ := by
    refine le_of_centralizer_of_card_lt (M := (B12 K p f).map θ₂)
      (A := (D12 K p f).map θ₁) (C := (D23 K p f).map θ₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (Subgroup.map_mono D23_le_B23).trans hM.le
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul, D12_D23_comm ha ht]
    · intro a ha c hc
      exact hcomm a (Subgroup.map_mono D12_le_B12 ha) c (Subgroup.map_mono D23_le_B23 hc)
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨m, hm, rfl⟩
      exact ⟨c * m * c⁻¹, D23_conj_mem_B12 hK hc hm, by simp⟩
    · intro m hm hcentral
      rw [← hM] at hm
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hm
      have hA := mem_diagTorus2_of_map_commute_two hK h₁ hs₀ (A := A)
        (hcentral _ ⟨_, mem_D12_iff.mpr ⟨s₀, rfl⟩, rfl⟩).symm
      exact ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · rw [hcard₂]
      calc Nat.card (MulAut ((D23 K p f).map θ₁)) < Nat.card ((D23 K p f).map θ₁) :=
            card_mulAut_lt _ (by rw [hcard₁]; exact one_lt_card_diagTorus2 hK)
        _ = Nat.card (diagTorus2 K p f) := hcard₁
    · rintro _ ⟨d, hd, rfl⟩ hd1 _ ⟨m, ⟨A, rfl⟩, rfl⟩ hdm
      obtain ⟨t, rfl⟩ := mem_D23_iff.mp hd
      have ht : (t : Kˣ) ≠ 1 := fun h => by
        have ht1 : t = 1 := Subtype.ext h
        exact hd1 (by rw [ht1, map_one, map_one, map_one])
      have hA := mem_diagTorus2_of_map_commute_zero hK h₂ ht (A := A) hdm.symm
      exact ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₃, hcard₁])

end Agree

end CFSG.ClassicalInvolution.Phan
