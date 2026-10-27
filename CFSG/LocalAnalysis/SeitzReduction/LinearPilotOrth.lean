module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthSL2
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImages

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  normalizer_le_normalizer_centralizerPerfectCore)
open scoped MatrixGroups

section Generic

variable {A B : Type*} [Group A] [Group B]

theorem commutator_range_eq_self_of_isPerfect [Group.IsPerfect A] (f : A →* B) :
    ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem eq_bot_or_eq_top_of_normal_range [IsSimpleGroup A] (f : A →* B) (N : Subgroup f.range)
    (hN : N.Normal) : N = ⊥ ∨ N = ⊤ := by
  have : (N.comap f.rangeRestrict).Normal := hN.comap _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap f.rangeRestrict) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := f.rangeRestrict_surjective x
    have hy : y ∈ N.comap f.rangeRestrict := hx
    rw [h, mem_bot] at hy
    rw [hy, map_one]
    exact one_mem _
  · right
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := f.rangeRestrict_surjective x
    have hy : y ∈ N.comap f.rangeRestrict := h ▸ mem_top y
    exact hy

end Generic

section Quadratic

variable {K F : Type*} [Field K] [Field F]

theorem apply_apply_of_mul_self_eq_one {σ : F ≃+* F} (hσσ : σ * σ = 1) (x : F) : σ (σ x) = x := by
  have h := DFunLike.congr_fun hσσ x
  exact h

theorem exists_trace_one_of_involution [CharP F 2] {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) : ∃ ω : F, σ ω = ω + 1 := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hs0 : x + σ x ≠ 0 := fun h => hx (by linear_combination h - x * h2)
  have hσs : σ (x + σ x) = x + σ x := by
    rw [map_add, apply_apply_of_mul_self_eq_one hσσ, add_comm]
  refine ⟨x / (x + σ x), ?_⟩
  rw [map_div₀, hσs]
  field_simp
  linear_combination -x * h2

theorem exists_eq_add_mul_of_trace_one [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ω : F} (hω : σ ω = ω + 1)
    (x : F) : ∃ k l : K, x = ι k + ι l * ω := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hσs : σ (x + σ x) = x + σ x := by
    rw [map_add, apply_apply_of_mul_self_eq_one hσσ, add_comm]
  obtain ⟨l, hl⟩ := (hfix _).1 hσs
  have hσy : σ (x + (x + σ x) * ω) = x + (x + σ x) * ω := by
    rw [map_add, map_mul, hσs, hω]
    linear_combination σ x * h2
  obtain ⟨k, hk⟩ := (hfix _).1 hσy
  refine ⟨k, l, ?_⟩
  rw [hk, hl]
  linear_combination (-(x + σ x) * ω) * h2

theorem natCard_eq_sq_of_trace_one [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ω : F} (hω : σ ω = ω + 1) :
    Nat.card F = Nat.card K ^ 2 := by
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have hω' : ω ∉ ι.range := notMem_range_of_trace_one ι hσι hω
  set φ : K × K → F := fun p => ι p.1 + ι p.2 * ω with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨k, l⟩ ⟨k', l'⟩ h
    simp only [hφ] at h
    by_cases hl : l = l'
    · subst hl
      rw [add_left_inj] at h
      rw [ι.injective h]
    · exfalso
      apply hω'
      have hne : ι (l - l') ≠ 0 := by
        rw [map_sub]
        exact sub_ne_zero.2 (fun h' => hl (ι.injective h'))
      refine ⟨(k' - k) / (l - l'), ?_⟩
      rw [map_div₀, div_eq_iff hne, map_sub, map_sub]
      linear_combination -h
  have hsurj : Function.Surjective φ := fun x => by
    obtain ⟨k, l, hkl⟩ := exists_eq_add_mul_of_trace_one ι hσσ hfix hω x
    exact ⟨(k, l), hkl.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_prod, sq]

theorem natCard_eq_sq_of_involution [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nat.card F = Nat.card K ^ 2 := by
  obtain ⟨ω, hω⟩ := exists_trace_one_of_involution hσ1 hσσ
  exact natCard_eq_sq_of_trace_one ι hσσ hfix hω

end Quadratic

section SL2

variable {R : Type*} [Field R]

theorem upperUnit_eq_one_iff {c : R} : upperUnit c = 1 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun g : SL(2, R) => (g : Matrix (Fin 2) (Fin 2) R) 0 1) h
    simpa [coe_upperUnit] using this
  · rintro rfl
    exact upperUnit_zero

theorem eq_top_of_upperUnit_one_mem_of_conj_mem [Finite R] [CharP R 2] {H : Subgroup SL(2, R)}
    (hu : upperUnit 1 ∈ H) (hw : weylUnit ∈ H)
    (hh : ∀ (α : Rˣ), ∀ x ∈ H, diagUnit α * x * (diagUnit α)⁻¹ ∈ H) : H = ⊤ := by
  have hU : ∀ c : R, upperUnit c ∈ H := by
    intro c
    by_cases hc : c = 0
    · rw [hc, upperUnit_zero]
      exact H.one_mem
    · obtain ⟨β, hβ⟩ := isSquare_of_charTwo' c
      have hβ0 : β ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hβ
        exact hc hβ
      have h := hh (Units.mk0 β hβ0) _ hu
      rwa [diagUnit_mul_upperUnit_mul_inv, Units.val_mk0, mul_one, ← hβ] at h
  have hL : ∀ c : R, lowerUnit c ∈ H := by
    intro c
    have h := H.mul_mem (H.mul_mem hw (hU (-c))) (H.inv_mem hw)
    rwa [weylUnit_mul_upperUnit_mul_inv, neg_neg] at h
  exact eq_top_of_upperUnit_mem_of_lowerUnit_mem hU hL

theorem eq_top_of_diag_mem_of_conj_mem [Finite R] [CharP R 2] (hq : 4 ≤ Nat.card R)
    {H : Subgroup (SL(2, R) × SL(2, R))} (hΔ : ∀ s : SL(2, R), (s, s) ∈ H)
    (hh : ∀ (α : Rˣ), ∀ p ∈ H,
      ((diagUnit α, 1) : SL(2, R) × SL(2, R)) * p * (diagUnit α, 1)⁻¹ ∈ H) : H = ⊤ := by
  have := isSimpleGroup_specialLinearGroup_two (K := R) hq
  set H₁ : Subgroup SL(2, R) := H.comap (MonoidHom.inl SL(2, R) SL(2, R)) with hH₁
  have hmem₁ : ∀ x : SL(2, R), x ∈ H₁ ↔ (x, (1 : SL(2, R))) ∈ H := fun x => Iff.rfl
  have hnorm : H₁.Normal := ⟨fun x hx g => by
    rw [hmem₁] at hx ⊢
    have h := H.mul_mem (H.mul_mem (hΔ g) hx) (H.inv_mem (hΔ g))
    simpa using h⟩
  obtain ⟨α, hα⟩ := exists_unit_mul_self_ne_one hq
  have h0 : upperUnit ((α : R) * α * 1 + -1) ∈ H₁ := by
    rw [hmem₁]
    have h := H.mul_mem (hh α _ (hΔ (upperUnit 1))) (H.inv_mem (hΔ (upperUnit 1)))
    have heq : ((diagUnit α, 1) : SL(2, R) × SL(2, R)) * (upperUnit 1, upperUnit 1) *
        (diagUnit α, 1)⁻¹ * (upperUnit 1, upperUnit 1)⁻¹ =
          (upperUnit ((α : R) * α * 1 + -1), 1) := by
      refine Prod.ext ?_ ?_
      · change diagUnit α * upperUnit 1 * (diagUnit α)⁻¹ * (upperUnit 1)⁻¹ = _
        rw [diagUnit_mul_upperUnit_mul_inv, upperUnit_inv, ← upperUnit_add]
      · change 1 * upperUnit 1 * 1⁻¹ * (upperUnit (1 : R))⁻¹ = 1
        group
    rwa [heq] at h
  have hne : H₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, mem_bot, upperUnit_eq_one_iff] at h0
    exact hα (by linear_combination h0)
  have htop : H₁ = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal H₁).resolve_left hne
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have h1 : (x * y⁻¹, (1 : SL(2, R))) ∈ H := (hmem₁ _).1 (htop ▸ mem_top _)
  have h := H.mul_mem h1 (hΔ y)
  simpa using h

end SL2

section Block

variable {n : ℕ}

theorem pairEmbed_mem_blockSpecialLinear {R : Type*} [Field R] {a b : Fin n} (hab : a ≠ b)
    (A : SL(2, R)) : pairEmbed hab A ∈ blockSpecialLinear (K := R) ({a, b} : Finset (Fin n)) := by
  rw [← range_pairEmbed hab]
  exact ⟨A, rfl⟩

@[expose] noncomputable def pairEmbedBlock {R : Type*} [Field R] {a b : Fin n} (hab : a ≠ b)
    {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) :
    SL(2, R) →* blockSpecialLinear (K := R) N :=
  (pairEmbed hab).codRestrict _ fun A =>
    blockSpecialLinear_mono habN (pairEmbed_mem_blockSpecialLinear hab A)

theorem coe_pairEmbedBlock {R : Type*} [Field R] {a b : Fin n} (hab : a ≠ b)
    {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) (A : SL(2, R)) :
    ((pairEmbedBlock hab habN A : blockSpecialLinear (K := R) N) :
      SpecialLinearGroup (Fin n) R) = pairEmbed hab A :=
  rfl

theorem range_pairEmbedBlock {R : Type*} [Field R] {a b : Fin n} (hab : a ≠ b)
    {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) :
    (pairEmbedBlock (R := R) hab habN).range =
      (blockSpecialLinear (K := R) ({a, b} : Finset (Fin n))).subgroupOf
        (blockSpecialLinear N) := by
  ext x
  rw [MonoidHom.mem_range, mem_subgroupOf, ← range_pairEmbed hab, MonoidHom.mem_range]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext hA⟩

theorem pairEmbed_diagUnit_apply_of_ne {R : Type*} [Field R] {a b : Fin n} (hab : a ≠ b)
    (α : Rˣ) {i j : Fin n} (hij : i ≠ j) :
    (pairEmbed hab (diagUnit α) : Matrix (Fin n) (Fin n) R) i j = 0 := by
  rw [pairEmbed_apply]
  by_cases h : i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))
  · rw [ite_eq_left h]
    obtain ⟨hi, hj⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · simp [coe_diagUnit, hi, hj, hab.symm]
    · simp [coe_diagUnit, hi, hj, hab.symm]
    · exact absurd (hi.trans hj.symm) hij
  · rw [ite_eq_right h, Matrix.one_apply_ne hij]

theorem commute_diagonal_of_apply_eq_zero {R : Type*} [CommRing R] {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, i ≠ j → M i j = 0) (d : Fin n → R) : Commute (diagonal d) M := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst hij
    exact mul_comm _ _
  · rw [hM i j hij, mul_zero, zero_mul]

theorem conjDiag_pairEmbedBlock_diagUnit {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    {a b : Fin n} (hab : a ≠ b) {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (α : Fˣ) :
    conjDiag ι N c (pairEmbedBlock hab habN (diagUnit α)) =
      pairEmbedBlock hab habN (diagUnit α) := by
  apply Subtype.ext
  rw [coe_conjDiag_apply, coe_pairEmbedBlock, mul_inv_eq_iff_eq_mul]
  have hc : ((SpecialLinearGroup.map ι (torusDiagSL c) * pairEmbed hab (diagUnit α) :
      SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((pairEmbed hab (diagUnit α) * SpecialLinearGroup.map ι (torusDiagSL c) :
        SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_map_torusDiagSL]
    exact (commute_diagonal_of_apply_eq_zero
      (fun i j hij => pairEmbed_diagUnit_apply_of_ne hab α hij) _).eq
  exact Subtype.ext hc

end Block

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type*}
  [Field F] {e : L ≃* projectiveSL n K} {t : G} {ι : K →+* F} {σ : F ≃+* F} {X : Subgroup G}
  {N : Finset (Fin n)}

namespace FieldNeighbourParam

variable (P : FieldNeighbourParam e t ι σ X N)

@[expose] noncomputable def pairHom {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) : SL(2, F) →* G :=
  P.Φ.comp (pairEmbedBlock hab habN)

theorem pairHom_apply {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (A : SL(2, F)) : P.pairHom hab habN A = P.Φ (pairEmbedBlock hab habN A) :=
  rfl

theorem pairHom_map {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (A : SL(2, K)) :
    P.pairHom hab habN (SpecialLinearGroup.map ι A) =
      ((e.symm (proj n K (pairEmbed hab A)) : L) : G) := by
  have hA : pairEmbed hab A ∈ blockSpecialLinear (K := K) N :=
    blockSpecialLinear_mono habN (pairEmbed_mem_blockSpecialLinear hab A)
  have hx : pairEmbedBlock hab habN (SpecialLinearGroup.map ι A) =
      ⟨SpecialLinearGroup.map ι (pairEmbed hab A), map_ringHom_mem_blockSpecialLinear ι hA⟩ :=
    Subtype.ext (map_pairEmbed ι hab A).symm
  rw [pairHom_apply, hx]
  exact P.N1 ⟨pairEmbed hab A, hA⟩

theorem pairHom_upperUnit_one {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) :
    P.pairHom hab habN (upperUnit 1) = ((e.symm (xab hab 1) : L) : G) := by
  have h := P.pairHom_map hab habN (upperUnit 1)
  rw [map_upperUnit, map_one, pairEmbed_upperUnit] at h
  exact h

theorem conj_pairHom {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (A : SL(2, F)) :
    t * P.pairHom hab habN A * t⁻¹ = P.pairHom hab habN (SpecialLinearGroup.map σ.toRingHom A) := by
  have hx : mapBlock σ N (pairEmbedBlock hab habN A) =
      pairEmbedBlock hab habN (SpecialLinearGroup.map σ.toRingHom A) :=
    Subtype.ext (map_pairEmbed σ.toRingHom hab A)
  rw [pairHom_apply, pairHom_apply, P.N3, hx]

theorem commute_pairHom_diagUnit {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) (c : blockTorusParam (K := K) (∅ : Finset (Fin n)))
    (α : Fˣ) :
    Commute (P.pairHom hab habN (diagUnit α))
      ((e.symm (proj n K (torusDiagSL c)) : L) : G) := by
  have h := P.N2 c (pairEmbedBlock hab habN (diagUnit α))
  rw [conjDiag_pairEmbedBlock_diagUnit] at h
  exact (mul_inv_eq_iff_eq_mul.1 h.symm).symm

theorem range_pairHom {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N) :
    (P.pairHom hab habN).range =
      ((blockSpecialLinear (K := F) ({a, b} : Finset (Fin n))).subgroupOf
        (blockSpecialLinear N)).map P.Φ := by
  rw [pairHom, MonoidHom.range_comp, range_pairEmbedBlock]

theorem pieceCore_eq_range_pairHom [Finite G] [Finite F] {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hF : 4 ≤ Nat.card F) (hX : X ≤ modelToG e (blockTorus (K := K) {a, b})) :
    pieceCore e {a, b} = (P.pairHom hab habN).range := by
  rw [P.range_pairHom, P.pieceCore_eq_map_of_notMem habN (by rw [Finset.card_pair hab]) hk hκ hF
    hX]

end FieldNeighbourParam

namespace SwapNeighbourParam

variable (P : SwapNeighbourParam e t X N)

@[expose] noncomputable def pairHom {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) : SL(2, K) × SL(2, K) →* G :=
  P.Ψ.comp ((pairEmbedBlock hab habN).prodMap (pairEmbedBlock hab habN))

theorem pairHom_apply {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (p : SL(2, K) × SL(2, K)) :
    P.pairHom hab habN p = P.Ψ (pairEmbedBlock hab habN p.1, pairEmbedBlock hab habN p.2) :=
  rfl

theorem pairHom_diag {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (s : SL(2, K)) :
    P.pairHom hab habN (s, s) = ((e.symm (proj n K (pairEmbed hab s)) : L) : G) :=
  P.diag _

theorem pairHom_upperUnit_one {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) :
    P.pairHom hab habN (upperUnit 1, upperUnit 1) = ((e.symm (xab hab 1) : L) : G) := by
  rw [pairHom_diag, pairEmbed_upperUnit]
  rfl

theorem conj_pairHom {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N)
    (p : SL(2, K) × SL(2, K)) :
    t * P.pairHom hab habN p * t⁻¹ = P.pairHom hab habN p.swap :=
  P.swap _ _

theorem commute_pairHom_diagUnit {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) (c : blockTorusParam (K := K) (∅ : Finset (Fin n)))
    (α : Kˣ) :
    Commute (P.pairHom hab habN (diagUnit α, 1))
      ((e.symm (proj n K (torusDiagSL c)) : L) : G) := by
  have h := P.N2 c (pairEmbedBlock hab habN (diagUnit α)) 1
  rw [conjDiag_pairEmbedBlock_diagUnit, map_one] at h
  rw [pairHom_apply]
  simp only [map_one]
  exact (mul_inv_eq_iff_eq_mul.1 h.symm).symm

theorem range_pairHom {a b : Fin n} (hab : a ≠ b) (habN : ({a, b} : Finset (Fin n)) ⊆ N) :
    (P.pairHom hab habN).range =
      (((blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))).subgroupOf
        (blockSpecialLinear N)).prod
          ((blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))).subgroupOf
            (blockSpecialLinear N))).map P.Ψ := by
  rw [pairHom, MonoidHom.range_comp, MonoidHom.range_prodMap, range_pairEmbedBlock]

theorem pieceCore_eq_range_pairHom [Finite G] [Finite K] {a b : Fin n} (hab : a ≠ b)
    (habN : ({a, b} : Finset (Fin n)) ⊆ N) {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hq : 4 ≤ Nat.card K) (hX : X ≤ modelToG e (blockTorus (K := K) {a, b})) :
    pieceCore e {a, b} = (P.pairHom hab habN).range := by
  rw [P.range_pairHom, P.pieceCore_eq_map habN hk hκ
    (commutator_blockSpecialLinear_eq_of_two_le (by rw [Finset.card_pair hab]) hq) hX]

end SwapNeighbourParam

end Param

section OrthPrelim

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

theorem modelToG_blockSL_pair_le_centralizer_compl (e : L ≃* projectiveSL n K) (a b : Fin n) :
    modelToG e (blockSL (K := K) ({a, b} : Finset (Fin n))) ≤
      centralizer (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) : Set G) :=
  modelToG_le_centralizer e fun x hx => mem_centralizer_iff.2 fun y hy =>
    (commute_blockSL_of_disjoint disjoint_compl_right x hx y hy).eq.symm

theorem pieceCore_le_centralizer_pairTorus (e : L ≃* projectiveSL n K) (a b : Fin n) :
    pieceCore e ({a, b} : Finset (Fin n)) ≤
      centralizer (modelToG e (pairTorus (K := K) a b) : Set G) :=
  (centralizerPerfectCore_le_centralizer _).trans
    (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_mono e (pairTorus_le_blockTorus a b))))

end OrthPrelim

section Orth

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  [Finite K] [CharP K 2]

theorem pieceCore_le_centralizer_blockSL_compl_field (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    (hHR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {F : Type*} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {X : Subgroup G}
    {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) {k : Fin n} (hk : k ∉ N)
    (hX : X ≤ modelToG e (blockTorus (K := K) {a, b})) (P : FieldNeighbourParam e t ι σ X N) :
    pieceCore e ({a, b} : Finset (Fin n)) ≤
      centralizer (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) : Set G) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_mul_xab e
    (fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hx)) hab hHR5
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have := isSimpleGroup_specialLinearGroup_two (K := K) hq
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  obtain ⟨ω, hω⟩ := exists_trace_one_of_involution hσ1 hσσ
  have hFK : Nat.card F = Nat.card K ^ 2 := natCard_eq_sq_of_trace_one ι hσσ hfix hω
  have hF : 4 ≤ Nat.card F := hFK ▸ hq.trans (Nat.le_self_pow two_ne_zero _)
  obtain ⟨κ, hκn⟩ := hκ
  have hκ1 : κ ≠ 1 := fun h => hκn (by rw [h, one_pow])
  set φ := P.pairHom hab habN with hφ
  set z : G := ((e.symm (xab hab 1) : L) : G) with hzdef
  have hz : φ (upperUnit 1) = z := P.pairHom_upperUnit_one hab habN
  have hM : pieceCore e ({a, b} : Finset (Fin n)) = φ.range :=
    P.pieceCore_eq_range_pairHom hab habN hk hκ1 hF hX
  set j : SL(2, K) →* G :=
    φ.comp ((MulAut.conj (upperUnit ω)).toMonoidHom.comp (SpecialLinearGroup.map ι)) with hjdef
  have hj : ∀ s, j s = φ (upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹) :=
    fun s => rfl
  have hfixed : ∀ s, (t * z) * j s * (t * z)⁻¹ = j s := by
    intro s
    set y := upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ with hydef
    have hy : y ∈ twistedSubfield ι ω := (mem_twistedSubfield ι).2 ⟨s, rfl⟩
    rw [hj, ← hz]
    calc t * φ (upperUnit 1) * φ y * (t * φ (upperUnit 1))⁻¹ =
          t * φ (upperUnit 1 * y * (upperUnit 1)⁻¹) * t⁻¹ := by
            simp only [map_mul, map_inv]
            group
      _ = φ (SpecialLinearGroup.map σ.toRingHom (upperUnit 1 * y * (upperUnit 1)⁻¹)) :=
            P.conj_pairHom hab habN _
      _ = φ (upperUnit 1 * SpecialLinearGroup.map σ.toRingHom y * upperUnit 1) := by
            congr 1
            rw [map_mul, map_mul, map_inv, map_upperUnit, map_one, upperUnit_one_inv]
      _ = φ y := by rw [twistedSubfield_fixed ι σ.toRingHom hσι hω hy]
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    have h := hfixed s
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hjφ : j.range ≤ φ.range := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  have hSY : j.range ≤ centralizer (modelToG e (pairTorus (K := K) a b) : Set G) :=
    hjφ.trans (hM ▸ pieceCore_le_centralizer_pairTorus e a b)
  have hzS : z ∈ j.range := ⟨upperUnit 1, by
    rw [hj, map_upperUnit, map_one, upperUnit_mul_comm, mul_inv_cancel_right, hz]⟩
  have hS := le_centralizer_blockSL_compl_of_conj_eq_mul hset hOut hq hn ⟨κ, hκn⟩ e htC ht hab hg
    (commutator_range_eq_self_of_isPerfect j) (eq_bot_or_eq_top_of_normal_range j) hSt hSY hzS
  rw [hM, MonoidHom.range_eq_map, ← sup_twistedSubfield_eq_top_of_trace_one ι hq hFK hσι hω,
    Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [hφ, P.pairHom_map]
    exact modelToG_blockSL_pair_le_centralizer_compl e a b
      (symm_mem_modelToG e (proj_mem_blockSL (pairEmbed_mem_blockSpecialLinear hab A)))
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_twistedSubfield ι).1 hy
    exact hS ⟨s, rfl⟩

theorem pieceCore_le_centralizer_blockSL_compl_swap (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    (hHR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {X : Subgroup G} {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) {k : Fin n}
    (hk : k ∉ N) (hX : X ≤ modelToG e (blockTorus (K := K) {a, b}))
    (P : SwapNeighbourParam e t X N) :
    pieceCore e ({a, b} : Finset (Fin n)) ≤
      centralizer (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) : Set G) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_mul_xab e
    (fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hx)) hab hHR5
  have := isSimpleGroup_specialLinearGroup_two (K := K) hq
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq
  obtain ⟨κ, hκn⟩ := hκ
  have hκ1 : κ ≠ 1 := fun h => hκn (by rw [h, one_pow])
  set ψ := P.pairHom hab habN with hψ
  set z : G := ((e.symm (xab hab 1) : L) : G) with hzdef
  set u : SL(2, K) × SL(2, K) := (upperUnit 1, upperUnit 1) with hudef
  have hz : ψ u = z := P.pairHom_upperUnit_one hab habN
  have hM : pieceCore e ({a, b} : Finset (Fin n)) = ψ.range :=
    P.pieceCore_eq_range_pairHom hab habN hk hκ1 hq hX
  obtain ⟨θ⟩ := nonempty_mulEquiv_twistedDiagSL2 (K := K)
  set j : SL(2, K) →* G := ψ.comp ((twistedDiagSL2 K).subtype.comp θ.toMonoidHom) with hjdef
  have hj : ∀ s, j s = ψ (θ s : twistedDiagSL2 K) := fun s => rfl
  have hjmem : ∀ p ∈ twistedDiagSL2 K, ψ p ∈ j.range := fun p hp =>
    ⟨θ.symm ⟨p, hp⟩, by rw [hj, MulEquiv.apply_symm_apply]⟩
  have hfixed : ∀ p ∈ twistedDiagSL2 K, (t * z) * ψ p * (t * z)⁻¹ = ψ p := by
    intro p hp
    rw [← hz]
    calc t * ψ u * ψ p * (t * ψ u)⁻¹ = t * ψ (u * p * u⁻¹) * t⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = ψ (u * p * u⁻¹).swap := P.conj_pairHom hab habN _
      _ = ψ p := by rw [hudef, twistedDiagSL2_fixed hp]
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    have h := hfixed _ (θ s).2
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hjψ : j.range ≤ ψ.range := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  have hSY : j.range ≤ centralizer (modelToG e (pairTorus (K := K) a b) : Set G) :=
    hjψ.trans (hM ▸ pieceCore_le_centralizer_pairTorus e a b)
  have hzS : z ∈ j.range := hz ▸ hjmem u upperUnit_one_pair_mem_twistedDiagSL2
  have hS := le_centralizer_blockSL_compl_of_conj_eq_mul hset hOut hq hn ⟨κ, hκn⟩ e htC ht hab hg
    (commutator_range_eq_self_of_isPerfect j) (eq_bot_or_eq_top_of_normal_range j) hSt hSY hzS
  rw [hM, MonoidHom.range_eq_map, ← diag_sup_twistedDiag_eq_top hq, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    change ψ (s, s) ∈ _
    rw [hψ, P.pairHom_diag]
    exact modelToG_blockSL_pair_le_centralizer_compl e a b
      (symm_mem_modelToG e (proj_mem_blockSL (pairEmbed_mem_blockSpecialLinear hab s)))
  · rintro _ ⟨p, hp, rfl⟩
    exact hS (hjmem p hp)

end Orth

section Pair

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

theorem mem_centralizer_modelToG_blockTorus_of_commute (e : L ≃* projectiveSL n K)
    (I : Finset (Fin n)) {y : G}
    (hy : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      Commute y ((e.symm (proj n K (torusDiagSL c)) : L) : G)) :
    y ∈ centralizer (modelToG e (blockTorus (K := K) I) : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hh
  obtain ⟨c, -, rfl⟩ := mem_blockTorus.1 hx
  exact (hy c).eq.symm

theorem conj_mem_centralizer_pieceCore (e : L ≃* projectiveSL n K) {I : Finset (Fin n)}
    {y x : G} (hy : y ∈ centralizer (modelToG e (blockTorus (K := K) I) : Set G))
    (hx : x ∈ centralizer (pieceCore e I : Set G)) :
    y * x * y⁻¹ ∈ centralizer (pieceCore e I : Set G) :=
  CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer
    (normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ hy)) hx

variable [Finite G]

theorem pieceCore_le_centralizer_pieceCore_of_fieldParam [CharP K 2] {F : Type*} [Field F]
    [Finite F] (e : L ≃* projectiveSL n K) {t : G} {ι : K →+* F} {σ : F ≃+* F}
    {I : Finset (Fin n)} {c d : Fin n} (hcd : c ≠ d)
    (hI : pieceCore e I ≤
      centralizer (modelToG e (blockSL (K := K) ({c, d} : Finset (Fin n))) : Set G))
    {X' : Subgroup G} {N' : Finset (Fin n)} (hcdN' : ({c, d} : Finset (Fin n)) ⊆ N')
    {k' : Fin n} (hk' : k' ∉ N') {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F)
    (hX' : X' ≤ modelToG e (blockTorus (K := K) {c, d})) (P' : FieldNeighbourParam e t ι σ X' N') :
    pieceCore e I ≤ centralizer (pieceCore e ({c, d} : Finset (Fin n)) : Set G) := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  set φ := P'.pairHom hcd hcdN' with hφ
  set C := centralizer (pieceCore e I : Set G) with hC
  have hJ : modelToG e (blockSL (K := K) ({c, d} : Finset (Fin n))) ≤ C := le_centralizer_iff.1 hI
  have hφK : ∀ A : SL(2, K), φ (SpecialLinearGroup.map ι A) ∈ C := fun A => by
    rw [hφ, P'.pairHom_map]
    exact hJ (symm_mem_modelToG e (proj_mem_blockSL (pairEmbed_mem_blockSpecialLinear hcd A)))
  have htop : C.comap φ = ⊤ := by
    refine eq_top_of_upperUnit_one_mem_of_conj_mem ?_ ?_ ?_
    · have h := hφK (upperUnit 1)
      rwa [map_upperUnit, map_one] at h
    · have h := hφK weylUnit
      rwa [map_weylUnit] at h
    · intro α x hx
      change φ (diagUnit α * x * (diagUnit α)⁻¹) ∈ C
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_centralizer_pieceCore e (mem_centralizer_modelToG_blockTorus_of_commute e I
        fun c => P'.commute_pairHom_diagUnit hcd hcdN' c α) hx
  rw [le_centralizer_iff, P'.pieceCore_eq_range_pairHom hcd hcdN' hk' hκ hF hX',
    MonoidHom.range_eq_map, ← htop]
  exact map_comap_le _ _

theorem pieceCore_le_centralizer_pieceCore_of_swapParam [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (e : L ≃* projectiveSL n K) {t : G} {I : Finset (Fin n)}
    {c d : Fin n} (hcd : c ≠ d)
    (hI : pieceCore e I ≤
      centralizer (modelToG e (blockSL (K := K) ({c, d} : Finset (Fin n))) : Set G))
    {X' : Subgroup G} {N' : Finset (Fin n)} (hcdN' : ({c, d} : Finset (Fin n)) ⊆ N')
    {k' : Fin n} (hk' : k' ∉ N') {κ : Kˣ} (hκ : κ ≠ 1)
    (hX' : X' ≤ modelToG e (blockTorus (K := K) {c, d})) (P' : SwapNeighbourParam e t X' N') :
    pieceCore e I ≤ centralizer (pieceCore e ({c, d} : Finset (Fin n)) : Set G) := by
  set ψ := P'.pairHom hcd hcdN' with hψ
  set C := centralizer (pieceCore e I : Set G) with hC
  have hJ : modelToG e (blockSL (K := K) ({c, d} : Finset (Fin n))) ≤ C := le_centralizer_iff.1 hI
  have htop : C.comap ψ = ⊤ := by
    refine eq_top_of_diag_mem_of_conj_mem hq ?_ ?_
    · intro s
      change ψ (s, s) ∈ C
      rw [hψ, P'.pairHom_diag]
      exact hJ (symm_mem_modelToG e (proj_mem_blockSL (pairEmbed_mem_blockSpecialLinear hcd s)))
    · intro α p hp
      change ψ ((diagUnit α, 1) * p * (diagUnit α, 1)⁻¹) ∈ C
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_centralizer_pieceCore e (mem_centralizer_modelToG_blockTorus_of_commute e I
        fun c => P'.commute_pairHom_diagUnit hcd hcdN' c α) hp
  rw [le_centralizer_iff, P'.pieceCore_eq_range_pairHom hcd hcdN' hk' hκ hq hX',
    MonoidHom.range_eq_map, ← htop]
  exact map_comap_le _ _

end Pair

section OrthPair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  [Finite K] [CharP K 2]

theorem pieceCore_le_centralizer_pieceCore_field (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    (hHR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {F : Type*} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {X : Subgroup G}
    {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) {k : Fin n} (hk : k ∉ N)
    (hX : X ≤ modelToG e (blockTorus (K := K) {a, b})) (P : FieldNeighbourParam e t ι σ X N)
    {c d : Fin n} (hcd : c ≠ d) (hdisj : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    {X' : Subgroup G} {N' : Finset (Fin n)} (hcdN' : ({c, d} : Finset (Fin n)) ⊆ N')
    {k' : Fin n} (hk' : k' ∉ N') (hX' : X' ≤ modelToG e (blockTorus (K := K) {c, d}))
    (P' : FieldNeighbourParam e t ι σ X' N') :
    pieceCore e ({a, b} : Finset (Fin n)) ≤
      centralizer (pieceCore e ({c, d} : Finset (Fin n)) : Set G) := by
  have hO := pieceCore_le_centralizer_blockSL_compl_field hset hOut hq hn hκ e htC ht hab hHR5 ι
    hσ1 hσσ hfix habN hk hX P
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF : 4 ≤ Nat.card F := (natCard_eq_sq_of_involution ι hσ1 hσσ hfix) ▸
    hq.trans (Nat.le_self_pow two_ne_zero _)
  obtain ⟨κ, hκn⟩ := hκ
  have hκ1 : κ ≠ 1 := fun h => hκn (by rw [h, one_pow])
  have hsub : ({c, d} : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n))ᶜ :=
    Finset.subset_compl_iff_disjoint_left.2 hdisj
  exact pieceCore_le_centralizer_pieceCore_of_fieldParam e hcd
    (hO.trans (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_mono e (blockSL_mono hsub)))))
    hcdN' hk' hκ1 hF hX' P'

theorem pieceCore_le_centralizer_pieceCore_swap (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    (hHR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {X : Subgroup G} {N : Finset (Fin n)} (habN : ({a, b} : Finset (Fin n)) ⊆ N) {k : Fin n}
    (hk : k ∉ N) (hX : X ≤ modelToG e (blockTorus (K := K) {a, b}))
    (P : SwapNeighbourParam e t X N) {c d : Fin n} (hcd : c ≠ d)
    (hdisj : Disjoint ({a, b} : Finset (Fin n)) {c, d}) {X' : Subgroup G} {N' : Finset (Fin n)}
    (hcdN' : ({c, d} : Finset (Fin n)) ⊆ N') {k' : Fin n} (hk' : k' ∉ N')
    (hX' : X' ≤ modelToG e (blockTorus (K := K) {c, d})) (P' : SwapNeighbourParam e t X' N') :
    pieceCore e ({a, b} : Finset (Fin n)) ≤
      centralizer (pieceCore e ({c, d} : Finset (Fin n)) : Set G) := by
  have hO := pieceCore_le_centralizer_blockSL_compl_swap hset hOut hq hn hκ e htC ht hab hHR5
    habN hk hX P
  obtain ⟨κ, hκn⟩ := hκ
  have hκ1 : κ ≠ 1 := fun h => hκn (by rw [h, one_pow])
  have hsub : ({c, d} : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n))ᶜ :=
    Finset.subset_compl_iff_disjoint_left.2 hdisj
  exact pieceCore_le_centralizer_pieceCore_of_swapParam hq e hcd
    (hO.trans (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_mono e (blockSL_mono hsub)))))
    hcdN' hk' hκ1 hX' P'

end OrthPair

end CFSG.SeitzReduction.LinearPilot
