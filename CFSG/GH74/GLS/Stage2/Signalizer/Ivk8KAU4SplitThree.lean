module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUDef
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OddBlock

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LieType.HighestRoot (closure_orderOf_three_eq_top)
open CFSG.ComponentClassification.CatFactsL4U4 (eq_bot_of_odd_block)
open CFSG.ComponentClassification.Burgoyne.PSL (compInd compInd_compl commute_compInd_compl)
open CFSG.ClassicalGroups.UnitaryFlag (mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (norm_det_eq_one
  norm_eq_one_of_scalar_mem_primeFormUnitary)
open scoped MatrixGroups

section TwoSL3

variable {Y : Type} [Group Y] {F : Type} [Field F]

theorem kaU4S3_sl3_mem_closure_odd [Finite F] (hF : Nat.card F = 3) (ι : SL(2, F) →* Y)
    {R : Subgroup Y} (hι : ∀ g, ι g ∈ R) (g : SL(2, F)) :
    ι g ∈ Subgroup.closure {x : Y | x ∈ R ∧ Odd (orderOf x)} := by
  have hg : g ∈ Subgroup.closure {y : SL(2, F) | orderOf y = 3} := by
    rw [closure_orderOf_three_eq_top hF]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨hι y, ?_⟩
    have hd : orderOf (ι y) ∣ orderOf y := orderOf_map_dvd ι y
    rw [hy] at hd
    exact Odd.of_dvd_nat (by decide) hd
  | one =>
    rw [map_one]
    exact one_mem _
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact inv_mem ha

theorem kaU4S3_sl3_ker_central (ι₁ ι₂ : SL(2, F) →* Y) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (hc : ∀ s t, Commute (ι₁ s) (ι₂ t)) {s t : SL(2, F)}
    (hst : ι₁ s * ι₂ t = 1) :
    s ∈ Subgroup.center SL(2, F) ∧ t ∈ Subgroup.center SL(2, F) := by
  have hs : ι₁ s = (ι₂ t)⁻¹ := eq_inv_of_mul_eq_one_left hst
  have ht : ι₂ t = (ι₁ s)⁻¹ := eq_inv_of_mul_eq_one_right hst
  refine ⟨Subgroup.mem_center_iff.2 fun g => ?_, Subgroup.mem_center_iff.2 fun g => ?_⟩
  · apply h₁
    rw [map_mul, map_mul, hs]
    exact ((hc g t).inv_right).eq
  · apply h₂
    rw [map_mul, map_mul, ht]
    exact ((hc s g).symm.inv_right).eq

theorem kaU4S3_all_of_two_sl3 [Finite Y] [Finite F]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {α : MulAut Y}
    (hF : Nat.card F = 3) (ι₁ ι₂ : SL(2, F) →* Y) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (hc : ∀ s t, Commute (ι₁ s) (ι₂ t))
    (hf₁ : ∀ s, α (ι₁ s) = ι₁ s) (hf₂ : ∀ t, α (ι₂ t) = ι₂ t)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → ∃ s t, c = ι₁ s * ι₂ t)
    (hOutTriv : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P →
      (∀ e ∈ P, e ∈ innSub Y → e = 1) → P = ⊥) : KAAll α := by
  set β : SL(2, F) × SL(2, F) →* Y := ι₁.noncommCoprod ι₂ hc
  have hβa : ∀ x : SL(2, F) × SL(2, F), β x = ι₁ x.1 * ι₂ x.2 :=
    fun x => MonoidHom.noncommCoprod_apply ι₁ ι₂ hc x
  refine ka_all_of_oddcore_triv hinj β.range ?_ ?_ ?_ ?_ hOutTriv
  · rintro _ ⟨x, rfl⟩
    rw [mem_fixSub, hβa, map_mul, hf₁, hf₂]
  · refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
    rintro _ ⟨⟨s, t⟩, rfl⟩
    rw [hβa]
    exact mul_mem
      (kaU4S3_sl3_mem_closure_odd hF ι₁ (R := β.range)
        (fun g => ⟨(g, 1), by rw [hβa, map_one, mul_one]⟩) s)
      (kaU4S3_sl3_mem_closure_odd hF ι₂ (R := β.range)
        (fun g => ⟨(1, g), by rw [hβa, map_one, one_mul]⟩) t)
  · intro c hc' ho
    obtain ⟨s, t, rfl⟩ := hodd c hc' ho
    exact ⟨(s, t), (hβa (s, t))⟩
  · intro p hp hp2 X hX hXR hnorm
    have : Fact p.Prime := ⟨hp⟩
    have hodd' : Odd (Nat.card ↥X) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hX
      rw [hn]
      exact (hp.odd_of_ne_two hp2).pow
    refine eq_bot_of_odd_block ⟨3, 1, Nat.prime_three, by decide, le_rfl, by rw [hF]; rfl⟩ β ?_ X
      hXR (fun g hg r hr => (Subgroup.mem_normalizer_iff.1 (hnorm g hg) r).1 hr) hodd'
    intro x hx
    exact kaU4S3_sl3_ker_central ι₁ ι₂ h₁ h₂ hc (by rw [← hβa]; exact hx)

end TwoSL3

section UArith

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem kaU4S3_pow_four (h3 : p ^ f = 3) {z : K} (hz : h.norm z = 1) : z ^ 4 = 1 := by
  rw [UnitaryFieldData.norm, h.bar_apply, h3] at hz
  linear_combination hz

theorem kaU4S3_eq_one_of_pow {δ : K} {m : ℕ} (hm : Odd m) (h4 : δ ^ 4 = 1) (hδ : δ ^ m = 1) :
    δ = 1 := by
  obtain ⟨t, rfl⟩ := hm
  have h2 : δ ^ 2 = 1 := by
    calc δ ^ 2 = (δ ^ 4) ^ t * δ ^ 2 := by rw [h4, one_pow, one_mul]
      _ = (δ ^ (2 * t + 1)) ^ 2 := by ring
      _ = 1 := by rw [hδ, one_pow]
  calc δ = (δ ^ 2) ^ t * δ := by rw [h2, one_pow, one_mul]
    _ = δ ^ (2 * t + 1) := by ring
    _ = 1 := hδ

include h in
theorem kaU4S3_scalar_pow {n : ℕ} (hn : 1 ≤ n) (z : StatedSU n (p ^ f) K)
    (hz : z ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) : z ^ n = 1 := by
  rw [← CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h hn,
    CFSG.ClassicalGroups.UnitaryFlag.mem_unitaryScalars] at hz
  obtain ⟨c, -, hcn, hc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hcn, map_one]
  rfl

theorem kaU4S3_exists_pow {m : ℕ} (hm : Odd m) : ∃ k : ℕ, 4 ∣ k ∧ k ≡ 1 [MOD m] := by
  have hcop : Nat.Coprime 4 m := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)
    simpa using this
  refine ⟨4 ^ Nat.totient m, dvd_pow_self 4 (Nat.totient_pos.2 hm.pos).ne', ?_⟩
  exact Nat.ModEq.pow_totient hcop

end UArith

section UBlocks

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

include h in
theorem kaU4S3_exists_su2_equiv :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* StatedSU 2 (p ^ f) K) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg h.card_eq_sq
  exact ⟨↥(CFSG.LieType.Steinberg.fixedSubfield K p f), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq,
    ⟨(CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
      (CFSG.LieType.Universal.Unitary.equivStatedSU h.card_eq_sq 2)⟩⟩

include h in
theorem kaU4S3_block_hom {F : Type} [Field F] (e₂ : SL(2, F) ≃* StatedSU 2 (p ^ f) K)
    (J : Finset (Fin n)) (hJ : J.card = 2) :
    ∃ ι : SL(2, F) →* StatedSU n (p ^ f) K, Function.Injective ι ∧ ι.range = uBlock p f K J := by
  have key : ∀ m : ℕ, m = 2 → ∃ e : SL(2, F) ≃* StatedSU m (p ^ f) K, True := by
    rintro m rfl
    exact ⟨e₂, trivial⟩
  obtain ⟨e, -⟩ := key J.card hJ
  refine ⟨(blockSU h J).comp e.toMonoidHom, (blockSU_injective h J).comp e.injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
    range_blockSU]

theorem kaU4S3_proj_block_injective {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) {G : Type*}
    [Group G] (ι : G →* StatedSU n (p ^ f) K) (hι : Function.Injective ι)
    (hr : ∀ g, ι g ∈ uBlock p f K I) :
    Function.Injective ((projH (StatedSU n (p ^ f) K)).comp ι) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ι g = 1 :=
    eq_one_of_mem_uBlock_scalars hk (hr g) ((QuotientGroup.eq_one_iff _).1 hg)
  exact hι (by rw [h1, map_one])

theorem kaU4S3_one_sub_compInd (J : Finset (Fin n)) :
    (1 : Matrix (Fin n) (Fin n) K) - compInd K J = diagonal fun i => if i ∈ J then 1 else 0 := by
  rw [compInd, ← diagonal_one, diagonal_sub]
  congr 1
  funext i
  by_cases hi : i ∈ J <;> simp [hi]

theorem kaU4S3_block_commute {I I' : Finset (Fin n)} (hII : Disjoint I I')
    {g g' : StatedSU n (p ^ f) K} (hg : g ∈ uBlock p f K I) (hg' : g' ∈ uBlock p f K I') :
    g * g' = g' * g := by
  have hsplit : ∀ {J : Finset (Fin n)} {x : StatedSU n (p ^ f) K}, x ∈ uBlock p f K J →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) * (1 - compInd K J) ∧
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        (1 - compInd K J) * (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) := by
    intro J x hx
    obtain ⟨h1, h2⟩ := hx
    constructor
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h2]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h1]
      abel
  have hzz : ∀ {A B : Finset (Fin n)}, Disjoint A B →
      (1 - compInd K A) * (1 - compInd K B) = 0 := by
    intro A B hAB
    rw [kaU4S3_one_sub_compInd, kaU4S3_one_sub_compInd, diagonal_mul_diagonal, ← diagonal_zero]
    congr 1
    funext i
    by_cases hi : i ∈ A
    · simp [hi, Finset.disjoint_left.1 hAB hi]
    · simp [hi]
  have hz := hzz hII
  have hz' := hzz hII.symm
  set G := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
  set H := ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hH
  have e1 : (G - 1) * (H - 1) = 0 := by
    rw [(hsplit hg).1, (hsplit hg').2, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - compInd K I),
      hz, Matrix.zero_mul, Matrix.mul_zero]
  have e2 : (H - 1) * (G - 1) = 0 := by
    rw [(hsplit hg').1, (hsplit hg).2, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - compInd K I'),
      hz', Matrix.zero_mul, Matrix.mul_zero]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, ← hG, ← hH]
  have hGH : G * H = (G - 1) * (H - 1) + G + H - 1 := by noncomm_ring
  have hHG : H * G = (H - 1) * (G - 1) + G + H - 1 := by noncomm_ring
  rw [hGH, hHG, e1, e2]

theorem kaU4S3_fix_block (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0) {J I : Finset (Fin n)}
    (hI : I = J ∨ I = Jᶜ) {x : StatedSU n (p ^ f) K} (hx : x ∈ uBlock p f K I) :
    uConjAut h hn (uSign h J) (projH (StatedSU n (p ^ f) K) x) =
      projH (StatedSU n (p ^ f) K) x := by
  have e := uLift_proj h hn (uSign h J) 1 x
  rw [map_one, mul_one] at e
  rw [e, (uLift_sign_eq_iff h h2 J x).2
    (commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hx))]

end UBlocks

section Idem

variable {R : Type*} [Ring R] {P M : R}

theorem kaU4S3_idem_pq (hPP : P * P = P) : P * (1 - P) = 0 := by
  rw [mul_sub, mul_one, hPP, sub_self]

theorem kaU4S3_idem_qp (hPP : P * P = P) : (1 - P) * P = 0 := by
  rw [sub_mul, one_mul, hPP, sub_self]

theorem kaU4S3_idem_qq (hPP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hPP]; abel

theorem kaU4S3_idem_qm (hPM : P * M = M * P) : (1 - P) * M = M * (1 - P) := by
  rw [sub_mul, mul_sub, one_mul, mul_one, hPM]

theorem kaU4S3_idem_pow (hPP : P * P = P) (hPM : P * M = M * P) (j : ℕ) :
    (M * (1 - P) + P) ^ j = M ^ j * (1 - P) + P := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih]
    calc (M ^ j * (1 - P) + P) * (M * (1 - P) + P)
        = M ^ j * ((1 - P) * M) * (1 - P) + M ^ j * ((1 - P) * P) + P * M * (1 - P) + P * P := by
          noncomm_ring
      _ = M ^ j * (M * (1 - P)) * (1 - P) + M ^ j * 0 + M * (P * (1 - P)) + P := by
          rw [kaU4S3_idem_qm hPM, kaU4S3_idem_qp hPP, hPM, hPP]; simp only [mul_assoc]
      _ = M ^ (j + 1) * (1 - P) + P := by
          rw [kaU4S3_idem_pq hPP, mul_zero, mul_zero, add_zero, add_zero, pow_succ, mul_assoc,
            mul_assoc, kaU4S3_idem_qq hPP]
          simp only [mul_assoc]

theorem kaU4S3_idem_prod (hPP : P * P = P) (hPM : P * M = M * P) :
    (M * (1 - P) + P) * (M * P + (1 - P)) = M := by
  calc (M * (1 - P) + P) * (M * P + (1 - P))
      = M * ((1 - P) * M) * P + M * ((1 - P) * (1 - P)) + P * M * P + P * (1 - P) := by
        noncomm_ring
    _ = M * (M * (1 - P)) * P + M * (1 - P) + M * (P * P) + 0 := by
        rw [kaU4S3_idem_qm hPM, kaU4S3_idem_qq hPP, hPM, kaU4S3_idem_pq hPP]; simp only [mul_assoc]
    _ = M * (M * ((1 - P) * P)) + M * (1 - P) + M * (P * P) + 0 := by simp only [mul_assoc]
    _ = M := by
        rw [kaU4S3_idem_qp hPP, hPP, mul_zero, mul_zero, zero_add, add_zero]
        noncomm_ring

theorem kaU4S3_idem_unitary {N : R} (hPP : P * P = P) (hPM : P * M = M * P) (hNM : N * M = 1)
    (hMN : M * N = 1) : ((1 - P) * N + P) * (M * (1 - P) + P) = 1 := by
  have hPN : P * N = N * P := by
    calc P * N = (N * M) * P * N := by rw [hNM, one_mul]
      _ = N * (M * P) * N := by simp only [mul_assoc]
      _ = N * (P * M) * N := by rw [hPM]
      _ = N * P * (M * N) := by simp only [mul_assoc]
      _ = N * P := by rw [hMN, mul_one]
  calc ((1 - P) * N + P) * (M * (1 - P) + P)
      = (1 - P) * (N * M) * (1 - P) + ((1 - P) * N) * P + P * M * (1 - P) + P * P := by
        noncomm_ring
    _ = (1 - P) * (1 - P) + (N * (1 - P)) * P + (M * P) * (1 - P) + P := by
        rw [hNM, mul_one, kaU4S3_idem_qm hPN, hPM, hPP]
    _ = (1 - P) + N * ((1 - P) * P) + M * (P * (1 - P)) + P := by
        rw [kaU4S3_idem_qq hPP]; simp only [mul_assoc]
    _ = 1 := by
        rw [kaU4S3_idem_qp hPP, kaU4S3_idem_pq hPP, mul_zero, mul_zero, add_zero, add_zero,
          sub_add_cancel]

end Idem

section USplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem kaU4S3_compInd_mul_self (I : Finset (Fin n)) :
    compInd K I * compInd K I = compInd K I := by
  rw [compInd, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [hi]

theorem kaU4S3_compInd_map (φ : K →+* K) (I : Finset (Fin n)) :
    (compInd K I).map φ = compInd K I := by
  rw [compInd, diagonal_map (map_zero φ)]
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [hi]

theorem kaU4S3_compInd_transpose (I : Finset (Fin n)) : (compInd K I)ᵀ = compInd K I := by
  rw [compInd, diagonal_transpose]

include h in
theorem kaU4S3_block_part (h3 : p ^ f = 3) {m : ℕ} (hm : Odd m) {g : StatedSU n (p ^ f) K}
    (hg : g ^ m = 1) {I : Finset (Fin n)}
    (hc : compInd K I * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K I) :
    ∃ x ∈ uBlock p f K I, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - compInd K I) + compInd K I := by
  set M : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  set P : Matrix (Fin n) (Fin n) K := compInd K I with hP
  have hPP : P * P = P := kaU4S3_compInd_mul_self I
  have hgU : (M.map h.bar)ᵀ * M = 1 := ((mem_unitarySU_iff h).1 g.2).2
  have hMMu : M * (M.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hgU
  set X : Matrix (Fin n) (Fin n) K := M * (1 - P) + P with hX
  have hXU : (X.map h.bar)ᵀ * X = 1 := by
    have e : (X.map h.bar)ᵀ = (1 - P) * (M.map h.bar)ᵀ + P := by
      have hb : ∀ A : Matrix (Fin n) (Fin n) K, A.map h.bar = h.bar.mapMatrix A := fun A => rfl
      have hPm : P.map h.bar = P := kaU4S3_compInd_map h.bar I
      have hPt : Pᵀ = P := kaU4S3_compInd_transpose I
      rw [hX, hb, map_add, map_mul, map_sub, map_one, ← hb P, hPm, Matrix.transpose_add,
        Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hPt, ← hb M]
    rw [e]
    exact kaU4S3_idem_unitary hPP hc hgU hMMu
  have hXdet : X.det = 1 := by
    have hN : h.norm X.det = 1 :=
      norm_det_eq_one h (1 : GL (Fin n) K) (A := uGL h X hXU) (uGL_mem h X hXU)
    have hMm : M ^ m = 1 := by
      have := congrArg (fun x : StatedSU n (p ^ f) K => ((x : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) hg
      simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
    have hXm : X ^ m = 1 := by
      rw [hX, kaU4S3_idem_pow hPP hc m, hMm, one_mul, sub_add_cancel]
    refine kaU4S3_eq_one_of_pow (m := m) hm (kaU4S3_pow_four h h3 hN) ?_
    rw [← Matrix.det_pow, hXm, Matrix.det_one]
  refine ⟨uSUmk h X hXdet hXU, ⟨?_, ?_⟩, rfl⟩
  · change P * X = P
    rw [hX, Matrix.mul_add, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, kaU4S3_idem_pq hPP, hPP,
      mul_zero, zero_add]
  · change X * P = P
    rw [hX, Matrix.add_mul, Matrix.mul_assoc, kaU4S3_idem_qp hPP, hPP, mul_zero, zero_add]

include h in
theorem kaU4S3_split (h3 : p ^ f = 3) {m : ℕ} (hm : Odd m) {g : StatedSU n (p ^ f) K}
    (hg : g ^ m = 1) {J : Finset (Fin n)}
    (hc : compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J) :
    ∃ x ∈ uBlock p f K J, ∃ x' ∈ uBlock p f K Jᶜ, g = x * x' := by
  obtain ⟨x, hx, hxe⟩ := kaU4S3_block_part h h3 hm hg hc
  obtain ⟨x', hx', hxe'⟩ := kaU4S3_block_part h h3 hm hg (commute_compInd_compl hc)
  refine ⟨x, hx, x', hx', ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, hxe, hxe', compInd_compl, sub_sub_cancel]
  exact (kaU4S3_idem_prod (kaU4S3_compInd_mul_self J) hc).symm

end USplit

section UFour

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem kaU4S3_two_ne_zero (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

include h in
theorem kaU4S3_odd_decomp (hp2 : p ≠ 2) (h3 : p ^ f = 3) (J : Finset (Fin 4))
    {c : StatedProj (StatedSU 4 (p ^ f) K)}
    (hc : uConjAut h (by norm_num) (uSign h J) c = c) (ho : Odd (orderOf c)) :
    ∃ x ∈ uBlock p f K J, ∃ x' ∈ uBlock p f K Jᶜ,
      c = projH (StatedSU 4 (p ^ f) K) x * projH (StatedSU 4 (p ^ f) K) x' := by
  have h2 := kaU4S3_two_ne_zero h hp2
  obtain ⟨g, rfl⟩ := projH_surjective c
  obtain ⟨k, hk4, hkm⟩ := kaU4S3_exists_pow ho
  set m := orderOf (projH (StatedSU 4 (p ^ f) K) g)
  have hπk : projH (StatedSU 4 (p ^ f) K) (g ^ k) = projH (StatedSU 4 (p ^ f) K) g := by
    rw [map_pow]
    exact (pow_eq_pow_iff_modEq.2 hkm).trans (pow_one _)
  have hlift : ∀ x : StatedSU 4 (p ^ f) K,
      uConjAut h (by norm_num) (uSign h J) (projH (StatedSU 4 (p ^ f) K) x) =
        projH (StatedSU 4 (p ^ f) K) (uLift h (uSign h J) 1 x) := by
    intro x
    have e := uLift_proj h (by norm_num) (uSign h J) 1 x
    rwa [map_one, mul_one] at e
  have hz : g⁻¹ * uLift h (uSign h J) 1 g ∈
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) := by
    rw [← projH_eq_projH_iff]
    exact hc.symm.trans (hlift g)
  set z := g⁻¹ * uLift h (uSign h J) 1 g with hzdef
  have hzc : ∀ y : StatedSU 4 (p ^ f) K, y * z = z * y :=
    Subgroup.mem_center_iff.1 (scalars_subgroupOf_le_center hz)
  have hz4 : z ^ 4 = 1 := kaU4S3_scalar_pow h (by norm_num) z hz
  have hzk : z ^ k = 1 := by
    obtain ⟨t, rfl⟩ := hk4
    rw [pow_mul, hz4, one_pow]
  have hθ : uLift h (uSign h J) 1 (g ^ k) = g ^ k := by
    have e : uLift h (uSign h J) 1 g = g * z := by rw [hzdef, mul_inv_cancel_left]
    rw [map_pow, e, Commute.mul_pow (hzc g) k, hzk, mul_one]
  have hgm : g ^ m ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) := by
    have e : projH (StatedSU 4 (p ^ f) K) (g ^ m) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    exact (QuotientGroup.eq_one_iff _).1 e
  have hgk : (g ^ k) ^ m = 1 := by
    obtain ⟨t, ht⟩ := hk4
    calc (g ^ k) ^ m = (g ^ m) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((g ^ m) ^ 4) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [kaU4S3_scalar_pow h (by norm_num) _ hgm, one_pow]
  obtain ⟨x, hx, x', hx', hxx⟩ := kaU4S3_split h h3 ho hgk
    ((uLift_sign_eq_iff h h2 J (g ^ k)).1 hθ)
  exact ⟨x, hx, x', hx', by rw [← hπk, hxx, map_mul]⟩

include h in
theorem kaU4S3_inner_of_odd (h3 : p ^ f = 3) {m : ℕ} (hm : Odd m) (A : uU h 4)
    (hA : (uConjAut h (by norm_num) A) ^ m = 1) :
    uConjAut h (by norm_num) A ∈ innSub (StatedProj (StatedSU 4 (p ^ f) K)) := by
  have hn : 3 ≤ 4 := by norm_num
  rw [← map_pow, uConjAut_eq_one_iff h hn] at hA
  obtain ⟨c, hc⟩ := hA
  have hcN : h.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num) 1 (hc ▸ (A ^ m).2)
  have hAm : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ m =
      Matrix.scalar (Fin 4) (c : K) := by
    have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hc
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
  have hdetm : (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det) ^ m = 1 := by
    rw [← Matrix.det_pow, hAm, Matrix.scalar_apply, Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact kaU4S3_pow_four h h3 hcN
  have hδ : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 :=
    kaU4S3_eq_one_of_pow hm (kaU4S3_pow_four h h3 (norm_det_eq_one h (1 : GL (Fin 4) K) A.2))
      hdetm
  exact ka_uConjAut_inner_of_det h (by norm_num) A 1 (by simp [UnitaryFieldData.norm])
    (by rw [hδ]; simp)

include h in
theorem kaU4S3_outTriv (h3 : p ^ f = 3) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (P : Subgroup (MulAut (StatedProj (StatedSU 4 (p ^ f) K)))) (hP : IsPGroup q ↥P)
    (hinn : ∀ e ∈ P, e ∈ innSub (StatedProj (StatedSU 4 (p ^ f) K)) → e = 1) : P = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hq hq2 hP he
  have hn : 3 ≤ 4 := by norm_num
  have hq' : ¬(4 = 3 ∧ p ^ f = 2) := fun hh => absurd hh.1 (by norm_num)
  obtain ⟨A, φ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq' e
  have hφm : φ ^ orderOf (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) φ) = 1 :=
    fieldAut_pow_eq_one h hn hq' (pow_orderOf_eq_one _)
  have hφ : φ = 1 := eq_one_of_odd_of_fix h hodd hφm (fun c hc => by
    rcases mem_three_of_bar h h3 hc with rfl | rfl | rfl <;> simp)
  subst hφ
  rw [map_one, mul_one] at he hodd ⊢
  exact hinn _ he (kaU4S3_inner_of_odd h h3 hodd A (pow_orderOf_eq_one _))

end UFour

section Main

theorem kaU4SplitThree_thm : KAU4SplitThree := by
  intro p f K _ _ h hp2 h3 J hJ
  have : Fact p.Prime := ⟨h.prime⟩
  have hn1 : 1 ≤ 4 := by norm_num
  have h2 := kaU4S3_two_ne_zero h hp2
  obtain ⟨F, _, _, hF, ⟨e₂⟩⟩ := kaU4S3_exists_su2_equiv h
  have hF3 : Nat.card F = 3 := hF.trans h3
  have hJc : (Jᶜ).card = 2 := by rw [Finset.card_compl, Fintype.card_fin, hJ]
  obtain ⟨ι₁, hι₁, hr₁⟩ := kaU4S3_block_hom h e₂ J hJ
  obtain ⟨ι₂, hι₂, hr₂⟩ := kaU4S3_block_hom h e₂ Jᶜ hJc
  have hm₁ : ∀ s, ι₁ s ∈ uBlock p f K J := fun s => hr₁ ▸ ⟨s, rfl⟩
  have hm₂ : ∀ s, ι₂ s ∈ uBlock p f K Jᶜ := fun s => hr₂ ▸ ⟨s, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin 4, a ∉ J := by
    by_contra hcon
    push Not at hcon
    have : J = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at hJ
    omega
  obtain ⟨b, hb⟩ : ∃ b : Fin 4, b ∈ J := Finset.card_pos.1 (by omega)
  have hb' : b ∉ Jᶜ := by simpa using hb
  refine kaU4S3_all_of_two_sl3 (ka_conj_inj_pu h.card_eq_sq (by norm_num) ?_) hF3
    ((projH (StatedSU 4 (p ^ f) K)).comp ι₁) ((projH (StatedSU 4 (p ^ f) K)).comp ι₂)
    (kaU4S3_proj_block_injective ha ι₁ hι₁ hm₁) (kaU4S3_proj_block_injective hb' ι₂ hι₂ hm₂)
    ?_ ?_ ?_ ?_ ?_
  · intro e
    simp at e
  · intro s t
    change projH _ (ι₁ s) * projH _ (ι₂ t) = projH _ (ι₂ t) * projH _ (ι₁ s)
    rw [← map_mul, ← map_mul, kaU4S3_block_commute disjoint_compl_right (hm₁ s) (hm₂ t)]
  · intro s
    exact kaU4S3_fix_block h hn1 h2 (Or.inl rfl) (hm₁ s)
  · intro t
    exact kaU4S3_fix_block h hn1 h2 (Or.inr rfl) (hm₂ t)
  · intro c hc ho
    obtain ⟨x, hx, x', hx', rfl⟩ := kaU4S3_odd_decomp h hp2 h3 J (mem_fixSub.1 hc) ho
    obtain ⟨s, rfl⟩ : x ∈ ι₁.range := hr₁ ▸ hx
    obtain ⟨t, rfl⟩ : x' ∈ ι₂.range := hr₂ ▸ hx'
    exact ⟨s, t, rfl⟩
  · intro q hq hq2 P hP hinn
    exact kaU4S3_outTriv h h3 q hq hq2 P hP hinn

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
