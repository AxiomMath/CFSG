module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def piI6 (K : Type) [Field K] (p f : ℕ) :
    unitarySU p f K 6 →* StatedProj (unitarySU p f K 6) :=
  QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (unitarySU p f K 6))

theorem piI6_eq_one_scalar {p f : ℕ} {x : unitarySU p f K 6} (hx : piI6 K p f x = 1) :
    ∃ u : Kˣ, (x : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) u := by
  have hx' : (x : GL (Fin 6) K) ∈ StatedScalars (Fin 6) K := by
    have h := (QuotientGroup.eq_one_iff x).mp hx
    exact (Subgroup.mem_subgroupOf).mp h
  obtain ⟨u, hu⟩ := hx'
  exact ⟨u, hu.symm⟩

theorem bar_mul_eq_one_scalar_I (h : UnitaryFieldData p f K) {g : GL (Fin 6) K}
    (hg : g ∈ unitarySU p f K 6) (u : Kˣ)
    (hu : g = Matrix.GeneralLinearGroup.scalar (Fin 6) u) : h.bar (u : K) * (u : K) = 1 := by
  rw [unitarySU_eq_gramSU h 6] at hg
  have hiso := (mem_gramSU.mp hg).1
  rw [hu, Matrix.GeneralLinearGroup.coe_scalar] at hiso
  have hm : (Matrix.scalar (Fin 6) (u : K)).map h.bar = Matrix.scalar (Fin 6) (h.bar (u : K)) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar)]
  have ht : ∀ x : K, (Matrix.scalar (Fin 6) x)ᵀ = Matrix.scalar (Fin 6) x := fun x => by
    rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
  rw [hm, ht, Matrix.mul_one] at hiso
  have e := congrFun (congrFun hiso 0) 0
  simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] using e

theorem det_scalar_six (u : K) : (Matrix.scalar (Fin 6) u).det = u ^ 6 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp [Finset.prod_const]

theorem lift6 [Finite K] (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    {E : Subgroup (StatedProj (unitarySU p f K 6))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ P : Subgroup (unitarySU p f K 6), P.map (piI6 K p f) = E ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ 3 = 1) ∧ Nat.card P = 27 := by
  let E' : Subgroup (unitarySU p f K 6) := E.comap (piI6 K p f)
  let ρ : E' →* E := ((piI6 K p f).comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (e : StatedProj (unitarySU p f K 6))
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show piI6 K p f x ∈ E
      have hx' : piI6 K p f x = (e : StatedProj (unitarySU p f K 6)) := hx
      rw [hx']
      exact e.2
    · apply Subtype.ext
      exact hx
  have h27 : 3 ^ 3 ∣ Nat.card E' := by
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, hq, hc]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := E') 3 h27
  let P : Subgroup (unitarySU p f K 6) := Q.map E'.subtype
  have hcardP : Nat.card P = 27 := by
    rw [show P = Q.map E'.subtype from rfl,
      Subgroup.card_map_of_injective (f := E'.subtype) (Subgroup.subtype_injective E'), hQ]
    norm_num
  have hPmem : ∀ x ∈ P, piI6 K p f x ∈ E := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hinj : ∀ x ∈ P, piI6 K p f x = 1 → x = 1 := by
    intro x hx hpi
    obtain ⟨u, hu⟩ := piI6_eq_one_scalar hpi
    have hbarU : h.bar (u : K) * (u : K) = 1 := bar_mul_eq_one_scalar_I h x.2 u hu
    have hx27 : x ^ 27 = 1 := by
      have h' := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
      have h'' := congrArg Subtype.val h'
      rw [hcardP] at h''
      simpa using h''
    have hx27M : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 27 = 1 := by
      have := congrArg (fun g : unitarySU p f K 6 => ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hx27
      simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
    rw [hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_pow] at hx27M
    have hu27K : (u : K) ^ 27 = 1 := by
      have := congrFun (congrFun hx27M 0) 0
      simpa [Matrix.diagonal_apply_eq] using this
    have hdet : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      have hx2 : (x : GL (Fin 6) K) ∈ gramSU h 1 := by
        rw [← unitarySU_eq_gramSU h 6]
        exact x.2
      exact (mem_gramSU.mp hx2).2
    rw [hu, Matrix.GeneralLinearGroup.coe_scalar, det_scalar_six] at hdet
    have hu3K : (u : K) ^ 3 = 1 := by
      have hg := pow_gcd_eq_one.mpr (⟨hdet, hu27K⟩ : (u : K) ^ 6 = 1 ∧ (u : K) ^ 27 = 1)
      have hg3 : Nat.gcd 6 27 = 3 := by norm_num
      rw [hg3] at hg
      exact hg
    have hb : h.bar (u : K) = (u : K) := hbar _ hu3K
    rw [hb] at hbarU
    have hu1K : (u : K) = 1 := by
      have h3 : (u : K) ^ 3 = (u : K) := by
        rw [show (u : K) ^ 3 = (u : K) * ((u : K) * (u : K)) by ring, hbarU, mul_one]
      rw [← h3, hu3K]
    have hu1 : u = 1 := Units.ext hu1K
    apply Subtype.ext
    rw [Subgroup.coe_one, hu, hu1, map_one]
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : piI6 K p f (x * y) = piI6 K p f (y * x) := by
      rw [map_mul, map_mul]
      have h2 := congrArg Subtype.val
        (hE.1.is_comm.comm ⟨piI6 K p f x, hPmem x hx⟩ ⟨piI6 K p f y, hPmem y hy⟩)
      simpa using h2
    have hmem : (y * x)⁻¹ * (x * y) ∈ P :=
      mul_mem (inv_mem (mul_mem hy hx)) (mul_mem hx hy)
    have hpi : piI6 K p f ((y * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (inv_mul_eq_one.mp (hinj _ hmem hpi)).symm
  have hpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hPmem x hx)
  have hmapE : P.map (piI6 K p f) = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hPmem x hx
    · rw [card_map_eq_of_injOn (piI6 K p f) P hinj, hcardP, hc]
  exact ⟨P, hmapE, hcomm, hpow, hcardP⟩

@[expose] def WittEigen6 (h : UnitaryFieldData p f K) : Prop :=
  (∀ x : K, x ^ 3 = 1 → h.bar x = x) → (∃ ζ : K, IsPrimitiveRoot ζ 3) →
  ∀ P : Subgroup (GL (Fin 6) K), (∀ g ∈ P, g ∈ gramSU h (1 : Matrix (Fin 6) (Fin 6) K)) →
    (∀ g ∈ P, ∀ g' ∈ P, g * g' = g' * g) → (∀ g ∈ P, g ^ 3 = 1) → Nat.card P = 27 →
    ∃ R : GL (Fin 6) K, ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (R : Matrix (Fin 6) (Fin 6) K) =
      (hypJ : Matrix (Fin 6) (Fin 6) K) ∧ ∀ g ∈ P, R⁻¹ * g * R ∈ Dfull K

theorem conj_mem_hyp (h : UnitaryFieldData p f K) {R : GL (Fin 6) K}
    (hR : ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (R : Matrix (Fin 6) (Fin 6) K) =
      (hypJ : Matrix (Fin 6) (Fin 6) K))
    {g : GL (Fin 6) K} (hg : g ∈ gramSU h (1 : Matrix (Fin 6) (Fin 6) K)) :
    R⁻¹ * g * R ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  rw [mem_gramSU] at hg ⊢
  obtain ⟨hgi, hgd⟩ := hg
  rw [Matrix.mul_one] at hgi
  have F1 : (R : Matrix (Fin 6) (Fin 6) K).map h.bar *
      ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have F2 : (((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ *
      (hypJ : Matrix (Fin 6) (Fin 6) K) = (R : Matrix (Fin 6) (Fin 6) K) := by
    rw [← hR, ← Matrix.mul_assoc, ← Matrix.transpose_mul, F1, transpose_one, Matrix.one_mul]
  have F3 : ((g : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (g : Matrix (Fin 6) (Fin 6) K) = 1 := hgi
  have hRR : (R : Matrix (Fin 6) (Fin 6) K) * ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv R
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul,
      Matrix.transpose_mul]
    set A := ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ with hA
    set B := ((g : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ with hB
    set C := (((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ with hC
    set J := (hypJ : Matrix (Fin 6) (Fin 6) K) with hJ
    set D := ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hD
    set E' := (g : Matrix (Fin 6) (Fin 6) K) with hE
    set F' := (R : Matrix (Fin 6) (Fin 6) K) with hF
    calc A * (B * C) * J * (D * E' * F')
        = A * B * (C * J) * (D * E' * F') := by simp only [Matrix.mul_assoc]
      _ = A * B * F' * (D * E' * F') := by rw [F2]
      _ = A * B * (F' * D) * E' * F' := by simp only [Matrix.mul_assoc]
      _ = A * (B * E') * F' := by
          rw [show A * B * (F' * D) * E' * F' = A * B * (F' * D) * E' * F' from rfl, hRR]
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = A * F' := by rw [F3, Matrix.mul_one]
      _ = J := hR
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hgd, mul_one]
    have hd := congrArg Matrix.det hRR
    rw [Matrix.det_mul, Matrix.det_one] at hd
    rw [mul_comm]
    exact hd

theorem conj_mem_gram1 (h : UnitaryFieldData p f K) {R : GL (Fin 6) K}
    (hR : ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (R : Matrix (Fin 6) (Fin 6) K) =
      (hypJ : Matrix (Fin 6) (Fin 6) K))
    {X : GL (Fin 6) K} (hX : X ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) :
    R * X * R⁻¹ ∈ gramSU h (1 : Matrix (Fin 6) (Fin 6) K) := by
  rw [mem_gramSU] at hX ⊢
  obtain ⟨hXi, hXd⟩ := hX
  have F1 : (R : Matrix (Fin 6) (Fin 6) K).map h.bar *
      ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hRR : (R : Matrix (Fin 6) (Fin 6) K) * ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv R
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul,
      Matrix.transpose_mul]
    set Rb := (R : Matrix (Fin 6) (Fin 6) K).map h.bar with hRb
    set Rib := ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar with hRib
    set Xb := (X : Matrix (Fin 6) (Fin 6) K).map h.bar with hXb
    set Rm := (R : Matrix (Fin 6) (Fin 6) K) with hRm
    set Rinv := ((R⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hRinv
    set Xm := (X : Matrix (Fin 6) (Fin 6) K) with hXm
    set J := (hypJ : Matrix (Fin 6) (Fin 6) K) with hJ
    calc Ribᵀ * (Xbᵀ * Rbᵀ) * (Rm * Xm * Rinv)
        = Ribᵀ * (Xbᵀ * (Rbᵀ * Rm) * Xm) * Rinv := by simp only [Matrix.mul_assoc]
      _ = Ribᵀ * (Xbᵀ * J * Xm) * Rinv := by rw [hR]
      _ = Ribᵀ * J * Rinv := by rw [hXi]
      _ = Ribᵀ * (Rbᵀ * Rm) * Rinv := by rw [hR]
      _ = (Rb * Rib)ᵀ * (Rm * Rinv) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F1, transpose_one, hRR, Matrix.mul_one]
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hXd, mul_one]
    have hd := congrArg Matrix.det hRR
    rw [Matrix.det_mul, Matrix.det_one] at hd
    linear_combination hd

@[expose] noncomputable def conjIsoHyp (h : UnitaryFieldData p f K) {R : GL (Fin 6) K}
    (hR : ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (R : Matrix (Fin 6) (Fin 6) K) =
      (hypJ : Matrix (Fin 6) (Fin 6) K)) :
    unitarySU p f K 6 ≃* gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) where
  toFun g := ⟨R⁻¹ * (g : GL (Fin 6) K) * R, conj_mem_hyp h hR (by
    rw [← unitarySU_eq_gramSU h 6]; exact g.2)⟩
  invFun X := ⟨R * (X : GL (Fin 6) K) * R⁻¹, by
    rw [unitarySU_eq_gramSU h 6]
    exact conj_mem_gram1 h hR X.2⟩
  left_inv g := by
    apply Subtype.ext
    show R * (R⁻¹ * (g : GL (Fin 6) K) * R) * R⁻¹ = (g : GL (Fin 6) K)
    group
  right_inv X := by
    apply Subtype.ext
    show R⁻¹ * (R * (X : GL (Fin 6) K) * R⁻¹) * R = (X : GL (Fin 6) K)
    group
  map_mul' g g' := by
    apply Subtype.ext
    simp [mul_assoc]

theorem psuIso_map_scalars (h : UnitaryFieldData p f K) {R : GL (Fin 6) K}
    (hR : ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (R : Matrix (Fin 6) (Fin 6) K) =
      (hypJ : Matrix (Fin 6) (Fin 6) K)) :
    ((StatedScalars (Fin 6) K).subgroupOf (unitarySU p f K 6)).map (conjIsoHyp h hR).toMonoidHom =
      (StatedScalars (Fin 6) K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [StatedScalars, MonoidHom.mem_range] at hn
    obtain ⟨u, hu⟩ := hn
    change R⁻¹ * (n : GL (Fin 6) K) * R ∈ StatedScalars (Fin 6) K
    rw [← hu, StatedScalars, MonoidHom.mem_range]
    refine ⟨u, ?_⟩
    rw [(commute_scalar u R⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
  · intro hx
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨(conjIsoHyp h hR).symm x, ?_, by simp⟩
    show (conjIsoHyp h hR).symm x ∈ (StatedScalars (Fin 6) K).subgroupOf (unitarySU p f K 6)
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    change ∃ v : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) v = R * (x : GL (Fin 6) K) * R⁻¹
    refine ⟨u, ?_⟩
    rw [← hu, (commute_scalar u R).eq, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def psuIso (h : UnitaryFieldData p f K) {R : GL (Fin 6) K}
    (hR : ((R : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (R : Matrix (Fin 6) (Fin 6) K) =
      (hypJ : Matrix (Fin 6) (Fin 6) K)) :
    StatedProj (unitarySU p f K 6) ≃* PSUJ h :=
  QuotientGroup.congr ((StatedScalars (Fin 6) K).subgroupOf (unitarySU p f K 6))
    ((StatedScalars (Fin 6) K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)))
    (conjIsoHyp h hR) (psuIso_map_scalars h hR)

theorem kerConcl_unitary6_of_witt [Finite K] (h : UnitaryFieldData p f K)
    (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x) {ζu : Kˣ} (hζ : IsPrimitiveRoot (ζu : K) 3)
    (hK4 : 4 ≤ Nat.card K) (hW : WittEigen6 h)
    {E : Subgroup (StatedProj (unitarySU p f K 6))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) : KerConcl E := by
  obtain ⟨P, hPE, hcomm, hpow, hcard⟩ := lift6 h hbar hE hc
  have hP'mem : ∀ g ∈ P.map (unitarySU p f K 6).subtype,
      g ∈ gramSU h (1 : Matrix (Fin 6) (Fin 6) K) := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← unitarySU_eq_gramSU h 6]
    exact x.2
  have hP'comm : ∀ g ∈ P.map (unitarySU p f K 6).subtype,
      ∀ g' ∈ P.map (unitarySU p f K 6).subtype, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hg'
    have := hcomm x hx x' hx'
    have h2 := congrArg Subtype.val this
    exact h2
  have hP'pow : ∀ g ∈ P.map (unitarySU p f K 6).subtype, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    have := congrArg Subtype.val (hpow x hx)
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    exact this
  have hP'card : Nat.card (P.map (unitarySU p f K 6).subtype) = 27 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hcard]
  obtain ⟨R, hR, hconj⟩ := hW hbar ⟨(ζu : K), hζ⟩ _ hP'mem hP'comm hP'pow hP'card
  have himage : P.map (conjIsoHyp h hR).toMonoidHom =
      (Dfull K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_subgroupOf]
      exact hconj _ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    · rw [Subgroup.card_map_of_injective (conjIsoHyp h hR).injective, hcard]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Dfull_le h hbar)).toEquiv]
      exact (Dfull_card K ⟨ζu, hζ⟩).le
  have hkerE : E.map (psuIso h hR).toMonoidHom =
      ((Dfull K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h) := by
    rw [← hPE, Subgroup.map_map, ← himage, Subgroup.map_map]
    congr 1
  exact kerConcl_of_equiv (psuIso h hR) E (by rw [hkerE]; exact kerConcl_Dfull h hbar hζ hK4)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
