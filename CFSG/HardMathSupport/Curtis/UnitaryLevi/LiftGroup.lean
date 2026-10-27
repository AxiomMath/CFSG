module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearConj
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CentralizerScalars

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank

section LiftGroup

variable {K : Type} [Field K] {n : ℕ} {Y : Type} [Group Y] {L : Subgroup Y}

@[expose] def Real (ρ : StatedSU n 2 K →* ↥L) (A : GL (Fin n) K) (u : Y) : Prop :=
  ∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
    (g' : GL (Fin n) K) = A * (g : GL (Fin n) K) * A⁻¹ ∧ u * (ρ g : Y) * u⁻¹ = (ρ g' : Y)

abbrev isoGroup (h : UnitaryFieldData 2 1 K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem real_one (ρ : StatedSU n 2 K →* ↥L) : Real ρ 1 1 := fun g =>
  ⟨g, by simp, by simp⟩

theorem real_mul {ρ : StatedSU n 2 K →* ↥L} {A A' : GL (Fin n) K} {u u' : Y}
    (h : Real ρ A u) (h' : Real ρ A' u') : Real ρ (A * A') (u * u') := fun g => by
  obtain ⟨g₁, hg₁, hρ₁⟩ := h' g
  obtain ⟨g₂, hg₂, hρ₂⟩ := h g₁
  refine ⟨g₂, ?_, ?_⟩
  · rw [hg₂, hg₁]
    group
  · calc u * u' * (ρ g : Y) * (u * u')⁻¹ = u * (u' * (ρ g : Y) * u'⁻¹) * u⁻¹ := by group
      _ = (ρ g₂ : Y) := by rw [hρ₁, hρ₂]

theorem real_inv {h : UnitaryFieldData 2 1 K} {ρ : StatedSU n 2 K →* ↥L} {A : GL (Fin n) K}
    {u : Y} (hA : A ∈ isoGroup h n) (hr : Real ρ A u) : Real ρ A⁻¹ u⁻¹ := fun g => by
  obtain ⟨g', hg', hρ⟩ := hr (conjSU h (inv_mem hA) g)
  have hgg : g' = g := by
    apply Subtype.ext
    rw [hg', coe_conjSU]
    group
  subst hgg
  refine ⟨conjSU h (inv_mem hA) g', by simp, ?_⟩
  rw [← hρ]
  group

variable [Finite K]

@[expose] def liftGroup (hK : Nat.card K = (2 ^ 1) ^ 2) (ρ : StatedSU n 2 K →* ↥L)
    (U : Subgroup Y) : Subgroup (GL (Fin n) K) where
  carrier := {A | A ∈ isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK
    le_rfl) n ∧ ∃ u ∈ U, Real ρ A u}
  mul_mem' := by
    rintro A A' ⟨hA, u, hu, hr⟩ ⟨hA', u', hu', hr'⟩
    exact ⟨mul_mem hA hA', u * u', mul_mem hu hu', real_mul hr hr'⟩
  one_mem' := ⟨one_mem _, 1, one_mem _, real_one ρ⟩
  inv_mem' := by
    rintro A ⟨hA, u, hu, hr⟩
    exact ⟨inv_mem hA, u⁻¹, inv_mem hu, real_inv hA hr⟩

theorem mem_liftGroup_iff (hK : Nat.card K = (2 ^ 1) ^ 2) (ρ : StatedSU n 2 K →* ↥L)
    (U : Subgroup Y) (A : GL (Fin n) K) :
    A ∈ liftGroup hK ρ U ↔
      (∀ x y : Fin n → K, stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq
        hK le_rfl) n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
          stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
            x y) ∧ ∃ u ∈ U, Real ρ A u := by
  rw [← mem_primeFormUnitary_one_iff_isometry]
  rfl

theorem isometry_of_mem_liftGroup {hK : Nat.card K = (2 ^ 1) ^ 2} {ρ : StatedSU n 2 K →* ↥L}
    {U : Subgroup Y} {A : GL (Fin n) K} (hA : A ∈ liftGroup hK ρ U) :
    A ∈ isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n :=
  hA.1

theorem exists_real_of_pow (hn : 4 ≤ n) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    {u : Y} (hu : u ∈ Subgroup.normalizer (L : Set Y)) {k : ℕ} (huk : u ^ 3 ^ k = 1) :
    ∃ A : GL (Fin n) K,
      A ∈ isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n ∧
      A ^ 3 ^ k ∈ StatedScalars (Fin n) K ∧ Real ρ A u := by
  obtain ⟨A, hA, hA3, hr⟩ := exists_unitary_conj_of_normalizer_pow hn hK ρ e hρe hu huk
  exact ⟨A, (mem_primeFormUnitary_one_iff_isometry _ A).mpr hA, hA3, hr⟩

theorem real_unique (hn : 4 ≤ n) (hK : Nat.card K = (2 ^ 1) ^ 2) (ρ : StatedSU n 2 K →* ↥L)
    (hρc : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K))
    {A A' : GL (Fin n) K} {u : Y} (h1 : Real ρ A u) (h2 : Real ρ A' u) :
    A⁻¹ * A' ∈ StatedScalars (Fin n) K := by
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by have := (Prod.mk.inj h).1; omega
  have hperf : Group.IsPerfect (StatedSU n (2 ^ 1) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn3 hnq
  refine scalar_of_conj_eq hK hn3 A A' ?_
  let f₁ : StatedSU n 2 K →* GL (Fin n) K :=
    (MulAut.conj A).toMonoidHom.comp (StatedSU n 2 K).subtype
  let f₂ : StatedSU n 2 K →* GL (Fin n) K :=
    (MulAut.conj A').toMonoidHom.comp (StatedSU n 2 K).subtype
  have key := eq_of_inv_mul_mem_center f₁ f₂ (fun g => by
    obtain ⟨g', hg'1, hg'2⟩ := h1 g
    obtain ⟨g'', hg''1, hg''2⟩ := h2 g
    have hρeq : (ρ g' : Y) = (ρ g'' : Y) := hg'2.symm.trans hg''2
    have hmem : ((g'⁻¹ * g'' : StatedSU n 2 K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
      rw [← hρc]
      have : ρ g' = ρ g'' := Subtype.ext hρeq
      rw [map_mul, map_inv, this, inv_mul_cancel]
      exact one_mem _
    have hf1 : f₁ g = (g' : GL (Fin n) K) := by
      rw [hg'1]; simp [f₁, MulAut.conj_apply]
    have hf2 : f₂ g = (g'' : GL (Fin n) K) := by
      rw [hg''1]; simp [f₂, MulAut.conj_apply]
    rw [hf1, hf2]
    have : (g' : GL (Fin n) K)⁻¹ * (g'' : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
      simpa using hmem
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at this)
  intro g
  have := DFunLike.congr_fun key g
  exact this

theorem exists_mem_liftGroup_real (hn : 4 ≤ n) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    {U : Subgroup Y} (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U) :
    ∀ u ∈ U, ∃ A ∈ liftGroup hK ρ U, Real ρ A u := by
  intro u hu
  obtain ⟨k, hk⟩ := hU3 ⟨u, hu⟩
  have huk : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨A, hA, -, hr⟩ := exists_real_of_pow hn hK ρ e hρe (hU hu) huk
  exact ⟨A, ⟨hA, u, hu, hr⟩, hr⟩

theorem scalar_pow_three (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ^ 3 = 1 := by
  have hc : c ^ 3 = 1 := by
    have h3 : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, hK]; norm_num
    rw [← h3]
    exact pow_card_eq_one'
  rw [← map_pow, hc, map_one]

theorem pow_eq_one_of_mem_liftGroup (hn : 4 ≤ n) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    (hρc : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K))
    {U : Subgroup Y} (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U)
    {A : GL (Fin n) K} (hA : A ∈ liftGroup hK ρ U) : ∃ k : ℕ, A ^ 3 ^ k = 1 := by
  obtain ⟨-, u, hu, hr⟩ := hA
  obtain ⟨k, hk⟩ := hU3 ⟨u, hu⟩
  have huk : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨A₀, -, hA₀, hr₀⟩ := exists_real_of_pow hn hK ρ e hρe (hU hu) huk
  obtain ⟨c, hc⟩ := real_unique hn hK ρ hρc hr₀ hr
  have hAc : A = A₀ * GeneralLinearGroup.scalar (Fin n) c := by
    rw [hc]; group
  have hcomm : Commute A₀ (GeneralLinearGroup.scalar (Fin n) c) := by
    refine Subgroup.mem_center_iff.mp ?_ A₀
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  obtain ⟨d, hd⟩ := hA₀
  refine ⟨k + 1, ?_⟩
  have h1 : A ^ 3 ^ k = GeneralLinearGroup.scalar (Fin n) (d * c ^ 3 ^ k) := by
    rw [hAc, hcomm.mul_pow, ← hd, map_mul, map_pow]
  rw [pow_succ, pow_mul, h1]
  exact scalar_pow_three hK _

theorem real_mem_iff {ρ : StatedSU n 2 K →* ↥L} {A : GL (Fin n) K} {u : Y} (hr : Real ρ A u)
    {P : Subgroup Y} (hu : u ∈ Subgroup.normalizer (P : Set Y)) {J : Subgroup (StatedSU n 2 K)}
    (hJ : ∀ y, y ∈ J ↔ (ρ y : Y) ∈ P) (y y' : StatedSU n 2 K)
    (hy : (y' : GL (Fin n) K) = A * (y : GL (Fin n) K) * A⁻¹) : y ∈ J ↔ y' ∈ J := by
  obtain ⟨g', hg', hρ⟩ := hr y
  have : g' = y' := Subtype.ext (hg'.trans hy.symm)
  subst this
  rw [hJ, hJ, ← hρ]
  exact Subgroup.mem_normalizer_iff.mp hu _

theorem mem_liftGroup_real_mem_iff {hK : Nat.card K = (2 ^ 1) ^ 2} {ρ : StatedSU n 2 K →* ↥L}
    {U P : Subgroup Y} (hUP : U ≤ Subgroup.normalizer (P : Set Y))
    {J : Subgroup (StatedSU n 2 K)} (hJ : ∀ y, y ∈ J ↔ (ρ y : Y) ∈ P)
    {A : GL (Fin n) K} (hA : A ∈ liftGroup hK ρ U) (y y' : StatedSU n 2 K)
    (hy : (y' : GL (Fin n) K) = A * (y : GL (Fin n) K) * A⁻¹) : y ∈ J ↔ y' ∈ J := by
  obtain ⟨-, u, hu, hr⟩ := hA
  exact real_mem_iff hr (hUP hu) hJ y y' hy

theorem real_commutes_scalar (ρ : StatedSU n 2 K →* ↥L)
    (hρc : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K))
    {hK : Nat.card K = (2 ^ 1) ^ 2} {U : Subgroup Y} {Dt : Subgroup (StatedSU n 2 K)}
    (hDtfix : ∀ u ∈ U, ∀ g ∈ Dt, u * (ρ g : Y) * u⁻¹ = (ρ g : Y))
    {A : GL (Fin n) K} (hA : A ∈ liftGroup hK ρ U) {x : StatedSU n 2 K} (hx : x ∈ Dt) :
    A * (x : GL (Fin n) K) * A⁻¹ * (x : GL (Fin n) K)⁻¹ ∈ StatedScalars (Fin n) K := by
  obtain ⟨-, u, hu, hr⟩ := hA
  obtain ⟨g', hg', hρ⟩ := hr x
  rw [← hg']
  have hρeq : ρ x = ρ g' := Subtype.ext ((hDtfix u hu x hx).symm.trans hρ)
  have hmem : ((x⁻¹ * g' : StatedSU n 2 K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
    rw [← hρc, map_mul, map_inv, hρeq, inv_mul_cancel]
    exact one_mem _
  have hs : (x : GL (Fin n) K)⁻¹ * (g' : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
    simpa using hmem
  have hc : (x : GL (Fin n) K)⁻¹ * (g' : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  have h1 : (g' : GL (Fin n) K) * (x : GL (Fin n) K)⁻¹ =
      (x : GL (Fin n) K)⁻¹ * (g' : GL (Fin n) K) := by
    have := Subgroup.mem_center_iff.mp hc (x : GL (Fin n) K)
    calc (g' : GL (Fin n) K) * (x : GL (Fin n) K)⁻¹
        = (x : GL (Fin n) K) * ((x : GL (Fin n) K)⁻¹ * (g' : GL (Fin n) K)) *
            (x : GL (Fin n) K)⁻¹ := by group
      _ = (x : GL (Fin n) K)⁻¹ * (g' : GL (Fin n) K) := by
        rw [this]; group
  rw [h1]
  exact hs

theorem mem_centralizer_of_real_one (ρ : StatedSU n 2 K →* ↥L) (hρ : Function.Surjective ρ)
    {c : Y} (hc : Real ρ 1 c) : c ∈ Subgroup.centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨g, hg⟩ := hρ ⟨y, hy⟩
  obtain ⟨g', hg', hρg⟩ := hc g
  have : g' = g := Subtype.ext (by rw [hg']; group)
  subst this
  rw [hg] at hρg
  have h1 : c * y * c⁻¹ = y := hρg
  calc y * c = c * y * c⁻¹ * c := by rw [h1]
    _ = c * y := by group

theorem commutator_mem_centralizer_of_real {hK : Nat.card K = (2 ^ 1) ^ 2}
    {ρ : StatedSU n 2 K →* ↥L} (hρ : Function.Surjective ρ) {U : Subgroup Y} {a b : Y}
    {Aa Ab : GL (Fin n) K} (hAa : Aa ∈ liftGroup hK ρ U) (hAb : Ab ∈ liftGroup hK ρ U)
    (hra : Real ρ Aa a) (hrb : Real ρ Ab b) (hcomm : Aa * Ab = Ab * Aa) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  have h1 : Real ρ (Aa * Ab * Aa⁻¹ * Ab⁻¹) (a * b * a⁻¹ * b⁻¹) :=
    real_mul (real_mul (real_mul hra hrb) (real_inv hAa.1 hra)) (real_inv hAb.1 hrb)
  have h2 : Aa * Ab * Aa⁻¹ * Ab⁻¹ = 1 := by
    rw [hcomm]; group
  rw [h2] at h1
  exact mem_centralizer_of_real_one ρ hρ h1

end LiftGroup

end CFSG.HardMathSupport.Curtis.UnitaryLevi
