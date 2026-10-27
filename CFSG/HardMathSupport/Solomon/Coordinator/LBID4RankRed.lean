module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4Center

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open Matrix

@[expose] def LBID4Core : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 →
    ∀ g : GL (Fin 4 ⊕ Fin 4) K, g ∈ StatedOmega (StatedQuadPlus 4 K) → g ^ 3 = 1 →
      ∃ E : Subgroup (GL (Fin 4 ⊕ Fin 4) K), E ≤ StatedOmega (StatedQuadPlus 4 K) ∧
        IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ g ∈ E

theorem lbid4_three_ne_zero {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f) : (3 : K) ≠ 0 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 3 := by
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    exact (ringChar.spec K 3).mp h'
  have h3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp hdvd
  rw [h3] at hcard
  have hc : 3 ∣ p ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 3 n.ne_zero
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow hc)).symm

theorem lbid4_closure_preserves {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q₀ : (ι → K) → K} {A : GL ι K}
    (hA : A ∈ Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v}) :
    ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v := by
  induction hA using Subgroup.closure_induction with
  | mem A hA => exact hA
  | one => intro v; simp
  | mul A B _ _ hA hB => intro v; rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  | inv A _ hA =>
    intro v
    have h := hA ((↑(A⁻¹) : Matrix ι ι K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm

theorem lbid4_omega_preserves {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q₀ : (ι → K) → K} {A : GL ι K} (hA : A ∈ StatedOmega Q₀) :
    ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v := by
  refine lbid4_closure_preserves (Q₀ := Q₀) ?_
  set O := Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v}
  have hle : ⁅O, O⁆ ≤ O := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
  exact hle hA

theorem lbid4_scalar_sq {K : Type} [Field K] {A : GL (Fin 4 ⊕ Fin 4) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus 4 K)) (hs : A ∈ StatedScalars (Fin 4 ⊕ Fin 4) K) :
    A ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hs
  have h := lbid4_omega_preserves hA (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal,
    StatedQuadPlus, Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, Fin.reduceEq, add_zero, zero_add, mul_one,
    mul_zero] at h
  have hc : (c : K) ^ 2 = 1 := by linear_combination h
  rw [← map_pow]
  have hc' : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc, Units.val_one])
  rw [hc', map_one]

theorem lbid4_lift {K : Type} [Field K] (x : StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (hx : x ^ 3 = 1) :
    ∃ g : StatedOmega (StatedQuadPlus 4 K), g ^ 3 = 1 ∧ (QuotientGroup.mk g : StatedProj _) = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hz : y ^ 3 ∈ (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx]
  have hz2 : (y ^ 3) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.mem_subgroupOf] at hz
    have := lbid4_scalar_sq (y ^ 3).2 hz
    simpa using this
  refine ⟨y ^ 4, ?_, ?_⟩
  · calc (y ^ 4) ^ 3 = ((y ^ 3) ^ 2) ^ 2 := by rw [← pow_mul, ← pow_mul, ← pow_mul]
      _ = 1 := by rw [hz2, one_pow]
  · rw [QuotientGroup.mk_pow, pow_succ, hx, one_mul]

theorem lbid4_image {K : Type} [Field K] {E : Subgroup (GL (Fin 4 ⊕ Fin 4) K)}
    (hEH : E ≤ StatedOmega (StatedQuadPlus 4 K)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (g : StatedOmega (StatedQuadPlus 4 K))
    (hg : (g : GL (Fin 4 ⊕ Fin 4) K) ∈ E) :
    ∃ A : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K))), IsElemAbelian 3 A ∧
      Nat.card A = 3 ^ 4 ∧ (QuotientGroup.mk g : StatedProj _) ∈ A := by
  let φ : E →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
      (StatedOmega (StatedQuadPlus 4 K)))).comp (Subgroup.inclusion hEH)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have haN : Subgroup.inclusion hEH a ∈ (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
        (StatedOmega (StatedQuadPlus 4 K)) := (QuotientGroup.eq_one_iff _).mp ha
    rw [Subgroup.mem_subgroupOf] at haN
    have h2 : (a : GL (Fin 4 ⊕ Fin 4) K) ^ 2 = 1 := lbid4_scalar_sq (hEH a.2) haN
    have h3 : (a : GL (Fin 4 ⊕ Fin 4) K) ^ 3 = 1 := hE.2 _ a.2
    have h1 : (a : GL (Fin 4 ⊕ Fin 4) K) = 1 := by
      calc (a : GL (Fin 4 ⊕ Fin 4) K) = (a : GL (Fin 4 ⊕ Fin 4) K) ^ 3 *
          ((a : GL (Fin 4 ⊕ Fin 4) K) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h2, h3, inv_one, mul_one]
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  refine ⟨φ.range, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.1 b.2
    have := hE.1
    apply Subtype.ext
    change (a : StatedProj (StatedOmega (StatedQuadPlus 4 K))) * b = b * a
    rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm' a' b']
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hE.2 _ a.2)
    rw [this, map_one]
  · rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  · exact ⟨⟨g, hg⟩, rfl⟩

theorem lbid4_lift_center {X : Type} [Group X] [Finite X]
    (hZ : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ (3 ^ k) = 1 → z = 1)
    {x : X} (hx3 : x ^ 3 = 1) {A : Subgroup (X ⧸ Subgroup.center X)} (hA : IsElemAbelian 3 A)
    (hAcard : Nat.card A = 3 ^ 4) (hxA : (QuotientGroup.mk x : X ⧸ Subgroup.center X) ∈ A) :
    4 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center X
  have hZ3 : ¬ 3 ∣ Nat.card Z := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h
    have h1 : (z : X) ^ (3 ^ 1) = 1 := by
      rw [pow_one, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
    have h2 : (z : X) = 1 := hZ z z.2 1 h1
    have h3 : z = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hz
    exact absurd hz (by norm_num)
  set P : Subgroup X := A.comap (QuotientGroup.mk' Z)
  have hPcard : Nat.card P = Nat.card Z * 3 ^ 4 := by
    rw [← hAcard]
    exact QuotientGroup.card_preimage_mk Z (A : Set (X ⧸ Z))
  have hxP : x ∈ P := hxA
  set xP : P := ⟨x, hxP⟩
  have hxP3 : xP ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hx3)
  have hpg : IsPGroup 3 (Subgroup.zpowers xP) := by
    have hord : orderOf xP ∣ 3 := orderOf_dvd_of_pow_eq_one hxP3
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hScard : Nat.card S = 3 ^ 4 := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hZ3, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* X := P.subtype.comp (S : Subgroup P).subtype
  set φ : S →* A := ((QuotientGroup.mk' Z).comp ι).codRestrict A fun s => s.1.2
  have hcop : Nat.Coprime (Nat.card ((S : Subgroup P).map P.subtype)) (Nat.card Z) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
    exact Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hZ3)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' Z) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ Z := ⟨⟨s, s.2, rfl⟩, h2⟩
    rw [(Subgroup.disjoint_of_coprime_natCard hcop).eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h1))
  have := hA.1
  obtain ⟨hcomm, hpow⟩ := CFSG.SectionRank.comm_pow_of_injective (p := 3) hφ
    (fun a b => mul_comm' _ _)
    (fun a => Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hA.2 _ (φ a).2))
  have hxS : xP ∈ S := hS (Subgroup.mem_zpowers xP)
  set xS : S := ⟨xP, hxS⟩
  have hιx : ι xS = x := rfl
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hScard ι
    (Subtype.val_injective.comp Subtype.val_injective) ?_
  rintro _ ⟨s, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy, ← hιx, ← map_mul, ← map_mul, hcomm]

theorem inputD4_rank_of_core (hcore : LBID4Core) {X : Type} [Group X] [Finite X]
    (hZ : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ (3 ^ k) = 1 → z = 1)
    (hD : LocalBalance.Lemma27Ns.IsD4Type X) (x : X) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    4 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨p, f, hp3, hadm, K, _, _, hK, ⟨e⟩⟩ := hD
  have h3 : (3 : K) ≠ 0 := lbid4_three_ne_zero hadm.1 hp3 hK
  set xb : StatedProj (StatedOmega (StatedQuadPlus 4 K)) := e (QuotientGroup.mk x)
  have hxb : xb ^ 3 = 1 := by rw [← map_pow, ← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one,
    map_one]
  obtain ⟨g, hg3, hgx⟩ := lbid4_lift xb hxb
  have hg3' : (g : GL (Fin 4 ⊕ Fin 4) K) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, hg3, OneMemClass.coe_one]
  obtain ⟨E, hEH, hE, hEcard, hgE⟩ := hcore K h3 g g.2 hg3'
  obtain ⟨Ab, hAb, hAbcard, hgAb⟩ := lbid4_image hEH hE hEcard g hgE
  have _ := hx1
  refine lbid4_lift_center hZ hx3 (A := Ab.map e.symm.toMonoidHom) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · have := hAb.1
      infer_instance
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hAb.2 y hy, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hAbcard]
  · refine ⟨xb, ?_, ?_⟩
    · rw [← hgx]
      exact hgAb
    · simp [xb]

theorem inputD4_of_core (hG : GriessAllModelsStatement) (hcore : LBID4Core) :
    LocalBalance.Lemma27Ns.InputD4 := by
  intro X _ _ hq _ hD
  have hZ := lbiD4_center hG ⟨hq.1.commutator_eq_top, hq.2.1⟩ hD
  exact ⟨hZ, fun x hx3 hx1 => inputD4_rank_of_core hcore hZ hD x hx3 hx1⟩

end CFSG.HardMathSupport.Solomon.Coordinator
