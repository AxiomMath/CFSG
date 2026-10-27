module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace TorusE27

variable {K : Type} [Field K] {ω : K}

@[expose] def chi (ω : K) (x : ZMod 3) : K := ω ^ x.val

theorem pow_mod_three (hω : ω ^ 3 = 1) (n : ℕ) : ω ^ (n % 3) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hω, one_pow, one_mul]

theorem chi_add (hω : ω ^ 3 = 1) (x y : ZMod 3) : chi ω (x + y) = chi ω x * chi ω y := by
  rw [chi, chi, chi, ZMod.val_add, pow_mod_three hω, pow_add]

theorem chi_zero : chi ω 0 = 1 := by simp [chi]

theorem chi_injective (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : Function.Injective (chi ω) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf ω = 3 := orderOf_eq_prime hω hω1
  intro x y hxy
  apply ZMod.val_injective
  exact pow_injOn_Iio_orderOf (Set.mem_Iio.2 (by rw [ho]; exact ZMod.val_lt x))
    (Set.mem_Iio.2 (by rw [ho]; exact ZMod.val_lt y)) hxy

@[expose] def w4 (v : Fin 3 → ZMod 3) : Fin 4 → ZMod 3 := ![v 0, v 1, v 2, -(v 0 + v 1 + v 2)]

theorem w4_zero (v : Fin 3 → ZMod 3) : w4 v 0 = v 0 := rfl
theorem w4_one (v : Fin 3 → ZMod 3) : w4 v 1 = v 1 := rfl
theorem w4_two (v : Fin 3 → ZMod 3) : w4 v 2 = v 2 := rfl
theorem w4_three (v : Fin 3 → ZMod 3) : w4 v 3 = -(v 0 + v 1 + v 2) := rfl

theorem w4_add (v v' : Fin 3 → ZMod 3) : w4 (v + v') = w4 v + w4 v' := by
  funext i
  fin_cases i <;> simp [w4] <;> ring

theorem fix_omega (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (τ : K ≃+* K) (hτ : τ ^ 3 = 1) : τ ω = ω := by
  have h0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  have hq : ∀ t : K, t ^ 3 = 1 → t ≠ 1 → t ^ 2 + t + 1 = 0 := fun t ht ht1 => by
    have : (t - 1) * (t ^ 2 + t + 1) = 0 := by linear_combination ht
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht1)
  have hx3 : (τ ω) ^ 3 = 1 := by rw [← map_pow, hω, map_one]
  have hx1 : τ ω ≠ 1 := fun h => hω1 (τ.injective (by rw [h, map_one]))
  have hω2 := hq ω hω hω1
  have hx2 := hq _ hx3 hx1
  have hprod : (τ ω - ω) * (τ ω - ω ^ 2) = 0 := by linear_combination hx2 - (τ ω) * hω2 + hω
  rcases mul_eq_zero.1 hprod with h | h
  · exact sub_eq_zero.1 h
  · have hx : τ ω = ω ^ 2 := sub_eq_zero.1 h
    have h3 : (τ ^ 3) ω = τ (τ (τ ω)) := by rw [pow_succ, pow_succ, pow_one]; rfl
    rw [hτ, hx, map_pow, hx, ← pow_mul, map_pow, hx, ← pow_mul] at h3
    have h4 : ω = ω ^ 8 := h3
    have h5 : ω ^ 8 = ω ^ 2 := by
      rw [show 8 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
    have h12 : ω * (ω - 1) = 0 := by linear_combination (h4.trans h5).symm
    rcases mul_eq_zero.1 h12 with h | h
    · exact absurd h h0
    · exact absurd (sub_eq_zero.1 h) hω1

variable (hω : ω ^ 3 = 1)

include hω in
theorem det_torus (v : Fin 3 → ZMod 3) :
    (diagonal fun i => chi ω (w4 v i) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_four, ← chi_add hω, ← chi_add hω, ← chi_add hω]
  rw [w4_zero, w4_one, w4_two, w4_three,
    show v 0 + v 1 + v 2 + -(v 0 + v 1 + v 2) = 0 by ring, chi_zero]

noncomputable def slE4 : Multiplicative (Fin 3 → ZMod 3) →* SpecialLinearGroup (Fin 4) K where
  toFun v := ⟨diagonal fun i => chi ω (w4 v.toAdd i), det_torus hω v.toAdd⟩
  map_one' := Subtype.ext (by
    change (diagonal fun i => chi ω (w4 0 i) : Matrix (Fin 4) (Fin 4) K) = 1
    have : w4 (0 : Fin 3 → ZMod 3) = 0 := by funext i; fin_cases i <;> simp [w4]
    simp [this, chi_zero])
  map_mul' v w := Subtype.ext (by
    change (diagonal fun i => chi ω (w4 (v.toAdd + w.toAdd) i) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun i => chi ω (w4 v.toAdd i)) * diagonal fun i => chi ω (w4 w.toAdd i)
    rw [diagonal_mul_diagonal, w4_add]
    simp only [Pi.add_apply, chi_add hω])

include hω in
theorem projSlE4_injective (hω1 : ω ≠ 1) :
    Function.Injective ((proj 4 K).comp (slE4 hω)) := by
  refine (injective_iff_map_eq_one _).2 fun v hv => ?_
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hv)
  have h : ∀ i, chi ω (w4 v.toAdd i) = c := fun i => by
    have h1 : ((slE4 hω v : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
        chi ω (w4 v.toAdd i) := by
      change (diagonal fun i => chi ω (w4 v.toAdd i) : Matrix (Fin 4) (Fin 4) K) i i = _
      simp
    rw [← h1, hc]
    simp [scalar_apply]
  have hi : ∀ i, w4 v.toAdd i = w4 v.toAdd 0 := fun i =>
    chi_injective hω hω1 ((h i).trans (h 0).symm)
  have h1 := hi 1
  have h2 := hi 2
  have h3 := hi 3
  rw [w4_one, w4_zero] at h1
  rw [w4_two, w4_zero] at h2
  rw [w4_three, w4_zero] at h3
  have h0 : v.toAdd 0 = 0 := by
    rw [h1, h2] at h3
    have h3' : (3 : ZMod 3) * v.toAdd 0 = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
    linear_combination -h3 - h3'
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1.trans h0
  · exact h2.trans h0

include hω in
theorem map_slE4 (hω1 : ω ≠ 1) (τ : K ≃+* K) (hτ : τ ^ 3 = 1)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    SpecialLinearGroup.map τ.toRingHom (slE4 hω v) = slE4 hω v := by
  refine Subtype.ext ?_
  change (diagonal fun i => chi ω (w4 v.toAdd i) : Matrix (Fin 4) (Fin 4) K).map τ =
    diagonal fun i => chi ω (w4 v.toAdd i)
  rw [diagonal_map (map_zero τ)]
  simp only [chi, map_pow, fix_omega hω hω1 τ hτ]

end TorusE27

@[expose] def KFactOuterThreeRankFourRestSL4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankThreeList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .B 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .A 5 q) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 3 q) →
    LieClAut.FieldExponentThree d.1 →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81

theorem kFactOuterThreeRankFourRestSL_of_sl4 (h : KFactOuterThreeRankFourRestSL4) :
    KFactOuterThreeRankFourRestSL := by
  classical
  intro X _ _ d hd hl hB hA5 h3 he hc H hinn hα
  by_cases hA : ∀ q : TauCeti.PrimePower, d.1 ≠ .A 3 q
  · exact h X d hd hl hB hA5 hA h3 he hc H hinn hα
  push Not at hA
  obtain ⟨q, hq⟩ := hA
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  obtain ⟨e⟩ := he
  have hp : q.p = 2 := hd.1
  have hev : Even q.exponent := hl
  obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hp] at hK
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hunits : Nat.card Kˣ = 2 ^ q.exponent - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have h1 := Nat.one_le_two_pow (n := q.exponent)
  have h2 : 2 ∣ 2 ^ q.exponent := dvd_pow_self 2 q.exponent_pos.ne'
  have hcop : (Nat.card Kˣ).Coprime 4 := by
    rw [hunits, show 4 = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega)))
  have hpow : ∀ c : Kˣ, ∃ u : Kˣ, c = u ^ 4 := fun c =>
    ⟨(powCoprime hcop).symm c, ((powCoprime hcop).apply_symm_apply c).symm.trans
      (powCoprime_apply hcop _)⟩
  have h3d : 3 ∣ Nat.card Kˣ := by
    rw [hunits]
    have : 2 ^ q.exponent % 3 = 1 := by
      obtain ⟨k, hk⟩ := hev
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3d
  have hω : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one,
    Units.val_one]
  have hω1 : (u : K) ≠ 1 := fun h1 => by
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu
  let b : projectiveSL 4 K ≃* StatedProj (StatedSL 4 K) :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 4 K)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K)
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  exact LieClAut.exists_rankFour_psl (m := 4) (by norm_num) hpow (e'.trans b.symm) hc hinn hαH
    hαk hαn (TorusE27.slE4 hω) (TorusE27.projSlE4_injective hω hω1) SpE27.pow_three_eq_one
    SpE27.card_e27 (fun τ hτ a => TorusE27.map_slE4 hω hω1 τ hτ a)

theorem kFactTenElevenOneLieAutRes_of_rankFourSL4
    (hK : KFactOuterThreeRankFourRestSL4) (h2 : KFactTenElevenOneLieAutFieldTwo) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_rankFourSL (kFactOuterThreeRankFourRestSL_of_sl4 hK) h2

end CFSG.LocalAnalysis.RankThreeTheoremC
