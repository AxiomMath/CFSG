module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Open.StatedSUFieldChange
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

section Cover

variable {G H : Type*} [Group G] [Group H]

theorem cover_properties (hG : IsQuasisimple G) {φ : G →* H} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) :
    ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ ∧ Subgroup.center H = (Subgroup.center G).map φ ∧
      Nonempty (H ⧸ Subgroup.center H ≃* G ⧸ Subgroup.center G) := by
  have : Group.IsPerfect G := hG.1
  have hH : Group.IsPerfect H := Group.IsPerfect.ofSurjective hφ
  refine ⟨?_, center_eq_map_center_of_isQuasisimple hG hφ hker,
    ⟨(centralQuotientEquivOfIsQuasisimple hG hφ hker).symm⟩⟩
  rw [← commutator_def H]
  exact hH.commutator_eq_top

theorem coprime_three_card_center [Finite H] (h : ∀ x ∈ Subgroup.center H, x * x = 1) :
    (Nat.card (Subgroup.center H)).Coprime 3 := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => ?_)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center H) 3 h3
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h x x.2)
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at this
  omega

end Cover

private theorem charP_of_card_sq {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = (p ^ f) ^ 2) : CharP K p := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])

private theorem eq_unitaryInvolution {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ p ^ f) : σ = unitaryInvolution K p f :=
  RingEquiv.ext fun c => by rw [hσ c, unitaryInvolution_apply]

private theorem conj_mem_center_iff {G : Type*} [Group G] (P g : G) :
    P * g * P⁻¹ ∈ Subgroup.center G ↔ g ∈ Subgroup.center G := by
  constructor
  · intro h
    have := (Subgroup.center G).normal_of_characteristic.conj_mem _ h P⁻¹
    rwa [show P⁻¹ * (P * g * P⁻¹) * P⁻¹⁻¹ = g by group] at this
  · intro h
    exact (Subgroup.center G).normal_of_characteristic.conj_mem _ h P

theorem mem_center_SU_iff {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hq : ∃ p f : ℕ, p.Prime ∧ q = p ^ f)
    (z : SU σ 6) :
    z ∈ Subgroup.center (SU σ 6) ↔
      ∃ l : K, ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        l • (1 : Matrix (Fin 6) (Fin 6) K) := by
  constructor
  · intro hz
    obtain ⟨p, f, hp, rfl⟩ := hq
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP K p := charP_of_card_sq hK
    obtain rfl := eq_unitaryInvolution hσ
    set P := (exists_wittMatrix hK 6).choose
    let e : SU (unitaryInvolution K p f) 6 ≃* StatedSU 6 (p ^ f) K :=
      (conjEquiv P (exists_wittMatrix hK 6).choose_spec).trans
        (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 6))
    have hcen : e z ∈ Subgroup.center (StatedSU 6 (p ^ f) K) := by
      rw [← map_center_mulEquiv e]
      exact ⟨z, hz, rfl⟩
    rw [(isQuasisimple_statedSU_of_card hK (n := 6) (by norm_num) (by simp)).2,
      Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
    have hcoe : ((e z : StatedSU 6 (p ^ f) K) : GL (Fin 6) K) =
        P * (z : GL (Fin 6) K) * P⁻¹ := rfl
    rw [hcoe, conj_mem_center_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
    obtain ⟨u, hu⟩ := hcen
    refine ⟨(u : K), ?_⟩
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hu
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rintro ⟨l, hl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Units.ext
    simp [hl]

private theorem nonempty_equiv_statedProj_of_eq {c f p e : ℕ} [Fact c.Prime] [Fact p.Prime]
    (hc : c = p) (hf : f = e) {G : Type*} [Group G]
    (h : G ≃* StatedProj (StatedSU 6 (c ^ f) (GaloisField c (2 * f)))) :
    Nonempty (G ≃* StatedProj (StatedSU 6 (p ^ e) (GaloisField p (2 * e)))) := by
  subst hc hf
  exact ⟨h⟩

theorem su6_cover {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (Q : TauCeti.PrimePower) (hQ : Q.card = q)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 Q).Valid)
    {H : Type*} [Group H] (φ : SU σ 6 →* H) (hφ : Function.Surjective φ)
    (hker : ∀ x, φ x = 1 → x ∈ Subgroup.center (SU σ 6))
    (hsq : ∀ z ∈ Subgroup.center (SU σ 6), φ (z * z) = 1) :
    ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ ∧ (Nat.card (Subgroup.center H)).Coprime 3 ∧
      Nonempty (H ⧸ Subgroup.center H ≃*
        (TauCeti.CFSGIndex.lie (⟨.twistedA 5 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group) := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  subst hQ
  have hK' : Nat.card K = (Q.p ^ Q.exponent) ^ 2 := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K Q.p := charP_of_card_sq hK'
  obtain rfl := eq_unitaryInvolution fun c => (hσ c).trans (by rw [TauCeti.PrimePower.card_def])
  have hnq : (6, Q.p ^ Q.exponent) ≠ (3, 2) := by simp
  have hqs := isQuasisimple_statedSU_of_card (n := 6) hK' (by norm_num) hnq
  have hQS : IsQuasisimple (SU (unitaryInvolution K Q.p Q.exponent) 6) :=
    isQuasisimple_SU hK' (by norm_num) hnq
  obtain ⟨hperf, hcen, ⟨e₀⟩⟩ := cover_properties hQS hφ fun x hx => hker x hx
  haveI : Finite H := Finite.of_surjective φ hφ
  refine ⟨hperf, coprime_three_card_center fun x hx => ?_, ?_⟩
  · rw [hcen] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← map_mul]
    exact hsq z hz
  · let e₁ := centerQuotientEquivStatedProj hK' hqs.2
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype (GaloisField Q.p (2 * Q.exponent)) := Fintype.ofFinite _
    have hcard : Fintype.card K = Fintype.card (GaloisField Q.p (2 * Q.exponent)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        GaloisField.card Q.p (2 * Q.exponent) (by have := Q.exponent_pos; omega), hK', pow_mul']
    let e₂ := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hcard) 6 (Q.p ^ Q.exponent)
    obtain ⟨e₃⟩ := nonempty_equiv_statedProj_of_eq
      (TauCeti.LieTypeIndex.characteristic_twistedA 5 Q)
      (TauCeti.LieTypeIndex.fieldExponent_twistedA 5 Q)
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 Q hv)
    exact ⟨e₀.trans (e₁.trans (e₂.trans e₃.symm))⟩

end CFSG.LieType.Chevalley.E6A5Cube
