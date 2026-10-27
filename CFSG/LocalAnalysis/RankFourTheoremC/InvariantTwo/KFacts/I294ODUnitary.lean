module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODMatrix
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofBSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.Open I294OD
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul SUid mem_SUid)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

@[expose] def I294ODUnitaryTorus : Prop :=
  ∀ {p n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r],
    p.Prime → 5 ≤ n → Nat.card K = (r ^ f) ^ 2 → p ∣ r ^ f + 1 →
    ∀ B : GL (Fin n) K, B ∈ Uid (unitaryInvolution K r f) n → B ^ p = 1 →
      ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* StatedSU n (r ^ f) K,
        Function.Injective F ∧
        (∀ x, B * (F x : GL (Fin n) K) = (F x : GL (Fin n) K) * B) ∧
        ∀ x, (F x : GL (Fin n) K) ∈ StatedScalars (Fin n) K → F x = 1

@[expose] def I294ODUnitaryMonomial : Prop :=
  ∀ {p n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r],
    p.Prime → p ≠ 2 → Nat.card K = (r ^ f) ^ 2 → p ∣ r ^ f + 1 → p + 3 ≤ n →
    ∀ B : GL (Fin n) K, B ∈ Uid (unitaryInvolution K r f) n → ∀ c : Kˣ,
      B ^ p = GeneralLinearGroup.scalar (Fin n) c → (∀ b : K, b ^ p ≠ (c : K)) →
      ∃ T : Subgroup (StatedSU n (r ^ f) K), IsElemAbelian p T ∧
        p ^ (p + 1) ≤ Nat.card (T.map (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K)))) ∧
        ∀ g ∈ T, ∃ g' ∈ T, B * (g : GL (Fin n) K) * B⁻¹ = (g' : GL (Fin n) K)

section Unitary

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

@[expose] noncomputable def odUZ (K : Type) [Field K] (n r f : ℕ) [Fact r.Prime] [CharP K r]
    [Finite K] :
    Subgroup (Uid (unitaryInvolution K r f) n) :=
  (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range.subgroupOf
    (Uid (unitaryInvolution K r f) n)

theorem mem_odUZ {B : Uid (unitaryInvolution K r f) n} :
    B ∈ odUZ K n r f ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = (B : GL (Fin n) K) :=
  Iff.rfl

theorem od_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h : (m + 1) ^ 2 = (m + 1 + 1) * (m + 1 - 1) + 1 := by
    rw [Nat.add_sub_cancel]
    ring
  omega

theorem od_unitary_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1) {b c : Kˣ} (hbc : b ^ p = c)
    (hc : c ^ (r ^ f + 1) = 1) : b ^ (r ^ f + 1) = 1 := by
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ (Fact.out : r.Prime).pos
  have hb : b ^ ((r ^ f + 1) * (r ^ f - 1)) = 1 := by
    rw [← od_sq_sub_one _ hq1, ← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have hd1 : (b ^ (r ^ f + 1)) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hbc, hc]
  have hd2 : (b ^ (r ^ f + 1)) ^ (r ^ f - 1) = 1 := by
    rw [← pow_mul]
    exact hb
  have hcop : Nat.Coprime p (r ^ f - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h2 : p ∣ 2 := by
      have h3 : r ^ f + 1 = (r ^ f - 1) + 2 := by omega
      rw [h3] at hpq
      exact (Nat.dvd_add_right h).1 hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have h4 := pow_gcd_eq_one.2 ⟨hd1, hd2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h4

theorem od_unitary_nonpower {p : ℕ} (hn1 : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1)
    {B : Uid (unitaryInvolution K r f) n} (hBZ : B ^ p ∈ odUZ K n r f)
    (hBnp : ∀ w ∈ odUZ K n r f, w ^ p ≠ B ^ p) :
    ∃ c : Kˣ, (B : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c ∧
      ∀ b : K, b ^ p ≠ (c : K) := by
  obtain ⟨c, hc⟩ := mem_odUZ.1 hBZ
  have hBp : (B : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c := by
    rw [hc]
    rfl
  have hcu : c ^ (r ^ f + 1) = 1 := by
    refine l212in_scalar_unitary hn1 ?_
    rw [hc]
    exact (B ^ p).2
  refine ⟨c, hBp, fun b hb => ?_⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (c : K) = 0 := by rw [← hb]; exact zero_pow hp.ne_zero
    exact c.ne_zero h0
  have hb'p : Units.mk0 b hb0 ^ p = c := Units.ext (by simpa using hb)
  have hb'q : Units.mk0 b hb0 ^ (r ^ f + 1) = 1 := od_unitary_pow_eq_one hp hp2 hK hpq hb'p hcu
  have hsc : GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) ∈
      Uid (unitaryInvolution K r f) n := (l212in_scalar_mem_Uid_iff hn1 _).2 hb'q
  refine hBnp ⟨_, hsc⟩ (mem_odUZ.2 ⟨Units.mk0 b hb0, rfl⟩) (Subtype.ext ?_)
  show (GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0)) ^ p = (B : GL (Fin n) K) ^ p
  rw [← map_pow, hb'p, hBp]

theorem od_unitary_matrix_pow {p : ℕ} {B : GL (Fin n) K} {c : Kˣ}
    (hBp : B ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    (B : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) (c : K) := by
  have h1 := congrArg Units.val hBp
  rw [GeneralLinearGroup.coe_scalar] at h1
  rw [← Units.val_pow_eq_pow_val, h1]

theorem odFamily_unitary_of_inputs {p : ℕ} (hT : I294ODUnitaryTorus)
    (hM : I294ODUnitaryMonomial) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ n) (hn0 : 0 < n)
    (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1) :
    ODFamily p n
      (l212in_suPhi hK :
        Uid (unitaryInvolution K r f) n →* MulAut (StatedProj (StatedSU n (r ^ f) K)))
      (l212in_detU : Uid (unitaryInvolution K r f) n →* rootsOfUnity (r ^ f + 1) K)
      (odUZ K n r f) := by
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  have hn1 : 1 ≤ n := hn0
  have hp2 : p ≠ 2 := by omega
  have hpK : p ∣ Nat.card K - 1 := by
    have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ (Fact.out : r.Prime).pos
    rw [hK, od_sq_sub_one _ hq1]
    exact Dvd.dvd.mul_right hpq _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ψ, hψ⟩ := l212in_aut_su_hom hn5 hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz B
    obtain ⟨c, hc⟩ := mem_odUZ.1 hz
    apply Subtype.ext
    show (z : GL (Fin n) K) * (B : GL (Fin n) K) = (B : GL (Fin n) K) * (z : GL (Fin n) K)
    rw [← hc]
    exact (l212in_scalar_comm (B : GL (Fin n) K) c).symm
  ·
    intro B
    constructor
    · intro hB
      have hconj : ∀ g : StatedSU n (r ^ f) K,
          ∃ hg : (B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ ∈
            StatedSU n (r ^ f) K,
          (QuotientGroup.mk ⟨_, hg⟩ : StatedProj (StatedSU n (r ^ f) K)) =
            QuotientGroup.mk g := by
        intro g
        refine ⟨l212in_conj_mem_statedSU hK B.2 g.2, ?_⟩
        have h1 : l212in_suPhi hK B (QuotientGroup.mk g) =
            (1 : MulAut (StatedProj (StatedSU n (r ^ f) K))) (QuotientGroup.mk g) := by rw [hB]
        rw [l212in_suPhi_mk, MulAut.one_apply] at h1
        exact h1
      obtain ⟨z, hz⟩ := l212in_conj_scalar_su hn5 hK B ((mem_Uid_iff _ _ _).1 B.2) hconj
      exact mem_odUZ.2 ⟨z, hz.symm⟩
    · intro hB
      obtain ⟨c, hc⟩ := mem_odUZ.1 hB
      ext y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [l212in_suPhi_mk, MulAut.one_apply]
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      rw [l212in_suConj_coe, ← hc, ← l212in_scalar_comm (g : GL (Fin n) K) c, mul_inv_cancel_right]
  ·
    intro w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c, hc⟩ := mem_odUZ.1 hz
      have hcu : c ^ (r ^ f + 1) = 1 := by
        refine l212in_scalar_unitary hn1 ?_
        rw [hc]
        exact z.2
      refine ⟨⟨c, (mem_rootsOfUnity _ _).2 hcu⟩, ?_⟩
      apply Subtype.ext
      show GeneralLinearGroup.det (z : GL (Fin n) K) = c ^ n
      rw [← hc, l212in_det_scalar]
    · rintro ⟨c, rfl⟩
      have hcu : (c : Kˣ) ^ (r ^ f + 1) = 1 := (mem_rootsOfUnity _ _).1 c.2
      have hsc : GeneralLinearGroup.scalar (Fin n) (c : Kˣ) ∈ Uid (unitaryInvolution K r f) n :=
        (l212in_scalar_mem_Uid_iff hn1 _).2 hcu
      refine ⟨⟨_, hsc⟩, mem_odUZ.2 ⟨c, rfl⟩, ?_⟩
      apply Subtype.ext
      show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) (c : Kˣ)) = (c : Kˣ) ^ n
      rw [l212in_det_scalar]
  ·
    intro x y
    set γ := x * y * x⁻¹ * y⁻¹ with hγ
    have h1 : ψ γ = 1 := by
      rw [hγ, map_mul, map_mul, map_mul, map_inv, map_inv, l212in_ringAut_comm (ψ x) (ψ y),
        mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨B, hB, hrep⟩ := (hψ γ).1
    refine ⟨⟨B, (mem_Uid_iff _ _ _).2 hB⟩, ?_⟩
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨hg, hγg⟩ := hrep g
    rw [hγg, l212in_suPhi_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show B * (g : GL (Fin n) K) * B⁻¹ = B * glAut (ψ γ) (g : GL (Fin n) K) * B⁻¹
    rw [h1, map_one, MulAut.one_apply]
  ·
    rintro B ⟨c, hc⟩
    have hc' : GeneralLinearGroup.det (B : GL (Fin n) K) = (c : Kˣ) ^ n := congrArg Subtype.val hc
    have hcu : (c : Kˣ) ^ (r ^ f + 1) = 1 := (mem_rootsOfUnity _ _).1 c.2
    have hsc : GeneralLinearGroup.scalar (Fin n) (c : Kˣ) ∈ Uid (unitaryInvolution K r f) n :=
      (l212in_scalar_mem_Uid_iff hn1 _).2 hcu
    have hB'U : (B : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ ∈
        Uid (unitaryInvolution K r f) n := mul_mem B.2 (inv_mem hsc)
    have hB'S : (B : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ ∈
        StatedSU n (r ^ f) K := by
      rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n]
      refine mem_SUid.2 ⟨?_, (mem_Uid_iff _ _ _).1 hB'U⟩
      have hdet : GeneralLinearGroup.det ((B : GL (Fin n) K) *
          (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹) = 1 := by
        rw [map_mul, map_inv, l212in_det_scalar, hc', mul_inv_cancel]
      rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
    refine ⟨QuotientGroup.mk ⟨_, hB'S⟩, ?_⟩
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, l212in_suPhi_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    have hs : (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ * (g : GL (Fin n) K) *
        GeneralLinearGroup.scalar (Fin n) (c : Kˣ) = g := by
      rw [mul_assoc, l212in_scalar_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [l212in_suConj_coe, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
    calc _ = (B : GL (Fin n) K) * ((GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ * g *
          GeneralLinearGroup.scalar (Fin n) (c : Kˣ)) * (B : GL (Fin n) K)⁻¹ := by group
      _ = _ := by rw [hs]
  ·
    intro ℓ
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective ℓ
    have hsS : (s : GL (Fin n) K) ∈ SUid (unitaryInvolution K r f) n := by
      rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n]
      exact s.2
    have hsU : (s : GL (Fin n) K) ∈ Uid (unitaryInvolution K r f) n :=
      CFSG.ComponentClassification.CatalogueBUnitaryIsometry.SUid_le_Uid _ _ hsS
    refine ⟨⟨s, hsU⟩, ?_, ?_⟩
    · apply Subtype.ext
      show GeneralLinearGroup.det (s : GL (Fin n) K) = 1
      refine Units.ext ?_
      rw [GeneralLinearGroup.val_det_apply, Units.val_one]
      exact (mem_SUid.1 hsS).1
    · ext z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
      rw [l212in_suPhi_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      simp only [l212in_suConj_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  ·
    intro γ
    obtain ⟨σ, B, hB, hg⟩ := l212in_aut_su hn5 hK γ
    choose hmem hγ using hg
    obtain ⟨ρ, hρ⟩ := l212in_exists_zpow_units σ
    have hBU : B ∈ Uid (unitaryInvolution K r f) n := (mem_Uid_iff _ _ _).2 hB
    let t : Uid (unitaryInvolution K r f) n →* Uid (unitaryInvolution K r f) n :=
      { toFun := fun B' => ⟨B * glAut σ (B' : GL (Fin n) K) * B⁻¹,
          mul_mem (mul_mem hBU (l212in_glAut_mem_Uid σ B'.2)) (inv_mem hBU)⟩
        map_one' := Subtype.ext (by
          show B * glAut σ (1 : GL (Fin n) K) * B⁻¹ = 1
          rw [map_one, mul_one, mul_inv_cancel])
        map_mul' := fun g h => Subtype.ext (by
          show B * glAut σ ((g : GL (Fin n) K) * (h : GL (Fin n) K)) * B⁻¹ =
            (B * glAut σ (g : GL (Fin n) K) * B⁻¹) * (B * glAut σ (h : GL (Fin n) K) * B⁻¹)
          rw [map_mul]
          group) }
    refine ⟨ρ, t, ?_, ?_, ?_⟩
    · intro B'
      have key : γ * l212in_suPhi hK B' = l212in_suPhi hK (t B') * γ := by
        ext z
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
        rw [MulAut.mul_apply, MulAut.mul_apply, l212in_suPhi_mk, hγ, hγ g, l212in_suPhi_mk]
        refine congrArg QuotientGroup.mk (Subtype.ext ?_)
        show B * glAut σ ((B' : GL (Fin n) K) * (g : GL (Fin n) K) * (B' : GL (Fin n) K)⁻¹) *
            B⁻¹ =
          (B * glAut σ (B' : GL (Fin n) K) * B⁻¹) * (B * glAut σ (g : GL (Fin n) K) * B⁻¹) *
            (B * glAut σ (B' : GL (Fin n) K) * B⁻¹)⁻¹
        simp only [map_mul, map_inv]
        group
      exact mul_inv_eq_iff_eq_mul.2 key
    · intro B'
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      change GeneralLinearGroup.det (B * glAut σ (B' : GL (Fin n) K) * B⁻¹) =
        (GeneralLinearGroup.det (B' : GL (Fin n) K)) ^ ρ
      rw [map_mul, map_mul, map_inv, l212in_det_glAut, hρ, mul_right_comm, mul_inv_cancel,
        one_mul]
    · intro z hz
      obtain ⟨c, hc⟩ := mem_odUZ.1 hz
      apply Subtype.ext
      show B * glAut σ (z : GL (Fin n) K) * B⁻¹ =
        ((z ^ ρ : Uid (unitaryInvolution K r f) n) : GL (Fin n) K)
      rw [Subgroup.coe_zpow, ← hc, l212in_glAut_scalar, l212in_conj_scalar, hρ,
        ← map_zpow (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) c ρ]
  ·
    intro B hB
    have hBp : (B : GL (Fin n) K) ^ p = 1 := by
      have h1 := congrArg Subtype.val hB
      simpa using h1
    obtain ⟨F, hFi, hFc, hFs⟩ := hT hp hn5 hK hpq (B : GL (Fin n) K) B.2 hBp
    refine ⟨(QuotientGroup.mk' _).comp F, ?_, fun a => ?_⟩
    · rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : F x ∈ (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).ker := hx
      rw [QuotientGroup.ker_mk'] at h1
      exact (injective_iff_map_eq_one F).1 hFi x (hFs x (Subgroup.mem_subgroupOf.1 h1))
    · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, l212in_suPhi_mk]
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      rw [l212in_suConj_coe, hFc a, mul_assoc, mul_inv_cancel, mul_one]
  ·
    intro hn3 B hBZ hBnp
    obtain ⟨c, hBp, hnp⟩ := od_unitary_nonpower hn1 hp hp2 hK hpq hBZ hBnp
    obtain ⟨T, hTe, hTcard, hTnorm⟩ := hM hp hp2 hK hpq hn3 (B : GL (Fin n) K) B.2 c hBp hnp
    refine ⟨T.map (QuotientGroup.mk' _), IsElemAbelian.map hTe _, hTcard, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hTnorm g hg
    refine ⟨g', hg', ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, l212in_suPhi_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by rw [l212in_suConj_coe]; exact hgg'.symm))
  ·
    intro hnp B hBZ hBnp c
    subst hnp
    obtain ⟨c0, hBp, hζ⟩ := od_unitary_nonpower hn1 hp hp2 hK hpq hBZ hBnp
    have hdet := det_eq_of_pow_eq hp hp2 hζ (od_unitary_matrix_pow hBp)
    intro hc
    have hc' : GeneralLinearGroup.det (B : GL (Fin n) K) = (c : Kˣ) ^ n := congrArg Subtype.val hc
    refine hζ ((c : Kˣ) : K) ?_
    rw [← hdet, ← GeneralLinearGroup.val_det_apply, hc', Units.val_pow_eq_pow_val]
  ·
    intro hnp A B hBZ hBnp hAB hAp
    subst hnp
    obtain ⟨c0, hBp, hζ⟩ := od_unitary_nonpower hn1 hp hp2 hK hpq hBZ hBnp
    have hA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ n = 1 := by
      have h1 : (A : GL (Fin n) K) ^ n = 1 := by simpa using congrArg Subtype.val hAp
      have h2 := congrArg Units.val h1
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
    have hAB' : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : GL (Fin n) K) =
        (B : GL (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have h1 : (A : GL (Fin n) K) * (B : GL (Fin n) K) =
          (B : GL (Fin n) K) * (A : GL (Fin n) K) := congrArg Subtype.val hAB
      have h2 := congrArg Units.val h1
      rwa [Units.val_mul, Units.val_mul] at h2
    obtain ⟨μ, hμ⟩ := scalar_of_commute hp hpK hζ (od_unitary_matrix_pow hBp) hA hAB'
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      have h1 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
        Units.mul_inv (A : GL (Fin n) K)
      rw [hμ] at h1
      simp at h1
    refine mem_odUZ.2 ⟨Units.mk0 μ hμ0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, hμ]
    rfl

theorem od_unitary_false {p n q : ℕ} [hpp : Fact p.Prime] (hT : I294ODUnitaryTorus)
    (hM : I294ODUnitaryMonomial) (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    (L : Subgroup X) [L.Normal] (hnab : ∃ a b : L, a * b ≠ b * a)
    (hcen : centralizer (L : Set X) = ⊥) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {z g : X} (hz : z ∈ D) (hz1 : z ≠ 1)
    (hg : CFSG.LocalAnalysis.RankThreeTheoremC.IsPlaneDiagonal p D z g) {x : X} (hxD : x ∈ D)
    (hx1 : x ≠ 1) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) {K : Type}
    [Field K] [Finite K] (hKq : Nat.card K = q ^ 2) (hpn : p ∣ n) (hpq : p ∣ q + 1)
    (e : L ≃* StatedProj (StatedSU n q K)) : False := by
  have hp : p.Prime := hpp.out
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · obtain ⟨a, b, hab⟩ := hnab
      haveI : Nontrivial L := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      haveI : Subsingleton (StatedProj (StatedSU 0 q K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact hn0
  obtain ⟨r, m, hr, hchar, -, hKr⟩ := exists_char_pow_card K
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
    refine (Nat.dvd_prime_pow hr).1 ?_
    rw [← hKr, hKq]
    exact dvd_pow_self q two_ne_zero
  subst hqf
  exact od_core ((odFamily_unitary_of_inputs hT hM hp hp5 hpn hn0 hKq hpq).transport e.symm) hp5
    hpn hn0 hcen hD hDcard hz hz1 hg hxD hx1 hx2

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC
