module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWInvolution
public import CFSG.RankThree.PartOne.K128.D4Syl

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.K128 CFSG.GH74.GLS.Stage2.Bender.Thm1

section Homocyclic

lemma card_pow_eq_one_zmod (r e : ℕ) [Fact r.Prime] (he : 1 ≤ e) :
    Nat.card {x : Multiplicative (ZMod (r ^ e)) // x ^ r = 1} = r := by
  have hr : r.Prime := Fact.out
  have : NeZero (r ^ e) := ⟨pow_ne_zero _ hr.ne_zero⟩
  classical
  have hcardA : Nat.card (Multiplicative (ZMod (r ^ e))) = r ^ e := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hle : Nat.card {x : Multiplicative (ZMod (r ^ e)) // x ^ r = 1} ≤ r := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hr.pos
  have hge : r ≤ Nat.card {x : Multiplicative (ZMod (r ^ e)) // x ^ r = 1} := by
    have hdvd : r ∣ Nat.card (Multiplicative (ZMod (r ^ e))) := by
      rw [hcardA]
      exact dvd_pow_self r (by omega)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hsub : ∀ x ∈ Subgroup.zpowers g, x ^ r = 1 := by
      rintro x ⟨k, rfl⟩
      have h1 : g ^ r = 1 := by
        have := pow_orderOf_eq_one g
        rwa [hg] at this
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
    have hinj : Function.Injective
        (fun x : Subgroup.zpowers g => (⟨(x : Multiplicative (ZMod (r ^ e))), hsub _ x.2⟩ :
          {x : Multiplicative (ZMod (r ^ e)) // x ^ r = 1})) := by
      intro a b h
      exact Subtype.ext (Subtype.mk.inj h)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_zpowers, hg] at this
  omega

lemma card_ker_pow_pi (r e : ℕ) [Fact r.Prime] (he : 1 ≤ e) :
    Nat.card (powMonoidHom r : (Fin 2 → Multiplicative (ZMod (r ^ e))) →* _).ker = r ^ 2 := by
  have h1 : Nat.card (powMonoidHom r : (Fin 2 → Multiplicative (ZMod (r ^ e))) →* _).ker =
      Nat.card {f : Fin 2 → Multiplicative (ZMod (r ^ e)) // f ^ r = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => by simp [MonoidHom.mem_ker])
  have h2 : {f : Fin 2 → Multiplicative (ZMod (r ^ e)) // f ^ r = 1} ≃
      (Fin 2 → {x : Multiplicative (ZMod (r ^ e)) // x ^ r = 1}) :=
    (Equiv.subtypeEquivRight fun f => by
      rw [funext_iff]
      simp only [Pi.pow_apply, Pi.one_apply]).trans
      (Equiv.subtypePiEquivPi (p := fun _ (x : Multiplicative (ZMod (r ^ e))) => x ^ r = 1))
  rw [h1, Nat.card_congr h2, Nat.card_pi, Fin.prod_univ_two, card_pow_eq_one_zmod r e he, sq]

lemma exists_plane_of_sylowShape_gen {G : Type*} [Group G] {r e : ℕ} [Fact r.Prime]
    (he : 1 ≤ e) (S : Subgroup G) (φ : S ≃* (Fin 2 → Multiplicative (ZMod (r ^ e)))) :
    ∃ E : Subgroup G, E ≤ S ∧ (∀ x ∈ E, x ^ r = 1) ∧ Nat.card E = r ^ 2 := by
  let E₀ : Subgroup (Fin 2 → Multiplicative (ZMod (r ^ e))) := (powMonoidHom r).ker
  let E : Subgroup G := (E₀.map φ.symm.toMonoidHom).map S.subtype
  have hmem : ∀ x : G, x ∈ E ↔ ∃ v ∈ E₀, ((φ.symm v : S) : G) = x := by
    intro x
    simp only [E, Subgroup.mem_map, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have hv : ∀ v ∈ E₀, v ^ r = 1 := fun v hv => by
    simpa [E₀, MonoidHom.mem_ker, powMonoidHom_apply] using hv
  refine ⟨E, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨v, -, rfl⟩ := (hmem x).1 hx
    exact (φ.symm v).2
  · intro x hx
    obtain ⟨v, hv', rfl⟩ := (hmem x).1 hx
    rw [← Subgroup.coe_pow, ← map_pow, hv v hv', map_one]
    rfl
  · rw [Subgroup.card_map_of_injective (Subtype.val_injective),
      Subgroup.card_map_of_injective φ.symm.injective]
    exact card_ker_pow_pi r e he

end Homocyclic



theorem exists_phi6_plane_with_involution {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    ∃ F : D4PhiFrame K σ (ℓ ^ f) (-1),
      ∃ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (∀ x ∈ E, x ^ r = 1) ∧ Nat.card E = r ^ 2 ∧
        (∀ y ∈ E, F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0 ∈
          twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr)) ∧
        ∃ w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          w * w = 1 ∧ ∀ y ∈ E, w * y * w⁻¹ = y⁻¹ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (by omega : 1 ≤ f * 3) (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨n, hn, w, hnW, hw, g0, hg0C, hg0, hperf, hconj⟩ :=
    d4T36_frame hf K hK σ hσ (Or.inr rfl) hr hr3 hrd L
  let F : D4PhiFrame K σ (ℓ ^ f) (-1) :=
    ⟨iterateFrobenius L ℓ f, fun c => iterateFrobenius_def ℓ f c, n, hn, w, hnW, hw, g0, hg0C,
      hg0, hperf⟩
  have hshape := sylowShape_D4_36 (ℓ := ℓ) hf K hK σ hσ (ε := -1) (Or.inr rfl) hr hr3 hrd
  have hd0 : d4T36d (-1) (ℓ ^ f) ≠ 0 := ((d4T36d_odd (Or.inr rfl) hq1).pos).ne'
  have hdvd : r ∣ d4T36d (-1) (ℓ ^ f) := by
    have h := d4T36d_cast (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) hq1
    rw [← h] at hrd
    exact_mod_cast hrd
  have he : 1 ≤ (d4T36d (-1) (ℓ ^ f)).factorization r :=
    (hr.factorization_pos_of_dvd hd0 hdvd)
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := inferInstance
  let S : Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := default
  obtain ⟨φ⟩ := hshape ((S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    S.isPGroup' S.not_dvd_index
  obtain ⟨E₁, hE₁S, hE₁p, hE₁c⟩ := exists_plane_of_sylowShape_gen he
    (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) φ
  have hE₁P : IsPGroup r E₁ := S.isPGroup'.to_le hE₁S
  obtain ⟨c, hc⟩ := hconj E₁ hE₁P
  have htor : ∀ y ∈ E₁.map (MulAut.conj c).toMonoidHom,
      F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0 ∈
        twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  obtain ⟨s, -, w, -, hww, hinv⟩ := exists_involution_inverting_torus hq1 F
  refine ⟨F, E₁.map (MulAut.conj c).toMonoidHom, ?_, ?_, htor, w, hww, fun y hy => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    change (c * y * c⁻¹) ^ r = 1
    rw [conj_pow, hE₁p y hy]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hE₁c
  · have h := hinv y (htor y hy)
    apply triEmb_injective (K := K) (σ := σ) (L := AlgebraicClosure K)
    rw [map_inv]
    have h2 : (F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0)⁻¹ =
        F.g0⁻¹ * (triEmb K σ (AlgebraicClosure K) y)⁻¹ * F.g0 := by group
    rw [h2] at h
    exact mul_left_cancel (mul_right_cancel h)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
