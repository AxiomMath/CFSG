module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev rho (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)

noncomputable abbrev innBar (L : Subgroup G) : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
  (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range

theorem rho_eq_conj (L : Subgroup G) {g : G} (hg : g ∈ L) :
    rho L ⟨g, L.le_normalizer hg⟩ =
      MulAut.conj ((⟨g, hg⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem rho_mem_innBar (L : Subgroup G) {g : G} (hg : g ∈ L) :
    rho L ⟨g, L.le_normalizer hg⟩ ∈ innBar L :=
  ⟨_, (rho_eq_conj L hg).symm⟩

theorem thetaQuot_eq_one_of_mem_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (K : Set G)) :
    Sec4.thetaQuotMulAut K
      (Sec4.compAction K ⟨g, Subgroup.centralizer_le_normalizer (K : Set G) hg⟩) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change g * (k : G) * g⁻¹ = k
    rw [(Subgroup.mem_centralizer_iff.mp hg k k.2).symm, mul_inv_cancel_right]

theorem thetaQuot_eq_one_of_rho_eq_one {L K : Subgroup G} (hKL : K ≤ L) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (h1 : rho L ⟨g, hgL⟩ = 1) :
    Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨g, hgK⟩) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
    have hk : ((⟨g * (k : G) * g⁻¹, hKL ((Sec4.compAction K ⟨g, hgK⟩ k).2)⟩ : L) :
        L ⧸ aschbacherSolvableCore 3 L) = ((⟨(k : G), hKL k.2⟩ : L) :
          L ⧸ aschbacherSolvableCore 3 L) := by
      have h := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
        τ ((⟨(k : G), hKL k.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) h1
      simp only [MulAut.one_apply] at h
      rw [← h]
      rfl
    have hρ : Sec8.Item87Res2Proof.toQuot hKL (Sec4.compAction K ⟨g, hgK⟩ k) =
        Sec8.Item87Res2Proof.toQuot hKL k := hk
    have hmem : (Sec4.compAction K ⟨g, hgK⟩ k)⁻¹ * k ∈ aschbacherSolvableCore 3 K :=
      Sec8.Item87Res2Proof.ker_toQuot_le hKL
        (by rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel])
    exact QuotientGroup.eq.mpr hmem

theorem thetaQuot_eq_conj (K : Subgroup G) {k : G} (hk : k ∈ K) :
    Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨k, K.le_normalizer hk⟩) =
      MulAut.conj ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) :=
  rho_eq_conj K hk

section Action

variable {L K : Subgroup G} {a b : G}

theorem rho_pow_mul_ne (hKL : K ≤ L) (hKb : K ≤ Subgroup.centralizer ({b} : Set G))
    (ha3 : a ^ 3 = 1) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hbL : b ∈ Subgroup.normalizer (L : Set G)) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hout : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) ∉
      (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
        MulAut (K ⧸ aschbacherSolvableCore 3 K)).range)
    {i j : ℕ} (hi : i % 3 ≠ 0) {k : G} (hk : k ∈ K) :
    rho L ⟨a, haL⟩ ^ i * rho L ⟨b, hbL⟩ ^ j ≠ rho L ⟨k, L.le_normalizer (hKL hk)⟩ := by
  intro h
  have hbC : b ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKb hx)
  have hbK : b ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hbC
  have hkK : k ∈ Subgroup.normalizer (K : Set G) := K.le_normalizer hk
  have hgL : a ^ i * b ^ j * k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ haL i) (Subgroup.pow_mem _ hbL j))
      (Subgroup.inv_mem _ (L.le_normalizer (hKL hk)))
  have hgK : a ^ i * b ^ j * k⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ haK i) (Subgroup.pow_mem _ hbK j))
      (Subgroup.inv_mem _ hkK)
  have hL1 : rho L ⟨a ^ i * b ^ j * k⁻¹, hgL⟩ = 1 := by
    have e : (⟨a ^ i * b ^ j * k⁻¹, hgL⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨a, haL⟩ : Subgroup.normalizer (L : Set G)) ^ i *
          (⟨b, hbL⟩ : Subgroup.normalizer (L : Set G)) ^ j *
          (⟨k, L.le_normalizer (hKL hk)⟩ : Subgroup.normalizer (L : Set G))⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow])
    rw [e, map_mul, map_mul, map_inv, map_pow, map_pow, h, mul_inv_cancel]
  have hK1 := thetaQuot_eq_one_of_rho_eq_one hKL hgL hgK hL1
  set τ := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) with hτ
  have eK : (⟨a ^ i * b ^ j * k⁻¹, hgK⟩ : Subgroup.normalizer (K : Set G)) =
      (⟨a, haK⟩ : Subgroup.normalizer (K : Set G)) ^ i *
        (⟨b, hbK⟩ : Subgroup.normalizer (K : Set G)) ^ j *
        (⟨k, hkK⟩ : Subgroup.normalizer (K : Set G))⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow])
  have hb1 := thetaQuot_eq_one_of_mem_centralizer hbC
  have hkc := thetaQuot_eq_conj K hk
  rw [eK] at hK1
  simp only [map_mul, map_inv, map_pow] at hK1
  have hb1' : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨b, hbK⟩) = 1 := hb1
  have hkc' : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨k, hkK⟩) =
      MulAut.conj ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := hkc
  rw [hb1', one_pow, mul_one, hkc', mul_inv_eq_one] at hK1
  have hτi : τ ^ i ∈ (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
      MulAut (K ⧸ aschbacherSolvableCore 3 K)).range := ⟨_, hK1.symm⟩
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow, ← map_pow]
    have : (⟨a, haK⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext (by simp [ha3])
    rw [this, map_one, map_one]
  have hτmod : τ ^ i = τ ^ (i % 3) := by
    conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hτ3, one_pow, one_mul]
  apply hout
  have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : i % 3 = 1 ∨ i % 3 = 2) with h1 | h2
  · rw [hτmod, h1, pow_one] at hτi
    exact hτi
  · rw [hτmod, h2] at hτi
    have : τ = (τ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hτ3, one_mul, pow_one]
    rw [this]
    exact Subgroup.pow_mem _ hτi 2

theorem rho_pow_ne_of_center_eq_bot (hKL : K ≤ L) (hKb : K ≤ Subgroup.centralizer ({b} : Set G))
    (hb3 : b ^ 3 = 1) (hbL : b ∈ Subgroup.normalizer (L : Set G)) (hβ1 : rho L ⟨b, hbL⟩ ≠ 1)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    {j : ℕ} (hj : j % 3 ≠ 0) {k : G} (hk : k ∈ K) :
    rho L ⟨b, hbL⟩ ^ j ≠ rho L ⟨k, L.le_normalizer (hKL hk)⟩ := by
  intro h
  have hbC : b ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKb hx)
  have hbK : b ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hbC
  have hkK : k ∈ Subgroup.normalizer (K : Set G) := K.le_normalizer hk
  have hgL : b ^ j * k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hbL j) (Subgroup.inv_mem _ (L.le_normalizer (hKL hk)))
  have hgK : b ^ j * k⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hbK j) (Subgroup.inv_mem _ hkK)
  have hL1 : rho L ⟨b ^ j * k⁻¹, hgL⟩ = 1 := by
    have e : (⟨b ^ j * k⁻¹, hgL⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨b, hbL⟩ : Subgroup.normalizer (L : Set G)) ^ j *
          (⟨k, L.le_normalizer (hKL hk)⟩ : Subgroup.normalizer (L : Set G))⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow])
    rw [e, map_mul, map_inv, map_pow, h, mul_inv_cancel]
  have hK1 := thetaQuot_eq_one_of_rho_eq_one hKL hgL hgK hL1
  have eK : (⟨b ^ j * k⁻¹, hgK⟩ : Subgroup.normalizer (K : Set G)) =
      (⟨b, hbK⟩ : Subgroup.normalizer (K : Set G)) ^ j *
        (⟨k, hkK⟩ : Subgroup.normalizer (K : Set G))⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow])
  have hb1 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨b, hbK⟩) = 1 :=
    thetaQuot_eq_one_of_mem_centralizer hbC
  have hkc : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨k, hkK⟩) =
      MulAut.conj ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := thetaQuot_eq_conj K hk
  rw [eK] at hK1
  simp only [map_mul, map_inv, map_pow] at hK1
  rw [hb1, one_pow, one_mul, hkc, inv_eq_one] at hK1
  have hcen : ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun σ : MulAut (K ⧸ aschbacherSolvableCore 3 K) => σ z) hK1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)
        = (((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) * z *
            ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)⁻¹) *
          ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := by rw [this]
      _ = ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) * z := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have h1 : orderOf k ∣ Nat.card (aschbacherSolvableCore 3 K) := by
    have := orderOf_dvd_natCard (⟨⟨k, hk⟩, hcen⟩ : aschbacherSolvableCore 3 K)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
  have h2 : orderOf (⟨k, L.le_normalizer (hKL hk)⟩ : Subgroup.normalizer (L : Set G)) =
      orderOf k := Subgroup.orderOf_mk _ _
  have hor : orderOf (rho L ⟨k, L.le_normalizer (hKL hk)⟩) ∣
      Nat.card (aschbacherSolvableCore 3 K) :=
    (orderOf_map_dvd _ _).trans (h2 ▸ h1)
  have hβ3 : rho L ⟨b, hbL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simp [hb3])
    rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hβo : orderOf (rho L ⟨b, hbL⟩) = 3 := orderOf_eq_prime hβ3 hβ1
  have hcop : (orderOf (rho L ⟨b, hbL⟩)).Coprime j := by
    rw [hβo]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun h3 => hj (Nat.mod_eq_zero_of_dvd h3))
  have hβjo : orderOf (rho L ⟨b, hbL⟩ ^ j) = 3 := by rw [Nat.Coprime.orderOf_pow hcop, hβo]
  rw [← h, hβjo] at hor
  exact hθ3 hor


noncomputable abbrev rhoK (hKL : K ≤ L) : K →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (rho L).comp (Subgroup.inclusion (hKL.trans L.le_normalizer))

omit [Finite G] in
theorem mem_center_of_conj_eq_one {X : Type*} [Group X] {x : X} (h : MulAut.conj x = 1) :
    x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro z
  have := congrArg (fun σ : MulAut X => σ z) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc z * x = (x * z * x⁻¹) * x := by rw [this]
    _ = x * z := by group

theorem card_quot_center_dvd_card (hKL : K ≤ L) :
    Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) ∣ Nat.card (rhoK hKL).range := by
  have hker : (rhoK hKL).ker ≤ (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)).comap
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) := by
    intro k hk
    rw [Subgroup.mem_comap]
    have h1 : rho L ⟨k, L.le_normalizer (hKL k.2)⟩ = 1 := hk
    have h2 := thetaQuot_eq_one_of_rho_eq_one hKL (L.le_normalizer (hKL k.2))
      (K.le_normalizer k.2) h1
    rw [thetaQuot_eq_conj K k.2] at h2
    exact mem_center_of_conj_eq_one h2
  have h := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.index_ker, Subgroup.index_eq_card] at h
  exact h


omit [Finite G] in
theorem card_sup_of_le_normalizer' {X Y : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (Y : Set G)) (hXY : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right X Y hXN
  let f : ↥X × ↥Y → ↥(X ⊔ Y) := fun p =>
    ⟨p.1 * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ X ⊓ Y := ⟨X.mul_mem (X.inv_mem a'.2) a.2, h2 ▸
        Y.mul_mem b'.2 (Y.inv_mem b.2)⟩
      rw [hXY, Subgroup.mem_bot] at h3
      have ha : a = a' := Subtype.ext (inv_mul_eq_one.1 h3).symm
      have hb : b = b' := Subtype.ext (by
        rw [ha] at h1
        exact mul_left_cancel h1)
      rw [ha, hb]
    · rintro ⟨g, hg⟩
      have hg' : g ∈ ((X : Set G) * (Y : Set G)) := by rw [← hset]; exact hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

@[expose] def Type418Arith (X : Type*) [Group X] : Prop :=
  7 ∣ Nat.card (X ⧸ Subgroup.center X) ∧ 3 ^ 2 ∣ Nat.card (X ⧸ Subgroup.center X) ∧
    (Subgroup.center X ≠ ⊥ → 3 ^ 4 ∣ Nat.card (X ⧸ Subgroup.center X))

theorem exists_centralizer_of_inner {L K : Subgroup G} {a b : G} (hKL : K ≤ L)
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G)) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hbL : b ∈ Subgroup.normalizer (L : Set G)) (hβ1 : rho L ⟨b, hbL⟩ ≠ 1)
    (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hout : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) ∉
      (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
        MulAut (K ⧸ aschbacherSolvableCore 3 K)).range)
    (hT : Type418Arith (K ⧸ aschbacherSolvableCore 3 K))
    (hαI : rho L ⟨a, haL⟩ ∈ innBar L) (hβI : rho L ⟨b, hbL⟩ ∈ innBar L) :
    orderOf (rho L ⟨b, hbL⟩) = 3 ∧
      3 ^ 4 ∣ Nat.card ↥(innBar L ⊓ Subgroup.centralizer {rho L ⟨b, hbL⟩}) ∧
      7 ∣ Nat.card ↥(innBar L ⊓ Subgroup.centralizer {rho L ⟨b, hbL⟩}) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set NL := Subgroup.normalizer (L : Set G) with hNL
  set α := rho L ⟨a, haL⟩ with hα
  set β := rho L ⟨b, hbL⟩ with hβ
  set T := (rhoK hKL).range with hTdef
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨a, haL⟩ : NL) ^ 3 = 1 := Subtype.ext (by simp [ha3])
    rw [this, map_one]
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨b, hbL⟩ : NL) ^ 3 = 1 := Subtype.ext (by simp [hb3])
    rw [this, map_one]
  have hβo : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  have hαβ : α * β = β * α := by
    rw [hα, hβ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  have hTI : T ≤ innBar L := by
    rintro _ ⟨k, rfl⟩
    exact rho_mem_innBar L (hKL k.2)
  have hTβ : ∀ t ∈ T, t * β = β * t := by
    rintro _ ⟨k, rfl⟩
    change rho L ⟨k, L.le_normalizer (hKL k.2)⟩ * rho L ⟨b, hbL⟩ =
      rho L ⟨b, hbL⟩ * rho L ⟨k, L.le_normalizer (hKL k.2)⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKb k.2))
  have hconj : ∀ (g : G) (hgL : g ∈ NL), g ∈ Subgroup.normalizer (K : Set G) →
      ∀ t ∈ T, rho L ⟨g, hgL⟩ * t * (rho L ⟨g, hgL⟩)⁻¹ ∈ T := by
    rintro g hgL hgK _ ⟨k, rfl⟩
    have hk' : g * (k : G) * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK k).mp k.2
    refine ⟨⟨g * k * g⁻¹, hk'⟩, ?_⟩
    change rho L ⟨g * k * g⁻¹, L.le_normalizer (hKL hk')⟩ =
      rho L ⟨g, hgL⟩ * rho L ⟨k, L.le_normalizer (hKL k.2)⟩ * (rho L ⟨g, hgL⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hαN : Subgroup.zpowers α ≤ Subgroup.normalizer (T : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hconj a haL haK t
    · intro ht
      have haK' : a⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ haK
      have h := hconj a⁻¹ (Subgroup.inv_mem _ haL) haK' _ ht
      have e : rho L ⟨a⁻¹, Subgroup.inv_mem _ haL⟩ = α⁻¹ := by
        rw [hα, ← map_inv]
        rfl
      rw [e, inv_inv] at h
      simpa [mul_assoc] using h
  have hαT : α ∉ T := by
    rintro ⟨k, hk⟩
    exact rho_pow_mul_ne hKL hKb ha3 haL hbL haK hout (i := 1) (j := 0) (by norm_num) k.2
      (by rw [pow_one, pow_zero, mul_one]; exact hk.symm)
  have hcardα : Nat.card ↥(Subgroup.zpowers α ⊔ T) = 3 * Nat.card T := by
    rw [card_sup_of_le_normalizer' hαN (by rw [inf_comm]; exact Sec4.inf_zpowers_eq_bot hα3 hαT),
      Nat.card_zpowers, orderOf_eq_prime hα3 (fun h => hαT (h ▸ T.one_mem))]
  set D := Subgroup.zpowers α ⊔ T with hD
  have hDβ : ∀ x ∈ D, x * β = β * x := by
    apply Sec4.commute_sup_of_commute
    · rintro _ ⟨m, rfl⟩
      exact (Commute.zpow_left hαβ m).eq
    · exact hTβ
  have hβC : β ∈ Subgroup.centralizer ({β} : Set _) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hDle : D ≤ innBar L ⊓ Subgroup.centralizer {β} := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨hαI, Subgroup.mem_centralizer_singleton_iff.mpr hαβ⟩
    · intro t ht
      exact ⟨hTI ht, Subgroup.mem_centralizer_singleton_iff.mpr (hTβ t ht)⟩
  have hdvdT := card_quot_center_dvd_card hKL
  obtain ⟨h7, h9, h81⟩ := hT
  refine ⟨hβo, ?_, ?_⟩
  · by_cases hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥
    ·
      have hβD : β ∉ D := by
        intro hmem
        have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers α) T hαN
        have hmem' : β ∈ ((Subgroup.zpowers α : Set (MulAut (L ⧸ aschbacherSolvableCore 3 L))) *
            (T : Set (MulAut (L ⧸ aschbacherSolvableCore 3 L)))) := by
          rw [← hset]; exact hmem
        obtain ⟨x, ⟨m, rfl⟩, t, ht, hxt⟩ := hmem'
        obtain ⟨k, rfl⟩ := ht
        have hk : rhoK hKL k = (α ^ m)⁻¹ * β := by
          rw [← hxt]; group
        have hmod : α ^ m = α ^ (m % 3) := by
          rw [← zpow_mod_orderOf, orderOf_eq_prime hα3 (fun h => hαT (h ▸ T.one_mem))]
          norm_num
        have h0 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
        have h3 : m % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
        rw [hmod] at hk
        rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with hr | hr | hr
        · rw [hr, zpow_zero, inv_one, one_mul] at hk
          exact rho_pow_ne_of_center_eq_bot hKL hKb hb3 hbL hβ1 hZ (j := 1) (by norm_num) k.2
            (by rw [pow_one]; exact hk.symm)
        · rw [hr, zpow_one] at hk
          refine rho_pow_mul_ne hKL hKb ha3 haL hbL haK hout (i := 2) (j := 1) (by norm_num) k.2 ?_
          rw [pow_one]
          change α ^ 2 * β = rhoK hKL k
          rw [hk, show α ^ 2 = α⁻¹ by
            rw [eq_inv_iff_mul_eq_one, ← pow_succ, hα3]]
        · rw [hr] at hk
          refine rho_pow_mul_ne hKL hKb ha3 haL hbL haK hout (i := 1) (j := 1) (by norm_num) k.2 ?_
          rw [pow_one, pow_one]
          change α * β = rhoK hKL k
          rw [hk, show (α ^ (2 : ℤ))⁻¹ = α by
            rw [inv_eq_iff_mul_eq_one, zpow_two, ← pow_two, ← pow_succ, hα3]]
      have hcard : Nat.card ↥(D ⊔ Subgroup.zpowers β) = Nat.card D * 3 :=
        Sec4.card_sup_zpowers_of_not_mem hβ3 hDβ hβD
      have hle : D ⊔ Subgroup.zpowers β ≤ innBar L ⊓ Subgroup.centralizer {β} := by
        refine sup_le hDle ?_
        rw [Subgroup.zpowers_le]
        exact ⟨hβI, hβC⟩
      have h1 := Subgroup.card_dvd_of_le hle
      rw [hcard, hD, hcardα] at h1
      refine Dvd.dvd.trans ?_ h1
      obtain ⟨c, hc⟩ := h9.trans hdvdT
      rw [hc]
      exact ⟨c, by ring⟩
    · have hle : T ≤ innBar L ⊓ Subgroup.centralizer {β} := fun t ht =>
        ⟨hTI ht, Subgroup.mem_centralizer_singleton_iff.mpr (hTβ t ht)⟩
      exact ((h81 hZ).trans hdvdT).trans (Subgroup.card_dvd_of_le hle)
  · have hle : T ≤ innBar L ⊓ Subgroup.centralizer {β} := fun t ht =>
      ⟨hTI ht, Subgroup.mem_centralizer_singleton_iff.mpr (hTβ t ht)⟩
    exact (h7.trans hdvdT).trans (Subgroup.card_dvd_of_le hle)

end Action

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
