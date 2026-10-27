module

public import CFSG.HardMathSupport.Malle.Coordinator.OuterFiveFixed

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

theorem conjAut_pow {M : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (M : Set G)) (n : ℕ) :
    conjAut hg ^ n = conjAut (Subgroup.pow_mem _ hg n) := by
  have h := map_pow (normalizerConj M) ⟨g, hg⟩ n
  rw [normalizerConj_apply, normalizerConj_apply] at h
  rw [← h]

theorem exists_conj_mem_normalizer_of_pow [Finite G] {M P : Subgroup G} (hPM : P ≤ M)
    (hP5 : IsPGroup 5 P) (hidx : ¬ 5 ∣ P.relIndex M) {q : G}
    (hqM : q ∈ Subgroup.normalizer (M : Set G)) {k : ℕ} (hq : q ^ (5 ^ k) = 1) :
    ∃ m ∈ M, m⁻¹ * q * m ∈ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P' : Sylow 5 M := (hP5.comap_subtype (K := M)).toSylow hidx
  have hPset : (P' : Set M) = ((P.subgroupOf M : Subgroup M) : Set M) := rfl
  set β := conjAut hqM with hβ
  have hβ5 : β ^ (5 ^ k) = 1 := by
    rw [hβ, conjAut_pow]
    ext x
    simp [hq]
  have hH : IsPGroup 5 (Subgroup.zpowers β) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hβ5)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hH.card_modEq_card_fixedPoints (Sylow 5 M)
  have h1 := card_sylow_modEq_one 5 M
  have hne : ∃ Q : Sylow 5 M, Q ∈ MulAction.fixedPoints (Subgroup.zpowers β) (Sylow 5 M) := by
    by_contra h0
    push Not at h0
    have h0' : Nat.card (MulAction.fixedPoints (Subgroup.zpowers β) (Sylow 5 M)) = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun x => h0 x.1 x.2⟩
    have := h1.symm.trans hmod
    rw [h0'] at this
    exact absurd this (by decide)
  obtain ⟨Q, hQ⟩ := hne
  have hβQ : β • Q = Q := hQ ⟨β, Subgroup.mem_zpowers β⟩
  obtain ⟨m, rfl⟩ := MulAction.exists_smul_eq M P' Q
  refine ⟨m, m.2, ?_⟩
  have hsub : ∀ y ∈ P, (m⁻¹ * q * m : G) * y * (m⁻¹ * q * m)⁻¹ ∈ P := by
    intro y hy
    have hyM : (m : G) * y * (m : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem m.2 (hPM hy)) (M.inv_mem m.2)
    have hmem : (⟨(m : G) * y * (m : G)⁻¹, hyM⟩ : M) ∈ ((m • P' : Sylow 5 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      show _ ∈ P.subgroupOf M
      rw [Subgroup.mem_subgroupOf]
      convert hy using 1
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    have hmem' : β ⟨(m : G) * y * (m : G)⁻¹, hyM⟩ ∈ ((m • P' : Sylow 5 M) : Subgroup M) := by
      rw [← hβQ, Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ β _ hmem
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem'
    change _ ∈ P.subgroupOf M at hmem'
    rw [Subgroup.mem_subgroupOf] at hmem'
    simpa [MulAut.conj_apply, hβ, mul_assoc] using hmem'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    convert hsub y hy using 1
    show (m⁻¹ * q * m : G) * y * (m⁻¹ * q * m)⁻¹ = _
    rfl
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem card_inf_centralizer_conj {M : Subgroup G} {c : G} (hc : c ∈ M) (g : G) :
    Nat.card (M ⊓ Subgroup.centralizer ({c * g * c⁻¹} : Set G) : Subgroup G) =
      Nat.card (M ⊓ Subgroup.centralizer ({g} : Set G) : Subgroup G) := by
  have h : (M ⊓ Subgroup.centralizer ({g} : Set G)).map (MulAut.conj c).toMonoidHom =
      M ⊓ Subgroup.centralizer ({c * g * c⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hyM, hyg⟩, rfl⟩
      refine ⟨M.mul_mem (M.mul_mem hc hyM) (M.inv_mem hc), ?_⟩
      calc c * y * c⁻¹ * (c * g * c⁻¹) = c * (y * g) * c⁻¹ := by group
        _ = c * (g * y) * c⁻¹ := by rw [hyg]
        _ = c * g * c⁻¹ * (c * y * c⁻¹) := by group
    · rintro ⟨hxM, hxg⟩
      refine ⟨c⁻¹ * x * c, ⟨M.mul_mem (M.mul_mem (M.inv_mem hc) hxM) hc, ?_⟩, by group⟩
      calc c⁻¹ * x * c * g = c⁻¹ * (x * (c * g * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * g * c⁻¹) * x) * c := by rw [hxg]
        _ = g * (c⁻¹ * x * c) := by group
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem card_modEq_card_inf_centralizer [Finite G] {S : Subgroup G} {q : G}
    (hqS : q ∈ Subgroup.normalizer (S : Set G)) {k : ℕ} (hq : q ^ (5 ^ k) = 1) :
    Nat.card S ≡ Nat.card (S ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G) [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set β := conjAut hqS with hβ
  have hβ5 : β ^ (5 ^ k) = 1 := by
    rw [hβ, conjAut_pow]
    ext x
    simp [hq]
  have hH : IsPGroup 5 (Subgroup.zpowers β) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hβ5)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hH.card_modEq_card_fixedPoints S
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers β) S) =
      Nat.card (S ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G) := by
    have hmem : ∀ s : S, s ∈ MulAction.fixedPoints (Subgroup.zpowers β) S ↔
        (s : G) ∈ Subgroup.centralizer ({q} : Set G) := by
      intro s
      rw [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h1 := congrArg Subtype.val (h ⟨β, Subgroup.mem_zpowers β⟩)
        change ((β s : S) : G) = s at h1
        rw [hβ, conjAut_apply] at h1
        calc (s : G) * q = q * s * q⁻¹ * q := by rw [h1]
          _ = q * s := by group
      · intro h
        rintro ⟨γ, hγ⟩
        have hβs : β ∈ MulAction.stabilizer (MulAut S) s := by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          change ((β s : S) : G) = s
          rw [hβ, conjAut_apply, ← h]
          group
        have hγs := (Subgroup.zpowers_le.mpr hβs) hγ
        rw [MulAction.mem_stabilizer_iff] at hγs
        exact hγs
    rw [Nat.card_congr (Equiv.subtypeEquivRight hmem)]
    exact Nat.card_congr ((Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv.symm.trans
      (Equiv.subtypeEquivRight (fun s => by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩))).symm
  rw [hfix] at hmod
  exact hmod

namespace OuterFiveData

variable {P Z : Subgroup G} {φ : G} (D : OuterFiveData P Z φ)
include D

theorem pow_mem_of_mul_pow_eq_one {n : G} (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (htw : n⁻¹ * (φ⁻¹ * n * φ) ∈ P) {e : ℕ} (he : (n * φ) ^ e = 1) (hφe : φ ^ e = 1) :
    n ^ e ∈ P := by
  set W := Subgroup.normalizer (P : Set G) with hW
  have hPW : P ≤ W := Subgroup.le_normalizer
  have : (P.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPW).mpr le_rfl
  let a : W := ⟨n, hnP⟩
  let b : W := ⟨φ, D.mem_normalizer⟩
  have hab : Commute (a : W ⧸ P.subgroupOf W) (b : W ⧸ P.subgroupOf W) := by
    show ((a * b : W) : W ⧸ P.subgroupOf W) = ((b * a : W) : W ⧸ P.subgroupOf W)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((a * b)⁻¹ * (b * a) : W) = (φ⁻¹ * n * φ)⁻¹ * n := by
      simp only [a, b, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    have h := P.inv_mem htw
    simpa [mul_assoc] using h
  have hbe : (b : W ⧸ P.subgroupOf W) ^ e = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : b ^ e = 1 := Subtype.ext (by simpa [b] using hφe)
    rw [this, QuotientGroup.mk_one]
  have habe : ((a * b : W) : W ⧸ P.subgroupOf W) ^ e = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (a * b) ^ e = 1 := Subtype.ext (by simpa [a, b] using he)
    rw [this, QuotientGroup.mk_one]
  have hae : (a : W ⧸ P.subgroupOf W) ^ e = 1 := by
    rw [QuotientGroup.mk_mul, hab.mul_pow, hbe, mul_one] at habe
    exact habe
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hae
  simpa [a] using hae

theorem mem_of_mul_pow_eq_one [Finite G] {K M : Subgroup G} (hPM : P ≤ M) (hMK : M ≤ K)
    (hφK : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K) (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hidx : ¬ 5 ∣ P.relIndex M) {n : G} (hnM : n ∈ M)
    (hnP : n ∈ Subgroup.normalizer (P : Set G)) {k : ℕ} (hk : (n * φ) ^ (5 ^ k) = 1) :
    n ∈ P := by
  set NM := M ⊓ Subgroup.normalizer (P : Set G) with hNM
  have hnN : n ∈ NM := ⟨hnM, hnP⟩
  have htw : n⁻¹ * (φ⁻¹ * n * φ) ∈ P :=
    D.twist_mem_of_centralizer_le (N := NM) (fun x hx => hMK hx.1)
      (fun x hx => D.normalizer_le_normalizer hx.2) hCZ hφK hnN
  have he : (n * φ) ^ (5 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul, hk, one_pow]
  have hφe : φ ^ (5 ^ (k + 1)) = 1 := by
    rw [pow_succ', pow_mul, D.order, one_pow]
  have hn5 : n ^ (5 ^ (k + 1)) ∈ P := D.pow_mem_of_mul_pow_eq_one hnP htw he hφe
  have hPNM : P ≤ NM := le_inf hPM Subgroup.le_normalizer
  have hnorm : (P.subgroupOf NM).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPNM).mpr inf_le_right
  have hnr : n ^ P.relIndex NM ∈ P := by
    have h := (P.subgroupOf NM).pow_index_mem (⟨n, hnN⟩ : NM)
    rw [Subgroup.mem_subgroupOf] at h
    simpa [Subgroup.relIndex] using h
  have hcop : Nat.Coprime (5 ^ (k + 1)) (P.relIndex NM) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro h
    apply hidx
    rw [← Subgroup.relIndex_mul_relIndex P NM M hPNM inf_le_left]
    exact Dvd.dvd.mul_right h _
  exact mem_of_pow_mem_of_coprime hcop hn5 hnr

end OuterFiveData

theorem exists_inv_mul_mem_normalizer [Finite G] {M S : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hSM : S ≤ M) (hSp : IsPGroup p S) (hSidx : ¬ p ∣ S.relIndex M) {φ : G}
    (hφM : φ ∈ Subgroup.normalizer (M : Set G)) :
    ∃ m ∈ M, m⁻¹ * φ ∈ Subgroup.normalizer (S : Set G) := by
  let S' : Sylow p M := (hSp.comap_subtype (K := M)).toSylow hSidx
  set α := conjAut hφM with hα
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S' (α • S')
  refine ⟨m, m.2, ?_⟩
  have hsub : ∀ y ∈ S, ((m : G)⁻¹ * φ) * y * ((m : G)⁻¹ * φ)⁻¹ ∈ S := by
    intro y hy
    have hyS' : (⟨y, hSM hy⟩ : M) ∈ (S' : Subgroup M) := by
      show _ ∈ S.subgroupOf M
      rw [Subgroup.mem_subgroupOf]; exact hy
    have hmem : α ⟨y, hSM hy⟩ ∈ ((m • S' : Sylow p M) : Subgroup M) := by
      rw [hm, Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ α _ hyS'
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    change _ ∈ S.subgroupOf M at hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    convert hmem using 1
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hα, conjAut_apply]
    group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact hsub y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem exists_pow_five_part [Finite G] {M : Subgroup G} {φ : G}
    (hφM : φ ∈ Subgroup.normalizer (M : Set G)) (hφ5 : φ ^ 5 = 1) {g : G} (hg : g * φ⁻¹ ∈ M) :
    ∃ e k : ℕ, (g ^ e) ^ (5 ^ k) = 1 ∧ g ^ e * φ⁻¹ ∈ M := by
  set o := orderOf g with ho
  have ho0 : o ≠ 0 := (orderOf_pos g).ne'
  set k := o.factorization 5
  set b := o / 5 ^ k with hb
  have hbo : 5 ^ k * b = o := Nat.ordProj_mul_ordCompl_eq_self o 5
  have hbcop : Nat.Coprime b 5 :=
    (Nat.coprime_ordCompl Nat.prime_five ho0).symm
  refine ⟨b ^ 4, k, ?_, ?_⟩
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [← ho, ← hbo, mul_comm (b ^ 4)]
    exact Nat.mul_dvd_mul_left _ (dvd_pow_self b (by norm_num))
  ·
    have hind : ∀ n : ℕ, g ^ n * (φ ^ n)⁻¹ ∈ M := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : g ^ (n + 1) * (φ ^ (n + 1))⁻¹ =
            (g ^ n * (φ ^ n)⁻¹) * (φ ^ n * (g * φ⁻¹) * (φ ^ n)⁻¹) := by group
        rw [h1]
        refine M.mul_mem ih ?_
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hφM n) _).mp hg
    have hφe : φ ^ (b ^ 4) = φ := by
      have hmod : b ^ 4 % 5 = 1 := by
        have hb5 : b % 5 ≠ 0 := by
          intro h
          have : 5 ∣ b := Nat.dvd_of_mod_eq_zero h
          have h1 := Nat.Coprime.coprime_dvd_left this hbcop
          norm_num at h1
        rw [Nat.pow_mod]
        have : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
        interval_cases h : b % 5 <;> simp_all
      rw [← Nat.div_add_mod (b ^ 4) 5, pow_add, pow_mul, hφ5, one_pow, one_mul, hmod, pow_one]
    have := hind (b ^ 4)
    rwa [hφe] at this

theorem conj_inv_mul_mem {M : Subgroup G} {φ : G} (hφM : φ ∈ Subgroup.normalizer (M : Set G))
    {m q : G} (hm : m ∈ M) (hq : q * φ⁻¹ ∈ M) : m⁻¹ * q * m * φ⁻¹ ∈ M := by
  have h1 : m⁻¹ * q * m * φ⁻¹ = m⁻¹ * (q * φ⁻¹) * (φ * m * φ⁻¹) := by group
  rw [h1]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) hq)
    ((Subgroup.mem_normalizer_iff.mp hφM m).mp hm)

namespace OuterFiveData

variable {P Z : Subgroup G} {φ : G} (D : OuterFiveData P Z φ)
include D

theorem exists_card_modEq_of_sylow [Finite G] {K M : Subgroup G}
    (hPcard : Nat.card P = Nat.card Z * Nat.card Z) (hPM : P ≤ M) (hMK : M ≤ K)
    (hφK : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K) (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hφM : φ ∈ Subgroup.normalizer (M : Set G)) (hP5 : IsPGroup 5 P)
    (hidx : ¬ 5 ∣ P.relIndex M)
    (hC : ∀ x ∈ Z, x ≠ 1 →
      M ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (P : Set G))
    {p : ℕ} [Fact p.Prime] {S : Subgroup G} (hSM : S ≤ M) (hSp : IsPGroup p S)
    (hSidx : ¬ p ∣ S.relIndex M) :
    ∃ s : ℕ, s ∣ Nat.card S ∧
      (s ∣ Nat.card (M ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) ∨
        s ∣ Nat.card (M ⊓ Subgroup.normalizer (P : Set G) : Subgroup G)) ∧
      Nat.card S ≡ s [MOD 5] := by
  obtain ⟨m, hm, hgS⟩ := exists_inv_mul_mem_normalizer hSM hSp hSidx hφM
  set g := m⁻¹ * φ with hg
  have hgφ : g * φ⁻¹ ∈ M := by rw [hg]; simpa using M.inv_mem hm
  obtain ⟨e, k, hqk, hqM⟩ := exists_pow_five_part hφM D.order hgφ
  set q := g ^ e with hq
  have hqS : q ∈ Subgroup.normalizer (S : Set G) := Subgroup.pow_mem _ hgS e
  have hqN : q ∈ Subgroup.normalizer (M : Set G) := by
    have : q = (q * φ⁻¹) * φ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hqM) hφM
  refine ⟨Nat.card (S ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G),
    Subgroup.card_dvd_of_le inf_le_left, ?_, card_modEq_card_inf_centralizer hqS hqk⟩
  have hSq : Nat.card (S ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G) ∣
      Nat.card (M ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G) :=
    Subgroup.card_dvd_of_le (inf_le_inf_right _ hSM)
  obtain ⟨m₁, hm₁, hq'P⟩ := exists_conj_mem_normalizer_of_pow hPM hP5 hidx hqN hqk
  set q' := m₁⁻¹ * q * m₁ with hq'
  have hqq' : q = m₁ * q' * m₁⁻¹ := by rw [hq']; group
  have hcardq : Nat.card (M ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G) =
      Nat.card (M ⊓ Subgroup.centralizer ({q'} : Set G) : Subgroup G) := by
    rw [hqq', card_inf_centralizer_conj hm₁]
  rw [hcardq] at hSq
  set n := q' * φ⁻¹ with hn
  have hnM : n ∈ M := conj_inv_mul_mem hφM hm₁ hqM
  have hnP : n ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mul_mem _ hq'P (Subgroup.inv_mem _ D.mem_normalizer)
  have hq'k : (n * φ) ^ (5 ^ k) = 1 := by
    have : n * φ = q' := by rw [hn]; group
    rw [this, hq', inv_conj_pow, hqk]
    group
  have hnmem : n ∈ P := D.mem_of_mul_pow_eq_one hPM hMK hφK hCZ hidx hnM hnP hq'k
  set y := φ⁻¹ * n * φ with hy
  have hyP : y ∈ P := D.conj_mem _ hnmem
  have hq'y : q' = φ * y := by rw [hy, hn]; group
  by_cases hyZ : y ∈ Z
  ·
    left
    obtain ⟨p₀, hp₀, hp₀eq⟩ := D.exists_conj_eq_mul hPcard hyZ
    have hq'φ : q' = p₀⁻¹ * φ * p₀ := by rw [hp₀eq, hq'y]
    have hcard' : Nat.card (M ⊓ Subgroup.centralizer ({q'} : Set G) : Subgroup G) =
        Nat.card (M ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) := by
      have : q' = p₀⁻¹ * φ * p₀⁻¹⁻¹ := by rw [inv_inv]; exact hq'φ
      rw [this, card_inf_centralizer_conj (M.inv_mem (hPM hp₀))]
    rw [← hcard']
    exact hSq
  ·
    right
    have hx : y ^ 5 ∈ Z := D.pow_five_mem hyP
    have hx1 : y ^ 5 ≠ 1 := fun h => hyZ (D.omega y hyP h)
    have hq'5 : q' ^ 5 = y ^ 5 := by rw [hq'y, D.mul_pow_five hyP]
    refine hSq.trans (Subgroup.card_dvd_of_le ?_)
    intro c hc
    rw [Subgroup.mem_inf] at hc
    have hc2 := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    refine Subgroup.mem_inf.mpr ⟨hc.1, hC _ hx hx1 (Subgroup.mem_inf.mpr ⟨hc.1, ?_⟩)⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hq'5]
    exact (Commute.pow_right hc2 5).eq

end OuterFiveData

end CFSG.HardMathSupport.Malle.Coordinator
