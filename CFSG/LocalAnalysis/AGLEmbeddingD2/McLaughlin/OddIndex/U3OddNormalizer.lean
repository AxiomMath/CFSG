module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddMod4

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F]

theorem eq_diagonal_of_commute {m : Matrix (Fin 3) (Fin 3) F} {d₀ d₁ d₂ : F} (h01 : d₀ ≠ d₁)
    (h02 : d₀ ≠ d₂) (h12 : d₁ ≠ d₂)
    (hc : m * Matrix.diagonal ![d₀, d₁, d₂] = Matrix.diagonal ![d₀, d₁, d₂] * m) :
    m = Matrix.diagonal ![m 0 0, m 1 1, m 2 2] := by
  have key : ∀ i j : Fin 3, ![d₀, d₁, d₂] i ≠ ![d₀, d₁, d₂] j → m i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hc i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have h : (![d₀, d₁, d₂] j - ![d₀, d₁, d₂] i) * m i j = 0 := by linear_combination this
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (Ne.symm hij))
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first
    | exact key _ _ (by simpa using h01) | exact key _ _ (by simpa using Ne.symm h01)
    | exact key _ _ (by simpa using h02) | exact key _ _ (by simpa using Ne.symm h02)
    | exact key _ _ (by simpa using h12) | exact key _ _ (by simpa using Ne.symm h12)

theorem diagonal_isometry_iff (σ : F ≃+* F) {d₀ d₁ d₂ : F} :
    conjTr σ (Matrix.diagonal ![d₀, d₁, d₂]) * antidiag 3 * Matrix.diagonal ![d₀, d₁, d₂] =
      antidiag 3 ↔ σ d₀ * d₂ = 1 ∧ σ d₁ * d₁ = 1 ∧ σ d₂ * d₀ = 1 := by
  refine ⟨fun h => ?_, fun ⟨h0, h1, h2⟩ => conjTr_diagonal_antidiag σ h0 h1 h2⟩
  have e02 := congrFun (congrFun h 0) 2
  have e11 := congrFun (congrFun h 1) 1
  have e20 := congrFun (congrFun h 2) 0
  simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at e02 e11 e20
  exact ⟨e02, e11, e20⟩

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_tSU_of_diagonal (hF : Nat.card F = (p ^ f) ^ 2) {x : SU (unitaryInvolution F p f) 3}
    {a b c : F} (hx : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, b, c]) :
    ∃ μ : Fˣ, tSU hF μ = x := by
  have hmem := x.2
  rw [mem_SU, hx] at hmem
  obtain ⟨hdet, hiso⟩ := hmem
  obtain ⟨h0, h1, h2⟩ := (diagonal_isometry_iff (unitaryInvolution F p f)).1 hiso
  simp only [Matrix.det_diagonal, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hdet
  have hσ : ∀ y : F, unitaryInvolution F p f y = y ^ (p ^ f) := unitaryInvolution_apply F p f
  rw [hσ] at h0 h1 h2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h2
    exact zero_ne_one h2
  have hq := one_le_prime_pow p f
  have hc : c = (a ^ (p ^ f))⁻¹ := eq_inv_of_mul_eq_one_right h0
  have hab : a * b = a ^ (p ^ f) := by
    have h := hdet
    rw [hc] at h
    field_simp at h
    exact h
  have hb : b = a ^ (p ^ f - 1) :=
    mul_left_cancel₀ ha0 (by rw [hab, ← pow_succ', Nat.sub_add_cancel hq])
  refine ⟨Units.mk0 a ha0, Subtype.ext (Units.ext ?_)⟩
  rw [coe_tSU, coe_tGL, hx, hb, hc]
  unfold tMat
  simp [Units.val_pow_eq_pow_val]

section Elements

variable (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1)

omit [Finite F] in
include hω in
theorem unit_ne_one_of_orderOf_three : ω ≠ 1 := by
  rintro rfl
  simp at hω

omit [Finite F] in
include hω in
theorem unit_sq_ne_one_of_orderOf_three : ω ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hω] at this
  omega

include hω hq3 in
theorem coe_tSU_omega :
    (((tSU hF ω : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(ω : F), 1, ((ω⁻¹ : Fˣ) : F)] := by
  have hω' : ω ^ (p ^ f) = ω := pow_eq_self_of_orderOf_three hω hq3
  have h1 : ω ^ (p ^ f - 1) = 1 := by
    have h := hω'
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by have := one_le_prime_pow p f; omega⟩
    rw [hk, pow_succ'] at h
    rw [hk, Nat.add_sub_cancel]
    exact mul_eq_left.1 h
  show tMat (p ^ f) ω = _
  unfold tMat
  rw [h1, hω']
  simp

include hω hq3 in
theorem centralizer_a0 :
    Subgroup.centralizer ({tSU hF ω} : Set (SU (unitaryInvolution F p f) 3)) = (tSU hF).range := by
  ext x
  constructor
  · intro hx
    have hc := hx (tSU hF ω) rfl
    have hm : (((tSU hF ω : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (((x : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (((x : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (((tSU hF ω : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) :=
      congrArg (fun g : SU (unitaryInvolution F p f) 3 => ((g : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)) hc
    rw [coe_tSU_omega hF hω hq3] at hm
    have hne1 : (ω : F) ≠ 1 := fun h => unit_ne_one_of_orderOf_three hω (Units.ext h)
    have hne2 : (ω : F) ≠ ((ω⁻¹ : Fˣ) : F) := by
      intro h
      have : ω * ω = 1 := by
        have h' : ω = ω⁻¹ := Units.ext h
        calc ω * ω = ω * ω⁻¹ := by rw [← h']
          _ = 1 := mul_inv_cancel ω
      exact unit_sq_ne_one_of_orderOf_three hω (by rw [sq]; exact this)
    have hne3 : (1 : F) ≠ ((ω⁻¹ : Fˣ) : F) := by
      intro h
      have : ω⁻¹ = 1 := (Units.ext h.symm)
      exact unit_ne_one_of_orderOf_three hω (inv_eq_one.1 this)
    have := eq_diagonal_of_commute hne1.symm.symm hne2 hne3 hm.symm
    exact exists_tSU_of_diagonal hF this
  · rintro ⟨μ, rfl⟩ g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [← map_mul, ← map_mul, mul_comm]

theorem mem_normalizer_zpowers_iff_of_orderOf_three {G : Type*} [Group G] {a s : G}
    (ha : orderOf a = 3) (hs2 : s * s = 1) (hsa : s * a * s⁻¹ = a⁻¹) (x : G) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) ↔
      x ∈ Subgroup.centralizer ({a} : Set G) ∨ s * x ∈ Subgroup.centralizer ({a} : Set G) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hne : a ≠ 1 := by
    rintro rfl
    simp at ha
  constructor
  · intro hx
    have hxa : x * a * x⁻¹ ∈ Subgroup.zpowers a :=
      ((Subgroup.mem_normalizer_iff.1 hx) a).1 (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxa
    have hmod : a ^ (k % 3) = a ^ k := by
      have h := zpow_mod_orderOf a k
      rw [ha] at h
      exact_mod_cast h
    have hk' : a ^ (k % 3) = x * a * x⁻¹ := hmod.trans hk
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · exfalso
      rw [hr, zpow_zero] at hk'
      apply hne
      have h2 : x * a * x⁻¹ = 1 := hk'.symm
      simpa using h2
    · left
      rw [hr, zpow_one] at hk'
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      calc g * x = (x * g * x⁻¹) * x := by rw [← hk']
        _ = x * g := by group
    · right
      rw [hr] at hk'
      have hinv : a ^ ((2 : ℤ)) = a⁻¹ := by
        rw [zpow_two, ← pow_two]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ha3)
      rw [hinv] at hk'
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have h1 : s * (x * g * x⁻¹) * s⁻¹ = g := by
        rw [← hk']
        calc s * g⁻¹ * s⁻¹ = (s * g * s⁻¹)⁻¹ := by group
          _ = g := by rw [hsa, inv_inv]
      have h2 : s * x * g * (s * x)⁻¹ = g :=
        calc s * x * g * (s * x)⁻¹ = s * (x * g * x⁻¹) * s⁻¹ := by group
          _ = g := h1
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · rintro (hx | hx)
    · exact mem_normalizer_zpowers_of_commute (by
        have := hx a rfl
        exact this.symm)
    · have hc : Commute (s * x) a := (hx a rfl).symm
      have h1 : s * x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
        mem_normalizer_zpowers_of_commute hc
      have hs : s ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
        mem_normalizer_zpowers_of_inv hs2 hsa
      have : x = s * (s * x) := by rw [← mul_assoc, hs2, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ hs h1

include hω hq3 in
theorem sSU_conj_a0 :
    (sSU : SU (unitaryInvolution F p f) 3) * tSU hF ω * sSU⁻¹ = (tSU hF ω)⁻¹ := by
  rw [sSU_conj_tSU, pow_eq_self_of_orderOf_three hω hq3, map_inv]

include hω in
theorem orderOf_tSU : orderOf (tSU hF ω) = 3 := by
  rw [orderOf_injective (tSU hF) (tSU_injective hF) ω, hω]

include hω hq3 in
theorem mem_normalizer_a0_iff (x : SU (unitaryInvolution F p f) 3) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) : Subgroup _) : Set _) ↔
      x ∈ (tSU hF).range ∨ ∃ t ∈ (tSU hF).range, x = t * sSU := by
  rw [mem_normalizer_zpowers_iff_of_orderOf_three (orderOf_tSU hF hω) sSU_mul_self
    (sSU_conj_a0 hF hω hq3), centralizer_a0 hF hω hq3]
  constructor
  · rintro (h | ⟨μ, hμ⟩)
    · exact Or.inl h
    · right
      refine ⟨tSU hF (μ ^ (p ^ f))⁻¹, ⟨_, rfl⟩, ?_⟩
      rw [← sSU_mul_tSU, hμ, ← mul_assoc, sSU_mul_self, one_mul]
  · rintro (h | ⟨t, ⟨μ, rfl⟩, rfl⟩)
    · exact Or.inl h
    · right
      refine ⟨(μ ^ (p ^ f))⁻¹, ?_⟩
      have h := sSU_conj_tSU hF μ
      rw [sSU_inv] at h
      rw [← h, mul_assoc]

end Elements

section Central

variable (hF : Nat.card F = (p ^ f) ^ 2)

theorem isCyclic_range_tSU : IsCyclic (tSU hF).range :=
  isCyclic_of_surjective (tSU hF).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

@[expose] noncomputable def zSU : SU (unitaryInvolution F p f) 3 := tSU hF (-1)

theorem zSU_mul_self : zSU hF * zSU hF = 1 := by
  rw [zSU, ← map_mul]
  simp

theorem zSU_ne_one (hp2 : p ≠ 2) : zSU hF ≠ 1 := by
  intro h
  have h1 : (-1 : Fˣ) = 1 := tSU_injective hF (by rw [← zSU, h, map_one])
  have h3 : (-1 : F) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h1
    simpa using this
  exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq F p]; exact hp2) h3

theorem sSU_mul_zSU (hp2 : p ≠ 2) :
    (sSU : SU (unitaryInvolution F p f) 3) * zSU hF = zSU hF * sSU := by
  rw [zSU, sSU_mul_tSU]
  have hodd : Odd (p ^ f) :=
    ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  rw [hodd.neg_one_pow]
  simp

@[expose] noncomputable def normA0 (hF : Nat.card F = (p ^ f) ^ 2) (ω : Fˣ) :
    Subgroup (SU (unitaryInvolution F p f) 3) :=
  Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) : Subgroup (SU (unitaryInvolution F p f) 3)) :
    Set (SU (unitaryInvolution F p f) 3))

theorem sSU_conj_range_mem :
    ∀ x ∈ (tSU hF).range, (sSU : SU (unitaryInvolution F p f) 3) * x * sSU⁻¹ ∈ (tSU hF).range := by
  rintro _ ⟨μ, rfl⟩
  rw [sSU_conj_tSU]
  exact ⟨_, rfl⟩

theorem normA0_eq {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) :
    normA0 hF ω = twoCoset (tSU hF).range sSU sSU_mul_self (sSU_conj_range_mem hF) := by
  ext x
  exact mem_normalizer_a0_iff hF hω hq3 x

theorem card_normA0 {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) :
    Nat.card (normA0 hF ω) = 2 * ((p ^ f) ^ 2 - 1) := by
  rw [normA0_eq hF hω hq3, card_twoCoset _ _ _ _ (sSU_not_mem_range hF), card_range_tSU hF]

theorem range_tSU_le_normA0 {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) :
    (tSU hF).range ≤ normA0 hF ω := by
  rintro _ ⟨μ, rfl⟩
  exact (mem_normalizer_a0_iff hF hω hq3 _).2 (Or.inl ⟨μ, rfl⟩)

theorem relIndex_range_normA0 {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) :
    ((tSU hF).range.subgroupOf (normA0 hF ω)).index = 2 := by
  have hcard : Nat.card ((tSU hF).range.subgroupOf (normA0 hF ω)) = (p ^ f) ^ 2 - 1 := by
    rw [← card_range_tSU hF]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (range_tSU_le_normA0 hF hω hq3)).toEquiv
  have h := Subgroup.card_mul_index ((tSU hF).range.subgroupOf (normA0 hF ω))
  rw [hcard, card_normA0 hF hω hq3] at h
  have hpos : 0 < (p ^ f) ^ 2 - 1 := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    omega
  exact Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_comm _ _))

theorem zSU_comm_normA0 {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) (hp2 : p ≠ 2)
    (x : SU (unitaryInvolution F p f) 3) (hx : x ∈ normA0 hF ω) :
    x * zSU hF = zSU hF * x := by
  have hcomm : ∀ μ : Fˣ, tSU hF μ * zSU hF = zSU hF * tSU hF μ := fun μ => by
    rw [zSU, ← map_mul, ← map_mul, mul_comm]
  rcases (mem_normalizer_a0_iff hF hω hq3 x).1 hx with ⟨μ, rfl⟩ | ⟨t, ⟨μ, rfl⟩, rfl⟩
  · exact hcomm μ
  · calc tSU hF μ * sSU * zSU hF = tSU hF μ * (sSU * zSU hF) := mul_assoc _ _ _
      _ = tSU hF μ * (zSU hF * sSU) := by rw [sSU_mul_zSU hF hp2]
      _ = (tSU hF μ * zSU hF) * sSU := (mul_assoc _ _ _).symm
      _ = (zSU hF * tSU hF μ) * sSU := by rw [hcomm]
      _ = zSU hF * (tSU hF μ * sSU) := mul_assoc _ _ _

theorem tSU_comm_normA0 {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) {ν : Fˣ}
    (hν : (ν ^ (p ^ f))⁻¹ = ν) (x : SU (unitaryInvolution F p f) 3) (hx : x ∈ normA0 hF ω) :
    x * tSU hF ν = tSU hF ν * x := by
  have hcomm : ∀ μ : Fˣ, tSU hF μ * tSU hF ν = tSU hF ν * tSU hF μ := fun μ => by
    rw [← map_mul, ← map_mul, mul_comm]
  rcases (mem_normalizer_a0_iff hF hω hq3 x).1 hx with ⟨μ, rfl⟩ | ⟨t, ⟨μ, rfl⟩, rfl⟩
  · exact hcomm μ
  · have hs : (sSU : SU (unitaryInvolution F p f) 3) * tSU hF ν = tSU hF ν * sSU := by
      rw [sSU_mul_tSU, hν]
    calc tSU hF μ * sSU * tSU hF ν = tSU hF μ * (sSU * tSU hF ν) := mul_assoc _ _ _
      _ = tSU hF μ * (tSU hF ν * sSU) := by rw [hs]
      _ = (tSU hF μ * tSU hF ν) * sSU := (mul_assoc _ _ _).symm
      _ = (tSU hF ν * tSU hF μ) * sSU := by rw [hcomm]
      _ = tSU hF ν * (tSU hF μ * sSU) := mul_assoc _ _ _

end Central

section Nu

variable (hF : Nat.card F = (p ^ f) ^ 2)

omit [CharP F p] in
include hF in
theorem exists_unit_orderOf_card_add_one (hp2 : p ≠ 2) :
    ∃ ν : Fˣ, orderOf ν = p ^ f + 1 ∧ ν ^ ((p ^ f + 1) / 2) = -1 ∧ (ν ^ (p ^ f))⁻¹ = ν := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgo : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hq2 : 2 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    by_contra h
    have h2 : p ^ f ≤ 1 := by omega
    have h3 : (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
  have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    rw [hk, Nat.add_sub_cancel]
    have h : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
    omega
  have hk0 : p ^ f - 1 ≠ 0 := by omega
  have hdvd : (p ^ f - 1) ∣ orderOf g := by rw [hgo, hsq]; exact Dvd.intro _ rfl
  have hν : orderOf (g ^ (p ^ f - 1)) = p ^ f + 1 := by
    rw [orderOf_pow_of_dvd hk0 hdvd, hgo, hsq]
    exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk0)
  set ν := g ^ (p ^ f - 1) with hνdef
  have hpow1 : ν ^ (p ^ f + 1) = 1 := hν ▸ pow_orderOf_eq_one ν
  refine ⟨ν, hν, ?_, ?_⟩
  · set x := ν ^ ((p ^ f + 1) / 2) with hx
    have h2 : (p ^ f + 1) / 2 * 2 = p ^ f + 1 := Nat.div_mul_cancel (by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m + 1, by omega⟩)
    have hxx : x * x = 1 := by
      rw [hx, ← pow_add, ← two_mul, mul_comm, h2, hpow1]
    have hx1 : x ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hν] at this
      have := Nat.le_of_dvd (by omega) this
      omega
    have hF' : ((x : Fˣ) : F) * ((x : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, hxx, Units.val_one]
    rcases mul_self_eq_one_iff.1 hF' with h | h
    · exact absurd (Units.ext h) hx1
    · exact Units.ext (by rw [h]; simp)
  · exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hpow1)

end Nu

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
