module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterData
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialOddComplementCore
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterGeneric
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumBasic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem card_W_B (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    (p ^ f % 4 = 1 → 2 * Nat.card (torusW G t s₀) = p ^ f + 1 ∧
      4 * Nat.card ((N t).map (C t).subtype) = p ^ f - 1) ∧
    (p ^ f % 4 = 3 → 2 * Nat.card (torusW G t s₀) = p ^ f - 1 ∧
      4 * Nat.card ((N t).map (C t).subtype) = p ^ f + 1) ∧
    (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) := by
  obtain ⟨-, h2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h21, -, h23, -⟩ :=
    h.clauses
  rw [h.card_F'] at h21 h23
  have hodd := Nat.odd_iff.mp (h.odd.pow : Odd (p ^ f))
  refine ⟨fun he => ?_, fun he => ?_, h21⟩
  · simp only [he, ↓reduceIte] at h2 h23
    constructor <;> omega
  · have he' : ¬ p ^ f % 4 = 1 := by omega
    simp only [he', ↓reduceIte] at h2 h23
    constructor <;> omega

theorem odd_card_W (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Odd (Nat.card (torusW G t s₀)) := by
  have _ := h.prime
  rw [torusW, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))

theorem odd_card_B (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Odd (Nat.card ((N t).map (C t).subtype)) := by
  have _ := h.prime
  rw [Subgroup.card_map_of_injective (C t).subtype_injective]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))

theorem card_W_B_arith (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    ¬ p ∣ Nat.card (torusW G t s₀) ∧ ¬ p ∣ Nat.card ((N t).map (C t).subtype) ∧
      Nat.Coprime (Nat.card (torusW G t s₀)) (Nat.card ((N t).map (C t).subtype)) := by
  obtain ⟨h1, h3, -⟩ := h.card_W_B
  have hp := h.prime
  have hf := h.one_le
  have hodd := Nat.odd_iff.mp (h.odd.pow : Odd (p ^ f))
  have hBodd := Nat.odd_iff.mp h.odd_card_B
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have key : ∀ a : ℕ, p ∣ a → (a ∣ p ^ f + 1 ∨ a ∣ p ^ f - 1) → False := by
    intro a hpa ha
    rcases ha with ha | ha
    · have h2 := (Nat.dvd_add_right hpq).mp (hpa.trans ha)
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · have h2 := (Nat.dvd_sub_iff_right hq1 hpq).mp (hpa.trans ha)
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases h4 with he | he
  · obtain ⟨hW, hB⟩ := h1 he
    refine ⟨fun hd => key _ hd (Or.inl ⟨2, by rw [← hW]; ring⟩),
      fun hd => key _ hd (Or.inr ⟨4, by rw [← hB]; ring⟩), ?_⟩
    have : Nat.card (torusW G t s₀) = 1 + Nat.card ((N t).map (C t).subtype) * 2 := by omega
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left _
  · obtain ⟨hW, hB⟩ := h3 he
    refine ⟨fun hd => key _ hd (Or.inr ⟨2, by rw [← hW]; ring⟩),
      fun hd => key _ hd (Or.inl ⟨4, by rw [← hB]; ring⟩), ?_⟩
    have : Nat.card ((N t).map (C t).subtype) * 2 = Nat.card (torusW G t s₀) + 1 := by omega
    rw [Nat.coprime_comm]
    have h5 : Nat.Coprime (Nat.card ((N t).map (C t).subtype) * 2) (Nat.card (torusW G t s₀)) := by
      rw [this]
      exact ((Nat.coprime_self_add_left).mpr (Nat.coprime_one_left _)).symm.symm
    exact Nat.Coprime.coprime_mul_right h5

theorem sq_sub_one_eq_eight_mul_odd {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ∃ k, q ^ 2 - 1 = 8 * k ∧ k % 2 = 1 := by
  have h16 : q ^ 2 % 16 = 9 := by
    have : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
    rw [Nat.pow_mod]
    rcases this with h | h | h | h <;> rw [h]
  refine ⟨(q ^ 2 - 1) / 8, ?_, ?_⟩ <;>
  · generalize q ^ 2 = x at h16 ⊢
    omega

theorem exists_card_C_eq (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    ∃ m, Nat.card (C t) = 16 * m ∧ m % 2 = 1 := by
  obtain ⟨-, -, h8⟩ := h.card_W_B
  obtain ⟨k, hk, hkodd⟩ := sq_sub_one_eq_eight_mul_odd h8
  have hBodd := Nat.odd_iff.mp h.odd_card_B
  have hqodd := Nat.odd_iff.mp (h.odd.pow : Odd (p ^ f))
  refine ⟨Nat.card ((N t).map (C t).subtype) * p ^ f * k, ?_, ?_⟩
  · rw [h.card_C, hk]
    ring
  · rw [Nat.mul_mod, Nat.mul_mod (Nat.card _), hBodd, hqodd, hkodd]

theorem card_sylow_two (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (T : Sylow 2 G) :
    Nat.card T = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, -, hSC⟩ := h.sylow_two
  obtain ⟨m, hm, hmodd⟩ := h.exists_card_C_eq
  have hTS : Nat.card T = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  rw [hTS]
  have h16G : 2 ^ 4 ∣ Nat.card G := by
    have := Subgroup.card_subgroup_dvd_card (C t)
    rw [hm] at this
    exact (Dvd.intro m rfl).trans this
  have h1 : 2 ^ 4 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card h16G
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  have h2 : Nat.card S ∣ 16 * m := by
    rw [← hm]
    exact Subgroup.card_dvd_of_le hSC
  have hcop : Nat.Coprime (Nat.card S) m := by
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hmodd))
  have h3 : Nat.card S ∣ 16 := hcop.dvd_of_dvd_mul_right h2
  exact Nat.dvd_antisymm h3 (by simpa using h1)

theorem isKleinFour_V (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    IsKleinFour (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) := by
  have hL := h.localData
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL.t_sq) hL.t_ne_one
  have hs2 : orderOf s₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL.s_sq) hL.s_ne_one
  exact isKleinFour_sup_zpowers ht2 hs2 (Ne.symm hL.s_ne) hL.ts

theorem eq_bot_of_le_centralizer_kleinFour (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.card (Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G)) =
      4 * Nat.card (torusW G t s₀) ∧
    ∀ T X : Subgroup G, IsKleinFour T → IsPGroup p X → X ≤ Subgroup.centralizer (T : Set G) →
      X = ⊥ := by
  obtain ⟨-, -, h3, h4, -⟩ := h.clauses
  set V := (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) with hV
  have hWV : torusW G t s₀ ≤ Subgroup.normalizer (V : Set G) :=
    ((le_sup_right : torusW G t s₀ ≤ V ⊔ torusW G t s₀).trans h3.le).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card (Subgroup.centralizer (V : Set G)) = 4 * Nat.card (torusW G t s₀) := by
    rw [← h3, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hWV h4,
      h.isKleinFour_V.card_four]
  refine ⟨hcard, fun T X hT hX hXT => ?_⟩
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := h.four_conj T hT
  have hXV : X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (V : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ T.map (MulAut.conj g).toMonoidHom := by rw [hg]; exact hv
    obtain ⟨τ, hτ, rfl⟩ := hv'
    have := Subgroup.mem_centralizer_iff.mp (hXT hx) τ hτ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * τ * g⁻¹ * (g * x * g⁻¹) = g * (τ * x) * g⁻¹ := by group
      _ = g * (x * τ) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * τ * g⁻¹) := by group
  have hdvd := Subgroup.card_dvd_of_le hXV
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk] at hdvd
  obtain ⟨hpW, -, -⟩ := h.card_W_B_arith
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : p ∣ 4 * Nat.card (torusW G t s₀) := (dvd_pow_self p hk0).trans hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h4 | hW
    · have h2 : p ∣ 2 ^ 2 := by norm_num; exact h4
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      rw [this] at h
      exact absurd h.odd (by decide)
    · exact hpW hW
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq X hk

theorem mem_centralizer_V_iff (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {x : G} :
    x ∈ Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) ↔
      t * x = x * t ∧ s₀ * x = x * s₀ := by
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    exact ⟨hx t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)),
      hx s₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))⟩
  · rintro ⟨h1, h2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases h.localData.mem_V_cases hv with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · calc t * s₀ * x = t * (s₀ * x) := by group
        _ = t * (x * s₀) := by rw [h2]
        _ = (t * x) * s₀ := by group
        _ = x * t * s₀ := by rw [h1]
        _ = x * (t * s₀) := by group

theorem exists_three_cycle (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    ∃ τ : G, τ * t * τ⁻¹ = s₀ ∧ τ * s₀ * τ⁻¹ = t * s₀ ∧
      ∀ w ∈ torusW G t s₀, τ * w * τ⁻¹ ∈ torusW G t s₀ := by
  obtain ⟨τ, h1, h2⟩ := h.three_cycle
  refine ⟨τ, h1, h2, ?_⟩
  set D := Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) :
    Set G) with hD
  have hconjD : ∀ x ∈ D, τ * x * τ⁻¹ ∈ D := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := h.mem_centralizer_V_iff.mp hx
    have hs : s₀ * (τ * x * τ⁻¹) = (τ * x * τ⁻¹) * s₀ := by
      rw [← h1]
      calc τ * t * τ⁻¹ * (τ * x * τ⁻¹) = τ * (t * x) * τ⁻¹ := by group
        _ = τ * (x * t) * τ⁻¹ := by rw [hx1]
        _ = τ * x * τ⁻¹ * (τ * t * τ⁻¹) := by group
    have hts : t * s₀ * (τ * x * τ⁻¹) = (τ * x * τ⁻¹) * (t * s₀) := by
      rw [← h2]
      calc τ * s₀ * τ⁻¹ * (τ * x * τ⁻¹) = τ * (s₀ * x) * τ⁻¹ := by group
        _ = τ * (x * s₀) * τ⁻¹ := by rw [hx2]
        _ = τ * x * τ⁻¹ * (τ * s₀ * τ⁻¹) := by group
    refine h.mem_centralizer_V_iff.mpr ⟨?_, hs⟩
    set y := τ * x * τ⁻¹
    calc t * y = t * s₀ * y * s₀⁻¹ * (s₀ * s₀⁻¹) := by
          rw [mul_inv_cancel, mul_one]
          calc t * y = t * s₀ * (s₀⁻¹ * y) := by group
            _ = t * s₀ * (y * s₀⁻¹) := by
              congr 1
              have : y * s₀ = s₀ * y := hs.symm
              calc s₀⁻¹ * y = s₀⁻¹ * (y * s₀) * s₀⁻¹ := by group
                _ = s₀⁻¹ * (s₀ * y) * s₀⁻¹ := by rw [this]
                _ = y * s₀⁻¹ := by group
            _ = t * s₀ * y * s₀⁻¹ := by group
      _ = y * (t * s₀) * s₀⁻¹ * (s₀ * s₀⁻¹) := by rw [hts]
      _ = y * t := by group
  have hDmap : D.map (MulAut.conj τ).toMonoidHom = D := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hconjD x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective]
  let e : D ≃* D := ((MulAut.conj τ).subgroupMap D).trans (MulEquiv.subgroupCongr hDmap)
  have he : ∀ x : D, ((e x : D) : G) = τ * x * τ⁻¹ := fun x => rfl
  have hmap := CFSG.pPrimeCore_map_iso 2 e
  intro w hw
  obtain ⟨w', hw', rfl⟩ := hw
  have : e w' ∈ CFSG.pPrimeCore 2 D := by
    rw [← hmap]
    exact ⟨w', hw', rfl⟩
  exact ⟨e w', this, he w'⟩

theorem le_C_of_isPGroup (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓB : ℓ ∣ Nat.card ((N t).map (C t).subtype))
    (P : Sylow ℓ ((N t).map (C t).subtype)) {Q : Subgroup G} (hQ : IsPGroup ℓ Q)
    (hPQ : (P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype ≤ Q) :
    Q ≤ C t ∧ Subgroup.normalizer (Q : Set G) ≤ C t := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hPC : (P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype ≤
      C t := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hQC : Q ≤ C t := by
    have hQ'p : IsPGroup ℓ (Q ⊓ C t : Subgroup G) := hQ.to_le inf_le_left
    have hNQ' := h.sylow_normalizer ℓ hℓ hℓB P _ inf_le_right hQ'p (le_inf hPQ hPC)
    by_contra hne
    have hne' : (Q ⊓ C t : Subgroup G) ≠ Q := fun heq => hne (heq ▸ inf_le_right)
    obtain ⟨y, hyQ, hyN, hyQ'⟩ := exists_mem_normalizer_not_mem_of_isPGroup hQ inf_le_left hne'
    exact hyQ' ⟨hyQ, hNQ' hyN⟩
  exact ⟨hQC, h.sylow_normalizer ℓ hℓ hℓB P Q hQC hQ hPQ⟩

theorem card_W_sup_B (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.card (torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
      Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) := by
  have hL := h.localData
  have hBW : (N t).map (C t).subtype ≤ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) :
      Set G) := hL.B_le_centralizer_W.trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint (torusW G t s₀) ((N t).map (C t).subtype) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxW, hxB⟩
    have : x ∈ J ⊓ (N t).map (C t).subtype := ⟨hL.W_le_J hxW, hxB⟩
    rwa [hL.JB_disj] at this
  exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hBW hdisj

theorem exists_normal_complement_torus_core (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (R : Subgroup G) (hR : Odd (Nat.card R)) (hWR : torusW G t s₀ ≤ R)
    (hBR : (N t).map (C t).subtype ≤ R)
    (hHall : Nat.Coprime (Nat.card (torusW G t s₀))
      ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀))) :
    Nat.card (torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
        Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ∧
      ∃ U : Subgroup G, U ≤ R ∧ R ≤ Subgroup.normalizer (U : Set G) ∧
        Disjoint U (torusW G t s₀ ⊔ (N t).map (C t).subtype) ∧
        U ⊔ (torusW G t s₀ ⊔ (N t).map (C t).subtype) = R ∧
        Nat.card U * Nat.card (torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
          Nat.card R ∧
        Nat.Coprime (Nat.card U) (Nat.card (torusW G t s₀)) := by
  set W := torusW G t s₀ with hW
  set B := (N t).map (C t).subtype with hB
  have hL := h.localData
  have hWB := h.card_W_sup_B
  refine ⟨hWB, ?_⟩
  obtain ⟨hHallR, M₁, hM₁R, hRM₁, hM₁W, -, hM₁card⟩ :=
    odd_subgroup_torus_hall_normal_complement h.clauses R hR hWR hHall
  obtain ⟨M₂, hM₂R, hRM₂, hM₂B, -, hM₂card⟩ :=
    hL.odd_normal_complement h.confine h.sylow_normalizer hR hBR
  obtain ⟨-, -, hcopWB⟩ := h.card_W_B_arith
  have hW0 : 0 < Nat.card W := Nat.card_pos
  have hB0 : 0 < Nat.card B := Nat.card_pos
  have hrel₁ : M₁.relIndex R = Nat.card W := by
    have := Subgroup.relIndex_mul_card M₁ R
    rw [inf_of_le_left hM₁R, ← hM₁card] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [this, mul_comm])
  have hrel₂ : M₂.relIndex R = Nat.card B := by
    have := Subgroup.relIndex_mul_card M₂ R
    rw [inf_of_le_left hM₂R, ← hM₂card] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [this, mul_comm])
  have hBM₁ : B ≤ M₁ := le_of_coprime_relIndex hM₁R hRM₁ hBR (by rw [hrel₁]; exact hcopWB.symm)
  have hWM₂ : W ≤ M₂ := le_of_coprime_relIndex hM₂R hRM₂ hWR (by rw [hrel₂]; exact hcopWB)
  set U := M₁ ⊓ M₂ with hU
  have hUR : U ≤ R := inf_le_left.trans hM₁R
  have hRU : R ≤ Subgroup.normalizer (U : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp (hRM₁ hr) x,
      ← Subgroup.mem_normalizer_iff.mp (hRM₂ hr) x]
  have hdisj : Disjoint U (W ⊔ B) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨hx₁, hx₂⟩, hxWB⟩
    obtain ⟨w, hw, b, hb, rfl⟩ := exists_mul_of_mem_sup (fun w hw b hb =>
      (Subgroup.mem_centralizer_iff.mp (hL.B_le_centralizer_W hb) w hw)) hxWB
    have hwM₁ : w ∈ M₁ := by
      have := M₁.mul_mem hx₁ (M₁.inv_mem (hBM₁ hb))
      rwa [mul_inv_cancel_right] at this
    have hw1 : w = 1 := by
      have : w ∈ M₁ ⊓ W := ⟨hwM₁, hw⟩
      rwa [disjoint_iff.mp hM₁W, Subgroup.mem_bot] at this
    subst hw1
    rw [one_mul] at hx₂ ⊢
    have : b ∈ M₂ ⊓ B := ⟨hx₂, hb⟩
    rwa [disjoint_iff.mp hM₂B] at this
  have hrelU : U.relIndex R ≤ Nat.card W * Nat.card B := by
    rw [← hrel₁, ← hrel₂]
    exact Subgroup.relIndex_inf_le
  have hcardU : Nat.card R ≤ Nat.card U * (Nat.card W * Nat.card B) := by
    have := Subgroup.relIndex_mul_card U R
    rw [inf_of_le_left hUR] at this
    rw [← this, mul_comm (U.relIndex R)]
    exact Nat.mul_le_mul_left _ hrelU
  have hWBU : W ⊔ B ≤ Subgroup.normalizer (U : Set G) := (sup_le hWR hBR).trans hRU
  have hsup : Nat.card (U ⊔ (W ⊔ B) : Subgroup G) =
      Nat.card U * Nat.card (W ⊔ B : Subgroup G) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U (W ⊔ B) hWBU hdisj
  have hle : U ⊔ (W ⊔ B) ≤ R := sup_le hUR (sup_le hWR hBR)
  have heq : U ⊔ (W ⊔ B) = R := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hsup, hWB]
    exact hcardU
  have hM₁rel : Nat.card M₁ = W.relIndex R := by
    have h1 := Subgroup.relIndex_mul_card W R
    rw [inf_of_le_left hWR, ← hM₁card] at h1
    exact Nat.eq_of_mul_eq_mul_right hW0 h1.symm
  refine ⟨U, hUR, hRU, hdisj, heq, ?_, ?_⟩
  · rw [← hsup, heq]
  · have hdvd : Nat.card U ∣ Nat.card M₁ := Subgroup.card_dvd_of_le inf_le_left
    rw [hM₁rel] at hdvd
    exact Nat.Coprime.coprime_dvd_left hdvd hHallR.symm

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
