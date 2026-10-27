module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocalBasic
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterProjective
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialDGroup
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchLocal

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

theorem mem_ker_κ_iff (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (c : C t) :
    κ c = 1 ↔ (c : G) ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers t := by
  rw [← MonoidHom.mem_ker, h.ker_κ]
  have hmap : (NZ t).map (C t).subtype = (N t).map (C t).subtype ⊔ Subgroup.zpowers t := by
    rw [NZ, Subgroup.map_sup, Z, MonoidHom.map_zpowers]
    rfl
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem (f := (C t).subtype) (C t).subtype_injective).symm

theorem card_B_sup_t (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.card ((N t).map (C t).subtype ⊔ Subgroup.zpowers t : Subgroup G) =
      Nat.card ((N t).map (C t).subtype) * 2 := by
  have hL := h.localData
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer
      (((N t).map (C t).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hL.B_conj t (Subgroup.mem_centralizer_singleton_iff.mpr rfl) x hx,
      fun hx => by
        have := hL.B_conj t (Subgroup.mem_centralizer_singleton_iff.mpr rfl) _ hx
        rwa [show t * (t * x * t⁻¹) * t⁻¹ = x by
          have ht : t⁻¹ = t := hL.t_inv_eq
          rw [ht, ← mul_assoc, ← mul_assoc, hL.t_sq, one_mul, mul_assoc, hL.t_sq, mul_one]] at this⟩
  have hdisj : Disjoint ((N t).map (C t).subtype) (Subgroup.zpowers t) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxB, hxt⟩
    rw [Subgroup.mem_bot]
    rcases hL.zpowers_t_cases x hxt with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hxB
      exact hL.not_odd_t (hL.B_odd t hxB)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, hL.t_orderOf]

theorem card_ker_κ (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.card κ.ker = Nat.card ((N t).map (C t).subtype) * 2 := by
  rw [← h.card_B_sup_t]
  have : κ.ker.map (C t).subtype = (N t).map (C t).subtype ⊔ Subgroup.zpowers t := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (h.mem_ker_κ_iff c).mp hc
    · intro hx
      have hxC : x ∈ C t := by
        refine (sup_le (Subgroup.map_subtype_le _) ?_) hx
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      exact ⟨⟨x, hxC⟩, (h.mem_ker_κ_iff ⟨x, hxC⟩).mpr hx, rfl⟩
  rw [← this, Subgroup.card_map_of_injective (C t).subtype_injective]

theorem card_comap_κ (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (Y : Subgroup (Equiv.Perm (Omega F))) (hY : Y ≤ coordinateD F) :
    Nat.card (Y.comap κ) = Nat.card Y * (Nat.card ((N t).map (C t).subtype) * 2) := by
  rw [UnitaryBranch.card_comap_of_le_range κ Y (h.range_κ ▸ hY), h.card_ker_κ]

omit [Finite G] in
theorem mem_of_pow_eq_one_of_mem_sup {Q Z : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQ : IsPGroup q Q) (hZ : Nat.Coprime q (Nat.card Z)) [Finite Z]
    (hZQ : ∀ z ∈ Z, ∀ u ∈ Q, z * u = u * z) {v : G} (hv : v ∈ Q ⊔ Z) {a : ℕ}
    (hva : v ^ q ^ a = 1) : v ∈ Q := by
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup (fun u hu z hz => (hZQ z hz u hu).symm) hv
  obtain ⟨b, hb⟩ := hQ ⟨u, hu⟩
  have hub : u ^ q ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcomm : Commute u z := (hZQ z hz u hu).symm
  have hm : (u * z) ^ q ^ (a + b) = 1 := by
    rw [pow_add, pow_mul, hva, one_pow]
  have hu' : u ^ q ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hub, one_pow]
  have hzm : z ^ q ^ (a + b) = 1 := by
    rw [hcomm.mul_pow, hu', one_mul] at hm
    exact hm
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ q ^ (a + b) := orderOf_dvd_of_pow_eq_one hzm
    have h2 : orderOf z ∣ Nat.card Z := by
      have := Subgroup.orderOf_dvd_natCard Z hz
      exact this
    have h3 : Nat.Coprime (q ^ (a + b)) (Nat.card Z) := Nat.Coprime.pow_left _ hZ
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2
    exact orderOf_eq_one_iff.mp this
  rw [hz1, mul_one]
  exact hu

theorem mem_coordinateG_iff (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (c : C t) :
    κ c ∈ coordinateG F ↔ (c : G) ∈ J ⊔ (N t).map (C t).subtype := by
  have hL := h.localData
  constructor
  · intro hc
    rw [← h.layer_κ] at hc
    obtain ⟨j, hj, hjc⟩ := hc
    have hker : κ (j⁻¹ * c) = 1 := by rw [map_mul, map_inv, hjc, inv_mul_cancel]
    rw [h.mem_ker_κ_iff] at hker
    have hjJ : (j : G) ∈ J := hj
    have hmem : (c : G) = j * ((j⁻¹ * c : C t) : G) := by simp
    rw [hmem]
    have hle : (N t).map (C t).subtype ⊔ Subgroup.zpowers t ≤ J ⊔ (N t).map (C t).subtype :=
      sup_le le_sup_right ((Subgroup.zpowers_le.mpr hL.t_mem).trans le_sup_left)
    exact (J ⊔ (N t).map (C t).subtype).mul_mem (Subgroup.mem_sup_left hjJ) (hle hker)
  · intro hc
    obtain ⟨j, hj, b, hb, hjb⟩ := exists_mul_of_mem_sup hL.JB_comm hc
    have hjC : j ∈ C t := hL.J_le hj
    have hbC : b ∈ C t := hL.B_le hb
    have hκb : κ ⟨b, hbC⟩ = 1 := (h.mem_ker_κ_iff ⟨b, hbC⟩).mpr (Subgroup.mem_sup_left hb)
    have hceq : c = ⟨j, hjC⟩ * ⟨b, hbC⟩ := Subtype.ext hjb
    rw [hceq, map_mul, hκb, mul_one, ← h.layer_κ]
    exact ⟨⟨j, hjC⟩, hj, rfl⟩

theorem κ_s₀ (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    κ ⟨s₀, h.localData.s_mem_C⟩ ∉ coordinateG F ∧ orderOf (κ ⟨s₀, h.localData.s_mem_C⟩) = 2 := by
  have hL := h.localData
  have hnot : s₀ ∉ J ⊔ (N t).map (C t).subtype := by
    intro hs
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.B_ne_bot
    have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have h1 := hL.commute_B_of_mem_sup hs hb
    have h2 := hL.s_inv b hb
    rw [h1, mul_inv_cancel_right] at h2
    exact hb1' (eq_one_of_mul_self_eq_one_of_odd (hL.B_odd b hb)
      (by calc b * b = b⁻¹ * b := by rw [← h2]
            _ = 1 := inv_mul_cancel b))
  refine ⟨fun hG => hnot ((h.mem_coordinateG_iff _).mp hG), ?_⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have : (⟨s₀, hL.s_mem_C⟩ : C t) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hL.s_sq)
    rw [this, map_one]
  · intro h1
    apply hnot
    have := (h.mem_ker_κ_iff _).mp h1
    have hle : (N t).map (C t).subtype ⊔ Subgroup.zpowers t ≤ J ⊔ (N t).map (C t).subtype :=
      sup_le le_sup_right ((Subgroup.zpowers_le.mpr hL.t_mem).trans le_sup_left)
    exact hle this

theorem mem_J_of_pow_eq_one (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {x : G}
    (hxC : x ∈ C t) {a : ℕ} (hxa : x ^ p ^ a = 1) : x ∈ J := by
  have hL := h.localData
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (orderOf x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hxa)
    rw [hk]
    exact h.odd.pow
  obtain ⟨j, hj, b, hb, rfl⟩ := exists_mul_of_mem_sup hL.JB_comm (hL.odd_mem x hxC hodd)
  have hpg : IsPGroup p (Subgroup.zpowers (j * b)) := by
    refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hxa
  have hbp := hL.isPGroup_zpowers_of_mul hj hb hpg
  obtain ⟨c, hc⟩ := hbp ⟨b, Subgroup.mem_zpowers b⟩
  have hc' : b ^ p ^ c = 1 := by simpa using congrArg Subtype.val hc
  have h1 : orderOf b ∣ p ^ c := orderOf_dvd_of_pow_eq_one hc'
  have h2 : orderOf b ∣ Nat.card ((N t).map (C t).subtype) := Subgroup.orderOf_dvd_natCard _ hb
  obtain ⟨-, hpB, -⟩ := h.card_W_B_arith
  have h3 : Nat.Coprime (p ^ c) (Nat.card ((N t).map (C t).subtype)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpB)
  have hb1 : b = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2)
  rw [hb1, mul_one]
  exact hj

theorem factorization_card_C (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    (Nat.card (C t)).factorization p = f := by
  have hp := h.prime
  have hf := h.one_le
  obtain ⟨-, hpB, -⟩ := h.card_W_B_arith
  have hq1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
  have hpq : p ∣ (p ^ f) ^ 2 := (dvd_pow_self p (by omega)).trans (dvd_pow_self _ two_ne_zero)
  have hm : ¬ p ∣ 2 * Nat.card ((N t).map (C t).subtype) * ((p ^ f) ^ 2 - 1) := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        subst this
        exact absurd h.odd (by decide)
      · exact hpB h2
    · have := (Nat.dvd_sub_iff_right hq1 hpq).mp h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  rw [h.card_C, show 2 * Nat.card ((N t).map (C t).subtype) * p ^ f * ((p ^ f) ^ 2 - 1) =
    p ^ f * (2 * Nat.card ((N t).map (C t).subtype) * ((p ^ f) ^ 2 - 1)) by ring]
  exact UnitaryBranch.factorization_prime_pow_mul hp hm

theorem injOn_κ_of_coprime (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {X : Subgroup G}
    (hcop : Nat.Coprime (Nat.card X) (Nat.card ((N t).map (C t).subtype) * 2)) :
    Set.InjOn κ (X.subgroupOf (C t)) := by
  intro a ha b hb hab
  have hker : κ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  rw [h.mem_ker_κ_iff] at hker
  have hX : ((a⁻¹ * b : C t) : G) ∈ X := X.mul_mem (X.inv_mem ha) hb
  have h1 : orderOf ((a⁻¹ * b : C t) : G) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hX
  have h2 : orderOf ((a⁻¹ * b : C t) : G) ∣ Nat.card ((N t).map (C t).subtype) * 2 := by
    rw [← h.card_B_sup_t]
    exact Subgroup.orderOf_dvd_natCard _ hker
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff] at h3
  have h4 : a⁻¹ * b = 1 := Subtype.ext h3
  exact (inv_mul_eq_one.mp h4)

theorem card_map_κ_of_coprime (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {X : Subgroup G} (hXC : X ≤ C t)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card ((N t).map (C t).subtype) * 2)) :
    Nat.card ((X.subgroupOf (C t)).map κ) = Nat.card X := by
  rw [← Nat.card_congr (mulEquivMapOfInjOn κ (h.injOn_κ_of_coprime hcop)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]

theorem coprime_of_isPGroup (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {X : Subgroup G} (hX : IsPGroup p X) :
    Nat.Coprime (Nat.card X) (Nat.card ((N t).map (C t).subtype) * 2) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  apply Nat.Coprime.pow_left
  obtain ⟨-, hpB, -⟩ := h.card_W_B_arith
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · exact hpB h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1
    subst this
    exact absurd h.odd (by decide)

theorem commute_of_mem_ker (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {z : G}
    (hz : z ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers t) {u : G} (hu : u ∈ J) :
    z * u = u * z := by
  have hL := h.localData
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_mul_of_mem_sup (fun b hb k hk => by
    rcases hL.zpowers_t_cases k hk with hk1 | hkt
    · rw [hk1, mul_one, one_mul]
    · rw [hkt]; exact Subgroup.mem_centralizer_singleton_iff.mp (hL.B_le hb)) hz
  have h1 : b * u = u * b := (hL.JB_comm u hu b hb).symm
  have h2 : k * u = u * k := by
    rcases hL.zpowers_t_cases k hk with hk1 | hkt
    · rw [hk1, mul_one, one_mul]
    · rw [hkt]; exact (Subgroup.mem_centralizer_singleton_iff.mp (hL.J_le hu)).symm
  calc b * k * u = b * (k * u) := by group
    _ = b * (u * k) := by rw [h2]
    _ = (b * u) * k := by group
    _ = u * b * k := by rw [h1]
    _ = u * (b * k) := by group

theorem coprime_card_ker (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.Coprime p (Nat.card ((N t).map (C t).subtype ⊔ Subgroup.zpowers t : Subgroup G)) := by
  have hp := h.prime
  obtain ⟨-, hpB, -⟩ := h.card_W_B_arith
  rw [h.card_B_sup_t, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · exact hpB h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1
    subst this
    exact absurd h.odd (by decide)

theorem mem_sup_ker_of_κ_mem (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {M : Subgroup G} {c : C t} (hc : κ c ∈ (M.subgroupOf (C t)).map κ) :
    (c : G) ∈ M ⊔ ((N t).map (C t).subtype ⊔ Subgroup.zpowers t) := by
  obtain ⟨u, hu, huc⟩ := hc
  have hker : κ (u⁻¹ * c) = 1 := by rw [map_mul, map_inv, huc, inv_mul_cancel]
  rw [h.mem_ker_κ_iff] at hker
  have : (c : G) = (u : G) * ((u⁻¹ * c : C t) : G) := by simp
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hker)

theorem mem_of_κ_mem_map (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {M : Subgroup G} (hker : (N t).map (C t).subtype ⊔ Subgroup.zpowers t ≤ M) {c : C t}
    (hc : κ c ∈ (M.subgroupOf (C t)).map κ) : (c : G) ∈ M :=
  sup_le le_rfl hker (h.mem_sup_ker_of_κ_mem hc)

theorem conj_eq_inv_of_not_mem_sup (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {c : G} (hc : c ∈ C t) (hcJB : c ∉ J ⊔ (N t).map (C t).subtype) {b : G}
    (hb : b ∈ (N t).map (C t).subtype) : c * b * c⁻¹ = b⁻¹ := by
  have hL := h.localData
  obtain ⟨x, hx, y, hy, hxy | hxy⟩ := hL.cover c hc
  · exact absurd (hxy ▸ Subgroup.mul_mem_sup hx hy) hcJB
  · subst hxy
    have hb' : b⁻¹ ∈ (N t).map (C t).subtype := Subgroup.inv_mem _ hb
    have h1 : s₀ * b * s₀⁻¹ = b⁻¹ := hL.s_inv b hb
    have h2 : y * b⁻¹ * y⁻¹ = b⁻¹ := by rw [hL.B_comm y hy b⁻¹ hb', mul_inv_cancel_right]
    have h3 : x * b⁻¹ * x⁻¹ = b⁻¹ := by rw [hL.JB_comm x hx b⁻¹ hb', mul_inv_cancel_right]
    calc x * y * s₀ * b * (x * y * s₀)⁻¹ = x * (y * (s₀ * b * s₀⁻¹) * y⁻¹) * x⁻¹ := by group
      _ = b⁻¹ := by rw [h1, h2, h3]

theorem mem_normalizer_sylow_iff (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {Q₁ : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t)) {x₀ : Omega F}
    (hx₀ : ∀ g ∈ (Q₁.subgroupOf (C t)).map κ, g x₀ = x₀) (c : C t) :
    (c : G) ∈ Subgroup.normalizer (Q₁ : Set G) ↔ κ c x₀ = x₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hQC : Q₁ ≤ C t := hQ₁.le
  have hQp : IsPGroup p Q₁ := hQ₁.isPGroup
  have hcard : Nat.card Q₁ = p ^ f := by rw [hQ₁.card_eq, h.factorization_card_C]
  have hQJ : Q₁ ≤ J := fun x hx => by
    obtain ⟨a, ha⟩ := hQp ⟨x, hx⟩
    exact h.mem_J_of_pow_eq_one (hQC hx) (by simpa using congrArg Subtype.val ha)
  set X := (Q₁.subgroupOf (C t)).map κ with hX
  have hXD : X ≤ coordinateD F := h.range_κ ▸ Subgroup.map_le_range κ _
  have hXp : IsPGroup p X := (hQp.comap_subtype (K := C t)).map κ
  have hXcard : Nat.card X = p ^ f := by
    rw [h.card_map_κ_of_coprime hQC (h.coprime_of_isPGroup hQp), hcard]
  have hX1 : X ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hXcard
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) hp.one_lt
    omega
  constructor
  · intro hcN
    have hκN : κ c ∈ Subgroup.normalizer (X : Set (Equiv.Perm (Omega F))) := by
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨c * u * c⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp hcN (u : G)).mp hu
    exact fixed_of_mem_normalizer_of_isPGroup hp h.odd h.card_F hXD hXp hX1 hx₀ hκN
  · intro hcx
    have hκN := mem_normalizer_of_fixes hp h.card_F hXD hXp hXcard hx₀ (h.range_κ ▸ ⟨c, rfl⟩) hcx
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have huC : u ∈ C t := hQC hu
    have hconjX : κ (c * ⟨u, huC⟩ * c⁻¹) ∈ X := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hκN _).mp ⟨_, (hu : (⟨u, huC⟩ : C t) ∈ _), rfl⟩
    obtain ⟨a, ha⟩ := hQp ⟨u, hu⟩
    have hpow : ((c * ⟨u, huC⟩ * c⁻¹ : C t) : G) ^ p ^ a = 1 := by
      have h1 : u ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conj_pow, h1, mul_one, mul_inv_cancel]
    have := mem_of_pow_eq_one_of_mem_sup hQp h.coprime_card_ker
      (fun z hz u hu => h.commute_of_mem_ker hz (hQJ hu)) (h.mem_sup_ker_of_κ_mem hconjX) hpow
    simpa using this

theorem sylow_C_facts (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {Q₁ : Subgroup G}
    (hQ₁ : IsSylowOf p Q₁ (C t)) :
    Nat.card Q₁ = p ^ f ∧ Q₁ ≤ J ∧ (∀ x ∈ Q₁, ∀ y ∈ Q₁, x * y = y * x) ∧
      C t ⊓ Subgroup.centralizer (Q₁ : Set G) =
        Q₁ ⊔ (N t).map (C t).subtype ⊔ Subgroup.zpowers t ∧
      Nat.card (C t ⊓ Subgroup.normalizer (Q₁ : Set G) : Subgroup G) =
        2 * Nat.card ((N t).map (C t).subtype) * p ^ f * (p ^ f - 1) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hL := h.localData
  have hQC : Q₁ ≤ C t := hQ₁.le
  have hQp : IsPGroup p Q₁ := hQ₁.isPGroup
  have hcard : Nat.card Q₁ = p ^ f := by rw [hQ₁.card_eq, h.factorization_card_C]
  have hQJ : Q₁ ≤ J := fun x hx => by
    obtain ⟨a, ha⟩ := hQp ⟨x, hx⟩
    exact h.mem_J_of_pow_eq_one (hQC hx) (by simpa using congrArg Subtype.val ha)
  have hcop := h.coprime_of_isPGroup hQp
  set X := (Q₁.subgroupOf (C t)).map κ with hX
  have hXD : X ≤ coordinateD F := h.range_κ ▸ Subgroup.map_le_range κ _
  have hXp : IsPGroup p X := (hQp.comap_subtype (K := C t)).map κ
  have hXcard : Nat.card X = p ^ f := by rw [h.card_map_κ_of_coprime hQC hcop, hcard]
  have hXC := coordinateD_inf_centralizer_eq_of_isPGroup hp h.odd h.card_F hXD hXp hXcard
  have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ coordinateD F ⊓ Subgroup.centralizer (X : Set (Equiv.Perm (Omega F))) := by
      rw [hXC]; exact hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb').2 a ha)
  have hinj := h.injOn_κ_of_coprime hcop
  have hab : ∀ x ∈ Q₁, ∀ y ∈ Q₁, x * y = y * x := by
    intro x hx y hy
    have hx' : (⟨x, hQC hx⟩ : C t) ∈ Q₁.subgroupOf (C t) := hx
    have hy' : (⟨y, hQC hy⟩ : C t) ∈ Q₁.subgroupOf (C t) := hy
    have h1 := hXab _ ⟨_, hx', rfl⟩ _ ⟨_, hy', rfl⟩
    rw [← map_mul, ← map_mul] at h1
    have := hinj (Subgroup.mul_mem _ hx' hy') (Subgroup.mul_mem _ hy' hx') h1
    exact congrArg Subtype.val this
  refine ⟨hcard, hQJ, hab, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨hxC, hxQ⟩
      have hκx : κ ⟨x, hxC⟩ ∈ X := by
        rw [← hXC]
        refine Subgroup.mem_inf.mpr ⟨h.range_κ ▸ ⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxQ _ hu)
      rw [sup_assoc]
      exact h.mem_sup_ker_of_κ_mem hκx
    · refine sup_le (sup_le (le_inf hQC fun x hx => Subgroup.mem_centralizer_iff.mpr
        fun y hy => hab y hy x hx) (le_inf hL.B_le fun b hb => Subgroup.mem_centralizer_iff.mpr
        fun y hy => (hL.JB_comm y (hQJ hy) b hb))) ?_
      rw [Subgroup.zpowers_le]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, Subgroup.mem_centralizer_iff.mpr
        fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hQC hy))⟩
  ·
    have hX1 : X ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hXcard
      have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) hp.one_lt
      omega
    obtain ⟨x₀, hx₀, -⟩ := existsUnique_fixed_of_isPGroup hp h.odd h.card_F hXD hXp hX1
    have hpre' : (C t ⊓ Subgroup.normalizer (Q₁ : Set G) : Subgroup G).subgroupOf (C t) =
        (coordinateD F ⊓ MulAction.stabilizer (Equiv.Perm (Omega F)) x₀).comap κ := by
      ext c
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      constructor
      · rintro ⟨-, hcN⟩
        exact ⟨h.range_κ ▸ ⟨c, rfl⟩, (h.mem_normalizer_sylow_iff hQ₁ hx₀ c).mp hcN⟩
      · rintro ⟨-, hcx⟩
        exact ⟨c.2, (h.mem_normalizer_sylow_iff hQ₁ hx₀ c).mpr hcx⟩
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      (C t ⊓ Subgroup.normalizer (Q₁ : Set G) : Subgroup G) ≤ C t)).toEquiv, hpre',
      h.card_comap_κ _ inf_le_left, card_coordinateD_inf_stabilizer, h.card_F]
    ring

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
