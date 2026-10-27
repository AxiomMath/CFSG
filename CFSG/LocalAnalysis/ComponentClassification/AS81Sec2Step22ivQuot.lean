module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.AS81.Sec2Quot

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem card_map_mul_card_inf_ker {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K)
    (Y : Subgroup H) : Nat.card (Y.map f) * Nat.card (Y ⊓ f.ker : Subgroup H) = Nat.card Y := by
  set g : ↥Y →* K := f.comp Y.subtype with hg
  have h1 := Subgroup.card_ker_mul_card_range g
  have hrange : g.range = Y.map f := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card g.ker = Nat.card (Y ⊓ f.ker : Subgroup H) := by
    have : g.ker = f.ker.subgroupOf Y := rfl
    rw [this, ← Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [hrange, hker, mul_comm] at h1
  exact h1

section Bar

variable {G : Type} [Group G] (W : Subgroup G)

@[expose] def nbar (X : Subgroup G) :
    Subgroup (↥(normalizer (W : Set G)) ⧸ W.subgroupOf (normalizer (W : Set G))) :=
  (X.subgroupOf (normalizer (W : Set G))).map (QuotientGroup.mk' _)

local notation "π" => QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))

variable {W}

theorem mk_eq_one_iff (n : ↥(normalizer (W : Set G))) : π n = 1 ↔ (n : G) ∈ W := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem mk_mem_nbar_iff {X : Subgroup G} (n : ↥(normalizer (W : Set G))) :
    π n ∈ nbar W X ↔ ∃ x ∈ X, x⁻¹ * (n : G) ∈ W := by
  constructor
  · rintro ⟨m, hm, hmn⟩
    refine ⟨m, mem_subgroupOf.mp hm, ?_⟩
    have h : π (m⁻¹ * n) = 1 := by rw [map_mul, map_inv, hmn, inv_mul_cancel]
    rw [mk_eq_one_iff] at h
    simpa using h
  · rintro ⟨x, hx, hxn⟩
    have hxN : x ∈ normalizer (W : Set G) := by
      have : x = n * (x⁻¹ * n)⁻¹ := by group
      rw [this]
      exact mul_mem n.2 (inv_mem (le_normalizer hxn))
    refine ⟨⟨x, hxN⟩, mem_subgroupOf.mpr hx, ?_⟩
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, mk_eq_one_iff]
    have : ((⟨x, hxN⟩ * n⁻¹ : ↥(normalizer (W : Set G))) : G) = x * (x⁻¹ * n)⁻¹ * x⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    rw [this]
    exact (mem_normalizer_iff.mp hxN _).mp (inv_mem hxn)

theorem mk_mem_nbar {X : Subgroup G} {x : G} (hx : x ∈ X) (hxN : x ∈ normalizer (W : Set G)) :
    π ⟨x, hxN⟩ ∈ nbar W X :=
  ⟨⟨x, hxN⟩, mem_subgroupOf.mpr hx, rfl⟩

theorem nbar_mono {X Y : Subgroup G} (h : X ≤ Y) : nbar W X ≤ nbar W Y :=
  map_mono fun _ hx => h hx

theorem isPGroup_nbar {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) : IsPGroup p (nbar W X) :=
  hX.comap_subtype.map _

theorem isElemAbelian_nbar {p : ℕ} {X : Subgroup G} (hX : IsElemAbelian p X) :
    IsElemAbelian p (nbar W X) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, z, hz, rfl⟩ := b
    apply Subtype.ext
    simp only [coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    have h := congrArg Subtype.val
      (hX.1.is_comm.comm ⟨x, mem_subgroupOf.mp hx⟩ ⟨z, mem_subgroupOf.mp hz⟩)
    exact Subtype.ext h
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (by simpa using hX.2 _ (mem_subgroupOf.mp hx)),
      map_one]

theorem card_nbar [Finite G] {X : Subgroup G} (hXN : X ≤ normalizer (W : Set G)) :
    Nat.card (nbar W X) * Nat.card (X ⊓ W : Subgroup G) = Nat.card X := by
  have h := card_map_mul_card_inf_ker π (X.subgroupOf (normalizer (W : Set G)))
  have hinf : X.subgroupOf (normalizer (W : Set G)) ⊓ W.subgroupOf (normalizer (W : Set G)) =
      (X ⊓ W).subgroupOf (normalizer (W : Set G)) := (Subgroup.comap_inf _ _ _).symm
  rw [QuotientGroup.ker_mk', hinf,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hXN)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv] at h
  exact h

theorem isSylowOf_nbar [Finite G] {T L : Subgroup G} (hTL : IsSylowOf 2 T L)
    (hLN : L ≤ normalizer (W : Set G)) (hLW : L ⊓ W ≤ T) :
    IsSylowOf 2 (nbar W T) (nbar W L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hT2, hidx⟩ := isSylowOf_iff.mp hTL
  refine isSylowOf_iff.mpr ⟨nbar_mono hle, isPGroup_nbar hT2, ?_⟩
  have hTW : T ⊓ W = L ⊓ W := le_antisymm (inf_le_inf_right W hle) (le_inf hLW inf_le_right)
  have h1 := card_nbar (hle.trans hLN)
  have h2 := card_nbar hLN
  have h3 := relIndex_mul_card (nbar W T) (nbar W L)
  have h4 := relIndex_mul_card T L
  rw [inf_eq_left.mpr (nbar_mono hle)] at h3
  rw [inf_eq_left.mpr hle] at h4
  rw [hTW] at h1
  have hpos : 0 < Nat.card (nbar W T) * Nat.card (L ⊓ W : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have heq : (nbar W T).relIndex (nbar W L) = T.relIndex L := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (nbar W T).relIndex (nbar W L) * (Nat.card (nbar W T) * Nat.card (L ⊓ W : Subgroup G))
        = Nat.card (nbar W L) * Nat.card (L ⊓ W : Subgroup G) := by rw [← h3]; ring
      _ = Nat.card L := h2
      _ = T.relIndex L * Nat.card T := h4.symm
      _ = T.relIndex L * (Nat.card (nbar W T) * Nat.card (L ⊓ W : Subgroup G)) := by rw [h1]
  rw [heq]
  exact hidx

theorem mk_mem_normalizer_nbar {X : Subgroup G} {n : ↥(normalizer (W : Set G))}
    (hn : (n : G) ∈ normalizer (X : Set G)) :
    π n ∈ normalizer (nbar W X : Set (↥(normalizer (W : Set G)) ⧸
      W.subgroupOf (normalizer (W : Set G)))) := by
  rw [mem_normalizer_iff]
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_nbar_iff, mk_mem_nbar_iff]
  have hnW := n.2
  constructor
  · rintro ⟨x, hx, hxm⟩
    refine ⟨n * x * (n : G)⁻¹, (mem_normalizer_iff.mp hn x).mp hx, ?_⟩
    have : (n * x * (n : G)⁻¹)⁻¹ * ((n * m * n⁻¹ : ↥(normalizer (W : Set G))) : G) =
        n * (x⁻¹ * m) * (n : G)⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    rw [this]
    exact (mem_normalizer_iff.mp hnW _).mp hxm
  · rintro ⟨x, hx, hxm⟩
    refine ⟨(n : G)⁻¹ * x * n, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
      simpa using this
    · have : ((n : G)⁻¹ * x * n)⁻¹ * (m : G) =
          (n : G)⁻¹ * (x⁻¹ * ((n * m * n⁻¹ : ↥(normalizer (W : Set G))) : G)) * n := by
        simp only [coe_mul, coe_inv]
        group
      rw [this]
      have := (mem_normalizer_iff.mp (inv_mem hnW) _).mp hxm
      simpa using this

theorem nbar_le_centralizer {X Y : Subgroup G} (h : X ≤ centralizer (Y : Set G)) :
    nbar W X ≤ centralizer (nbar W Y : Set (↥(normalizer (W : Set G)) ⧸
      W.subgroupOf (normalizer (W : Set G)))) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp (h (mem_subgroupOf.mp hx)) y (mem_subgroupOf.mp hy))

theorem commutator_mem_of_mk_mem_centralizer {Y : Subgroup G}
    (hYN : Y ≤ normalizer (W : Set G)) {n : ↥(normalizer (W : Set G))}
    (hn : π n ∈ centralizer (nbar W Y : Set (↥(normalizer (W : Set G)) ⧸
      W.subgroupOf (normalizer (W : Set G))))) {y : G} (hy : y ∈ Y) :
    (n : G) * y * (n : G)⁻¹ * y⁻¹ ∈ W := by
  have h := mem_centralizer_iff.mp hn _ (mk_mem_nbar hy (hYN hy))
  have h2 : π (n * ⟨y, hYN hy⟩ * n⁻¹ * (⟨y, hYN hy⟩ : ↥(normalizer (W : Set G)))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
    group
  rw [mk_eq_one_iff] at h2
  simpa using h2

theorem exists_pow_eq_one_of_mk (hW : IsPGroup 2 W) {n : ↥(normalizer (W : Set G))} {k : ℕ}
    (hk : (π n) ^ 2 ^ k = 1) : ∃ m : ℕ, (n : G) ^ 2 ^ m = 1 := by
  rw [← map_pow, mk_eq_one_iff] at hk
  obtain ⟨j, hj⟩ := hW ⟨_, hk⟩
  refine ⟨k + j, ?_⟩
  have h := congrArg Subtype.val hj
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  rw [pow_add, pow_mul]
  exact h

theorem exists_pow_mul_eq_one (hW : IsPGroup 2 W) {n w : G}
    (hn : n ∈ normalizer (W : Set G)) (hn2 : ∃ k : ℕ, n ^ 2 ^ k = 1) (hw : w ∈ W) :
    ∃ k : ℕ, (w * n) ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hn2
  have hz : IsPGroup 2 (zpowers n) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hX : IsPGroup 2 (W ⊔ zpowers n : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hW hz (zpowers_le.mpr hn)
  obtain ⟨j, hj⟩ := hX ⟨w * n, mul_mem (mem_sup_left hw) (mem_sup_right (mem_zpowers n))⟩
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

end Bar

section Std

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isPGroup_zpowers_of_pow {t : X} {k : ℕ} (hk : t ^ 2 ^ k = 1) : IsPGroup 2 (zpowers t) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem isSylowOf_of_forall_mem_normalizer {R C : Subgroup X} (hRC : R ≤ C) (hR : IsPGroup 2 R)
    (h : ∀ c ∈ C, c ∈ normalizer (R : Set X) → (∃ k : ℕ, c ^ 2 ^ k = 1) → c ∈ R) :
    IsSylowOf 2 R C := by
  obtain ⟨S, hS, hRS⟩ := AschbacherTheorem3.exists_isSylowOf_le hR hRC
  suffices hSR : S = R by rwa [hSR] at hS
  by_contra hne
  have : Group.IsNilpotent ↥S := hS.isPGroup.isNilpotent
  have hlt : R.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun h' => hne (le_antisymm h' hRS)
  have h1 := Group.normalizerCondition_of_isNilpotent _ hlt
  rw [← subgroupOf_normalizer_eq hRS] at h1
  obtain ⟨x, hxN, hxR⟩ := IsConcreteLE.exists_of_lt h1
  have hxN' : (x : X) ∈ normalizer (R : Set X) := hxN
  obtain ⟨k, hk⟩ := hS.isPGroup x
  exact hxR (mem_subgroupOf.mpr (h x (hS.le x.2) hxN' ⟨k, by simpa using congrArg Subtype.val hk⟩))

theorem standardComponentIsStandard_of_sylow {M R : Subgroup X} (hM : IsQuasisimple M)
    (hR : IsSylowOf 2 R (centralizer (M : Set X))) (hR1 : R ≠ ⊥)
    (hN : ∀ x : X, ∀ r ∈ R, r ≠ 1 → x * r * x⁻¹ ∈ R → x ∈ normalizer (M : Set X))
    (hno : ∀ x : X, ∀ r ∈ R, r ≠ 1 → x * r * x⁻¹ ∉ M)
    (hinv : ∃ m ∈ M, m ≠ 1 ∧ m ^ 2 = 1) : standardComponentIsStandard M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (M : Set X) with hC
  have hCN : C ≤ normalizer (M : Set X) := centralizer_le_normalizer _
  have hNC : normalizer (M : Set X) ≤ normalizer (C : Set X) := fun g hg => by
    rw [mem_normalizer_iff]
    intro c
    simp only [hC, mem_centralizer_iff]
    constructor
    · intro hc m hm
      have hm' := (mem_normalizer_iff.mp (inv_mem hg) m).mp hm
      rw [inv_inv] at hm'
      have h := hc _ hm'
      calc m * (g * c * g⁻¹) = g * ((g⁻¹ * m * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * m * g)) * g⁻¹ := by rw [h]
        _ = g * c * g⁻¹ * m := by group
    · intro hc m hm
      have hm' := (mem_normalizer_iff.mp hg m).mp hm
      have h := hc _ hm'
      have h2 : g * (m * c) * g⁻¹ = g * (c * m) * g⁻¹ := by
        calc g * (m * c) * g⁻¹ = (g * m * g⁻¹) * (g * c * g⁻¹) := by group
          _ = (g * c * g⁻¹) * (g * m * g⁻¹) := h
          _ = g * (c * m) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  have hconj : ∀ t ∈ C, (∃ k : ℕ, t ^ 2 ^ k = 1) → ∃ c ∈ C, c⁻¹ * t * c ∈ R := by
    rintro t ht ⟨k, hk⟩
    obtain ⟨c, hc, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR
      (isPGroup_zpowers_of_pow hk) (zpowers_le.mpr ht)
    refine ⟨c, hc, hle ?_⟩
    rw [mem_rightConjugate_iff]
    simp [mul_assoc]
  have hne : ∀ {a b : X}, a ≠ 1 → b⁻¹ * a * b ≠ 1 := fun {a b} ha hb => ha (by
    have := congrArg (fun z => b * z * b⁻¹) hb
    simpa [mul_assoc] using this)
  have h2el : ∀ {t : X}, t ^ 2 = 1 → ∃ k : ℕ, t ^ 2 ^ k = 1 := fun {t} ht => ⟨1, by rwa [pow_one]⟩
  obtain ⟨r₀, hr₀, hr₀1⟩ : ∃ r ∈ R, r ≠ 1 := by
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
    exact ⟨r, hr, fun h => hr1 (Subtype.ext h)⟩
  refine ⟨hM, ?_, ?_, ?_, ?_⟩
  ·
    rcases hR.isPGroup.card_eq_or_dvd with h1 | h2
    · exact absurd ((Subgroup.card_eq_one).mp h1) hR1
    · exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le hR.le))
  ·
    intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    obtain ⟨⟨t, htC, htg⟩, ht⟩ := exists_prime_orderOf_dvd_card' 2 hodd
    have ht2 : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (⟨t, htC, htg⟩ : ↥(C ⊓ C.map (MulAut.conj g).toMonoidHom))
      rw [ht] at h
      have h' := congrArg Subtype.val h
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
      exact h'
    have ht1 : t ≠ 1 := by
      rintro rfl
      have h := orderOf_one (G := ↥(C ⊓ C.map (MulAut.conj g).toMonoidHom))
      rw [show (⟨1, htC, htg⟩ : ↥(C ⊓ C.map (MulAut.conj g).toMonoidHom)) = 1 from rfl] at ht
      rw [ht] at h
      exact absurd h (by norm_num)
    obtain ⟨c', hc', hc't⟩ := htg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc't
    have hc'2 : c' ^ 2 = 1 := by
      have h : g * c' ^ 2 * g⁻¹ = 1 := by
        rw [sq, show g * (c' * c') * g⁻¹ = (g * c' * g⁻¹) * (g * c' * g⁻¹) by group, hc't, ← sq,
          ht2]
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    obtain ⟨c₁, hc₁, hr₁⟩ := hconj t htC (h2el ht2)
    obtain ⟨c₂, hc₂, hr₂⟩ := hconj c' hc' (h2el hc'2)
    set x := c₂⁻¹ * g⁻¹ * c₁ with hx
    have hxr : x * (c₁⁻¹ * t * c₁) * x⁻¹ = c₂⁻¹ * c' * c₂ := by
      rw [← hc't, hx]
      group
    have hxN := hN x _ hr₁ (hne ht1) (hxr ▸ hr₂)
    have hg' : g = c₁ * x⁻¹ * c₂⁻¹ := by rw [hx]; group
    apply hg
    rw [hg']
    exact mul_mem (mul_mem (le_normalizer hc₁) (inv_mem (hNC hxN))) (inv_mem (le_normalizer hc₂))
  ·
    refine le_antisymm (fun g hg => ?_) hNC
    have hgr : g * r₀ * g⁻¹ ∈ C := (mem_normalizer_iff.mp hg r₀).mp (hR.le hr₀)
    obtain ⟨k, hk⟩ := hR.isPGroup ⟨r₀, hr₀⟩
    have hk' : (g * r₀ * g⁻¹) ^ 2 ^ k = 1 := by
      rw [conj_pow]
      have := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [this]
      group
    obtain ⟨c, hc, hcr⟩ := hconj _ hgr ⟨k, hk'⟩
    have hxN := hN (c⁻¹ * g) r₀ hr₀ hr₀1 (by
      have : c⁻¹ * g * r₀ * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * r₀ * g⁻¹) * c := by group
      rw [this]
      exact hcr)
    have : g = c * (c⁻¹ * g) := by group
    rw [this]
    exact mul_mem (hCN hc) hxN
  ·
    intro g hg
    rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff] at hg
    obtain ⟨m, hm, hm1, hm2⟩ := hinv
    have htC : g * m * g⁻¹ ∈ C := hg ⟨m, hm, rfl⟩
    have ht2 : (g * m * g⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hm2]
      group
    obtain ⟨c, hc, hcr⟩ := hconj _ htC (h2el ht2)
    have ht1 : g * m * g⁻¹ ≠ 1 := by
      have := hne (b := g⁻¹) hm1
      simpa using this
    apply hno (g⁻¹ * c) _ hcr (hne ht1)
    have : g⁻¹ * c * (c⁻¹ * (g * m * g⁻¹) * c) * (g⁻¹ * c)⁻¹ = m := by group
    rw [this]
    exact hm

end Std

end CFSG.ComponentClassification.AS81.Sec2Quot
