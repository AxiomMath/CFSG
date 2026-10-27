module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Abs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped commutatorElement

namespace ConfA

structure Facts (K₀ : Type) [Group K₀] (q : ℕ) (α : MulAut K₀) : Prop where
  card_innFix : Nat.card (Cat8.innFix K₀ α) ∣ 2 * Cat8.ordL2 (q ^ 2)
  card_L0 : Nat.card (Cat8.L0 K₀ α) = Cat8.ordL2 (q ^ 2)
  type : ∀ τ ∈ Cat8.Inn K₀, τ * α = α * τ → τ * τ = 1 → τ ≠ 1 → Cat8.IsAdmQ K₀ q (α * τ) →
    τ ∉ Cat8.L0 K₀ α ∧
      ∀ z ∈ Cat8.L0 K₀ α, z * z = 1 → z ≠ 1 → ∃ k ∈ Cat8.Inn K₀, k⁻¹ * z * k = τ
  dihedral : ∀ D : Subgroup (MulAut K₀), D ≤ Cat8.L0 K₀ α → IsPGroup 2 D →
    Nat.card D = 2 ^ (Cat8.ordL2 (q ^ 2)).factorization 2 →
      Nat.card ↥(D ⊓ centralizer (D : Set (MulAut K₀))) = 2 ∧
        ∃ t ∈ D, t * t ≠ 1 ∧ t * t ∈ centralizer (D : Set (MulAut K₀))

theorem eight_dvd_ordL2 {q : ℕ} (hq : Odd q) : 8 ∣ Cat8.ordL2 (q ^ 2) := by
  obtain ⟨j, rfl⟩ := hq
  obtain ⟨s, hs⟩ := Nat.even_mul_succ_self j
  have h1 : (2 * j + 1) ^ 2 = 8 * s + 1 := by
    have : (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 := by ring
    rw [this, hs]
    ring
  have h2 : (8 * s + 1) ^ 2 - 1 = 16 * (s * (4 * s + 1)) := by
    have : (8 * s + 1) ^ 2 = 16 * (s * (4 * s + 1)) + 1 := by ring
    omega
  show 8 ∣ (2 * j + 1) ^ 2 * (((2 * j + 1) ^ 2) ^ 2 - 1) / 2
  rw [h1, h2, show (8 * s + 1) * (16 * (s * (4 * s + 1))) =
    2 * (8 * ((8 * s + 1) * (s * (4 * s + 1)))) by ring, Nat.mul_div_cancel_left _ two_pos]
  exact dvd_mul_right 8 _

section General

theorem inn_normal (G : Type*) [Group G] : ((MulAut.conj : G →* MulAut G).range).Normal := by
  refine ⟨fun x hx φ => ?_⟩
  obtain ⟨g, rfl⟩ := hx
  refine ⟨φ g, ?_⟩
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply,
    MulAut.inv_apply]

variable {G : Type*} [Group G]

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem conj_mem_commutator {H : Subgroup G} {x : G} (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H) {y : G}
    (hy : y ∈ ⁅H, H⁆) : x * y * x⁻¹ ∈ ⁅H, H⁆ := by
  have h1 : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact hx h hh
  have h2 : (MulAut.conj x).toMonoidHom y ∈ (⁅H, H⁆ : Subgroup G).map
      (MulAut.conj x).toMonoidHom := mem_map_of_mem _ hy
  rw [Subgroup.map_commutator] at h2
  exact commutator_mono h1 h1 h2

theorem relIndex_eq_two {I Q : Subgroup G} [I.Normal] {a : G} (ha2 : a * a = 1) (haI : a ∉ I)
    (haQ : a ∈ Q) (hQ : Q ≤ I ⊔ zpowers a) : I.relIndex Q = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨a, haQ⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [Subgroup.coe_mul]
  rcases CatFactsSp4.mem_or_mul_mem_of_mem_sup ha2 (hQ b.2) with hb | hb
  · refine Or.inr ⟨hb, fun h => haI ?_⟩
    have := mul_mem (inv_mem hb) h
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨hb, fun h => haI ?_⟩
    have := mul_mem (inv_mem h) hb
    rwa [inv_mul_cancel_left] at this

variable [Finite G]

theorem eq_of_card_two_mul {H N M : Subgroup G} (hHN : H ≤ N) (hNM : N ≤ M) (hne : ¬ N ≤ H)
    (hM : Nat.card M = 2 * Nat.card H) : N = M := by
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hHN
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hNM
  have hH0 : 0 < Nat.card H := Nat.card_pos
  have hjk : j * k = 2 := by
    have : Nat.card H * (j * k) = Nat.card H * 2 := by
      rw [← mul_assoc, ← hj, ← hk, hM, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hH0 this
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro k hjk) with h1 | h2
  · exfalso
    apply hne
    have : H = N := Subgroup.eq_of_le_of_card_ge hHN (by rw [hj, h1, mul_one])
    rw [← this]
  · have hk1 : k = 1 := by
      rw [h2] at hjk
      omega
    exact Subgroup.eq_of_le_of_card_ge hNM (by rw [hk, hk1, mul_one])

theorem card_inf_eq {p : ℕ} [Fact p.Prime] {C Q L : Subgroup G} (hQC : Q ≤ C) (hLC : L ≤ C)
    (hL : ∀ x ∈ C, ∀ y ∈ L, x * y * x⁻¹ ∈ L)
    (hQ : ∃ T : Sylow p ↥C, (T : Subgroup ↥C) = Q.subgroupOf C) :
    Nat.card ↥(Q ⊓ L) = p ^ (Nat.card L).factorization p := by
  obtain ⟨T, hT⟩ := hQ
  have : (L.subgroupOf C).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hL x x.2 n hn⟩
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal T (N := L.subgroupOf C)
  have h1 := P.card_eq_multiplicity
  have hLc : Nat.card ↥(L.subgroupOf C) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv
  have hinf : Q.subgroupOf C ⊓ L.subgroupOf C = (Q ⊓ L).subgroupOf C := by
    ext x
    simp [mem_subgroupOf]
  have hPc : Nat.card P = Nat.card ↥(Q ⊓ L) := by
    rw [hP, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hT, hinf,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hQC)).toEquiv]
  rw [← hPc, h1, hLc]

omit [Finite G] in
theorem mem_of_central {p : ℕ} [Fact p.Prime] {C Q : Subgroup G} {x : G} (hxC : x ∈ C)
    (hx : ∀ y ∈ C, x * y = y * x) {k : ℕ} (hxk : x ^ p ^ k = 1)
    (hQ : ∃ T : Sylow p ↥C, (T : Subgroup ↥C) = Q.subgroupOf C) : x ∈ Q := by
  obtain ⟨T, hT⟩ := hQ
  set x' : C := ⟨x, hxC⟩ with hx'
  have hn : (zpowers x').Normal := by
    refine ⟨fun y hy c => ?_⟩
    have hcx : c * x' = x' * c := Subtype.ext (hx c c.2).symm
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    rw [(Commute.zpow_right hcx i).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers x') i
  have hp : IsPGroup p (zpowers x') := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : x' ^ p ^ k = 1 := Subtype.ext hxk
    change (x' ^ i) ^ p ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  have hle := hp.le_sylow_of_normal T
  have hxT : x' ∈ (T : Subgroup C) := hle (mem_zpowers x')
  rw [hT] at hxT
  exact hxT

omit [Finite G] in
theorem mem_of_normalizes {C Q : Subgroup G} {g : G} (hgC : g ∈ C) (hQC : Q ≤ C)
    (hgN : g ∈ normalizer (Q : Set G)) (hg2 : g * g ∈ Q)
    (hQ : ∃ T : Sylow 2 ↥C, (T : Subgroup ↥C) = Q.subgroupOf C) : g ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hQ
  set g' : C := ⟨g, hgC⟩ with hg'
  have hQ2 : IsPGroup 2 Q := by
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe hQC)
  obtain ⟨n, hn⟩ := hQ2 ⟨g * g, hg2⟩
  have hgn : g' ^ 2 ^ (n + 1) = 1 := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [SubgroupClass.coe_pow, pow_succ', pow_mul, pow_two]
    exact h1
  have hp : IsPGroup 2 (zpowers g') := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨n + 1, Subtype.ext ?_⟩
    change (g' ^ i) ^ 2 ^ (n + 1) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgn, one_zpow]
  have hgT : g' ∈ normalizer ((T : Subgroup C) : Set C) := by
    rw [mem_normalizer_iff]
    intro h
    rw [hT, mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp hgN h
  have hle : zpowers g' ≤ normalizer ((T : Subgroup C) : Set C) := zpowers_le.mpr hgT
  have hsup := hp.to_sup_of_normal_right' T.isPGroup' hle
  have heq := T.is_maximal' hsup le_sup_right
  have hgT' : g' ∈ (T : Subgroup C) := heq ▸ mem_sup_left (mem_zpowers g')
  rw [hT] at hgT'
  exact hgT'

end General

end ConfA

end CFSG.ComponentClassification.GSThmB
