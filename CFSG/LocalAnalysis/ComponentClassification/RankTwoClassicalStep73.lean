module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep74
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOddCenter

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

@[expose] def LinearTwoResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .linear → D.q = 2 → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      ∀ t : G, D.HasRank t 2 → t ∈ admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆)

@[expose] def SymplecticTwoOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → D.q = 2 → CFSG.Open.IsQuasisimple ↥A →
      Odd (Nat.card (center A)) → Odd (Nat.card (outerAutomorphismGroup ↥A))

section Elementary

variable {G : Type} [Group G]

theorem ClassicalModel.q_eq_two_or_four_le {A : Subgroup G} (D : ClassicalModel A) :
    D.q = 2 ∨ 4 ≤ D.q := by
  have key : ∀ m : ℕ, 1 ≤ m → 2 ^ m = 2 ∨ 4 ≤ 2 ^ m := by
    intro m hm
    rcases Nat.lt_or_ge m 2 with h | h
    · left
      obtain rfl : m = 1 := by omega
      rfl
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
  cases D with
  | linear n m hn hm => exact key m hm
  | unitary n m hn hm => exact key m hm
  | symplectic n m hn hm => exact key m hm
  | orthPlus n m hn hm => exact key m hm
  | orthMinus n m hn hm => exact key m hm

theorem four_group_mem [Finite G] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (hT4 : Nat.card T = 4) {t u : G} (ht : t ∈ T) (hu : u ∈ T) (ht1 : t ≠ 1) (hu1 : u ≠ 1)
    (hut : u ≠ t) {v : G} (hv : v ∈ T) : v = 1 ∨ v = t ∨ v = u ∨ v = t * u := by
  classical
  have ht2 : t * t = 1 := by rw [← sq]; exact hT.2 t ht
  have htu1 : t * u ≠ 1 := by
    intro h
    apply hut
    calc u = t * (t * u) := by rw [← mul_assoc, ht2, one_mul]
      _ = t := by rw [h, mul_one]
  have htut : t * u ≠ t := fun h => hu1 (by simpa using h)
  have htuu : t * u ≠ u := fun h => ht1 (by simpa using h)
  let s : Finset G := {1, t, u, t * u}
  have hs : s.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair htuu.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hut.symm, htut.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ht1.symm, hu1.symm, htu1.symm⟩
  have hsub : (s : Set G) ⊆ (T : Set G) := by
    intro x hx
    simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem T
    · exact ht
    · exact hu
    · exact mul_mem ht hu
  have heq : (s : Set G) = (T : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hs, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hT4]
  have hv' : v ∈ (s : Set G) := heq ▸ hv
  simpa [s] using hv'

theorem sq_mem_centralizer_of_four [Finite G] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (hT4 : Nat.card T = 4) {t a : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hat : a * t = t * a)
    (haN : a ∈ normalizer (T : Set G)) : a ^ 2 ∈ centralizer (T : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq]; exact hT.2 t ht
  have hconj : ∀ v ∈ T, a * v * a⁻¹ ∈ T := fun v hv => (mem_normalizer_iff.mp haN v).mp hv
  have hat' : a * t * a⁻¹ = t := by rw [hat, mul_inv_cancel_right]
  rw [mem_centralizer_iff]
  intro u hu
  suffices h : a * (a * u * a⁻¹) * a⁻¹ = u by
    rw [sq]
    calc u * (a * a) = a * (a * u * a⁻¹) * a⁻¹ * (a * a) := by rw [h]
      _ = a * a * u := by group
  by_cases hu1 : u = 1
  · rw [hu1, mul_one, mul_inv_cancel, mul_one, mul_inv_cancel]
  by_cases hut : u = t
  · rw [hut, hat', hat']
  have hu' := hconj u hu
  rcases four_group_mem hT hT4 ht hu ht1 hu1 hut hu' with h | h | h | h
  · exfalso
    apply hu1
    calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply hut
    calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
      _ = a⁻¹ * (a * t * a⁻¹) * a := by rw [h, hat']
      _ = t := by group
  · rw [h, h]
  · have h2 : a * (t * u) * a⁻¹ = u := by
      calc a * (t * u) * a⁻¹ = (a * t * a⁻¹) * (a * u * a⁻¹) := by group
        _ = t * (t * u) := by rw [hat', h]
        _ = u := by rw [← mul_assoc, ht2, one_mul]
    rw [h, h2]

theorem conj_pow_odd {T : Subgroup G} {x : G} (hx2 : x ^ 2 ∈ centralizer (T : Set G)) {r : ℕ}
    (hr : Odd r) {v : G} (hv : v ∈ T) : x ^ r * v * (x ^ r)⁻¹ = x * v * x⁻¹ := by
  obtain ⟨j, rfl⟩ := hr
  have h : (x ^ 2) ^ j * v = v * (x ^ 2) ^ j := (mem_centralizer_iff.mp (pow_mem hx2 j) v hv).symm
  rw [pow_succ', pow_mul]
  calc x * (x ^ 2) ^ j * v * (x * (x ^ 2) ^ j)⁻¹ =
      x * ((x ^ 2) ^ j * v * ((x ^ 2) ^ j)⁻¹) * x⁻¹ := by group
    _ = x * v * x⁻¹ := by rw [h, mul_inv_cancel_right]

theorem exists_two_part [Finite G] (x : G) : ∃ (k r : ℕ), Odd r ∧ (x ^ r) ^ 2 ^ k = 1 := by
  obtain ⟨k, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  exact ⟨k, r, hr, by rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]⟩

theorem isPGroup_zpowers_of_pow {y : G} {k : ℕ} (hy : y ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(zpowers y) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

end Elementary

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem false_of_mem_residual (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZ : Odd (Nat.card (center ↥A))) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hres : t ∈ admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
      ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆)) : False := by
  have htg : t ∈ rightConjugate A g :=
    (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT ht ht1 hOut).1 hres
  have htK : t ∈ rightConjugate (centralizer (A : Set G)) g := hc.sylowT.le ht
  rw [mem_rightConjugate_iff] at htg htK
  have h2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq,
      (hc.elemT h32).2 t ht, mul_one, mul_inv_cancel]
  have h1 := eq_one_of_mem_centralizer hZ htg htK h2
  apply ht1
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem false_of_outer (h32 : Lemma32) (hOutOdd : Odd (Nat.card (outerAutomorphismGroup ↥A)))
    (hT4 : Nat.card T = 4) {t a : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hat : a ∈ centralizer ({t} : Set G)) (haN : a ∈ normalizer (T : Set G))
    (haC : a ∉ centralizer (T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTe := hc.elemT h32
  have ha2 := sq_mem_centralizer_of_four hTe hT4 ht ht1 (mem_centralizer_singleton_iff.mp hat)
    haN
  obtain ⟨w, hw, hAw⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hNT : normalizer (T : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
    have h := Lemma36.normalizer_le hc.hyp hc.sylowR w
    rwa [← hw, hAw] at h
  set b := g * a * g⁻¹ with hb
  set T₁ := rightConjugate T g⁻¹ with hT₁
  have hT₁K : IsSylowOf 2 T₁ (centralizer (A : Set G)) := hc.swap.sylowR
  have hbA : b ∈ normalizer (A : Set G) := (mem_normalizer_rightConjugate_iff A g a).mp (hNT haN)
  have hmemT₁ : ∀ v, v ∈ T₁ ↔ g⁻¹ * v * g ∈ T := fun v => by
    rw [hT₁, mem_rightConjugate_iff, inv_inv]
  have hbconj : ∀ v, g⁻¹ * (b * v * b⁻¹) * g = a * (g⁻¹ * v * g) * a⁻¹ := fun v => by
    rw [hb]; group
  have hbN : ∀ v ∈ T₁, b * v * b⁻¹ ∈ T₁ := by
    intro v hv
    rw [hmemT₁, hbconj]
    exact (mem_normalizer_iff.mp haN _).mp ((hmemT₁ v).mp hv)
  have hb2 : ∀ v ∈ T₁, b ^ 2 * v * (b ^ 2)⁻¹ = v := by
    intro v hv
    have hv' := (hmemT₁ v).mp hv
    have h1 : a ^ 2 * (g⁻¹ * v * g) = (g⁻¹ * v * g) * a ^ 2 :=
      (mem_centralizer_iff.mp ha2 _ hv').symm
    calc b ^ 2 * v * (b ^ 2)⁻¹ = g * (a ^ 2 * (g⁻¹ * v * g) * (a ^ 2)⁻¹) * g⁻¹ := by
          rw [hb, sq, sq]; group
      _ = v := by rw [h1]; group
  have hbC : ∃ v ∈ T₁, b * v * b⁻¹ ≠ v := by
    by_contra hall
    push Not at hall
    apply haC
    rw [mem_centralizer_iff]
    intro u hu
    have hu' : g * u * g⁻¹ ∈ T₁ := by rw [hmemT₁]; simpa [mul_assoc] using hu
    have h1 := hall _ hu'
    rw [hb] at h1
    have h2 : a * u * a⁻¹ = u := by
      calc a * u * a⁻¹ = g⁻¹ * (g * a * g⁻¹ * (g * u * g⁻¹) * (g * a * g⁻¹)⁻¹) * g := by group
        _ = u := by rw [h1]; group
    calc u * a = a * u * a⁻¹ * a := by rw [h2]
      _ = a * u := by group
  obtain ⟨v₀, hv₀, hbv₀⟩ := hbC
  obtain ⟨k, r, hr, hb₂⟩ := exists_two_part b
  have hbr : ∀ v ∈ T₁, b ^ r * v * (b ^ r)⁻¹ = b * v * b⁻¹ := by
    intro v hv
    have hb2' : b ^ 2 ∈ centralizer (T₁ : Set G) := by
      rw [mem_centralizer_iff]
      intro u hu
      calc u * b ^ 2 = b ^ 2 * u * (b ^ 2)⁻¹ * b ^ 2 := by rw [hb2 u hu]
        _ = b ^ 2 * u := by group
    exact conj_pow_odd hb2' hr hv
  have hb₂A : b ^ r ∈ normalizer (A : Set G) := pow_mem hbA r
  have hmap : A.map (MulAut.conj (b ^ r)).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hb₂A
  let σ : MulAut ↥A := ((MulAut.conj (b ^ r)).subgroupMap A).trans (MulEquiv.subgroupCongr hmap)
  have hσ : ∀ x : ↥A, ((σ x : ↥A) : G) = b ^ r * x * (b ^ r)⁻¹ := fun x => rfl
  have hσn : ∀ (n : ℕ) (x : ↥A), (((σ ^ n) x : ↥A) : G) = (b ^ r) ^ n * x * ((b ^ r) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hσ, pow_succ]
      group
  have hσk : σ ^ 2 ^ k = 1 := by
    ext x
    rw [hσn, hb₂, one_mul, inv_one, mul_one]
    rfl
  have hσbar : outerAutomorphismMap ↥A σ = 1 := by
    have h1 : orderOf (outerAutomorphismMap ↥A σ) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hσk, map_one])
    have h2 := orderOf_dvd_natCard (outerAutomorphismMap ↥A σ)
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (outerAutomorphismGroup ↥A)) :=
      Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr
        fun h => (Nat.not_even_iff_odd.mpr hOutOdd) (even_iff_two_dvd.mpr h))
    have h3 : orderOf (outerAutomorphismMap ↥A σ) = 1 :=
      Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
    exact orderOf_eq_one_iff.mp h3
  have hσin : σ ∈ innerAutomorphismSubgroup ↥A := by
    rw [← outerAutomorphismMap_ker]
    exact hσbar
  obtain ⟨x, hx⟩ := hσin
  have hxσ : ∀ y : ↥A, (b ^ r) * (y : G) * (b ^ r)⁻¹ = (x : G) * y * (x : G)⁻¹ := by
    intro y
    rw [← hσ, ← hx]
    rfl
  set c := (x : G)⁻¹ * b ^ r with hcdef
  have hcK : c ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := hxσ ⟨y, hy⟩
    simp only at h1
    calc y * c = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (b ^ r) := by rw [hcdef]; group
      _ = (x : G)⁻¹ * ((b ^ r) * y * (b ^ r)⁻¹) * (b ^ r) := by rw [h1]
      _ = c * y := by rw [hcdef]; group
  have hxT : ∀ v ∈ T₁, (x : G) * v = v * x := fun v hv =>
    (mem_centralizer_iff.mp (hT₁K.le hv) x x.2)
  have hcact : ∀ v ∈ T₁, c * v * c⁻¹ = b * v * b⁻¹ := by
    intro v hv
    have h1 := hbN v hv
    calc c * v * c⁻¹ = (x : G)⁻¹ * (b ^ r * v * (b ^ r)⁻¹) * x := by rw [hcdef]; group
      _ = (x : G)⁻¹ * (b * v * b⁻¹) * x := by rw [hbr v hv]
      _ = b * v * b⁻¹ := by rw [mul_assoc, ← hxT _ h1]; group
  have hc2 : c ^ 2 ∈ centralizer (T₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro u hu
    have h1 : c ^ 2 * u * (c ^ 2)⁻¹ = u := by
      calc c ^ 2 * u * (c ^ 2)⁻¹ = c * (c * u * c⁻¹) * c⁻¹ := by rw [sq]; group
        _ = b * (b * u * b⁻¹) * b⁻¹ := by rw [hcact u hu, hcact _ (hbN u hu)]
        _ = b ^ 2 * u * (b ^ 2)⁻¹ := by rw [sq]; group
        _ = u := hb2 u hu
    calc u * c ^ 2 = c ^ 2 * u * (c ^ 2)⁻¹ * c ^ 2 := by rw [h1]
      _ = c ^ 2 * u := by group
  have hbNT : b ∈ normalizer (T₁ : Set G) := by
    rw [hT₁, mem_normalizer_rightConjugate_iff, inv_inv]
    have h1 : g⁻¹ * b * g = a := by rw [hb]; group
    rw [h1]
    exact haN
  have hxN : (x : G)⁻¹ ∈ normalizer (T₁ : Set G) := by
    refine centralizer_le_normalizer _ (inv_mem ?_)
    rw [mem_centralizer_iff]
    intro v hv
    exact (hxT v hv).symm
  have hcN : c ∈ normalizer (T₁ : Set G) := mul_mem hxN (pow_mem hbNT r)
  obtain ⟨k', r', hr', hc₂⟩ := exists_two_part c
  have hc₂K : c ^ r' ∈ centralizer (A : Set G) := pow_mem hcK r'
  have hc₂N : zpowers (c ^ r') ≤ normalizer (T₁ : Set G) := zpowers_le.mpr (pow_mem hcN r')
  have hP : IsPGroup 2 ↥(T₁ ⊔ zpowers (c ^ r')) :=
    IsPGroup.to_sup_of_normal_left' hT₁K.isPGroup (isPGroup_zpowers_of_pow hc₂) hc₂N
  have heq : T₁ ⊔ zpowers (c ^ r') = T₁ :=
    hT₁K.eq_of_le le_sup_left (sup_le hT₁K.le (zpowers_le.mpr hc₂K)) hP
  have hc₂T : c ^ r' ∈ T₁ := heq ▸ mem_sup_right (mem_zpowers _)
  have hcomm : c ^ r' * v₀ = v₀ * c ^ r' :=
    congrArg Subtype.val ((hc.swap.elemR h32).1.is_comm.comm ⟨_, hc₂T⟩ ⟨v₀, hv₀⟩)
  apply hbv₀
  rw [← hcact v₀ hv₀, ← conj_pow_odd hc2 hr' hv₀, hcomm, mul_inv_cancel_right]

end Sec3

theorem step73_of (I : Inputs74) (h33 : Lemma33Three) (hTwo : Classical222Two)
    (hLT : LinearTwoResidual) (hSO : SymplecticTwoOut) : Step73 := by
  intro G _ _ A D hA hTy
  rcases D.q_eq_two_or_four_le with hq2 | hq
  swap
  · exact hq
  exfalso
  have hOut := I.hOut ↥A hA.standard.1.1 hTy
  obtain ⟨g, hg, R, T, hR, hT, -, -, hTR, -, -⟩ := section3Config_of I.h32 h33 I.h4 I.h34 G A hA
  have hc : Sec3 A R T g := ⟨hA, hR, hg, hT, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  obtain ⟨t, ht, ht1, hcase⟩ :=
    hTwo G A T D hq2 (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)
  cases hf : D.family with
  | linear =>
    simp only [CaseQTwo, hf] at hcase
    have hZ := D.odd_card_center_of_linear hf hA.standard.1
    exact hc.false_of_mem_residual I.h32 I.h4 I.h34 hOut hZ ht ht1
      (hLT G A D hf hq2 hA.standard.1 hZ t hcase)
  | unitary => simp only [CaseQTwo, hf] at hcase
  | symplectic =>
    simp only [CaseQTwo, hf] at hcase
    obtain ⟨hZ, hT4', a, ha, haN, haC⟩ := hcase
    exact hc.false_of_outer I.h32 (hSO G A D hf hq2 hA.standard.1 hZ) hT4' ht ht1
      (mem_inf.mp ha).2 haN haC
  | orthPlus => simp only [CaseQTwo, hf] at hcase
  | orthMinus => simp only [CaseQTwo, hf] at hcase

end CFSG.ComponentClassification.RankTwoClassical
