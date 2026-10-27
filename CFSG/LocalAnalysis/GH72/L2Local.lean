module

public import CFSG.GroupTheory.ABGDGroups.LinearSignalizers
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter (PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo)

section General

variable {M : Type*} [Group M]

theorem mem_of_index_eq_two_of_odd_orderOf {H : Subgroup M} (hH : H.index = 2) {x : M}
    (hx : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨k, hk⟩ := hx
  have h : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h]
  exact H.pow_mem (Subgroup.sq_mem_of_index_two hH x) _

theorem le_of_index_eq_two_of_odd [Finite M] {H K : Subgroup M} (hH : H.index = 2)
    (hK : Odd (Nat.card K)) : K ≤ H := fun x hx =>
  mem_of_index_eq_two_of_odd_orderOf hH (hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hx))

theorem odd_orderOf_of_mem_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup M}
    (hQ : IsPGroup p Q) {x : M} (hx : x ∈ Q) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have hdvd : orderOf x ∣ p ^ k := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [hj]
  exact (hp.odd_of_ne_two hp2).pow

theorem exists_isSylowOf_forall_le_of_odd_mem [Finite M] {C R : Subgroup M} (hRC : R ≤ C)
    (hR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ R) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ P : Subgroup M, IsSylowOf p P C ∧ ∀ Q : Subgroup M, Q ≤ C → IsPGroup p Q → Q ≤ P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p C
  have hle : ∀ Q : Subgroup M, Q ≤ C → IsPGroup p Q → Q ≤ R := fun Q hQC hQ x hx =>
    hodd x (hQC hx) (odd_orderOf_of_mem_isPGroup hp hp2 hQ hx)
  refine ⟨P, hP, fun Q hQC hQ => ?_⟩
  have hPR := hle P hP.le hP.isPGroup
  have hQR := hle Q hQC hQ
  have hN : P ≤ normalizer (Q : Set M) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun n hn => by
      rw [hR x (hPR hx) n (hQR hn), mul_inv_cancel_right]
      exact hn
  have hQP : IsPGroup p (Q ⊔ P : Subgroup M) := IsPGroup.to_sup_of_normal_left' hQ hP.isPGroup hN
  have h := hP.eq_of_le le_sup_right (sup_le hQC hP.le) hQP
  rw [← h]
  exact le_sup_left

theorem exists_isCyclic_forall_odd_mem_of_mulEquiv_dihedralGroup {D : Subgroup M} {m : ℕ}
    [NeZero m] (e : D ≃* DihedralGroup m) :
    ∃ R : Subgroup M, R ≤ D ∧ IsCyclic R ∧ ∀ x ∈ D, Odd (orderOf x) → x ∈ R := by
  set f : DihedralGroup m →* M := D.subtype.comp e.symm.toMonoidHom
  refine ⟨(zpowers (DihedralGroup.r 1)).map f, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e.symm y).2
  · rw [MonoidHom.map_zpowers]
    infer_instance
  · intro x hx hodd
    have hfx : f (e ⟨x, hx⟩) = x := by simp [f]
    have hord : Odd (orderOf (e ⟨x, hx⟩)) := by
      rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    rw [← hfx]
    refine mem_map_of_mem f ?_
    rcases h : e ⟨x, hx⟩ with i | i
    · rw [← ZMod.natCast_zmod_val i, ← DihedralGroup.r_one_pow]
      exact Subgroup.pow_mem _ (mem_zpowers _) _
    · rw [h, DihedralGroup.orderOf_sr] at hord
      exact absurd hord (by decide)

theorem sq_eq_one_of_mem_kleinFour {Z : Subgroup M} (hZ : IsKleinFour Z) {a : M} (ha : a ∈ Z) :
    a ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : Z)
  rw [hZ.exponent_two] at h
  simpa using congrArg Subtype.val h

theorem mul_comm_of_mem_kleinFour {Z : Subgroup M} (hZ : IsKleinFour Z) {a b : M} (ha : a ∈ Z)
    (hb : b ∈ Z) : a * b = b * a := by
  have h1 := sq_eq_one_of_mem_kleinFour hZ (Z.mul_mem ha hb)
  have h2 := sq_eq_one_of_mem_kleinFour hZ ha
  have h3 := sq_eq_one_of_mem_kleinFour hZ hb
  rw [sq] at h1 h2 h3
  calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
    _ = (a * a) * b * a * (b * b) := by group
    _ = b * a := by rw [h2, h3, one_mul, mul_one]

theorem mem_kleinFour_cases {Z : Subgroup M} (hZ : IsKleinFour Z) {a c : M} (ha : a ∈ Z)
    (hc : c ∈ Z) (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hac : a ≠ c) {z : M} (hz : z ∈ Z) :
    z = 1 ∨ z = a ∨ z = c ∨ z = a * c := by
  haveI := hZ
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have := IsKleinFour.eq_mul_of_ne_all (x := (⟨a, ha⟩ : Z)) (y := ⟨c, hc⟩) (z := ⟨z, hz⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => hac (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact h4 (congrArg Subtype.val this)

theorem exists_mem_kleinFour_ne {Z : Subgroup M} (hZ : IsKleinFour Z) {a : M} (ha : a ∈ Z) :
    ∃ c ∈ Z, c ≠ 1 ∧ c ≠ a := by
  by_contra h
  push Not at h
  have hle : Z ≤ zpowers a := fun z hz => by
    by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem _
    rw [h z hz hz1]
    exact mem_zpowers a
  haveI := hZ
  exact IsKleinFour.not_isCyclic (Subgroup.isCyclic_of_le hle)

theorem sq_conj_eq (g z : M) : g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ := by
  rw [sq, mul_inv_rev]
  simp only [mul_assoc]

theorem mul_comm_of_conj_eq {x z : M} (h : x * z * x⁻¹ = z) : z * x = x * z := by
  calc z * x = x * z * x⁻¹ * x := by rw [h]
    _ = x * z := inv_mul_cancel_right _ _

theorem eq_of_conj_eq_conj {g a b : M} (h : g * a * g⁻¹ = g * b * g⁻¹) : a = b := by
  have := congrArg (fun z => g⁻¹ * z * g) h
  simpa [mul_assoc] using this

theorem conj_ne_of_sq_not_mem_centralizer {Z : Subgroup M} (hZ : IsKleinFour Z) {g : M}
    (hg : g ∈ normalizer (Z : Set M)) (hg2 : g ^ 2 ∉ centralizer (Z : Set M)) {a : M}
    (ha : a ∈ Z) (ha1 : a ≠ 1) : g * a * g⁻¹ ≠ a := by
  intro hga
  obtain ⟨c, hc, hc1, hca⟩ := exists_mem_kleinFour_ne hZ ha
  have hgc : g * c * g⁻¹ ∈ Z := (mem_normalizer_iff.mp hg c).mp hc
  have hgc1 : g * c * g⁻¹ ≠ 1 := fun h => hc1 (eq_of_conj_eq_conj (g := g) (by rw [h]; group))
  have hgca : g * c * g⁻¹ ≠ a := fun h => hca (eq_of_conj_eq_conj (g := g) (by rw [h, hga]))
  have ha2 : a * a = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hZ ha
  suffices hfix : g ^ 2 * a * (g ^ 2)⁻¹ = a ∧ g ^ 2 * c * (g ^ 2)⁻¹ = c by
    apply hg2
    rw [mem_centralizer_iff]
    intro z hz
    rcases mem_kleinFour_cases hZ ha hc ha1 hc1 (Ne.symm hca) hz with rfl | rfl | rfl | rfl
    · simp
    · exact mul_comm_of_conj_eq hfix.1
    · exact mul_comm_of_conj_eq hfix.2
    · apply mul_comm_of_conj_eq
      calc g ^ 2 * (a * c) * (g ^ 2)⁻¹ = (g ^ 2 * a * (g ^ 2)⁻¹) * (g ^ 2 * c * (g ^ 2)⁻¹) := by
            group
        _ = a * c := by rw [hfix.1, hfix.2]
  rcases mem_kleinFour_cases hZ ha hc ha1 hc1 (Ne.symm hca) hgc with h | h | h | h
  · exact absurd h hgc1
  · exact absurd h hgca
  · exact ⟨by rw [sq_conj_eq, hga, hga], by rw [sq_conj_eq, h, h]⟩
  · refine ⟨by rw [sq_conj_eq, hga, hga], ?_⟩
    rw [sq_conj_eq, h]
    calc g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) := by group
      _ = a * (a * c) := by rw [hga, h]
      _ = c := by rw [← mul_assoc, ha2, one_mul]

theorem conj_conj_eq_mul_of_sq_not_mem_centralizer {Z : Subgroup M} (hZ : IsKleinFour Z) {g : M}
    (hg : g ∈ normalizer (Z : Set M)) (hg2 : g ^ 2 ∉ centralizer (Z : Set M)) {a : M}
    (ha : a ∈ Z) (ha1 : a ≠ 1) :
    g * (g * a * g⁻¹) * g⁻¹ = a * (g * a * g⁻¹) := by
  obtain ⟨a₁, ha₁def⟩ : ∃ x : M, x = g * a * g⁻¹ := ⟨_, rfl⟩
  rw [← ha₁def]
  have ha₁ : a₁ ∈ Z := ha₁def ▸ (mem_normalizer_iff.mp hg a).mp ha
  have ha₁1 : a₁ ≠ 1 := fun h => ha1 (eq_of_conj_eq_conj (g := g) (by rw [← ha₁def, h]; group))
  have ha₁a : a₁ ≠ a := ha₁def ▸ conj_ne_of_sq_not_mem_centralizer hZ hg hg2 ha ha1
  have ha₂ : g * a₁ * g⁻¹ ∈ Z := (mem_normalizer_iff.mp hg a₁).mp ha₁
  have ha₂1 : g * a₁ * g⁻¹ ≠ 1 := fun h => ha₁1 (eq_of_conj_eq_conj (g := g) (by rw [h]; group))
  have ha₂a₁ : g * a₁ * g⁻¹ ≠ a₁ := conj_ne_of_sq_not_mem_centralizer hZ hg hg2 ha₁ ha₁1
  rcases mem_kleinFour_cases hZ ha ha₁ ha1 ha₁1 (Ne.symm ha₁a) ha₂ with h | h | h | h
  · exact absurd h ha₂1
  ·
    exfalso
    have ha2 : a * a = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hZ ha
    have hc1 : a * a₁ ≠ 1 := fun h' => ha₁a (by
      calc a₁ = a * a * a₁ := by rw [ha2, one_mul]
        _ = a := by rw [mul_assoc, h', mul_one])
    apply conj_ne_of_sq_not_mem_centralizer hZ hg hg2 (Z.mul_mem ha ha₁) hc1
    calc g * (a * a₁) * g⁻¹ = (g * a * g⁻¹) * (g * a₁ * g⁻¹) := by group
      _ = a₁ * a := by rw [← ha₁def, h]
      _ = a * a₁ := mul_comm_of_mem_kleinFour hZ ha₁ ha
  · exact absurd h ha₂a₁
  · exact h

theorem exists_pow_conj_eq_of_sq_not_mem_centralizer {Z : Subgroup M} (hZ : IsKleinFour Z) {g : M}
    (hg : g ∈ normalizer (Z : Set M)) (hg2 : g ^ 2 ∉ centralizer (Z : Set M)) {a b : M}
    (ha : a ∈ Z) (ha1 : a ≠ 1) (hb : b ∈ Z) (hb1 : b ≠ 1) :
    ∃ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = b := by
  have h2 := conj_conj_eq_mul_of_sq_not_mem_centralizer hZ hg hg2 ha ha1
  obtain ⟨a₁, ha₁def⟩ : ∃ x : M, x = g * a * g⁻¹ := ⟨_, rfl⟩
  rw [← ha₁def] at h2
  have ha₁ : a₁ ∈ Z := ha₁def ▸ (mem_normalizer_iff.mp hg a).mp ha
  have ha₁1 : a₁ ≠ 1 := fun h => ha1 (eq_of_conj_eq_conj (g := g) (by rw [← ha₁def, h]; group))
  have ha₁a : a₁ ≠ a := ha₁def ▸ conj_ne_of_sq_not_mem_centralizer hZ hg hg2 ha ha1
  rcases mem_kleinFour_cases hZ ha ha₁ ha1 ha₁1 (Ne.symm ha₁a) hb with rfl | rfl | rfl | rfl
  · exact absurd rfl hb1
  · exact ⟨0, by group⟩
  · exact ⟨1, by rw [pow_one, ha₁def]⟩
  · exact ⟨2, by rw [sq_conj_eq, ← ha₁def, h2]⟩

theorem pow_three_mem_centralizer_of_sq_not_mem_centralizer {Z : Subgroup M} (hZ : IsKleinFour Z)
    {g : M} (hg : g ∈ normalizer (Z : Set M)) (hg2 : g ^ 2 ∉ centralizer (Z : Set M)) :
    g ^ 3 ∈ centralizer (Z : Set M) := by
  rw [mem_centralizer_iff]
  intro a ha'
  have ha : a ∈ Z := ha'
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  apply mul_comm_of_conj_eq
  have h2 := conj_conj_eq_mul_of_sq_not_mem_centralizer hZ hg hg2 ha ha1
  obtain ⟨a₁, ha₁def⟩ : ∃ x : M, x = g * a * g⁻¹ := ⟨_, rfl⟩
  rw [← ha₁def] at h2
  have ha₁ : a₁ ∈ Z := ha₁def ▸ (mem_normalizer_iff.mp hg a).mp ha
  have ha₁2 : a₁ * a₁ = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hZ ha₁
  have h3 : g ^ 3 * a * (g ^ 3)⁻¹ = g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ := by
    rw [pow_succ, sq, mul_inv_rev, mul_inv_rev]
    simp only [mul_assoc]
  rw [h3, ← ha₁def, h2]
  calc g * (a * a₁) * g⁻¹ = (g * a * g⁻¹) * (g * a₁ * g⁻¹) := by group
    _ = a₁ * (a * a₁) := by rw [← ha₁def, h2]
    _ = a * (a₁ * a₁) := by
        rw [← mul_assoc, mul_comm_of_mem_kleinFour hZ ha₁ ha, mul_assoc]
    _ = a := by rw [ha₁2, mul_one]

theorem exists_pow_three_element_of_sq_not_mem_centralizer [Finite M] {Z : Subgroup M}
    (hZ : IsKleinFour Z) {g : M} (hg : g ∈ normalizer (Z : Set M))
    (hg2 : g ^ 2 ∉ centralizer (Z : Set M)) :
    ∃ m : ℕ, (∃ n : ℕ, orderOf (g ^ m) = 3 ^ n) ∧ ∀ a ∈ Z, a ≠ 1 → g ^ m * a * (g ^ m)⁻¹ ≠ a := by
  obtain ⟨n, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    exact (orderOf_pos g).ne' hnm
  refine ⟨m, ⟨n, ?_⟩, fun a ha ha1 => ?_⟩
  · rw [orderOf_pow_of_dvd hm0 (by rw [hnm]; exact dvd_mul_left _ _), hnm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · have h3 := pow_three_mem_centralizer_of_sq_not_mem_centralizer hZ hg hg2
    have hcomm : ∀ j : ℕ, ∀ z ∈ Z, (g ^ 3) ^ j * z * ((g ^ 3) ^ j)⁻¹ = z := fun j z hz => by
      have : (g ^ 3) ^ j ∈ centralizer (Z : Set M) := Subgroup.pow_mem _ h3 j
      rw [mem_centralizer_iff] at this
      rw [← this z hz, mul_inv_cancel_right]
    have hsplit : g ^ m = (g ^ 3) ^ (m / 3) * g ^ (m % 3) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hconj : g ^ m * a * (g ^ m)⁻¹ = g ^ (m % 3) * a * (g ^ (m % 3))⁻¹ := by
      rw [hsplit]
      have hz : g ^ (m % 3) * a * (g ^ (m % 3))⁻¹ ∈ Z :=
        (mem_normalizer_iff.mp (Subgroup.pow_mem _ hg _) a).mp ha
      calc (g ^ 3) ^ (m / 3) * g ^ (m % 3) * a * ((g ^ 3) ^ (m / 3) * g ^ (m % 3))⁻¹
          = (g ^ 3) ^ (m / 3) * (g ^ (m % 3) * a * (g ^ (m % 3))⁻¹) * ((g ^ 3) ^ (m / 3))⁻¹ := by
            group
        _ = g ^ (m % 3) * a * (g ^ (m % 3))⁻¹ := hcomm _ _ hz
    rw [hconj]
    have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hmod with h | h
    · rw [h, pow_one]
      exact conj_ne_of_sq_not_mem_centralizer hZ hg hg2 ha ha1
    · rw [h, sq_conj_eq, conj_conj_eq_mul_of_sq_not_mem_centralizer hZ hg hg2 ha ha1]
      intro h'
      apply ha1
      have h1 : g * a * g⁻¹ = 1 := mul_left_cancel (a := a) (h'.trans (mul_one a).symm)
      exact eq_of_conj_eq_conj (g := g) (by rw [h1]; group)

theorem gw_lemma_2_1_of_isSimpleGroup [Finite M] [IsSimpleGroup M] (h4 : 4 < Nat.card M)
    (hD : HasDihedralSylowTwo M) :
    (∀ x y : M, BenderSuzuki.PFAppendixIII.IsInvolution x →
      BenderSuzuki.PFAppendixIII.IsInvolution y → ∃ g : M, g * x * g⁻¹ = y) ∧
    (∀ S : Sylow 2 M, ∀ Z : Subgroup M, Z ≤ (S : Subgroup M) → IsKleinFour Z →
      CFSG.GorensteinWalter.NormalizerContainsCPrime Z) := by
  have hidx : ∀ N : Subgroup M, N.Normal → N.index ≠ 2 ∧ N.index ≠ 4 := fun N hN => by
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
    · rw [Subgroup.index_bot]
      omega
    · rw [Subgroup.index_top]
      omega
  rcases CFSG.GorensteinWalter.gw_lemma_2_1 hD with ⟨-, h2, h3⟩ | ⟨⟨N, hN, h2⟩, -⟩ |
      ⟨⟨N, hN, h4'⟩, -⟩
  · exact ⟨h2, h3⟩
  · exact absurd h2 (hidx N hN).1
  · exact absurd h4' (hidx N hN).2

theorem exists_mem_normalizer_sq_not_mem_centralizer [Finite M] [IsSimpleGroup M]
    (h4 : 4 < Nat.card M) (hD : HasDihedralSylowTwo M) {Z : Subgroup M} (hZ : IsKleinFour Z) :
    ∃ g ∈ normalizer (Z : Set M), g ^ 2 ∉ centralizer (Z : Set M) := by
  obtain ⟨S, hZS⟩ := (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hZ).exists_le_sylow
  obtain ⟨g, hg, hgc⟩ :=
    Set.exists_of_ssubset ((gw_lemma_2_1_of_isSimpleGroup h4 hD).2 S Z hZS hZ)
  exact ⟨g, hg, fun h => hgc ⟨hg, h⟩⟩

theorem exists_mem_normalizer_not_mem_of_lt [Finite M] {p : ℕ} [Fact p.Prime] {P P' : Subgroup M}
    (hP' : IsPGroup p P') (hlt : P < P') : ∃ x ∈ P', x ∈ normalizer (P : Set M) ∧ x ∉ P := by
  haveI : Group.IsNilpotent P' := hP'.isNilpotent
  have hH : P.subgroupOf P' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hlt.not_ge
    intro x hx
    have : (⟨x, hx⟩ : P') ∈ P.subgroupOf P' := h ▸ mem_top _
    exact this
  obtain ⟨y, hy, hyH⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hH)
  refine ⟨y, y.2, ?_, hyH⟩
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have hn' : (⟨n, hlt.le hn⟩ : P') ∈ P.subgroupOf P' := hn
  have := (mem_normalizer_iff.mp hy _).mp hn'
  exact this

theorem exists_isCyclic_forall_odd_mem_map {N : Type*} [Group N] (f : M →* N)
    (hf : Function.Injective f) {t : M} {R : Subgroup M} (hR : R ≤ centralizer ({t} : Set M))
    (hRc : IsCyclic R) (hodd : ∀ x ∈ centralizer ({t} : Set M), Odd (orderOf x) → x ∈ R) :
    R.map f ≤ f.range ⊓ centralizer ({f t} : Set N) ∧ IsCyclic (R.map f) ∧
      ∀ x ∈ f.range ⊓ centralizer ({f t} : Set N), Odd (orderOf x) → x ∈ R.map f := by
  refine ⟨?_, (R.equivMapOfInjective f hf).isCyclic.mp hRc, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y * t = t * y := mem_centralizer_singleton_iff.mp (hR hy)
    exact ⟨⟨y, rfl⟩, mem_centralizer_singleton_iff.mpr (by rw [← map_mul, hy', map_mul])⟩
  · rintro _ ⟨⟨y, rfl⟩, hyc⟩ hodd'
    have hyc' : f y * f t = f t * f y := mem_centralizer_singleton_iff.mp hyc
    exact mem_map_of_mem f (hodd y (mem_centralizer_singleton_iff.mpr
      (hf (by rw [map_mul, hyc', map_mul]))) (by rwa [orderOf_injective f hf] at hodd'))

section Transport

variable {N : Type*} [Group N] (f : M →* N) (hf : Function.Injective f)
include hf

theorem card_comap_of_le_range {K : Subgroup N} (hK : K ≤ f.range) :
    Nat.card (K.comap f) = Nat.card K := by
  conv_rhs => rw [← map_comap_eq_self hK]
  rw [card_map_of_injective hf]

private noncomputable def comapEquivOfLeRange {K : Subgroup N} (hK : K ≤ f.range) : K.comap f ≃* K :=
  ((K.comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (map_comap_eq_self hK))

theorem isKleinFour_comap {V : Subgroup N} (hV : IsKleinFour V) (hVr : V ≤ f.range) :
    IsKleinFour (V.comap f) :=
  ⟨by rw [Nat.card_congr (comapEquivOfLeRange f hf hVr).toEquiv]; exact hV.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv (comapEquivOfLeRange f hf hVr)]; exact hV.exponent_two⟩

theorem isCyclic_of_isCyclic_comap {K : Subgroup N} (hK : K ≤ f.range)
    (h : IsCyclic (K.comap f)) : IsCyclic K :=
  (comapEquivOfLeRange f hf hK).isCyclic.mp h

omit hf in
theorem comap_le_normalizer_comap {V K : Subgroup N} (hVK : V ≤ normalizer (K : Set N)) :
    V.comap f ≤ normalizer ((K.comap f : Subgroup M) : Set M) :=
  (comap_mono hVK).trans (le_normalizer_comap f)

end Transport

end General

section Linear

variable {F : Type} [Field F] [Finite F]

theorem exists_modEq_four_of_odd {q : ℕ} (hq : Odd q) :
    ∃ ε : ℤ, (q : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
  obtain ⟨k, rfl⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · refine ⟨1, ?_, Or.inl rfl⟩
    rw [Int.ModEq]
    push_cast
    omega
  · refine ⟨-1, ?_, Or.inr rfl⟩
    rw [Int.ModEq]
    push_cast
    omega

theorem odd_of_isOddPrimePower {q : ℕ} (h : IsOddPrimePower q) : Odd q := by
  obtain ⟨p, n, -, hp, -, rfl⟩ := h
  exact hp.pow

theorem three_le_of_isOddPrimePower {q : ℕ} (h : IsOddPrimePower q) : 3 ≤ q := by
  obtain ⟨p, n, hp, hpodd, hn, rfl⟩ := h
  have h3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  calc 3 ≤ p := h3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn

theorem psl2_exists_isCyclic_forall_odd_mem (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F}
    (ht : orderOf t = 2) :
    ∃ R : Subgroup (PSL2 F), R ≤ centralizer ({t} : Set (PSL2 F)) ∧ IsCyclic R ∧
      ∀ x ∈ centralizer ({t} : Set (PSL2 F)), Odd (orderOf x) → x ∈ R := by
  obtain ⟨ε, hε, hε1⟩ := exists_modEq_four_of_odd (odd_of_isOddPrimePower hF)
  obtain ⟨m, hm, ⟨e⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hF hε hε1 ht
  have h3 := three_le_of_isOddPrimePower hF
  haveI : NeZero m := ⟨by rintro rfl; rcases hε1 with rfl | rfl <;> omega⟩
  exact exists_isCyclic_forall_odd_mem_of_mulEquiv_dihedralGroup e

theorem pgl2_index_range_toPGL (hF : IsOddPrimePower (Nat.card F)) :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.index = 2 :=
  CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF

theorem pgl2_exists_isCyclic_forall_odd_mem (hF : IsOddPrimePower (Nat.card F)) {g : PGL2 F}
    (hg : orderOf g = 2) :
    ∃ R : Subgroup (PGL2 F), R ≤ centralizer ({g} : Set (PGL2 F)) ∧ IsCyclic R ∧
      ∀ x ∈ centralizer ({g} : Set (PGL2 F)), Odd (orderOf x) → x ∈ R := by
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hJ := pgl2_index_range_toPGL hF
  by_cases hgJ : g ∈ toPGL.range
  · obtain ⟨t, rfl⟩ := hgJ
    have ht : orderOf t = 2 := by rwa [orderOf_injective toPGL hinj] at hg
    obtain ⟨R, hR, hRc, hodd⟩ := psl2_exists_isCyclic_forall_odd_mem hF ht
    obtain ⟨h1, h2, h3⟩ := exists_isCyclic_forall_odd_mem_map toPGL hinj hR hRc hodd
    exact ⟨R.map toPGL, h1.trans inf_le_right, h2, fun x hx hxo =>
      h3 x ⟨mem_of_index_eq_two_of_odd_orderOf hJ hxo, hx⟩ hxo⟩
  · obtain ⟨ε, hε, hε1⟩ := exists_modEq_four_of_odd (odd_of_isOddPrimePower hF)
    obtain ⟨m, hm, ⟨e⟩⟩ :=
      CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hF hε hε1 hg hgJ
    have h3 := three_le_of_isOddPrimePower hF
    haveI : NeZero m := ⟨by rintro rfl; rcases hε1 with rfl | rfl <;> omega⟩
    obtain ⟨R, hRD, hRc, hodd⟩ := exists_isCyclic_forall_odd_mem_of_mulEquiv_dihedralGroup e
    exact ⟨R, hRD.trans inf_le_right, hRc, fun x hx hxo =>
      hodd x ⟨mem_of_index_eq_two_of_odd_orderOf hJ hxo, hx⟩ hxo⟩

theorem pgl2_card_inf_centralizer_of_mem (hF : IsOddPrimePower (Nat.card F)) {ε : ℤ}
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {g : PGL2 F}
    (hg : orderOf g = 2)
    (hgJ : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    (Nat.card ↥((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
      centralizer ({g} : Set (PGL2 F))) : ℤ) = Nat.card F - ε := by
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  obtain ⟨t, rfl⟩ := hgJ
  have ht : orderOf t = 2 := by rwa [orderOf_injective toPGL hinj] at hg
  obtain ⟨m, hm, ⟨e⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hF hε hε1 ht
  have h3 := three_le_of_isOddPrimePower hF
  haveI : NeZero m := ⟨by rintro rfl; rcases hε1 with rfl | rfl <;> omega⟩
  have hmap := CFSG.ABGDGroups.map_inf_centralizer_of_injective toPGL hinj ⊤ t
  rw [top_inf_eq, ← MonoidHom.range_eq_map] at hmap
  rw [← hmap, card_map_of_injective hinj, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  push_cast
  exact hm

theorem pgl2_card_inf_centralizer_of_not_mem (hF : IsOddPrimePower (Nat.card F)) {ε : ℤ}
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {g : PGL2 F}
    (hg : orderOf g = 2)
    (hgJ : g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    (Nat.card ↥((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
      centralizer ({g} : Set (PGL2 F))) : ℤ) = Nat.card F + ε := by
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hF hε hε1 hg hgJ
  have h3 := three_le_of_isOddPrimePower hF
  haveI : NeZero m := ⟨by rintro rfl; rcases hε1 with rfl | rfl <;> omega⟩
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  push_cast
  exact hm

theorem pgl2_isLinearDecomposition (hF : IsOddPrimePower (Nat.card F)) (S : Sylow 2 (PGL2 F)) :
    CFSG.ABGDGroups.IsLinearDecomposition
      (SemidirectProduct.inl : PGL2 F →* CFSG.GorensteinWalter.PGammaL2 F) ⊤ ⊥ S where
  isOddPrimePower_card := hF
  injective := SemidirectProduct.inl_injective
  normal := inferInstance
  map_eq := Or.inr (Or.inl (MonoidHom.range_eq_map _).symm)
  isCyclic := inferInstance
  odd_card := by rw [card_bot]; exact odd_one
  inf_eq_bot := inf_bot_eq _
  sup_eq_top := sup_bot_eq _
  map_le_fieldRange := by rw [Subgroup.map_bot]; exact bot_le
  le_centralizer := bot_le

theorem pgl2_centralizer_kleinFour
    (hF : IsOddPrimePower (Nat.card F)) {V : Subgroup (PGL2 F)} (hV : IsKleinFour V) :
    centralizer (V : Set (PGL2 F)) = V := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (PGL2 F)))
  have h := (pgl2_isLinearDecomposition hF S).inf_centralizer_kleinFour hV
  rwa [top_inf_eq] at h

theorem pgl2_exists_mem_normalizer_conj_eq_mul
    (hF : IsOddPrimePower (Nat.card F)) {V : Subgroup (PGL2 F)}
    (hV : IsKleinFour V) {u a : PGL2 F} (hu : u ∈ V) (hu1 : u ≠ 1)
    (huJ : u ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (ha : a ∈ V) (ha1 : a ≠ 1)
    (haJ : a ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ∃ g ∈ normalizer (V : Set (PGL2 F)), g * a * g⁻¹ = u * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJdef
  have hJ : J.index = 2 := pgl2_index_range_toPGL hF
  haveI hJn : J.Normal := normal_of_index_eq_two hJ
  have hCV := pgl2_centralizer_kleinFour hF hV
  have hu2 : orderOf u = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV hu) hu1
  have ha2 : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV ha) ha1
  have hua : u ≠ a := fun h => haJ (h ▸ huJ)
  set Cu := centralizer ({u} : Set (PGL2 F)) with hCudef
  have hVCu : V ≤ Cu := fun v hv => mem_centralizer_singleton_iff.mpr
    (mul_comm_of_mem_kleinFour hV hv hu)
  have h8 : 2 ^ 3 ∣ Nat.card Cu := by
    obtain ⟨ε, hε, hε1⟩ := exists_modEq_four_of_odd (odd_of_isOddPrimePower hF)
    set D := J ⊓ Cu with hDdef
    have hD := pgl2_card_inf_centralizer_of_mem hF hε hε1 hu2 huJ
    have h4 : 4 ∣ Nat.card D := by
      have : (4 : ℤ) ∣ (Nat.card D : ℤ) := by rw [hD]; exact Int.ModEq.dvd hε.symm
      exact_mod_cast this
    have haD : zpowers a ≤ normalizer (D : Set (PGL2 F)) := by
      rw [zpowers_le]
      apply mem_normalizer_fintype
      intro n hn
      exact ⟨hJn.conj_mem n hn.1 a, Cu.mul_mem (Cu.mul_mem (hVCu ha) hn.2) (Cu.inv_mem (hVCu ha))⟩
    have hdisj : Disjoint D (zpowers a) := by
      rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hxD, hxa⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxa
      rw [← zpow_mod_orderOf, ha2] at hxD ⊢
      have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
      rcases hk with hk | hk
      · rw [hk, zpow_zero]
        exact one_mem _
      · rw [hk, zpow_one] at hxD
        exact absurd hxD.1 haJ
    have hcard : Nat.card ↥(D ⊔ zpowers a) = Nat.card D * 2 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D (zpowers a) haD
        hdisj, Nat.card_zpowers, ha2]
    have hle : D ⊔ zpowers a ≤ Cu := sup_le inf_le_right (zpowers_le.mpr (hVCu ha))
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    obtain ⟨k, hk⟩ := h4
    rw [hk] at hdvd
    exact dvd_trans ⟨k, by ring⟩ hdvd
  have hV2 : IsPGroup 2 (V.subgroupOf Cu) :=
    (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hV).comap_subtype
  obtain ⟨S, hS⟩ := hV2.exists_le_sylow
  set T := (S : Subgroup Cu).map Cu.subtype with hTdef
  have hT2 : IsPGroup 2 T := S.isPGroup'.map _
  have hVT : V ≤ T := fun v hv => ⟨⟨v, hVCu hv⟩, hS (by simpa [mem_subgroupOf] using hv), rfl⟩
  have hTcard : 2 ^ 3 ∣ Nat.card T := by
    rw [hTdef, card_map_of_injective Cu.subtype_injective]
    exact S.pow_dvd_card_of_pow_dvd_card h8
  have hVT' : V < T := by
    refine lt_of_le_of_ne hVT fun h => ?_
    rw [← h, hV.card_four] at hTcard
    norm_num at hTcard
  obtain ⟨g, hgT, hgN, hgV⟩ := exists_mem_normalizer_not_mem_of_lt hT2 hVT'
  have hgCu : g ∈ Cu := by
    obtain ⟨y, -, rfl⟩ := hgT
    exact y.2
  refine ⟨g, hgN, ?_⟩
  have hgu : g * u * g⁻¹ = u := by
    rw [mem_centralizer_singleton_iff.mp hgCu, mul_inv_cancel_right]
  have hga : g * a * g⁻¹ ∈ V := (mem_normalizer_iff.mp hgN a).mp ha
  rcases mem_kleinFour_cases hV hu ha hu1 ha1 hua hga with h | h | h | h
  · exact absurd (eq_of_conj_eq_conj (g := g) (by rw [h]; group)) ha1
  · exact absurd (eq_of_conj_eq_conj (g := g) (by rw [h, hgu])) (Ne.symm hua)
  · exfalso
    apply hgV
    rw [← hCV, mem_centralizer_iff]
    intro z hz
    rcases mem_kleinFour_cases hV hu ha hu1 ha1 hua hz with hz' | hz' | hz' | hz'
    · rw [hz', one_mul, mul_one]
    · rw [hz']
      exact mul_comm_of_conj_eq hgu
    · rw [hz']
      exact mul_comm_of_conj_eq h
    · rw [hz']
      apply mul_comm_of_conj_eq
      calc g * (u * a) * g⁻¹ = (g * u * g⁻¹) * (g * a * g⁻¹) := by group
        _ = u * a := by rw [hgu, h]
  · exact h

end Linear

end CFSG.GH72
