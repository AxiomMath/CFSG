module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.Transfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section GmhGeneral

variable {G : Type*} [Group G]

theorem gmh_exists_mul_of_mem_sup {H K : Subgroup G} (hH : H ≤ normalizer (K : Set G)) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right H K hH] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem gmh_mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ x ∈ K, g * x * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => h x hx, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
  have : y = x := by
    have := congrArg (fun z => g⁻¹ * z * g) e
    simpa [mul_assoc] using this
  exact this ▸ hy

theorem gmh_conj_mem_iff {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) (x : G) :
    g * x * g⁻¹ ∈ K ↔ x ∈ K :=
  ((mem_normalizer_iff.mp hg) x).symm

theorem gmh_inv_mul_mem_of_relIndex_le_two [Finite G] {K X : Subgroup G}
    (hidx : K.relIndex X ≤ 2) {x y : G} (hx : x ∈ X) (hy : y ∈ X) (hxK : x ∉ K) (hyK : y ∉ K) :
    x⁻¹ * y ∈ K := by
  set K' := K.subgroupOf X with hK'
  have hne0 : K'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne1 : K'.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have : (⟨x, hx⟩ : X) ∈ K' := by rw [h1]; exact Subgroup.mem_top _
    exact hxK this
  have h2 : K'.index = 2 := by
    have : K'.index ≤ 2 := hidx
    omega
  have hx' : (⟨x, hx⟩ : X)⁻¹ ∉ K' := fun h => hxK (by
    have := K'.inv_mem h
    rw [inv_inv] at this
    exact this)
  have hy' : (⟨y, hy⟩ : X) ∉ K' := hyK
  have hmem := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨x, hx⟩ : X)⁻¹)
    (b := ⟨y, hy⟩)).mpr (iff_of_false hx' hy')
  exact hmem

theorem gmh_eq_one_of_sq_of_odd {y : G} (hy2 : y ^ 2 = 1) (hodd : Odd (orderOf y)) : y = 1 := by
  have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem gmh_mem_of_pow_odd_mem {B : Subgroup G} {d : G} {m : ℕ} (hsq : d ^ 2 ∈ B) (hm : Odd m)
    (hdm : d ^ m ∈ B) : d ∈ B := by
  obtain ⟨j, rfl⟩ := hm
  have e : d = ((d ^ 2) ^ j)⁻¹ * d ^ (2 * j + 1) := by
    rw [← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e]
  exact mul_mem (inv_mem (pow_mem hsq j)) hdm

theorem gmh_pow_conj_eq {g x a : G} (h : g * x * g⁻¹ = x * a) (hga : g * a = a * g) (k : ℕ) :
    g ^ k * x * (g ^ k)⁻¹ = x * a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hga' : g * a ^ k * g⁻¹ = a ^ k := by
      rw [(Commute.pow_right hga k).eq, mul_inv_cancel_right]
    calc g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by
          rw [pow_succ']; group
      _ = (g * x * g⁻¹) * (g * a ^ k * g⁻¹) := by rw [ih]; group
      _ = x * a ^ (k + 1) := by rw [h, hga', pow_succ', mul_assoc]

theorem gmh_exists_pow_mul {B : Subgroup G} {d b : G} (hd : ∀ x ∈ B, d⁻¹ * x * d ∈ B)
    (hb : b ∈ B) (k : ℕ) : ∃ c ∈ B, (d * b) ^ k = d ^ k * c := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc, hck⟩ := ih
    refine ⟨d⁻¹ * c * d * b, mul_mem (hd c hc) hb, ?_⟩
    rw [pow_succ, hck, pow_succ]
    group

theorem gmh_exists_two_complement [Finite G] {N A R : Subgroup G} (hAN : A ≤ N)
    (hNA : N ≤ centralizer (A : Set G)) (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hR : IsSylowOf 2 R N)
    (hRcard : Nat.card R ≤ 2 * Nat.card A) :
    A ≤ R ∧ A.relIndex R ≤ 2 ∧ (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      ∃ Y : Subgroup G, Y ≤ N ∧ (∀ y ∈ Y, Odd (orderOf y)) ∧
        (∀ n ∈ N, Odd (orderOf n) → n ∈ Y) ∧ ∀ n ∈ N, ∃ y ∈ Y, ∃ r ∈ R, y * r = n := by
  classical
  have hRN : R ≤ N := hR.le
  have hRp : IsPGroup 2 R := hR.isPGroup
  have hAp : IsPGroup 2 A := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hA2 g g.2, Subgroup.coe_one])⟩
  have hRA : R ≤ normalizer (A : Set G) := fun r hr =>
    centralizer_le_normalizer _ (hNA (hRN hr))
  have hcomm : ∀ n ∈ N, ∀ a ∈ A, a * n = n * a := fun n hn a ha =>
    mem_centralizer_iff.mp (hNA hn) a ha
  have hAR : A ≤ R := by
    have hsup : IsPGroup 2 (R ⊔ A : Subgroup G) := hRp.to_sup_of_normal_right' hAp hRA
    have := hR.eq_of_le le_sup_left (sup_le hRN hAN) hsup
    exact le_sup_right.trans this.le
  have hidx : A.relIndex R ≤ 2 := by
    have h1 := relIndex_mul_card (H := A) (K := R)
    rw [inf_of_le_left hAR] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    by_contra hc
    push Not at hc
    have : 3 * Nat.card A ≤ Nat.card R := by rw [← h1]; exact Nat.mul_le_mul_right _ hc
    omega
  have hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    by_cases haA : a ∈ A
    · exact hcomm b (hRN hb) a haA
    by_cases hbA : b ∈ A
    · exact (hcomm a (hRN ha) b hbA).symm
    have hc := gmh_inv_mul_mem_of_relIndex_le_two hidx ha hb haA hbA
    have hca : (a⁻¹ * b) * a = a * (a⁻¹ * b) := hcomm a (hRN ha) _ hc
    calc a * b = a * (a * (a⁻¹ * b)) := by group
      _ = a * ((a⁻¹ * b) * a) := by rw [hca]
      _ = b * a := by group
  refine ⟨hAR, hidx, hRab, ?_⟩
  obtain ⟨Q, hQ⟩ := hR.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ x : N, x ∈ (Q : Subgroup N) ↔ (x : G) ∈ R := fun x => by
    rw [hQ, mem_subgroupOf]
  have hQnc : normalizer ((Q : Subgroup N) : Set N) ≤ centralizer ((Q : Subgroup N) : Set N) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro h hh
    set k := (Q : Subgroup N).relIndex (normalizer ((Q : Subgroup N) : Set N)) with hk
    have hkodd : Odd k := by
      have h1 : k ∣ (Q : Subgroup N).index := relIndex_dvd_index_of_le le_normalizer
      have h2 := Q.not_dvd_index
      rw [Nat.odd_iff]
      have : ¬ 2 ∣ k := fun h3 => h2 (h3.trans h1)
      omega
    have hgk : ((g : N) : G) ^ k ∈ R := by
      have h1 := Subgroup.pow_index_mem
        ((Q : Subgroup N).subgroupOf (normalizer ((Q : Subgroup N) : Set N))) ⟨g, hg⟩
      rw [mem_subgroupOf] at h1
      have h2 := (hmemQ _).mp h1
      have h3 : ((g : N) : G) ^ k = ((g : N) : G) ^
          ((Q : Subgroup N).subgroupOf (normalizer ((Q : Subgroup N) : Set N))).index := rfl
      rw [h3]
      simpa using h2
    have hxR : ((h : N) : G) ∈ R := (hmemQ h).mp hh
    have hgN : ((g : N) : G) ∈ N := g.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    set x : G := ((h : N) : G) with hx
    set γ : G := ((g : N) : G) with hγ
    by_cases hxA : x ∈ A
    · exact hcomm γ hgN x hxA
    have hconjR : γ * x * γ⁻¹ ∈ R := by
      have h1 := (mem_normalizer_iff.mp hg h).mp hh
      have h2 := (hmemQ _).mp h1
      simpa using h2
    have hconjA : γ * x * γ⁻¹ ∉ A := by
      intro h1
      apply hxA
      have h2 := hcomm γ hgN _ h1
      have : x = γ * x * γ⁻¹ := by
        calc x = γ⁻¹ * ((γ * x * γ⁻¹) * γ) := by group
          _ = γ⁻¹ * (γ * (γ * x * γ⁻¹)) := by rw [h2]
          _ = γ * x * γ⁻¹ := by group
      rw [this]
      exact h1
    set c := x⁻¹ * (γ * x * γ⁻¹) with hc
    have hcA : c ∈ A := gmh_inv_mul_mem_of_relIndex_le_two hidx hxR hconjR hxA hconjA
    have hγc : γ * c = c * γ := (hcomm γ hgN c hcA).symm
    have hconj : γ * x * γ⁻¹ = x * c := by rw [hc]; group
    have hpow := gmh_pow_conj_eq hconj hγc k
    have hγk : γ ^ k * x * (γ ^ k)⁻¹ = x := by
      rw [hRab _ hgk _ hxR, mul_inv_cancel_right]
    have hck : c ^ k = 1 := by
      rw [hγk] at hpow
      exact (mul_eq_left.mp hpow.symm)
    have hc1 : c = 1 :=
      gmh_eq_one_of_sq_of_odd (hA2 c hcA) (hkodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hck))
    calc x * γ = γ * (γ⁻¹ * x * γ) := by group
      _ = γ * x := by
        congr 1
        have : γ * x * γ⁻¹ = x := by rw [hconj, hc1, mul_one]
        calc γ⁻¹ * x * γ = γ⁻¹ * (γ * x * γ⁻¹) * γ := by rw [this]
          _ = x := by group
  have hcomp := MonoidHom.ker_transferSylow_isComplement' Q hQnc
  have hodd := MonoidHom.not_dvd_card_ker_transferSylow Q hQnc
  set Y' := (MonoidHom.transferSylow Q hQnc).ker with hY'
  refine ⟨Y'.map N.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨y, hy, rfl⟩
    have h1 : orderOf (N.subtype y) = orderOf (⟨y, hy⟩ : Y') := by
      rw [orderOf_injective N.subtype N.subtype_injective, ← Subgroup.orderOf_mk]
    rw [h1, Nat.odd_iff]
    have h2 := orderOf_dvd_natCard (⟨y, hy⟩ : Y')
    have : ¬ 2 ∣ orderOf (⟨y, hy⟩ : Y') := fun h3 => hodd (h3.trans h2)
    omega
  ·
    intro n hn hnodd
    set n' : N := ⟨n, hn⟩
    have hindex : Y'.index = Nat.card (Q : Subgroup N) := hcomp.symm.index_eq_card
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hpow : n' ^ Y'.index ∈ Y' := Subgroup.pow_index_mem Y' n'
    have hord : orderOf n' = orderOf n := by
      rw [← orderOf_injective N.subtype N.subtype_injective n']
      rfl
    have hcop : Nat.Coprime Y'.index (orderOf n') := by
      rw [hindex, hj, hord]
      exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hnodd)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have : n' ∈ Y' := by rw [← hm]; exact pow_mem hpow m
    exact ⟨n', this, rfl⟩
  ·
    intro n hn
    obtain ⟨⟨y, r⟩, hyr, -⟩ := (isComplement'_def.mp hcomp).existsUnique ⟨n, hn⟩
    refine ⟨(y : N), ⟨y, y.2, rfl⟩, (r : N), (hmemQ r).mp r.2, ?_⟩
    have := congrArg Subtype.val hyr
    simpa using this

theorem gmh_conj_mem_of_two_cosets {K X : Subgroup G}
    (hK2 : ∀ x ∈ X, ∀ y ∈ X, x ∉ K → y ∉ K → x⁻¹ * y ∈ K) {g : G}
    (hgX : g ∈ normalizer (X : Set G)) (hgK : g ∈ normalizer (K : Set G)) {x : G} (hx : x ∈ X) :
    x⁻¹ * (g * x * g⁻¹) ∈ K := by
  by_cases hxK : x ∈ K
  · exact mul_mem (inv_mem hxK) ((gmh_conj_mem_iff hgK x).mpr hxK)
  · exact hK2 x hx _ ((gmh_conj_mem_iff hgX x).mpr hx) hxK
      (fun h => hxK ((gmh_conj_mem_iff hgK x).mp h))

theorem gmh_comm_mem_of_two_cosets {N C B : Subgroup G} {e : G}
    (hCN : ∀ x ∈ N, ∀ y ∈ N, x ∉ C → y ∉ C → x⁻¹ * y ∈ C)
    (hBC : ∀ x ∈ C, ∀ y ∈ C, x ∉ B → y ∉ B → x⁻¹ * y ∈ B) (hCle : C ≤ N)
    (hBn : ∀ n ∈ N, ∀ b ∈ B, n * b * n⁻¹ ∈ B) (heN : e ∈ normalizer (N : Set G))
    (heC : e ∈ normalizer (C : Set G)) (heB : e ∈ normalizer (B : Set G))
    (hodd : Odd (orderOf e)) {n : G} (hn : n ∈ N) : n * e * n⁻¹ * e⁻¹ ∈ B := by
  set d := n⁻¹ * (e * n * e⁻¹) with hd
  have hdC : d ∈ C := gmh_conj_mem_of_two_cosets hCN heN heC hn
  have hdN : d ∈ N := hCle hdC
  have hb' : d⁻¹ * (e * d * e⁻¹) ∈ B := gmh_conj_mem_of_two_cosets hBC heC heB hdC
  have hnd : e * n * e⁻¹ = n * d := by rw [hd]; group
  have h1 : e * d * e⁻¹ = d * (d⁻¹ * (e * d * e⁻¹)) := by group
  have hind : ∀ k : ℕ, ∃ b ∈ B, e ^ k * n * (e ^ k)⁻¹ = n * d ^ k * b := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨b, hb, hk⟩ := ih
      obtain ⟨c, hc, hck⟩ := gmh_exists_pow_mul (B := B) (d := d) (b := d⁻¹ * (e * d * e⁻¹))
        (fun x hx => by simpa using hBn d⁻¹ (inv_mem hdN) x hx) hb' k
      refine ⟨c * (e * b * e⁻¹), mul_mem hc ((gmh_conj_mem_iff heB b).mpr hb), ?_⟩
      calc e ^ (k + 1) * n * (e ^ (k + 1))⁻¹ = e * (e ^ k * n * (e ^ k)⁻¹) * e⁻¹ := by
            rw [pow_succ']; group
        _ = e * (n * d ^ k * b) * e⁻¹ := by rw [hk]
        _ = (e * n * e⁻¹) * (e * d * e⁻¹) ^ k * (e * b * e⁻¹) := by rw [conj_pow]; group
        _ = (n * d) * (d * (d⁻¹ * (e * d * e⁻¹))) ^ k * (e * b * e⁻¹) := by rw [hnd, ← h1]
        _ = n * d ^ (k + 1) * (c * (e * b * e⁻¹)) := by rw [hck, pow_succ']; group
  obtain ⟨b, hb, hk⟩ := hind (orderOf e)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
  have h' : d ^ orderOf e * b = 1 := by
    have h2 : n * (d ^ orderOf e * b) = n := by rw [← mul_assoc]; exact hk.symm
    exact mul_eq_left.mp h2
  have hdm : d ^ orderOf e ∈ B := by
    rw [eq_inv_of_mul_eq_one_left h']
    exact inv_mem hb
  have hd2 : d ^ 2 ∈ B := by
    by_cases hdB : d ∈ B
    · exact pow_mem hdB 2
    · have h2 := hBC d⁻¹ (inv_mem hdC) d hdC (fun h => hdB (by simpa using inv_mem h)) hdB
      simpa [sq] using h2
  have hdB : d ∈ B := gmh_mem_of_pow_odd_mem hd2 hodd hdm
  have e1 : n * e * n⁻¹ * e⁻¹ = n * d⁻¹ * n⁻¹ := by rw [hd]; group
  rw [e1]
  exact hBn n hn _ (inv_mem hdB)

theorem gmh_eq_one_or_eq_of_mem_zpowers {v z : G} (hv : v ^ 2 = 1) (hz : z ∈ zpowers v) :
    z = 1 ∨ z = v := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hvv : v ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hv]
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, hvv, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hvv, one_zpow, one_mul, zpow_one]

theorem gmh_sup_zpowers_facts {F : Subgroup G} {v : G} (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hFsq : ∀ a ∈ F, a ^ 2 = 1) (hvF : ∀ a ∈ F, v * a = a * v) (hv2 : v ^ 2 = 1) :
    (∀ x ∈ F ⊔ zpowers v, ∃ a ∈ F, x = a ∨ x = a * v) ∧
      (∀ x ∈ F ⊔ zpowers v, ∀ y ∈ F ⊔ zpowers v, x * y = y * x) ∧
      ∀ x ∈ F ⊔ zpowers v, x ^ 2 = 1 := by
  have hvC : v ∈ centralizer (F : Set G) := mem_centralizer_iff.mpr fun a ha => (hvF a ha).symm
  have hzN : zpowers v ≤ normalizer (F : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hvC)
  have hmem : ∀ x ∈ F ⊔ zpowers v, ∃ a ∈ F, x = a ∨ x = a * v := by
    intro x hx
    have hx' : x ∈ ((F ⊔ zpowers v : Subgroup G) : Set G) := hx
    rw [coe_mul_of_right_le_normalizer_left F (zpowers v) hzN] at hx'
    obtain ⟨a, ha, z, hz, rfl⟩ := hx'
    rcases gmh_eq_one_or_eq_of_mem_zpowers hv2 hz with rfl | rfl
    · exact ⟨a, ha, Or.inl (mul_one a)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  refine ⟨hmem, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := hmem x hx
    obtain ⟨b, hb, hyb⟩ := hmem y hy
    have hab : Commute a b := hFab a ha b hb
    have hva : Commute v a := hvF a ha
    have hvb : Commute v b := hvF b hb
    have hx' : Commute x b ∧ Commute x v := by
      rcases hxa with h1 | h1 <;> rw [h1]
      · exact ⟨hab, hva.symm⟩
      · exact ⟨hab.mul_left hvb, hva.symm.mul_left (Commute.refl v)⟩
    rcases hyb with h2 | h2 <;> rw [h2]
    · exact hx'.1.eq
    · exact (hx'.1.mul_right hx'.2).eq
  · intro x hx
    obtain ⟨a, ha, h1 | h1⟩ := hmem x hx <;> rw [h1]
    · exact hFsq a ha
    · rw [(show Commute a v from (hvF a ha).symm).mul_pow, hFsq a ha, hv2, one_mul]

theorem gmh_conj_mem_centralizer {F : Subgroup G} {g x : G} (hg : g ∈ normalizer (F : Set G))
    (hx : x ∈ centralizer (F : Set G)) : g * x * g⁻¹ ∈ centralizer (F : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : g⁻¹ * a * g ∈ F := by
    apply (gmh_conj_mem_iff hg (g⁻¹ * a * g)).mp
    rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
    exact ha
  have h1 := mem_centralizer_iff.mp hx _ ha'
  calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * a := by group

theorem gmh_mem_normalizer_centralizer [Finite G] {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (centralizer (A : Set G) : Set G) :=
  gmh_mem_normalizer_of_conj_mem fun _ hc =>
    gmh_conj_mem_centralizer (F := A) hg hc

theorem gmh_conj_mem_of_nArg [Finite G] {F A₁ P R H : Subgroup G} {v e : G}
    (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hFsq : ∀ a ∈ F, a ^ 2 = 1) (hA₁F : A₁ ≤ F)
    (hvF : ∀ a ∈ F, v * a = a * v) (hv2 : v ^ 2 = 1) (hvnF : v ∉ F)
    (hR : IsSylowOf 2 R (centralizer ((F ⊔ zpowers v : Subgroup G) : Set G)))
    (hRcard : Nat.card R ≤ 2 * Nat.card (F ⊔ zpowers v : Subgroup G))
    (hFP : F ≤ P)
    (hPN : P ≤ normalizer ((F ⊔ zpowers v : Subgroup G) : Set G))
    (hPC : P ≤ centralizer (F : Set G)) (hPsq : ∀ x ∈ P, x ^ 2 ∈ A₁)
    (hPtr : ∀ a ∈ F, ∃ u ∈ P, u * v * u⁻¹ = a * v)
    (hHv : H ≤ centralizer ({v} : Set G)) (hHF : H ≤ normalizer (F : Set G))
    (hHodd : Odd (Nat.card H))
    (hHab : ∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ x ∈ F,
      (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x)
    (he : e ∈ H) (heP : e ∈ normalizer (P : Set G))
    (hetr : ∀ a ∈ A₁, ∀ b ∈ A₁, a ≠ 1 → b ≠ 1 → ∃ n : ℕ, (e ^ n)⁻¹ * a * e ^ n = b)
    (hy : ∃ y ∈ P, (y * e * y⁻¹ * e⁻¹) ^ 2 ≠ 1) :
    ∀ h ∈ H, ∀ a ∈ A₁, h * a * h⁻¹ ∈ A₁ := by
  classical
  set A : Subgroup G := F ⊔ zpowers v with hA
  obtain ⟨hAmem, hAab, hAsq⟩ := gmh_sup_zpowers_facts hFab hFsq hvF hv2
  have hFA : F ≤ A := le_sup_left
  have hvA : v ∈ A := mem_sup_right (mem_zpowers v)
  set N₁ : Subgroup G := centralizer (A : Set G) with hN₁
  have hmemN₁ : ∀ c, (∀ a ∈ F, a * c = c * a) → v * c = c * v → c ∈ N₁ := by
    intro c hcF hcv
    rw [hN₁, mem_centralizer_iff]
    intro x hx
    obtain ⟨a, ha, h1 | h1⟩ := hAmem x hx <;> rw [h1]
    · exact hcF a ha
    · calc a * v * c = a * (c * v) := by rw [mul_assoc, hcv]
        _ = c * (a * v) := by rw [← mul_assoc, hcF a ha, mul_assoc]
  have hAN₁ : A ≤ N₁ := fun x hx => mem_centralizer_iff.mpr fun y hy => hAab y hy x hx
  have hN₁F : ∀ c ∈ N₁, ∀ a ∈ F, a * c = c * a := fun c hc a ha =>
    mem_centralizer_iff.mp hc a (hFA ha)
  obtain ⟨hAR, hidx, -, Y, hYN₁, hYodd, hYmem, hYR⟩ :=
    gmh_exists_two_complement hAN₁ le_rfl hAsq hR hRcard
  have hRN₁ : R ≤ N₁ := hR.le
  have hnormY : ∀ g ∈ normalizer (A : Set G), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    refine hYmem _ ((gmh_conj_mem_iff (gmh_mem_normalizer_centralizer hg) y).mpr (hYN₁ hy)) ?_
    have h1 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [h1]
    exact hYodd y hy
  have hN₁A : N₁ ≤ normalizer (A : Set G) := centralizer_le_normalizer _
  have hYnorm : ∀ g ∈ normalizer (A : Set G), g ∈ normalizer (Y : Set G) := fun g hg =>
    gmh_mem_normalizer_of_conj_mem (hnormY g hg)
  have hHA : ∀ h ∈ H, h ∈ normalizer (A : Set G) := by
    intro h hh
    apply gmh_mem_normalizer_of_conj_mem
    intro x hx
    have hhv : h * v * h⁻¹ = v := by
      rw [mem_centralizer_singleton_iff.mp (hHv hh), mul_inv_cancel_right]
    have hha : ∀ a ∈ F, h * a * h⁻¹ ∈ F := fun a ha => (gmh_conj_mem_iff (hHF hh) a).mpr ha
    obtain ⟨a, ha, h1 | h1⟩ := hAmem x hx <;> rw [h1]
    · exact hFA (hha a ha)
    · rw [show h * (a * v) * h⁻¹ = (h * a * h⁻¹) * (h * v * h⁻¹) by group, hhv]
      exact mul_mem (hFA (hha a ha)) hvA
  set N₀ : Subgroup G := normalizer (A : Set G) ⊓ centralizer (F : Set G) with hN₀
  have hPN₀ : P ≤ N₀ := le_inf hPN hPC
  have hphi : ∀ x ∈ N₀, ∃ a ∈ F, x * v * x⁻¹ = a * v := by
    intro x hx
    have h1 : x * v * x⁻¹ ∈ A := (gmh_conj_mem_iff (mem_inf.mp hx).1 v).mpr hvA
    obtain ⟨a, ha, h2 | h2⟩ := hAmem _ h1
    · exfalso
      apply hvnF
      have hax : a * x = x * a := mem_centralizer_iff.mp (mem_inf.mp hx).2 a ha
      have : v = a := by
        calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
          _ = x⁻¹ * (a * x) := by rw [h2, mul_assoc]
          _ = a := by rw [hax, inv_mul_cancel_left]
      rw [this]
      exact ha
    · exact ⟨a, ha, h2⟩
  have hN₀P : ∀ x ∈ N₀, ∃ u ∈ P, u⁻¹ * x ∈ N₁ := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := hphi x hx
    obtain ⟨u, hu, hua⟩ := hPtr a ha
    refine ⟨u, hu, hmemN₁ _ (fun b hb => ?_) ?_⟩
    · have h1 : Commute b u := mem_centralizer_iff.mp (hPC hu) b hb
      have h2 : Commute b x := mem_centralizer_iff.mp (mem_inf.mp hx).2 b hb
      exact (h1.inv_right.mul_right h2).eq
    · calc v * (u⁻¹ * x) = u⁻¹ * (u * v * u⁻¹) * x := by group
        _ = u⁻¹ * (x * v * x⁻¹) * x := by rw [hua, hxa]
        _ = u⁻¹ * x * v := by group
  have hoddN₀ : ∀ x ∈ N₀, Odd (orderOf x) → x ∈ Y := by
    intro x hx hxodd
    obtain ⟨a, ha, hxa⟩ := hphi x hx
    have hxa' : x * v * x⁻¹ = v * a := by rw [hxa, hvF a ha]
    have hax : x * a = a * x := (mem_centralizer_iff.mp (mem_inf.mp hx).2 a ha).symm
    have hpow := gmh_pow_conj_eq hxa' hax (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
    have ha1 : a ^ orderOf x = 1 := mul_eq_left.mp hpow.symm
    have ha' : a = 1 := gmh_eq_one_of_sq_of_odd (hFsq a ha)
      (hxodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ha1))
    rw [ha', mul_one] at hxa'
    have hxv : v * x = x * v := by
      calc v * x = x * v * x⁻¹ * x := by rw [hxa']
        _ = x * v := by group
    exact hYmem x (hmemN₁ x (fun b hb => mem_centralizer_iff.mp (mem_inf.mp hx).2 b hb) hxv)
      hxodd
  have hHcomm : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈ Y := by
    intro h₁ hh₁ h₂ hh₂
    have hc : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈ H :=
      mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)
    refine hoddN₀ _ (mem_inf.mpr ⟨hHA _ hc, mem_centralizer_iff.mpr fun x hx => ?_⟩)
      (hHodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard H hc))
    have h1 := hHab h₁ hh₁ h₂ hh₂ x hx
    set c := h₁ * h₂ * h₁⁻¹ * h₂⁻¹
    calc x * c = c * x * c⁻¹ * c := by rw [h1]
      _ = c * x := by group
  have heodd : Odd (orderOf e) := hHodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard H he)
  have heA : e ∈ normalizer (A : Set G) := hHA e he
  have hYN : ∀ n ∈ N₁, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := fun n hn => hnormY n (hN₁A hn)
  have hAY : A ≤ normalizer (Y : Set G) := fun a ha => hYnorm a (hN₁A (hAN₁ ha))
  have hFY : F ≤ normalizer (Y : Set G) := fun a ha => hAY (hFA ha)
  have hcommN₁ : ∀ n ∈ N₁, n * e * n⁻¹ * e⁻¹ ∈ F ⊔ Y := by
    intro n hn
    refine gmh_comm_mem_of_two_cosets (N := N₁) (C := A ⊔ Y) (B := F ⊔ Y) ?_ ?_
      (sup_le hAN₁ hYN₁) ?_ (gmh_mem_normalizer_centralizer heA) ?_ ?_ heodd hn
    · intro x hx y hy hxC hyC
      obtain ⟨y₁, hy₁, r₁, hr₁, rfl⟩ := hYR x hx
      obtain ⟨y₂, hy₂, r₂, hr₂, rfl⟩ := hYR y hy
      have hr₁A : r₁ ∉ A := fun h => hxC (mul_mem (mem_sup_right hy₁) (mem_sup_left h))
      have hr₂A : r₂ ∉ A := fun h => hyC (mul_mem (mem_sup_right hy₂) (mem_sup_left h))
      have hr : r₁⁻¹ * r₂ ∈ A := gmh_inv_mul_mem_of_relIndex_le_two hidx hr₁ hr₂ hr₁A hr₂A
      have hyy : r₁⁻¹ * (y₁⁻¹ * y₂) * r₁⁻¹⁻¹ ∈ Y :=
        hYN _ (inv_mem (hRN₁ hr₁)) _ (mul_mem (inv_mem hy₁) hy₂)
      rw [show (y₁ * r₁)⁻¹ * (y₂ * r₂) = (r₁⁻¹ * (y₁⁻¹ * y₂) * r₁⁻¹⁻¹) * (r₁⁻¹ * r₂) by group]
      exact mul_mem (mem_sup_right hyy) (mem_sup_left hr)
    · intro x hx y hy hxB hyB
      obtain ⟨a₁, ha₁, y₁, hy₁, rfl⟩ := gmh_exists_mul_of_mem_sup hAY hx
      obtain ⟨a₂, ha₂, y₂, hy₂, rfl⟩ := gmh_exists_mul_of_mem_sup hAY hy
      obtain ⟨f₁, hf₁, h1 | h1⟩ := hAmem a₁ ha₁
      · exact absurd (mul_mem (mem_sup_left (h1 ▸ hf₁)) (mem_sup_right hy₁)) hxB
      obtain ⟨f₂, hf₂, h2 | h2⟩ := hAmem a₂ ha₂
      · exact absurd (mul_mem (mem_sup_left (h2 ▸ hf₂)) (mem_sup_right hy₂)) hyB
      rw [h1, h2]
      have hv' : v⁻¹ * (f₁⁻¹ * f₂) * v = f₁⁻¹ * f₂ := by
        rw [mul_assoc, ← hvF _ (mul_mem (inv_mem hf₁) hf₂), inv_mul_cancel_left]
      rw [show (f₁ * v * y₁)⁻¹ * (f₂ * v * y₂) = y₁⁻¹ * (v⁻¹ * (f₁⁻¹ * f₂) * v) * y₂ by group,
        hv']
      exact mul_mem (mul_mem (mem_sup_right (inv_mem hy₁))
        (mem_sup_left (mul_mem (inv_mem hf₁) hf₂))) (mem_sup_right hy₂)
    · intro n' hn' b hb
      obtain ⟨f, hf, y, hy, rfl⟩ := gmh_exists_mul_of_mem_sup hFY hb
      have hfn : n' * f * n'⁻¹ = f := by
        rw [← hN₁F n' hn' f hf, mul_inv_cancel_right]
      rw [show n' * (f * y) * n'⁻¹ = (n' * f * n'⁻¹) * (n' * y * n'⁻¹) by group, hfn]
      exact mul_mem (mem_sup_left hf) (mem_sup_right (hYN n' hn' y hy))
    · apply gmh_mem_normalizer_of_conj_mem
      intro x hx
      obtain ⟨a, ha, y, hy, rfl⟩ := gmh_exists_mul_of_mem_sup hAY hx
      rw [show e * (a * y) * e⁻¹ = (e * a * e⁻¹) * (e * y * e⁻¹) by group]
      exact mul_mem (mem_sup_left ((gmh_conj_mem_iff heA a).mpr ha))
        (mem_sup_right (hnormY e heA y hy))
    · apply gmh_mem_normalizer_of_conj_mem
      intro x hx
      obtain ⟨a, ha, y, hy, rfl⟩ := gmh_exists_mul_of_mem_sup hFY hx
      rw [show e * (a * y) * e⁻¹ = (e * a * e⁻¹) * (e * y * e⁻¹) by group]
      exact mul_mem (mem_sup_left ((gmh_conj_mem_iff (hHF he) a).mpr ha))
        (mem_sup_right (hnormY e heA y hy))
  have hPY : P ≤ normalizer (Y : Set G) := fun p hp => hYnorm p (hPN hp)
  set K : Subgroup G := closure ({z | ∃ x ∈ N₀, z = x * e * x⁻¹ * e⁻¹} ∪ (Y : Set G)) with hK
  have hKle : K ≤ P ⊔ Y := by
    rw [hK, closure_le]
    rintro z (⟨x, hx, rfl⟩ | hz)
    · obtain ⟨u, hu, hun⟩ := hN₀P x hx
      have h1 := hcommN₁ _ hun
      obtain ⟨f, hf, y, hy, hfy⟩ := gmh_exists_mul_of_mem_sup hFY h1
      have hue : u * e * u⁻¹ * e⁻¹ ∈ P := by
        rw [show u * e * u⁻¹ * e⁻¹ = u * (e * u⁻¹ * e⁻¹) by group]
        exact mul_mem hu ((gmh_conj_mem_iff heP _).mpr (inv_mem hu))
      have e1 : x * e * x⁻¹ * e⁻¹ = (u * f * u⁻¹) * (u * y * u⁻¹) * (u * e * u⁻¹ * e⁻¹) := by
        rw [show u * f * u⁻¹ * (u * y * u⁻¹) = u * (f * y) * u⁻¹ by group, hfy]
        group
      rw [e1]
      refine mul_mem (mul_mem (mem_sup_left ?_) (mem_sup_right ?_)) (mem_sup_left hue)
      · exact mul_mem (mul_mem hu (hFP hf)) (inv_mem hu)
      · exact (gmh_conj_mem_iff (hPY hu) y).mpr hy
    · exact mem_sup_right hz
  have hN₀H : ∀ h ∈ H, ∀ x ∈ N₀, h * x * h⁻¹ ∈ N₀ := by
    intro h hh x hx
    refine mem_inf.mpr ⟨mul_mem (mul_mem (hHA h hh) (mem_inf.mp hx).1) (inv_mem (hHA h hh)), ?_⟩
    exact gmh_conj_mem_centralizer (hHF hh) (mem_inf.mp hx).2
  have hKH : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    induction hk using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with ⟨x, hx, rfl⟩ | hz
      · have hx' := hN₀H h hh x hx
        have hc := hHcomm h hh e he
        set x' := h * x * h⁻¹
        set c := h * e * h⁻¹ * e⁻¹
        rw [show h * (x * e * x⁻¹ * e⁻¹) * h⁻¹ =
          (x' * c * x'⁻¹) * (x' * e * x'⁻¹ * e⁻¹) * c⁻¹ by simp only [x', c]; group]
        have hxc : x' * c * x'⁻¹ ∈ Y := hnormY x' (mem_inf.mp hx').1 c hc
        exact mul_mem (mul_mem (subset_closure (Or.inr hxc))
          (subset_closure (Or.inl ⟨x', hx', rfl⟩))) (inv_mem (subset_closure (Or.inr hc)))
      · exact subset_closure (Or.inr (hnormY h (hHA h hh) z hz))
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ by group]
      exact inv_mem ha
  set M : Subgroup G := closure ({z | ∃ k ∈ K, z = k ^ 2} ∪ (Y : Set G)) with hM
  have hMH : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
    intro h hh m hm
    induction hm using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with ⟨k, hk, rfl⟩ | hz
      · rw [← conj_pow]
        exact subset_closure (Or.inl ⟨_, hKH h hh k hk, rfl⟩)
      · exact subset_closure (Or.inr (hnormY h (hHA h hh) z hz))
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ by group]
      exact inv_mem ha
  have hA₁Y : A₁ ≤ normalizer (Y : Set G) := fun a ha => hFY (hA₁F ha)
  have hMle : M ≤ A₁ ⊔ Y := by
    rw [hM, closure_le]
    rintro z (⟨k, hk, rfl⟩ | hz)
    · obtain ⟨p, hp, y, hy, rfl⟩ := gmh_exists_mul_of_mem_sup hPY (hKle hk)
      have hpy : p⁻¹ * y * p⁻¹⁻¹ ∈ Y := (gmh_conj_mem_iff (hPY (inv_mem hp)) y).mpr hy
      rw [show (p * y) ^ 2 = p ^ 2 * ((p⁻¹ * y * p⁻¹⁻¹) * y) by rw [sq, sq]; group]
      exact mul_mem (mem_sup_left (hPsq p hp)) (mem_sup_right (mul_mem hpy hy))
    · exact mem_sup_right hz
  have hA₁M : A₁ ≤ M := by
    obtain ⟨y₀, hy₀, hy₀'⟩ := hy
    set z₀ := y₀ * e * y₀⁻¹ * e⁻¹ with hz₀
    have hz₀K : z₀ ∈ K := subset_closure (Or.inl ⟨y₀, hPN₀ hy₀, rfl⟩)
    have hz₀P : z₀ ∈ P := by
      rw [hz₀, show y₀ * e * y₀⁻¹ * e⁻¹ = y₀ * (e * y₀⁻¹ * e⁻¹) by group]
      exact mul_mem hy₀ ((gmh_conj_mem_iff heP _).mpr (inv_mem hy₀))
    have hz₀M : z₀ ^ 2 ∈ M := subset_closure (Or.inl ⟨z₀, hz₀K, rfl⟩)
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem _
    obtain ⟨n, hn⟩ := hetr _ (hPsq z₀ hz₀P) a ha hy₀' ha1
    rw [← hn]
    have h1 := hMH _ (inv_mem (pow_mem he n)) _ hz₀M
    rwa [inv_inv] at h1
  intro h hh a ha
  have h1 : h * a * h⁻¹ ∈ A₁ ⊔ Y := hMle (hMH h hh a (hA₁M ha))
  obtain ⟨a', ha', y, hy, hay⟩ := gmh_exists_mul_of_mem_sup hA₁Y h1
  have hcomm : Commute a' y := mem_centralizer_iff.mp (hYN₁ hy) a' (hFA (hA₁F ha'))
  have hsq : (h * a * h⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hFsq a (hA₁F ha), mul_one, mul_inv_cancel]
  rw [← hay, hcomm.mul_pow, hFsq a' (hA₁F ha'), one_mul] at hsq
  have hy1 : y = 1 := gmh_eq_one_of_sq_of_odd hsq (hYodd y hy)
  rw [← hay, hy1, mul_one]
  exact ha'

end GmhGeneral

end CFSG.SeitzReduction.RankOne
