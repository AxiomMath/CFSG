module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Odd
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Local

variable {X : Type*} [Group X]

structure LocalData (y t : X) (K : Subgroup X) : Prop where
  y_cent : ∀ x : X, x * y = y * x
  y_ord : orderOf y = 3
  t_sq : t * t = 1
  t_ne : t ≠ 1
  K_t : ∀ k ∈ K, k * t = t * k
  K_S5 : Nonempty (K ≃* Equiv.Perm (Fin 5))
  cent_t : centralizer ({t} : Set X) = zpowers t ⊔ (zpowers y ⊔ K)

variable {y t : X} {K : Subgroup X}

theorem zpow_involution (a : X) (ha : a * a = 1) (n : ℤ) : a ^ n = 1 ∨ a ^ n = a := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [hk, zpow_add_one, zpow_mul, zpow_two, ha, one_zpow, one_mul]

theorem LocalData.y_cube (h : LocalData y t K) (j : ℤ) : (y ^ j) ^ 3 = 1 := by
  have h3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h.y_ord] at this
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]

theorem LocalData.K_y (h : LocalData y t K) : ∀ k ∈ K, k * y = y * k := fun k _ => h.y_cent k

theorem LocalData.sup_comm_t (h : LocalData y t K) :
    ∀ a ∈ zpowers y ⊔ K, a * t = t * a := by
  intro a ha
  have : a ∈ centralizer ({t} : Set X) := by
    rw [h.cent_t]
    exact Subgroup.mem_sup_right ha
  exact mem_centralizer_singleton_iff.1 this

theorem LocalData.decomp (h : LocalData y t K) {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    ∃ n j : ℤ, ∃ k ∈ K, g = t ^ n * (y ^ j * k) := by
  rw [h.cent_t] at hg
  obtain ⟨n, a, ha, rfl⟩ := exists_zpow_mul_of_mem_sup h.sup_comm_t hg
  obtain ⟨j, k, hk, rfl⟩ := exists_zpow_mul_of_mem_sup h.K_y ha
  exact ⟨n, j, k, hk, rfl⟩

theorem LocalData.K_trivial_of_central (h : LocalData y t K) {k : X} (hk : k ∈ K)
    (hc : ∀ k' ∈ K, k * k' = k' * k) : k = 1 := by
  obtain ⟨e⟩ := h.K_S5
  have : e ⟨k, hk⟩ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    obtain ⟨k', rfl⟩ := e.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc k' k'.2)
  have h1 : (⟨k, hk⟩ : K) = 1 := e.injective (by rw [this, map_one])
  exact congrArg Subtype.val h1

theorem mem_zpowers_sq_of_odd {g : X} (hg : Odd (orderOf g)) : g ∈ zpowers (g * g) := by
  obtain ⟨s, hs⟩ := hg
  have : (g * g) ^ (s + 1) = g := by
    rw [← pow_two, ← pow_mul, show 2 * (s + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have h2 : (g * g) ^ (s + 1) ∈ zpowers (g * g) := pow_mem (mem_zpowers _) _
  rwa [this] at h2

variable [Finite X]

omit [Finite X] in
theorem LocalData.y_mem_O (h : LocalData y t K) : y ∈ Open.fusionOddCore X := by
  have hN : (zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hn
    have : g * y ^ m * g⁻¹ = y ^ m := ((show Commute g y from h.y_cent g).zpow_right m).mul_inv_cancel
    rw [this]
    exact zpow_mem (mem_zpowers y) m
  have hodd : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, h.y_ord]
    decide
  exact le_fusionOddCore_of_odd' hodd (mem_zpowers y)

theorem LocalData.O_inf_K (h : LocalData y t K) : Open.fusionOddCore X ⊓ K = ⊥ := by
  obtain ⟨e⟩ := h.K_S5
  exact inf_eq_bot_of_odd e (natCard_fusionOddCore_odd' X)

theorem LocalData.O_inf_cent (h : LocalData y t K) :
    Open.fusionOddCore X ⊓ centralizer ({t} : Set X) = zpowers y := by
  apply le_antisymm
  · rintro g ⟨hgO, hgt⟩
    obtain ⟨n, j, k, hk, rfl⟩ := h.decomp hgt
    set a : X := y ^ j * k with ha
    have hamem : a ∈ zpowers y ⊔ K :=
      mul_mem (Subgroup.mem_sup_left (zpow_mem (mem_zpowers y) j)) (Subgroup.mem_sup_right hk)
    have hca : a * t ^ n = t ^ n * a := (show Commute a t from h.sup_comm_t a hamem).zpow_right n
    have ht2 : t ^ n * t ^ n = 1 := by
      rcases zpow_involution t h.t_sq n with h1 | h1 <;> rw [h1]
      · simp
      · exact h.t_sq
    have hg2 : t ^ n * a * (t ^ n * a) = a * a := by
      calc t ^ n * a * (t ^ n * a) = t ^ n * (a * t ^ n) * a := by simp only [mul_assoc]
        _ = t ^ n * (t ^ n * a) * a := by rw [hca]
        _ = (t ^ n * t ^ n) * (a * a) := by simp only [mul_assoc]
        _ = a * a := by rw [ht2, one_mul]
    have hodd : Odd (orderOf (t ^ n * a)) :=
      Odd.of_dvd_nat (natCard_fusionOddCore_odd' X) (Subgroup.orderOf_dvd_natCard _ hgO)
    have hmem := mem_zpowers_sq_of_odd hodd
    rw [hg2] at hmem
    have hgM : t ^ n * a ∈ zpowers y ⊔ K :=
      (Subgroup.zpowers_le.2 (mul_mem hamem hamem)) hmem
    obtain ⟨j', k', hk', hgeq⟩ := exists_zpow_mul_of_mem_sup h.K_y hgM
    have hyO : y ^ j' ∈ Open.fusionOddCore X := zpow_mem h.y_mem_O j'
    have hk'O : k' ∈ Open.fusionOddCore X := by
      have : k' = (y ^ j')⁻¹ * (t ^ n * a) := by rw [hgeq]; group
      rw [this]
      exact mul_mem (inv_mem hyO) hgO
    have hk'1 : k' = 1 := by
      have : k' ∈ Open.fusionOddCore X ⊓ K := ⟨hk'O, hk'⟩
      rw [h.O_inf_K, mem_bot] at this
      exact this
    rw [hgeq, hk'1, mul_one]
    exact zpow_mem (mem_zpowers y) j'
  · intro g hg
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨zpow_mem h.y_mem_O m, mem_centralizer_singleton_iff.2 ?_⟩
    exact ((show Commute y t from (h.y_cent t).symm).zpow_left m)

theorem sq_eq_one_of_mem_O {z : X} (hz : z * z = 1) (hzO : z ∈ Open.fusionOddCore X) : z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz)
  have h2 : orderOf z ∣ Nat.card (Open.fusionOddCore X) := Subgroup.orderOf_dvd_natCard _ hzO
  have h3 : Odd (orderOf z) := Odd.of_dvd_nat (natCard_fusionOddCore_odd' X) h2
  have : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h4 | h4
    · exact h4
    · rw [h4] at h3
      exact absurd h3 (by decide)
  exact orderOf_eq_one_iff.1 this

omit [Finite X] in
theorem LocalData.zpowers_normal (h : LocalData y t K) : (zpowers y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hn
  have : g * y ^ m * g⁻¹ = y ^ m :=
    ((show Commute g y from h.y_cent g).zpow_right m).mul_inv_cancel
  rw [this]
  exact zpow_mem (mem_zpowers y) m

theorem LocalData.O_inv_comm (h : LocalData y t K) :
    (∀ o ∈ Open.fusionOddCore X, t * o * t⁻¹ * o ∈ zpowers y) ∧
    (∀ o₁ ∈ Open.fusionOddCore X, ∀ o₂ ∈ Open.fusionOddCore X,
      o₁ * o₂ * o₁⁻¹ * o₂⁻¹ ∈ zpowers y) := by
  have hN := h.zpowers_normal
  have hNodd : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, h.y_ord]
    decide
  have hNO : zpowers y ≤ Open.fusionOddCore X := Subgroup.zpowers_le.2 h.y_mem_O
  have hT2 := map_centralizer_eq_of_odd (zpowers y) hNodd h.t_sq
  let π : X →* X ⧸ zpowers y := QuotientGroup.mk' (zpowers y)
  let Ob : Subgroup (X ⧸ zpowers y) := (Open.fusionOddCore X).map π
  have hn : ∀ o ∈ Ob, π t * o * (π t)⁻¹ ∈ Ob := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨t * o * t⁻¹, (inferInstance : (Open.fusionOddCore X).Normal).conj_mem o ho t,
      by simp [map_mul, map_inv]⟩
  have hfix : ∀ o ∈ Ob, π t * o = o * π t → o = 1 := by
    rintro _ ⟨o, ho, rfl⟩ hc
    have hm : π o ∈ centralizer ({π t} : Set (X ⧸ zpowers y)) :=
      mem_centralizer_singleton_iff.2 hc.symm
    rw [← hT2] at hm
    obtain ⟨c, hc', hco⟩ := hm
    have h1 : c⁻¹ * o ∈ zpowers y := (QuotientGroup.eq).1 hco
    have hcO : c ∈ Open.fusionOddCore X := by
      have : c = o * (c⁻¹ * o)⁻¹ := by group
      rw [this]
      exact mul_mem ho (inv_mem (hNO h1))
    have hc1 : c ∈ zpowers y := by
      rw [← h.O_inf_cent]
      exact ⟨hcO, hc'⟩
    rw [← hco]
    exact (QuotientGroup.eq_one_iff c).2 hc1
  have htt : π t * π t = 1 := by rw [← map_mul, h.t_sq, map_one]
  obtain ⟨hinv, hcomm⟩ := inv_of_centralizer_eq_bot htt hn hfix
  constructor
  · intro o ho
    have h1 := hinv (π o) ⟨o, ho, rfl⟩
    refine (QuotientGroup.eq_one_iff _).1 ?_
    show π (t * o * t⁻¹ * o) = 1
    rw [map_mul, map_mul, map_mul, map_inv, h1]
    group
  · intro o₁ ho₁ o₂ ho₂
    have h1 := hcomm (π o₁) ⟨o₁, ho₁, rfl⟩ (π o₂) ⟨o₂, ho₂, rfl⟩
    refine (QuotientGroup.eq_one_iff _).1 ?_
    show π (o₁ * o₂ * o₁⁻¹ * o₂⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group

theorem LocalData.cent_quot (h : LocalData y t K) :
    centralizer ({QuotientGroup.mk' (Open.fusionOddCore X) t} :
        Set (X ⧸ Open.fusionOddCore X)) =
      zpowers (QuotientGroup.mk' (Open.fusionOddCore X) t) ⊔
        K.map (QuotientGroup.mk' (Open.fusionOddCore X)) := by
  rw [← map_centralizer_eq_of_odd _ (natCard_fusionOddCore_odd' X) h.t_sq, h.cent_t, Subgroup.map_sup,
    Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have : QuotientGroup.mk' (Open.fusionOddCore X) y = 1 :=
    (QuotientGroup.eq_one_iff y).2 h.y_mem_O
  rw [this, zpowers_one_eq_bot, bot_sup_eq]

theorem LocalData.K_card (h : LocalData y t K) :
    Nat.card (K.map (QuotientGroup.mk' (Open.fusionOddCore X))) = 120 := by
  obtain ⟨e⟩ := h.K_S5
  have hinj : Function.Injective
      ((QuotientGroup.mk' (Open.fusionOddCore X)).comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : (k : X) ∈ Open.fusionOddCore X := (QuotientGroup.eq_one_iff _).1 hk
    have h2 : (k : X) ∈ Open.fusionOddCore X ⊓ K := ⟨h1, k.2⟩
    rw [h.O_inf_K, mem_bot] at h2
    exact Subtype.ext h2
  have hr : ((QuotientGroup.mk' (Open.fusionOddCore X)).comp K.subtype).range =
      K.map (QuotientGroup.mk' (Open.fusionOddCore X)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr e.toEquiv,
    perm5_card]

theorem LocalData.disj (h : LocalData y t K) :
    Disjoint (zpowers (QuotientGroup.mk' (Open.fusionOddCore X) t))
      (K.map (QuotientGroup.mk' (Open.fusionOddCore X))) := by
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx1
  have htb : QuotientGroup.mk' (Open.fusionOddCore X) t *
      QuotientGroup.mk' (Open.fusionOddCore X) t = 1 := by rw [← map_mul, h.t_sq, map_one]
  rcases zpow_involution _ htb n with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hx2
    obtain ⟨k, hk, hkt⟩ := hx2
    have hO : t⁻¹ * k ∈ Open.fusionOddCore X := (QuotientGroup.eq).1 hkt.symm
    have hkt' : k * t = t * k := h.K_t k hk
    have hcent : t⁻¹ * k ∈ centralizer ({t} : Set X) := by
      refine mem_centralizer_singleton_iff.2 ?_
      have h2 : t⁻¹ * t = t * t⁻¹ := by group
      calc t⁻¹ * k * t = t⁻¹ * (k * t) := mul_assoc _ _ _
        _ = t⁻¹ * (t * k) := by rw [hkt']
        _ = t * (t⁻¹ * k) := by rw [← mul_assoc, h2, mul_assoc]
    have hy : t⁻¹ * k ∈ zpowers y := by
      rw [← h.O_inf_cent]
      exact ⟨hO, hcent⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hy
    have hkeq : k = t * y ^ j := by rw [hj]; group
    have hk1 : k = 1 := by
      apply h.K_trivial_of_central hk
      intro k' hk'
      have hc1 : k' * t = t * k' := h.K_t k' hk'
      have hc2 : k' * y ^ j = y ^ j * k' :=
        ((show Commute k' y from h.y_cent k').zpow_right j)
      rw [hkeq]
      calc t * y ^ j * k' = t * (y ^ j * k') := mul_assoc _ _ _
        _ = t * (k' * y ^ j) := by rw [hc2]
        _ = (t * k') * y ^ j := by rw [mul_assoc]
        _ = (k' * t) * y ^ j := by rw [hc1]
        _ = k' * (t * y ^ j) := by rw [mul_assoc]
    have ht1 : t = (y ^ j)⁻¹ := by
      rw [hk1] at hkeq
      exact (mul_eq_one_iff_eq_inv.1 hkeq.symm)
    have ht3 : t ^ 3 = 1 := by
      rw [ht1, inv_pow, h.y_cube, inv_one]
    apply h.t_ne
    calc t = t * t * t := by rw [h.t_sq, one_mul]
      _ = t ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := ht3

theorem LocalData.central_trivial (h : LocalData y t K) {z k₀ : X} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hk0 : k₀ * t * k₀⁻¹ = t * z) (d : X ⧸ Open.fusionOddCore X)
    (hd : ∀ g : X ⧸ Open.fusionOddCore X, g * d = d * g) : d = 1 := by
  set π := QuotientGroup.mk' (Open.fusionOddCore X) with hπ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective d
  have hdt := hd (π t)
  have hm : (QuotientGroup.mk x : X ⧸ Open.fusionOddCore X) ∈
      centralizer ({π t} : Set (X ⧸ Open.fusionOddCore X)) :=
    mem_centralizer_singleton_iff.2 hdt.symm
  rw [← map_centralizer_eq_of_odd _ (natCard_fusionOddCore_odd' X) h.t_sq] at hm
  obtain ⟨c, hc, hcx⟩ := hm
  have hcx' : (QuotientGroup.mk x : X ⧸ Open.fusionOddCore X) = π c := hcx.symm
  rw [hcx'] at hd ⊢
  obtain ⟨n, j, k, hk, rfl⟩ := h.decomp hc
  have hy1 : π (y ^ j) = 1 := by
    have hπy : π y = 1 := (QuotientGroup.eq_one_iff y).2 h.y_mem_O
    rw [map_zpow, hπy, one_zpow]
  have hcπ : π (t ^ n * (y ^ j * k)) = π (t ^ n) * π k := by
    rw [map_mul, map_mul, hy1, one_mul]
  rw [hcπ] at hd ⊢
  have hKc : ∀ k' ∈ K, k * k' = k' * k := by
    intro k' hk'
    have hd' := hd (π k')
    have hcomm : k' * t ^ n = t ^ n * k' :=
      ((show Commute k' t from h.K_t k' hk').zpow_right n)
    have e1 : π k' * π (t ^ n) = π (t ^ n) * π k' := by rw [← map_mul, ← map_mul, hcomm]
    have e2 : π (t ^ n) * (π k' * π k) = π (t ^ n) * (π k * π k') := by
      calc π (t ^ n) * (π k' * π k) = (π (t ^ n) * π k') * π k := (mul_assoc _ _ _).symm
        _ = (π k' * π (t ^ n)) * π k := by rw [e1]
        _ = π k' * (π (t ^ n) * π k) := mul_assoc _ _ _
        _ = (π (t ^ n) * π k) * π k' := hd'
        _ = π (t ^ n) * (π k * π k') := mul_assoc _ _ _
    have e3 : π k' * π k = π k * π k' := mul_left_cancel e2
    rw [← map_mul, ← map_mul] at e3
    have e4 : (k' * k)⁻¹ * (k * k') ∈ Open.fusionOddCore X := (QuotientGroup.eq).1 e3
    have e5 : (k' * k)⁻¹ * (k * k') ∈ K :=
      mul_mem (inv_mem (mul_mem hk' hk)) (mul_mem hk hk')
    have e6 : (k' * k)⁻¹ * (k * k') ∈ Open.fusionOddCore X ⊓ K := ⟨e4, e5⟩
    rw [h.O_inf_K, mem_bot] at e6
    exact (inv_mul_eq_one.1 e6).symm
  have hk1 : k = 1 := h.K_trivial_of_central hk hKc
  rw [hk1, map_one, mul_one] at hd ⊢
  have htb : π t * π t = 1 := by rw [← map_mul, h.t_sq, map_one]
  rw [map_zpow]
  rcases zpow_involution _ htb n with h1 | h1
  · exact h1
  · exfalso
    rw [map_zpow, h1] at hd
    have hd2 := hd (π k₀)
    have hk0' : k₀ * t = t * z * k₀ := mul_inv_eq_iff_eq_mul.1 hk0
    have e1 : π k₀ * π t = π t * (π z * π k₀) := by
      rw [← map_mul, ← map_mul, ← map_mul, hk0', mul_assoc]
    have e2 : π t * (π z * π k₀) = π t * π k₀ := by rw [← e1]; exact hd2
    have e3 : π z * π k₀ = π k₀ := mul_left_cancel e2
    have e4 : π z = 1 := by
      exact mul_right_cancel (b := π k₀) (e3.trans (one_mul _).symm)
    exact hz1 (sq_eq_one_of_mem_O hz2 ((QuotientGroup.eq_one_iff z).1 e4))

theorem LocalData.zstar_bot (h : LocalData y t K) {z k₀ : X} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hk0 : k₀ * t * k₀⁻¹ = t * z) :
    Open.fusionZStar (X ⧸ Open.fusionOddCore X) = ⊥ := by
  rw [eq_bot_iff]
  intro d hd
  rw [mem_bot]
  have hbot := fusionOddCore_quotient_eq_bot' X
  apply h.central_trivial hz2 hz1 hk0
  intro g
  have hc : QuotientGroup.mk' (Open.fusionOddCore (X ⧸ Open.fusionOddCore X)) d ∈
      center ((X ⧸ Open.fusionOddCore X) ⧸ Open.fusionOddCore (X ⧸ Open.fusionOddCore X)) := hd
  have h1 := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk' _ g)
  have h3 : QuotientGroup.mk' (Open.fusionOddCore (X ⧸ Open.fusionOddCore X)) (g * d) =
      QuotientGroup.mk' (Open.fusionOddCore (X ⧸ Open.fusionOddCore X)) (d * g) := by
    rw [map_mul, map_mul]
    exact h1
  have h4 : (g * d)⁻¹ * (d * g) ∈ Open.fusionOddCore (X ⧸ Open.fusionOddCore X) :=
    (QuotientGroup.eq).1 h3
  rw [hbot, mem_bot] at h4
  exact inv_mul_eq_one.1 h4

theorem exists_elemAbelian_quot (A : Subgroup X) (hA : Open.IsElemAbelian 2 A)
    (hcard : Nat.card A = 16) :
    ∃ B : Subgroup (X ⧸ Open.fusionOddCore X), Open.IsElemAbelian 2 B ∧ Nat.card B = 16 := by
  set π := QuotientGroup.mk' (Open.fusionOddCore X) with hπ
  have hinj : Function.Injective (π.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : X) ∈ Open.fusionOddCore X := (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (a : X) * a = 1 := by
      have := hA.2 a a.2
      rwa [pow_two] at this
    exact Subtype.ext (sq_eq_one_of_mem_O h2 h1)
  have hr : (π.comp A.subtype).range = A.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨A.map π, ⟨?_, ?_⟩, ?_⟩
  · have : IsMulCommutative A := hA.1
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a0, ha0, ha⟩ := a.2
    obtain ⟨b0, hb0, hb⟩ := b.2
    apply Subtype.ext
    show (a : X ⧸ Open.fusionOddCore X) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, setLike_mul_comm ha0 hb0]
  · rintro x ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  · rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]

end Local

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
