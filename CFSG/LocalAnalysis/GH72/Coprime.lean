module

public import CFSG.LocalAnalysis.GH72.Vocabulary
import CFSG.GroupTheory.OddInversion
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_iSup_eq_of_le_normalizer {ι : Sort*} {H : Subgroup G} {K : ι → Subgroup G}
    (hK : ∀ i, K i ≤ normalizer (H : Set G)) : ⁅H, ⨆ i, K i⁆ = ⨆ i, ⁅H, K i⁆ := by
  set L : Subgroup G := ⨆ i, ⁅H, K i⁆
  have hLH : L ≤ H := iSup_le fun i => le_normalizer_iff_commutator_le_left.mp (hK i)
  have hKL : ∀ i, K i ≤ normalizer (L : Set G) := fun i =>
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hLH le_rfl).trans (le_iSup (fun j => ⁅H, K j⁆) i))
  refine le_antisymm ?_ (iSup_le fun i => commutator_mono le_rfl (le_iSup K i))
  rw [commutator_le]
  intro h hh k hk
  suffices hC : k ∈ normalizer (L : Set G) ∧ ⁅h, k⁆ ∈ L from hC.2
  refine iSup_induction K (C := fun k => k ∈ normalizer (L : Set G) ∧ ⁅h, k⁆ ∈ L) hk ?_ ?_ ?_
  · intro i k hk
    exact ⟨hKL i hk, le_iSup (fun j => ⁅H, K j⁆) i (commutator_mem_commutator hh hk)⟩
  · exact ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
  · rintro k₁ k₂ ⟨hk₁, hc₁⟩ ⟨hk₂, hc₂⟩
    refine ⟨mul_mem hk₁ hk₂, ?_⟩
    have e : ⁅h, k₁ * k₂⁆ = ⁅h, k₁⁆ * (k₁ * ⁅h, k₂⁆ * k₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hc₁ ((mem_normalizer_iff.mp hk₁ _).mp hc₂)

theorem commutator_sup_eq_of_le_normalizer {H K₁ K₂ : Subgroup G}
    (h₁ : K₁ ≤ normalizer (H : Set G)) (h₂ : K₂ ≤ normalizer (H : Set G)) :
    ⁅H, K₁ ⊔ K₂⁆ = ⁅H, K₁⁆ ⊔ ⁅H, K₂⁆ := by
  have h := commutator_iSup_eq_of_le_normalizer (H := H) (K := fun b : Bool => cond b K₁ K₂)
    (fun b => by cases b <;> assumption)
  simpa only [iSup_bool_eq, cond_true, cond_false] using h

theorem iSup_commutator_eq_of_commute {ι : Sort*} {H : ι → Subgroup G} {K : Subgroup G}
    (hK : ∀ i, K ≤ normalizer (H i : Set G)) (hH : ∀ i j, H i ≤ centralizer (H j : Set G)) :
    ⁅⨆ i, H i, K⁆ = ⨆ i, ⁅H i, K⁆ := by
  set L : Subgroup G := ⨆ i, ⁅H i, K⁆
  have hLH : L ≤ ⨆ i, H i :=
    iSup_mono fun i => le_normalizer_iff_commutator_le_left.mp (hK i)
  have hHL : ∀ j, H j ≤ normalizer (L : Set G) := by
    intro j y hy
    have hyc : y ∈ centralizer (L : Set G) := by
      have hc : (⨆ i, H i) ≤ centralizer (H j : Set G) := iSup_le fun i => hH i j
      exact centralizer_le hLH (le_centralizer_iff.mp hc hy)
    rw [mem_centralizer_iff] at hyc
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← hyc z hz, mul_inv_cancel_right]
      exact hz
    · intro hz
      have hw := hyc _ hz
      have e : z = y * z * y⁻¹ := by
        calc z = y⁻¹ * ((y * z * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * z * y⁻¹)) := by rw [hw]
          _ = y * z * y⁻¹ := by group
      rw [e]
      exact hz
  refine le_antisymm ?_ (iSup_le fun i => commutator_mono (le_iSup H i) le_rfl)
  rw [commutator_le]
  intro y hy k hk
  suffices hC : y ∈ normalizer (L : Set G) ∧ ⁅y, k⁆ ∈ L from hC.2
  refine iSup_induction H (C := fun y => y ∈ normalizer (L : Set G) ∧ ⁅y, k⁆ ∈ L) hy ?_ ?_ ?_
  · intro i y hy
    exact ⟨hHL i hy, le_iSup (fun j => ⁅H j, K⁆) i (commutator_mem_commutator hy hk)⟩
  · exact ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  · rintro y₁ y₂ ⟨hy₁, hc₁⟩ ⟨hy₂, hc₂⟩
    refine ⟨mul_mem hy₁ hy₂, ?_⟩
    have e : ⁅y₁ * y₂, k⁆ = y₁ * ⁅y₂, k⁆ * y₁⁻¹ * ⁅y₁, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp hy₁ _).mp hc₂) hc₁

theorem mem_normalizer_C_of_commute {g x : G} (hgx : g * x = x * g) :
    g ∈ normalizer ((C x : Subgroup G) : Set G) :=
  le_normalizer (mem_centralizer_singleton_iff.mpr hgx)

theorem mem_normalizer_commutator_zpowers {K : Subgroup G} {g x : G}
    (hgK : g ∈ normalizer (K : Set G)) (hgx : g * x = x * g) :
    g ∈ normalizer ((⁅K, zpowers x⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hgK ⊢
  rw [map_commutator, hgK, MonoidHom.map_zpowers]
  congr 2
  change g * x * g⁻¹ = x
  rw [hgx, mul_inv_cancel_right]

section Abelian

variable {K : Subgroup G} (hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hodd : Odd (Nat.card K))
  {x : G} (hx : orderOf x = 2) (hxK : x ∈ normalizer (K : Set G))

include hx in
theorem eq_one_or_eq_of_mem_zpowers {g : G} (hg : g ∈ zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  have hx2 : x ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hx, pow_orderOf_eq_one]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, hx2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

include hodd in
theorem eq_one_of_conj_eq_self_of_conj_eq_inv {h : G} (hhK : h ∈ K) (h₁ : x * h * x⁻¹ = h)
    (h₂ : x * h * x⁻¹ = h⁻¹) : h = 1 := by
  have hh : h = h⁻¹ := h₁.symm.trans h₂
  have hsq : h ^ 2 = (1 : G) ^ 2 := by
    rw [one_pow, sq]
    nth_rewrite 2 [hh]
    exact mul_inv_cancel h
  exact OddInversion.sq_injOn hodd hhK K.one_mem hsq

include hodd in
theorem mem_commutator_zpowers_of_conj_eq_inv {h : G} (hhK : h ∈ K) (hh : x * h * x⁻¹ = h⁻¹) :
    h ∈ ⁅K, zpowers x⁆ := by
  obtain ⟨d, ⟨hdK, hd⟩, hd2⟩ :=
    OddInversion.exists_sq_eq_of_mem_invertedSet hodd (t := x) ⟨hhK, hh⟩
  have e : ⁅d⁻¹, x⁆ = h⁻¹ := by
    rw [commutatorElement_def, inv_inv, ← hd2]
    calc d⁻¹ * x * d * x⁻¹ = d⁻¹ * (x * d * x⁻¹) := by group
      _ = (d ^ 2)⁻¹ := by rw [hd, sq, mul_inv_rev]
  have : h⁻¹ ∈ ⁅K, zpowers x⁆ :=
    e ▸ commutator_mem_commutator (K.inv_mem hdK) (mem_zpowers x)
  simpa using inv_mem this

include hab hodd hx hxK

theorem mem_commutator_zpowers_iff {h : G} :
    h ∈ ⁅K, zpowers x⁆ ↔ h ∈ K ∧ x * h * x⁻¹ = h⁻¹ := by
  let J : Subgroup G :=
    { carrier := {h | h ∈ K ∧ x * h * x⁻¹ = h⁻¹}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨K.mul_mem ha hb, ?_⟩
        calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
          _ = (a * b)⁻¹ := by rw [mul_inv_rev, hab _ (K.inv_mem hb) _ (K.inv_mem ha)]
      one_mem' := ⟨K.one_mem, by group⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨K.inv_mem ha, by rw [← conj_inv, ha']⟩ }
  constructor
  · intro hh
    have hle : ⁅K, zpowers x⁆ ≤ J := by
      rw [commutator_le]
      intro k hk g hg
      rcases eq_one_or_eq_of_mem_zpowers hx hg with rfl | rfl
      · rw [commutatorElement_one_right]
        exact J.one_mem
      · have hmem := OddInversion.mul_conj_inv_mem_invertedSet hx hxK hk
        have e : ⁅k, g⁆ = k * (g * k * g⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact hmem
    exact hle hh
  · rintro ⟨hhK, hh⟩
    exact mem_commutator_zpowers_of_conj_eq_inv hodd hhK hh

theorem inf_centralizer_sup_commutator_zpowers : K ⊓ C x ⊔ ⁅K, zpowers x⁆ = K := by
  refine le_antisymm (sup_le inf_le_left ?_) ?_
  · intro h hh
    exact ((mem_commutator_zpowers_iff hab hodd hx hxK).mp hh).1
  · intro h hh
    obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
      (OddInversion.odd_involution_product_decomposition hodd hx hxK).1.surjOn hh
    simp only at hcj
    rw [← hcj]
    refine mul_mem (le_sup_left (b := ⁅K, zpowers x⁆) hc) (le_sup_right (a := K ⊓ C x) ?_)
    exact (mem_commutator_zpowers_iff hab hodd hx hxK).mpr hj

theorem inf_centralizer_inf_commutator_zpowers : K ⊓ C x ⊓ ⁅K, zpowers x⁆ = ⊥ := by
  rw [eq_bot_iff]
  rintro h ⟨⟨hhK, hhC⟩, hh⟩
  have hfix : x * h * x⁻¹ = h := by
    rw [← mem_centralizer_singleton_iff.mp hhC, mul_inv_cancel_right]
  exact (mem_bot).mpr (eq_one_of_conj_eq_self_of_conj_eq_inv hodd hhK hfix
    ((mem_commutator_zpowers_iff hab hodd hx hxK).mp hh).2)

end Abelian

section FourGroup

theorem mem_normalizer_fourGroup {H : Subgroup G} {g x y : G}
    (hgH : g ∈ normalizer (H : Set G)) (hgx : g * x = x * g) (hgy : g * y = y * g) :
    g ∈ normalizer ((H ⊓ C x ⊓ C y : Subgroup G) : Set G) ∧
      g ∈ normalizer ((⁅H ⊓ C x, zpowers y⁆ : Subgroup G) : Set G) ∧
      g ∈ normalizer ((⁅H ⊓ C y, zpowers x⁆ : Subgroup G) : Set G) ∧
      g ∈ normalizer ((⁅H, zpowers x⁆ ⊓ ⁅H, zpowers y⁆ : Subgroup G) : Set G) := by
  have hx : g ∈ normalizer ((H ⊓ C x : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hgH, mem_normalizer_C_of_commute hgx⟩
  have hy : g ∈ normalizer ((H ⊓ C y : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hgH, mem_normalizer_C_of_commute hgy⟩
  exact ⟨inf_normalizer_le_normalizer_inf ⟨hx, mem_normalizer_C_of_commute hgy⟩,
    mem_normalizer_commutator_zpowers hx hgy, mem_normalizer_commutator_zpowers hy hgx,
    inf_normalizer_le_normalizer_inf
      ⟨mem_normalizer_commutator_zpowers hgH hgx, mem_normalizer_commutator_zpowers hgH hgy⟩⟩

variable {H : Subgroup G} (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hodd : Odd (Nat.card H))
  {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
  (hxH : x ∈ normalizer (H : Set G)) (hyH : y ∈ normalizer (H : Set G))
include hab hodd hx hy hxy hxH hyH

theorem mem_fourGroup₁_iff {h : G} :
    h ∈ ⁅H ⊓ C x, zpowers y⁆ ↔ h ∈ H ∧ x * h * x⁻¹ = h ∧ y * h * y⁻¹ = h⁻¹ := by
  have hyC : y ∈ normalizer ((H ⊓ C x : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyH, mem_normalizer_C_of_commute hxy.symm⟩
  rw [mem_commutator_zpowers_iff (K := H ⊓ C x) (fun a ha b hb => hab a ha.1 b hb.1)
    (hodd.of_dvd_nat (card_dvd_of_le inf_le_left)) hy hyC, mem_inf,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨hhH, hhx⟩, hhy⟩
    exact ⟨hhH, by rw [← hhx, mul_inv_cancel_right], hhy⟩
  · rintro ⟨hhH, hhx, hhy⟩
    refine ⟨⟨hhH, ?_⟩, hhy⟩
    calc h * x = x * h * x⁻¹ * x := by rw [hhx]
      _ = x * h := by group

theorem mem_fourGroup₂_iff {h : G} :
    h ∈ ⁅H ⊓ C y, zpowers x⁆ ↔ h ∈ H ∧ y * h * y⁻¹ = h ∧ x * h * x⁻¹ = h⁻¹ :=
  mem_fourGroup₁_iff hab hodd hy hx hxy.symm hyH hxH

theorem mem_fourGroup₃_iff {h : G} :
    h ∈ ⁅H, zpowers x⁆ ⊓ ⁅H, zpowers y⁆ ↔ h ∈ H ∧ x * h * x⁻¹ = h⁻¹ ∧ y * h * y⁻¹ = h⁻¹ := by
  rw [mem_inf, mem_commutator_zpowers_iff hab hodd hx hxH,
    mem_commutator_zpowers_iff hab hodd hy hyH]
  exact ⟨fun ⟨⟨hhH, hhx⟩, _, hhy⟩ => ⟨hhH, hhx, hhy⟩,
    fun ⟨hhH, hhx, hhy⟩ => ⟨⟨hhH, hhx⟩, hhH, hhy⟩⟩

theorem fourGroup_sup_eq :
    H ⊓ C x ⊓ C y ⊔ ⁅H ⊓ C x, zpowers y⁆ ⊔ ⁅H ⊓ C y, zpowers x⁆ ⊔
      (⁅H, zpowers x⁆ ⊓ ⁅H, zpowers y⁆) = H := by
  refine le_antisymm (sup_le (sup_le (sup_le (inf_le_left.trans inf_le_left)
    (fun h hh => ((mem_fourGroup₁_iff hab hodd hx hy hxy hxH hyH).mp hh).1))
    (fun h hh => ((mem_fourGroup₂_iff hab hodd hx hy hxy hxH hyH).mp hh).1))
    (fun h hh => ((mem_fourGroup₃_iff hab hodd hx hy hxy hxH hyH).mp hh).1)) ?_
  have hCx : H ⊓ C x ⊔ ⁅H, zpowers x⁆ = H :=
    inf_centralizer_sup_commutator_zpowers hab hodd hx hxH
  have hyC : y ∈ normalizer ((H ⊓ C x : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyH, mem_normalizer_C_of_commute hxy.symm⟩
  have hab₁ : ∀ a ∈ H ⊓ C x, ∀ b ∈ H ⊓ C x, a * b = b * a := fun a ha b hb => hab a ha.1 b hb.1
  have hodd₁ : Odd (Nat.card (H ⊓ C x : Subgroup G)) :=
    hodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hC₁ : H ⊓ C x ⊓ C y ⊔ ⁅H ⊓ C x, zpowers y⁆ = H ⊓ C x :=
    inf_centralizer_sup_commutator_zpowers hab₁ hodd₁ hy hyC
  have hxJ : ∀ {h : G}, h ∈ ⁅H, zpowers x⁆ ↔ h ∈ H ∧ x * h * x⁻¹ = h⁻¹ :=
    mem_commutator_zpowers_iff hab hodd hx hxH
  have hJH : ⁅H, zpowers x⁆ ≤ H := fun h hh => (hxJ.mp hh).1
  have hyJ : y ∈ normalizer ((⁅H, zpowers x⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator_zpowers hyH hxy.symm
  have hab₂ : ∀ a ∈ ⁅H, zpowers x⁆, ∀ b ∈ ⁅H, zpowers x⁆, a * b = b * a :=
    fun a ha b hb => hab a (hJH ha) b (hJH hb)
  have hodd₂ : Odd (Nat.card (⁅H, zpowers x⁆ : Subgroup G)) :=
    hodd.of_dvd_nat (card_dvd_of_le hJH)
  have hC₂ : ⁅H, zpowers x⁆ ⊓ C y ⊔ ⁅⁅H, zpowers x⁆, zpowers y⁆ = ⁅H, zpowers x⁆ :=
    inf_centralizer_sup_commutator_zpowers hab₂ hodd₂ hy hyJ
  have hyJ' : ∀ {h : G}, h ∈ ⁅⁅H, zpowers x⁆, zpowers y⁆ ↔
      h ∈ ⁅H, zpowers x⁆ ∧ y * h * y⁻¹ = h⁻¹ :=
    mem_commutator_zpowers_iff hab₂ hodd₂ hy hyJ
  have hle₂ : ⁅H, zpowers x⁆ ⊓ C y ≤ ⁅H ⊓ C y, zpowers x⁆ := by
    rintro h ⟨hh, hhy⟩
    obtain ⟨hhH, hhx⟩ := hxJ.mp hh
    refine (mem_fourGroup₂_iff hab hodd hx hy hxy hxH hyH).mpr ⟨hhH, ?_, hhx⟩
    rw [← mem_centralizer_singleton_iff.mp hhy, mul_inv_cancel_right]
  have hle₃ : ⁅⁅H, zpowers x⁆, zpowers y⁆ ≤ ⁅H, zpowers x⁆ ⊓ ⁅H, zpowers y⁆ := by
    intro h hh
    obtain ⟨hhJ, hhy⟩ := hyJ'.mp hh
    obtain ⟨hhH, hhx⟩ := hxJ.mp hhJ
    exact (mem_fourGroup₃_iff hab hodd hx hy hxy hxH hyH).mpr ⟨hhH, hhx, hhy⟩
  calc H = H ⊓ C x ⊔ ⁅H, zpowers x⁆ := hCx.symm
    _ = H ⊓ C x ⊓ C y ⊔ ⁅H ⊓ C x, zpowers y⁆ ⊔
          (⁅H, zpowers x⁆ ⊓ C y ⊔ ⁅⁅H, zpowers x⁆, zpowers y⁆) := by rw [hC₁, hC₂]
    _ ≤ H ⊓ C x ⊓ C y ⊔ ⁅H ⊓ C x, zpowers y⁆ ⊔ ⁅H ⊓ C y, zpowers x⁆ ⊔
          (⁅H, zpowers x⁆ ⊓ ⁅H, zpowers y⁆) := by
        rw [sup_assoc _ ⁅H ⊓ C y, zpowers x⁆]
        exact sup_le_sup_left (sup_le_sup hle₂ hle₃) _

end FourGroup

theorem exists_inverted_mem_coset {O : Subgroup G} (hO : Odd (Nat.card O)) {t k : G}
    (ht : t * t = 1) (htO : t ∈ normalizer (O : Set G)) (hkO : k ∈ normalizer (O : Set G))
    (hk : k * (t * k * t⁻¹) ∈ O) : ∃ o ∈ O, t * (k * o) * t⁻¹ = (k * o)⁻¹ := by
  classical
  have : Finite O := OddInversion.finite_of_odd_card hO
  letI : Fintype O := Fintype.ofFinite O
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hOk : ∀ o ∈ O, k⁻¹ * o * k ∈ O := fun o ho => by
    have := (mem_normalizer_iff.mp (inv_mem hkO) o).mp ho
    simpa only [inv_inv] using this
  have hOt : ∀ o ∈ O, t * o * t⁻¹ ∈ O := fun o ho => (mem_normalizer_iff.mp htO o).mp ho
  have hk' : t * k * t⁻¹ * k ∈ O := by
    have := hOk _ hk
    simpa only [mul_assoc, inv_mul_cancel_left] using this
  have hmem : ∀ o ∈ O, k⁻¹ * (t * (k * o)⁻¹ * t⁻¹) ∈ O := by
    intro o ho
    have e : k⁻¹ * (t * (k * o)⁻¹ * t⁻¹) =
        (k⁻¹ * (t * o⁻¹ * t⁻¹) * k) * (t * k * t⁻¹ * k)⁻¹ := by group
    rw [e]
    exact mul_mem (hOk _ (hOt _ (inv_mem ho))) (inv_mem hk')
  let f : O → O := fun o => ⟨k⁻¹ * (t * (k * o)⁻¹ * t⁻¹), hmem o o.2⟩
  have hf : Function.Involutive f := by
    intro o
    apply Subtype.ext
    change k⁻¹ * (t * (k * (k⁻¹ * (t * (k * (o : G))⁻¹ * t⁻¹)))⁻¹ * t⁻¹) = o
    have e : k⁻¹ * (t * (k * (k⁻¹ * (t * (k * (o : G))⁻¹ * t⁻¹)))⁻¹ * t⁻¹) =
        k⁻¹ * ((t * t) * (k * o) * (t⁻¹ * t⁻¹)) := by group
    rw [e, ht, htinv, ht]
    group
  have hcard : ¬ 2 ∣ Fintype.card O := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hO)
  obtain ⟨o, ho⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) (σ := hf.toPerm f)
    (hp := ⟨Nat.prime_two⟩) hcard (by
      ext a
      simp [sq, Equiv.Perm.mul_apply, hf a])
  refine ⟨o, o.2, ?_⟩
  have hfo : k⁻¹ * (t * (k * (o : G))⁻¹ * t⁻¹) = o := congrArg Subtype.val ho
  have hko : t * (k * (o : G))⁻¹ * t⁻¹ = k * o := inv_mul_eq_iff_eq_mul.mp hfo
  calc t * (k * (o : G)) * t⁻¹ = t * (t * (k * (o : G))⁻¹ * t⁻¹) * t⁻¹ := by rw [hko]
    _ = (t * t) * (k * (o : G))⁻¹ * (t⁻¹ * t⁻¹) := by group
    _ = (k * (o : G))⁻¹ := by rw [ht, htinv, ht, one_mul, mul_one]

theorem IsMaxInvIn.of_le {p : ℕ} {A H K P : Subgroup G} (hP : IsMaxInvIn p A H P) (hPK : P ≤ K)
    (hKH : K ≤ H) : IsMaxInvIn p A K P :=
  ⟨hPK, hP.2.1, hP.2.2.1, fun Q hQK hQ hAQ hPQ => hP.2.2.2 Q (hQK.trans hKH) hQ hAQ hPQ⟩

theorem isSylowOf_inf_O_of_isMaxInvIn [Finite G] {p : ℕ} (hp : p.Prime) {A H P : Subgroup G}
    (hA : IsPGroup 2 A) (hAH : A ≤ normalizer (H : Set G)) (hP : IsMaxInvIn p A H P) :
    ABGLocalTools.IsSylowOf p (P ⊓ O H) (O H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPH, hPp, hAP, hmax⟩ := hP
  have hOodd : Odd (Nat.card (O H)) := by
    rw [card_map_of_injective H.subtype_injective]
    exact ComponentClassification.OddCore.odd_card H
  have hHO : normalizer (H : Set G) ≤ normalizer (O H : Set G) :=
    ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image H
  have hOH : O H ≤ H := map_subtype_le _
  by_cases hp2 : p = 2
  · subst hp2
    rw [ABGLocalTools.isSylowOf_iff]
    refine ⟨inf_le_right, hPp.to_inf_left, ?_⟩
    have hbot : P ⊓ O H = ⊥ := by
      rcases (hPp.to_inf_left (K := O H)).card_eq_or_dvd with h1 | h2
      · exact card_eq_one.mp h1
      · exact absurd (h2.trans (card_dvd_of_le inf_le_right))
          (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hOodd))
    rw [hbot, relIndex_bot_left]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hOodd)
  ·
    set R : Subgroup G := O H ⊔ P with hR
    have hRH : R ≤ H := sup_le hOH hPH
    have hRodd : Odd (Nat.card R) := by
      have hPodd : Odd (Nat.card P) := by
        obtain ⟨n, hn⟩ := hPp.exists_card_eq
        rw [hn]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      have hsup : Odd (Nat.card ((CFSG.oddCore H) ⊔ P.subgroupOf H : Subgroup H)) := by
        refine ComponentClassification.OddCore.odd_card_sup _ _
          (ComponentClassification.OddCore.odd_card H) ?_
        rw [Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv]
        exact hPodd
      have hmap : ((CFSG.oddCore H) ⊔ P.subgroupOf H : Subgroup H).map H.subtype = R := by
        rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hPH]
      rw [← hmap, card_map_of_injective H.subtype_injective]
      exact hsup
    have hnorm_sup : ∀ g ∈ normalizer (O H : Set G), g ∈ normalizer (P : Set G) →
        g ∈ normalizer (R : Set G) := by
      intro g hgO hgP
      rw [mem_normalizer_iff_map_conj_eq] at hgO hgP ⊢
      rw [hR, Subgroup.map_sup, hgO, hgP]
    have hAR : A ≤ normalizer (R : Set G) := fun a ha => hnorm_sup a (hHO (hAH ha)) (hAP ha)
    have hcop : Nat.Coprime 2 (Nat.card R) := (Nat.coprime_two_left).mpr hRodd
    let _action := SignalizerFunctor.Helpers.conjugationAction A R hAR
    obtain ⟨Q, hPQ, hQ⟩ := SignalizerFunctor.Helpers.invariant_sylow_containing 2 p
      Nat.prime_two hp hA hcop (P.subgroupOf R) hPp.comap_subtype
      (SignalizerFunctor.Helpers.normalized_subgroup_invariant_subgroup A R P hAR hAP)
    set Q' : Subgroup G := (Q : Subgroup R).map R.subtype with hQ'
    have hPQ' : P ≤ Q' := by
      rw [hQ', ← map_subgroupOf_eq_of_le (le_sup_right : P ≤ R)]
      exact map_mono hPQ
    have hAQ' : A ≤ normalizer (Q' : Set G) := by
      apply SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A R hAR
      change ∀ a : A, ∀ x ∈ (Q : Subgroup R), a • x ∈ (Q : Subgroup R)
      intro a x hx
      have hmem := smul_mem_pointwise_smul x a (Q : Subgroup R) hx
      rwa [← Sylow.pointwise_smul_def, hQ a] at hmem
    have hQ'R : Q' ≤ R := map_subtype_le _
    have hQ'p : IsPGroup p Q' := Q.isPGroup'.map R.subtype
    have hQ'eq : Q' = P := hmax Q' (hQ'R.trans hRH) hQ'p hAQ' hPQ'
    have hsyl : ABGLocalTools.IsSylowOf p P R := hQ'eq ▸ ⟨Q, rfl⟩
    exact hsyl.inf_of_le_normalizer le_sup_left
      (sup_le le_normalizer (hPH.trans (le_normalizer.trans hHO)))

end CFSG.GH72
