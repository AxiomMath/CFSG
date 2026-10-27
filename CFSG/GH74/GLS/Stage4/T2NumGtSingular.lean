module

public import CFSG.GH74.GLS.Stage4.T2NumGtTwoPart
public import CFSG.GH74.GLS.Stage4.T2NumGtT5
public import CFSG.GH74.GLS.Stage4.T2NumGtIvkExp
public import CFSG.GH74.GLS.Stage4.T2NumGtP56
public import CFSG.GH74.GLS.Stage4.T2NumGtDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem t5_transport_exp {G : Type} [Group G] [Finite G] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z y : G} {K₂ J : Subgroup G}
    (hJy : J ≤ centralizer ({y} : Set G)) (hKJ : K₂ ≤ J)
    (hJ : IsSLnEps 3 ↥J 1 (p ^ n) ∨ IsLnEps 3 ↥J 1 (p ^ n))
    (hz2 : orderOf z = 2) (hzK : z ∈ K₂) (hzc : ∀ x ∈ K₂, z * x = x * z)
    {X : Subgroup G} (hXK : X ≤ K₂) (hXp : IsPGroup p ↥X) (hXc : Nat.card ↥X = p ^ n) :
    ∃ R : Subgroup G, IsPGroup p ↥R ∧ X ≤ R ∧ R ≤ centralizer (X : Set G) ∧
      Nat.card ↥R = (p ^ n) ^ 3 ∧ (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧
      (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧ (∀ r ∈ R, z * r * z⁻¹ * r ∈ X) ∧
      (∀ r ∈ R, y * r = r * y) ∧ (∀ r ∈ R, r ^ p ∈ X) := by
  have hIVK := ivk_4_1_R_L3_exp
  have hXJ : X ≤ J := hXK.trans hKJ
  have hzJ : z ∈ J := hKJ hzK
  let z' : ↥J := ⟨z, hzJ⟩
  have hz'2 : orderOf z' = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk z hzJ
  have hX'c : X.subgroupOf J ≤ centralizer ({z'} : Set ↥J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    exact hzc x (hXK (Subgroup.mem_subgroupOf.1 hx))
  have hX'p : IsPGroup p ↥(X.subgroupOf J) := hXp.comap_subtype (K := J)
  have hX'card : Nat.card ↥(X.subgroupOf J) = p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, hXc]
  obtain ⟨R', -, hR'p, hXR', hR'c, hR'card, hZ, hcom1, hcom2, hinv, hexp⟩ :=
    hIVK ↥J p n hp hp2 hJ z' hz'2 (X.subgroupOf J) hX'c hX'p hX'card
  have hmapX : (X.subgroupOf J).map J.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXJ
  have hinj : Function.Injective J.subtype := J.subtype_injective
  refine ⟨R'.map J.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 3 * n) ?_
    rw [Subgroup.card_map_of_injective hinj, hR'card, ← pow_mul, mul_comm]
  · rw [← hmapX]
    exact Subgroup.map_mono hXR'
  · rintro _ ⟨r', hr', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hmapX] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have := (Subgroup.mem_centralizer_iff.1 (hR'c hr')) x' hx'
    exact congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective hinj, hR'card]
  · rintro _ ⟨r', hr', rfl⟩ hcomm
    have : r' ∈ X.subgroupOf J := by
      refine hZ r' hr' (fun s' hs' => ?_)
      exact Subtype.ext (hcomm _ ⟨s', hs', rfl⟩)
    exact Subgroup.mem_subgroupOf.1 this
  · rw [← hmapX, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcom1
  · rintro _ ⟨r', hr', rfl⟩ _ ⟨s', hs', rfl⟩
    have := hcom2 r' hr' s' hs'
    exact Subgroup.mem_subgroupOf.1 this
  · rintro _ ⟨r', hr', rfl⟩
    have := hinv r' hr'
    exact Subgroup.mem_subgroupOf.1 this
  · rintro _ ⟨r', hr', rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hJy r'.2)).symm
  · rintro _ ⟨r', hr', rfl⟩
    have := hexp r' hr'
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this

theorem ch6Gt_singular (hP56 : Ch6T2Prop56GtGen) : Ch6GtTS := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn hlt z K₁ K₂ F₁ F₂ _ _ t hSet hRem p n hp hp2 hq₂p hmod N u hz
    hK₁ hK₂ hq₁ hq₂ hSec
  have hloc := hSec.loc
  have hlt' : N.q₂ < N.q₁ := by rw [hq₁, hq₂]; exact hlt
  have h2part : ∀ k : ℕ, 2 ^ k ∣ N.q₁ - 1 ↔ 2 ^ k ∣ N.q₂ - 1 := by
    rw [hq₁, hq₂]; exact t5_two_part hSet hmod
  obtain ⟨y, hyH, hyz, hyp, hyodd, hyq, hya⟩ := t5_singular_gt N u hSec hlt' h2part
  obtain ⟨J, hJy, hKJ, hJ⟩ := hP56 G hStd hr Gs q₁ q₂ hAt h99 hn hlt z K₁ K₂ F₁ F₂ t hSet hRem p n hp hp2
    hq₂p hmod N u hz hK₁ hK₂ hq₁ hq₂ hSec y hyH hyz hyp hyodd hya
  have hz2 : orderOf z = 2 := hSet.central.1
  have hzc : ∀ x ∈ K₂, z * x = x * z := by
    intro x hx
    have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_right hx)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hX₂K₂ : N.X₂ ≤ N.K₂ := by rw [hloc.K₂_eq]; exact le_sup_left
  have hX₂p : IsPGroup p ↥N.X₂ :=
    IsPGroup.of_card (n := n) (by rw [hloc.card_X₂, hq₂, hq₂p])
  have hX₂c : Nat.card ↥N.X₂ = p ^ n := by rw [hloc.card_X₂, hq₂, hq₂p]
  have hJ' : IsSLnEps 3 ↥J 1 (p ^ n) ∨ IsLnEps 3 ↥J 1 (p ^ n) := by rw [← hq₂p]; exact hJ
  have hKJ' : N.K₂ ≤ J := by rw [hK₂]; exact hKJ
  have hz2' : orderOf N.z = 2 := by rw [hz]; exact hz2
  have hzK' : N.z ∈ N.K₂ := hloc.z_mem_K₂
  have hzc' : ∀ x ∈ N.K₂, N.z * x = x * N.z := by rw [hz, hK₂]; exact hzc
  obtain ⟨R, hRp, hXR, hRc, hRcard, hRZ, hRcom1, hRcom2, hRinv, hRy, hRexp⟩ :=
    t5_transport_exp hp hp2 hJy hKJ' hJ' hz2' hzK' hzc' hX₂K₂ hX₂p hX₂c
  refine ⟨y, R, ?_⟩
  exact
    { yK := hyH.2
      y_ne := hyz
      y_prime := hyp
      y_odd := hyodd
      y_dvd := hyq
      R_p := hRp
      X_le := hXR
      R_cent := hRc
      R_card := by rw [hRcard, hq₂, hq₂p]
      R_center := hRZ
      X_comm := hRcom1
      R_comm := hRcom2
      R_inv := hRinv
      R_exp := hRexp
      y_cent := hRy }

end CFSG.GH74.GLS.Stage4.Rest
