module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo
public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.Blueprint.Catalog
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ComponentClassification.Sol76T13.R12

open CFSG Subgroup CFSG.LocalCores
open scoped commutatorElement

@[expose] def QuasisimpleRankTwoCentralInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → CFSG.pRank 2 Q = 2 → ∀ z ∈ center Q, orderOf z = 2 →
      (∀ w ∈ center Q, w ^ 4 = 1 → w = 1 ∨ w = z) ∧
      ∃ s t : Q, t * t = 1 ∧ t ∉ center Q ∧ s * s = z ∧ s * t = t * s

variable {W : Type} [Group W] [Finite W]

theorem commute_of_mem_pCore {K : Subgroup W} (hK : IsComponent K) {x k : W}
    (hx : x ∈ pCore 2 W) (hk : k ∈ K) : k * x = x * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxF : x ∈ ComponentClassification.Fitting.subgroup W := pCore_le_fitting W 2 hx
  have hkL : k ∈ ComponentClassification.Layer.subgroup W := by
    rw [← layer_eq_componentClassification]
    exact component_le_layer hK hk
  have h := ComponentClassification.GeneralizedFitting.fitting_layer_commute W
  have h1 : ⁅x, k⁆ = 1 := by
    have := commutator_mem_commutator hxF hkL
    rwa [h, mem_bot] at this
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

section Local

variable {K₁ K₂ : Subgroup W} {z s t : W}

theorem mem_zpowers_of_twoElement (hK₁ : IsComponent K₁) (hK₂ : IsComponent K₂)
    (hne : K₁ ≠ K₂) (hzZ : z ∈ center W) (hzK : z ∈ K₂) (hz2 : orderOf z = 2)
    (hsK : s ∈ K₂) (htK : t ∈ K₂) (ht2 : t * t = 1) (htn : ∃ k ∈ K₂, t * k ≠ k * t)
    (hs2 : s * s = z) (hst : s * t = t * s)
    (hP1 : ∀ w ∈ K₂, (∀ k ∈ K₂, w * k = k * w) → w ^ 4 = 1 → w = 1 ∨ w = z)
    (hY : CFSG.Open.pRank 2 ((pCore 2 W ⊔ layer W) ⊓ centralizer (K₁ : Set W)) ≤ 2)
    {x : W} (hxM : x ∈ pCore 2 W ⊔ layer W) (hx1 : x ∈ centralizer (K₁ : Set W))
    (hx2 : x ∈ centralizer (K₂ : Set W)) {k : ℕ} (hxo : orderOf x = 2 ^ k) :
    x ∈ zpowers z := by
  set M := (pCore 2 W ⊔ layer W) ⊓ centralizer (K₁ : Set W) with hMdef
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    norm_num at hz2
  have hzc : ∀ g : W, z * g = g * z := fun g => (mem_center_iff.mp hzZ g).symm
  have hK₂M : ∀ y ∈ K₂, y ∈ M := fun y hy =>
    mem_inf.mpr ⟨mem_sup_right (component_le_layer hK₂ hy),
      mem_centralizer_iff.mpr fun a ha => (Sol76.commute_of_ne hK₁ hK₂ hne ha hy).eq⟩
  have hzM : z ∈ M := hK₂M z hzK
  have htM : t ∈ M := hK₂M t htK
  have hsM : s ∈ M := hK₂M s hsK
  have ht1 : t ≠ 1 := by
    rintro rfl
    obtain ⟨k, -, hk⟩ := htn
    exact hk (by group)
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hzt : z ≠ t := by
    rintro rfl
    obtain ⟨k, -, hk⟩ := htn
    exact hk (hzc k)
  have hnC : ∀ y ∈ centralizer (K₂ : Set W), y ≠ t ∧ y ≠ z * t := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rintro rfl
      obtain ⟨k, hk, hk'⟩ := htn
      exact hk' (mem_centralizer_iff.mp hy k hk).symm
    · rintro rfl
      obtain ⟨k, hk, hk'⟩ := htn
      apply hk'
      have h1 := mem_centralizer_iff.mp hy k hk
      have e1 : z * (t * k) = z * t * k := by group
      have e2 : z * (k * t) = k * (z * t) := by rw [← mul_assoc, hzc k, mul_assoc]
      have h2 : z * (t * k) = z * (k * t) := by rw [e1, e2]; exact h1.symm
      exact mul_left_cancel h2
  have hcen : ∀ y ∈ centralizer (K₂ : Set W), ∀ k ∈ K₂, y * k = k * y := fun y hy k hk =>
    (mem_centralizer_iff.mp hy k hk).symm
  have hinv : ∀ u ∈ M, u ∈ centralizer (K₂ : Set W) → orderOf u = 2 → u = z := by
    intro u huM huC hu2
    by_contra huz
    obtain ⟨hut, huzt⟩ := hnC u huC
    have h3 := CFSG.ProperTwoGeneratedCore.Assembly.three_le_pRank_of_commuting_involutions
      hzM htM huM hz2 hto hu2 (hzc t) (hzc u) (mem_centralizer_iff.mp huC t htK) hzt huz hut
        huzt
    omega
  have hfour : ∀ w ∈ M, w ∈ centralizer (K₂ : Set W) → w * w = z → False := by
    intro w hwM hwC hww
    have hsw : s * w = w * s := mem_centralizer_iff.mp hwC s hsK
    have hwK : ∀ y ∈ K₂, s * w ≠ y := by
      intro y hy hy'
      have hwy : w = s⁻¹ * y := by rw [← hy']; group
      have hwK2 : w ∈ K₂ := hwy ▸ mul_mem (inv_mem hsK) hy
      have h4 : w ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hww, hzz]
      rcases hP1 w hwK2 (hcen w hwC) h4 with h | h
      · rw [h, mul_one] at hww
        exact hz1 hww.symm
      · rw [h, hzz] at hww
        exact hz1 hww.symm
    have hv2 : s * w * (s * w) = 1 := by
      calc s * w * (s * w) = s * (w * s) * w := by group
        _ = s * (s * w) * w := by rw [hsw]
        _ = s * s * (w * w) := by group
        _ = 1 := by rw [hs2, hww, hzz]
    have hv1 : s * w ≠ 1 := hwK 1 (one_mem _)
    have hvo : orderOf (s * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
    have hvM : s * w ∈ M := mul_mem hsM hwM
    have htv : Commute t (s * w) := by
      change t * (s * w) = s * w * t
      calc t * (s * w) = t * s * w := by group
        _ = s * t * w := by rw [hst]
        _ = s * (t * w) := by group
        _ = s * (w * t) := by rw [mem_centralizer_iff.mp hwC t htK]
        _ = s * w * t := by group
    have h3 := CFSG.ProperTwoGeneratedCore.Assembly.three_le_pRank_of_commuting_involutions
      hzM htM hvM hz2 hto hvo (hzc t) (hzc (s * w)) htv hzt
      (fun h => hwK z hzK h) (fun h => hwK t htK h) (fun h => hwK (z * t) (mul_mem hzK htK) h)
    omega
  have hxMM : x ∈ M := mem_inf.mpr ⟨hxM, hx1⟩
  rcases k with _ | _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hxo
    rw [hxo]
    exact one_mem _
  · rw [hinv x hxMM hx2 (by rw [hxo, zero_add, pow_one])]
    exact mem_zpowers z
  · exfalso
    set y := x ^ (2 ^ k) with hydef
    have hyo : orderOf y = 4 := by
      have h1 : 2 ^ k ∣ orderOf x := by
        rw [hxo]
        exact pow_dvd_pow 2 (by omega)
      rw [hydef, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) h1, hxo,
        show k + 1 + 1 = k + 2 from rfl, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
      norm_num
    have hyM : y ∈ M := pow_mem hxMM _
    have hyC : y ∈ centralizer (K₂ : Set W) := pow_mem hx2 _
    have hyy : y * y = z := by
      have hyyM : y * y ∈ M := mul_mem hyM hyM
      have hyyC : y * y ∈ centralizer (K₂ : Set W) := mul_mem hyC hyC
      refine hinv _ hyyM hyyC ?_
      have h2 : 2 ∣ orderOf y := by
        rw [hyo]
        norm_num
      rw [← pow_two, orderOf_pow_of_dvd two_ne_zero h2, hyo]
    exact hfour y hyM hyC hyy

theorem card_le_two_of_centralizer (hO : pPrimeCore 2 W = ⊥) (hK₁ : IsComponent K₁)
    (hK₂ : IsComponent K₂) (hne : K₁ ≠ K₂) (hzZ : z ∈ center W) (hzK : z ∈ K₂)
    (hz2 : orderOf z = 2) (hsK : s ∈ K₂) (htK : t ∈ K₂) (ht2 : t * t = 1)
    (htn : ∃ k ∈ K₂, t * k ≠ k * t) (hs2 : s * s = z) (hst : s * t = t * s)
    (hP1 : ∀ w ∈ K₂, (∀ k ∈ K₂, w * k = k * w) → w ^ 4 = 1 → w = 1 ∨ w = z)
    (hY : CFSG.Open.pRank 2 ((pCore 2 W ⊔ layer W) ⊓ centralizer (K₁ : Set W)) ≤ 2)
    {T : Subgroup W} (hT₁ : T ≤ centralizer (K₁ : Set W))
    (hT₂ : T ≤ centralizer (K₂ : Set W)) : Nat.card T ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey : ∀ {x : W}, x ∈ pCore 2 W ⊔ layer W → x ∈ centralizer (K₁ : Set W) →
      x ∈ centralizer (K₂ : Set W) → ∀ {k : ℕ}, orderOf x = 2 ^ k → x ∈ zpowers z :=
    fun {_} hxM hx1 hx2 {_} hxo =>
      mem_zpowers_of_twoElement hK₁ hK₂ hne hzZ hzK hz2 hsK htK ht2 htn hs2 hst hP1 hY hxM hx1
        hx2 hxo
  have hz2' : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hzc : ∀ g : W, z * g = g * z := fun g => (mem_center_iff.mp hzZ g).symm
  have hord : ∀ {P : Subgroup W}, IsPGroup 2 P → ∀ x ∈ P, ∃ k : ℕ, orderOf x = 2 ^ k := by
    intro P hP x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨m, hm⟩
  have hO2 : pCore 2 W ≤ zpowers z := by
    intro x hx
    obtain ⟨k, hk⟩ := hord pCore_isPGroup x hx
    exact hkey (mem_sup_left hx)
      (mem_centralizer_iff.mpr fun a ha => commute_of_mem_pCore hK₁ hx ha)
      (mem_centralizer_iff.mpr fun a ha => commute_of_mem_pCore hK₂ hx ha) hk
  have hcomp : ∀ Y : Subgroup W, IsComponent Y → Y = K₁ ∨ Y = K₂ := by
    intro Y hY'
    by_contra hYne
    push Not at hYne
    obtain ⟨hY1, hY2⟩ := hYne
    have hYz : ∀ y ∈ Y, (∃ k : ℕ, orderOf y = 2 ^ k) → y ∈ zpowers z := by
      rintro y hy ⟨k, hk⟩
      exact hkey (mem_sup_right (component_le_layer hY' hy))
        (mem_centralizer_iff.mpr fun a ha => (Sol76.commute_of_ne hK₁ hY' (Ne.symm hY1) ha hy).eq)
        (mem_centralizer_iff.mpr fun a ha => (Sol76.commute_of_ne hK₂ hY' (Ne.symm hY2) ha hy).eq)
        hk
    obtain ⟨hperf, hsimp, hnab⟩ := hY'.1
    have : IsSimpleGroup (↥Y ⧸ center ↥Y) := hsimp
    obtain ⟨heven, -⟩ := CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab
    have h2Y : 2 ∣ Nat.card ↥Y := by
      obtain ⟨m, hm⟩ := Subgroup.card_quotient_dvd_card (center ↥Y)
      rw [hm]
      exact Dvd.dvd.mul_right (even_iff_two_dvd.mp heven) m
    have := Fintype.ofFinite ↥Y
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
    have hSle : (S : Subgroup ↥Y).map Y.subtype ≤ zpowers z := by
      rintro _ ⟨y, hy, rfl⟩
      exact hYz _ y.2 (hord (S.isPGroup'.map Y.subtype) _ ⟨y, hy, rfl⟩)
    have hScard : Nat.card ↥(S : Subgroup ↥Y) = 2 := by
      apply le_antisymm
      · have h1 := card_le_of_le hSle
        rwa [card_map_of_injective Y.subtype_injective, hz2'] at h1
      · have h1 := S.card_eq_multiplicity
        have h2 : 1 ≤ (Nat.card ↥Y).factorization 2 :=
          (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2Y
        rw [h1]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h2
    have hcyc : IsCyclic ↥(S : Subgroup ↥Y) := isCyclic_of_prime_card hScard
    have heven' : Even (Fintype.card ↥Y) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mpr h2Y
    obtain ⟨-, -, -, hidx⟩ := LinearGroups.cyclic_sylow_index_two heven' S hcyc
    have hker := Abelianization.commutator_subset_ker
      (Equiv.Perm.sign.comp (MulAction.toPermHom ↥Y ↥Y))
    have : Group.IsPerfect ↥Y := hperf
    rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hker
    rw [hker, index_top] at hidx
    norm_num at hidx
  have hlayer : layer W ≤ K₁ ⊔ K₂ := by
    refine sSup_le fun Y hY => ?_
    rcases hcomp Y hY with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hTF : T ≤ centralizer (generalizedFitting W : Set W) := by
    rw [le_centralizer_iff]
    have hFit : fittingSubgroup W = pCore 2 W := Fitting_eq_pcore W 2 hO
    rw [generalizedFitting, hFit]
    refine sup_le ?_ (hlayer.trans (sup_le ?_ ?_))
    · intro x hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp (hO2 hx)
      refine mem_centralizer_iff.mpr fun g _ => ?_
      exact ((Commute.zpow_left (show Commute z g from hzc g) n)).symm.eq
    · exact le_centralizer_iff.mp hT₁
    · exact le_centralizer_iff.mp hT₂
  have hC : centralizer (generalizedFitting W : Set W) ≤ fittingSubgroup W :=
    CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup W
  have hTfit : T ≤ pCore 2 W := by
    have h1 := hTF.trans hC
    rwa [Fitting_eq_pcore W 2 hO] at h1
  have h1 := card_le_of_le (hTfit.trans hO2)
  rwa [hz2'] at h1

end Local

end CFSG.ComponentClassification.Sol76T13.R12
