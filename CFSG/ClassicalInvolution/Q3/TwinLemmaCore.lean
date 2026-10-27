module

public import CFSG.ClassicalInvolution.Q3.TwinLemmaSL2
public import CFSG.ClassicalInvolution.Q3.TwinLemmaBasic
import CFSG.ClassicalInvolution.Q3.Subnormal
import CFSG.ClassicalInvolution.Q3.TwinLemmaFrattini

public section

namespace CFSG.ClassicalInvolution.Q3.Twin

open CFSG
open scoped MatrixGroups commutatorElement

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem isSubnormal_quatIn {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3)) (hJ : J.IsSubnormal) :
    (quatIn e).IsSubnormal := by
  have hn : ((quatIn e).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (quatIn_le e)]
    intro h k hh hk
    exact conj_mem_quatIn e hk hh
  have := hn.isSubnormal.trans' hJ
  rwa [Subgroup.map_subgroupOf_eq_of_le (quatIn_le e)] at this

theorem commutator_eq_quatIn {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3)) (hJ : J.IsSubnormal)
    {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U) (hQU : quatIn e ≤ U) {s : Y} (hs : s ∈ J)
    (h3 : s ^ 3 = 1) (h1 : s ≠ 1) : ⁅U, Subgroup.zpowers s⁆ = quatIn e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf s = 3 := orderOf_eq_prime h3 h1
  have hpg : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hJtop : CFSG.Open.IsSubnormal J ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal hJ
  have hle : ⁅U, Subgroup.zpowers s⁆ ≤ J :=
    commutator_le_of_isSubnormal Nat.prime_three hJtop le_top
      (inferInstance : (U.subgroupOf ⊤).Normal) (not_three_dvd_card_of_isPGroup_two hU)
      (Subgroup.zpowers_le.mpr hs) hpg
  have hleU : ⁅U, Subgroup.zpowers s⁆ ≤ U := Subgroup.commutator_le_left _ _
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨n, hn⟩ := hU ⟨y, hleU hy⟩
    exact mem_quatIn_of_pow_two_pow e (hle hy) (n := n) (by simpa using congrArg Subtype.val hn)
  · calc quatIn e = ⁅quatIn e, Subgroup.zpowers s⁆ := (commutator_quatIn e hs h3 h1).symm
      _ ≤ ⁅U, Subgroup.zpowers s⁆ := Subgroup.commutator_mono hQU le_rfl

omit [Finite Y] in
theorem commutator_mem_of_eq {U Q : Subgroup Y} {s : Y} (hc : ⁅U, Subgroup.zpowers s⁆ = Q) :
    ∀ u ∈ U, s * u * s⁻¹ * u⁻¹ ∈ Q := by
  intro u hu
  rw [← hc, Subgroup.commutator_comm]
  have := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) hu
  rwa [commutatorElement_def] at this

omit [Finite Y] in
theorem conj_mem_quatIn_of_commute {J₁ J₂ : Subgroup Y} (hY : J₁ ⊔ J₂ = ⊤)
    (e₁ : ↥J₁ ≃* SL(2, ZMod 3)) (e₂ : ↥J₂ ≃* SL(2, ZMod 3)) {U : Subgroup Y} [U.Normal]
    (hQ₁U : quatIn e₁ ≤ U) (hQ₂U : quatIn e₂ ≤ U) {s₁ s₂ : Y} (hs₁J : s₁ ∈ J₁)
    (hs₁3 : s₁ ^ 3 = 1) (hs₁1 : s₁ ≠ 1) (hs₂J : s₂ ∈ J₂) (hs₂3 : s₂ ^ 3 = 1) (hs₂1 : s₂ ≠ 1)
    (hc₁ : ⁅U, Subgroup.zpowers s₁⁆ = quatIn e₁) (hcomm : s₂ * s₁ = s₁ * s₂) :
    ∀ y : Y, ∀ q ∈ quatIn e₁, y * q * y⁻¹ ∈ quatIn e₁ := by
  have hU : U ≤ Subgroup.normalizer ((quatIn e₁ : Subgroup Y) : Set Y) := by
    rw [← hc₁]; exact Subgroup.normalizer_commutator_ge_left U _
  have hs₁ : Subgroup.zpowers s₁ ≤ Subgroup.normalizer ((quatIn e₁ : Subgroup Y) : Set Y) := by
    rw [← hc₁]; exact Subgroup.normalizer_commutator_ge_right U _
  have hs₂ : s₂ ∈ Subgroup.normalizer ((quatIn e₁ : Subgroup Y) : Set Y) := by
    rw [← hc₁]; exact mem_normalizer_commutator s₂ hcomm
  have hJ₁ : J₁ ≤ Subgroup.normalizer ((quatIn e₁ : Subgroup Y) : Set Y) :=
    (quatIn_sup_zpowers e₁ hs₁J hs₁3 hs₁1).symm.le.trans (sup_le (hQ₁U.trans hU) hs₁)
  have hJ₂ : J₂ ≤ Subgroup.normalizer ((quatIn e₁ : Subgroup Y) : Set Y) :=
    (quatIn_sup_zpowers e₂ hs₂J hs₂3 hs₂1).symm.le.trans
      (sup_le (hQ₂U.trans hU) (Subgroup.zpowers_le.mpr hs₂))
  have hYN : ⊤ ≤ Subgroup.normalizer ((quatIn e₁ : Subgroup Y) : Set Y) := hY ▸ sup_le hJ₁ hJ₂
  intro y q hq
  exact (Subgroup.mem_normalizer_iff.mp (hYN (Subgroup.mem_top y)) q).mp hq

omit [Finite Y] in
theorem commute_of_inf_central {U Q₁ Q₂ : Subgroup Y} {s : Y} (hc : ⁅U, Subgroup.zpowers s⁆ = Q₁)
    (hQ₂U : Q₂ ≤ U) (hQ₂n : ∀ y : Y, ∀ q ∈ Q₂, y * q * y⁻¹ ∈ Q₂) (hs3 : s ^ 3 = 1)
    (hcen : ∀ w ∈ Q₁ ⊓ Q₂, (∀ t : Y, w * t = t * w) ∧ w ^ 2 = 1) :
    ∀ x ∈ Q₂, s * x = x * s := by
  intro x hx
  have hw₂ : x * s * x⁻¹ * s⁻¹ ∈ Q₂ := by
    have h := mul_mem hx (hQ₂n s x⁻¹ (inv_mem hx))
    simpa [mul_assoc] using h
  have hw₁ : x * s * x⁻¹ * s⁻¹ ∈ Q₁ := by
    rw [← hc]
    have := Subgroup.commutator_mem_commutator (hQ₂U hx) (Subgroup.mem_zpowers s)
    rwa [commutatorElement_def] at this
  have hw := hcen _ ⟨hw₁, hw₂⟩
  have h1 : x * s * x⁻¹ * s⁻¹ = 1 :=
    eq_one_of_commutator_central rfl hw.1 hw.2 hs3
  have : x * s = s * x := by
    calc x * s = (x * s * x⁻¹ * s⁻¹) * (s * x) := by group
      _ = s * x := by rw [h1, one_mul]
  exact this.symm

omit [Finite Y] in
theorem commute_of_centralizes {Q₁ Q₂ : Subgroup Y} {s : Y}
    (hQ₂c : ⁅Q₂, Subgroup.zpowers s⁆ = Q₂) (hs : ∀ x ∈ Q₁, x * s = s * x)
    (hQ₁n : ∀ y : Y, ∀ q ∈ Q₁, y * q * y⁻¹ ∈ Q₁)
    (hQ₂n : ∀ y : Y, ∀ q ∈ Q₂, y * q * y⁻¹ ∈ Q₂)
    (hcen : ∀ w ∈ Q₁ ⊓ Q₂, ∀ t : Y, w * t = t * w) : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := by
  intro x hx
  have hxs : s ∈ Subgroup.centralizer ({x} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hs x hx).symm
  have hle : Q₂ ≤ Subgroup.centralizer ({x} : Set Y) := by
    rw [← hQ₂c, Subgroup.commutator_le]
    intro y hy g hg
    have hg' : g ∈ Subgroup.centralizer ({x} : Set Y) := Subgroup.zpowers_le.mpr hxs hg
    have hxg : x * g = g * x := (Subgroup.mem_centralizer_singleton_iff.mp hg').symm
    have hw₂ : x * y * x⁻¹ * y⁻¹ ∈ Q₂ := mul_mem (hQ₂n x y hy) (inv_mem hy)
    have hw₁ : x * y * x⁻¹ * y⁻¹ ∈ Q₁ := by
      have h := mul_mem hx (hQ₁n y x⁻¹ (inv_mem hx))
      simpa [mul_assoc] using h
    have key := commute_commutator_of_central rfl (hcen _ ⟨hw₁, hw₂⟩) hxg
    rw [commutatorElement_def]
    exact Subgroup.mem_centralizer_singleton_iff.mpr key.symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem twinLemma3_core {J₁ J₂ : Subgroup Y} {z : Y} (hY : J₁ ⊔ J₂ = ⊤)
    (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) (h₁ : J₁.IsSubnormal)
    (h₂ : J₂.IsSubnormal) (e₁ : ↥J₁ ≃* SL(2, ZMod 3)) (e₂ : ↥J₂ ≃* SL(2, ZMod 3))
    (hz : orderOf z = 2) (hz₁ : z ∈ J₁) (hz₂ : z ∈ J₂) : J₁ = J₂ ∨ ⁅J₁, J₂⁆ = ⊥ := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hzc : ∀ y : Y, z * y = y * z := by
    have hJ₁ : J₁ ≤ Subgroup.centralizer {z} := fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.mpr (involution_central_in e₁ hz₁ hz2 hz1 j hj).symm
    have hJ₂ : J₂ ≤ Subgroup.centralizer {z} := fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.mpr (involution_central_in e₂ hz₂ hz2 hz1 j hj).symm
    intro y
    have : y ∈ Subgroup.centralizer ({z} : Set Y) := by
      have h := sup_le hJ₁ hJ₂
      rw [hY] at h
      exact h (Subgroup.mem_top y)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hsolv : Group.IsSolvable Y :=
    isSolvable_of_sup_eq_top hY h₁ h₂ (isSolvable_subgroup e₁) (isSolvable_subgroup e₂)
  have hUn : (pCore 2 Y).Normal := pCore_normal
  have hU2 : IsPGroup 2 (pCore 2 Y) := pCore_isPGroup
  have hCU : Subgroup.centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y := centralizer_pCore_le hsolv hO
  set U : Subgroup Y := pCore 2 Y with hUdef
  have hQ₁U : quatIn e₁ ≤ U :=
    le_pCore_of_isSubnormal (isSubnormal_quatIn e₁ h₁) (isPGroup_quatIn e₁)
  have hQ₂U : quatIn e₂ ≤ U :=
    le_pCore_of_isSubnormal (isSubnormal_quatIn e₂ h₂) (isPGroup_quatIn e₂)
  obtain ⟨S⟩ : Nonempty (Sylow 3 Y) := inferInstance
  have hP3 : IsPGroup 3 (S : Subgroup Y) := S.isPGroup'
  obtain ⟨s₁, hs₁S, hs₁J, hs₁3, hs₁1⟩ :=
    exists_mem_inf_sylow_three h₁ (natCard_subgroup e₁) S
  obtain ⟨s₂, hs₂S, hs₂J, hs₂3, hs₂1⟩ :=
    exists_mem_inf_sylow_three h₂ (natCard_subgroup e₂) S
  have hc₁ : ⁅U, Subgroup.zpowers s₁⁆ = quatIn e₁ :=
    commutator_eq_quatIn e₁ h₁ hU2 hQ₁U hs₁J hs₁3 hs₁1
  have hc₂ : ⁅U, Subgroup.zpowers s₂⁆ = quatIn e₂ :=
    commutator_eq_quatIn e₂ h₂ hU2 hQ₂U hs₂J hs₂3 hs₂1
  obtain ⟨x₁, y₁, hx₁, hy₁, hg₁⟩ := exists_closure_quatIn e₁
  obtain ⟨x₂, y₂, hx₂, hy₂, hg₂⟩ := exists_closure_quatIn e₂
  have hcomm : s₁ * s₂ = s₂ * s₁ := by
    refine mul_comm_of_displaced_into_closure hU2 hCU hP3 hs₁S hs₂S ({x₁, y₁, x₂, y₂} : Finset Y)
      ?_ Finset.card_le_four ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [hQ₁U hx₁, hQ₁U hy₁, hQ₂U hx₂, hQ₂U hy₂]
    · intro u hu
      have h := commutator_mem_of_eq hc₁ u hu
      rw [← hg₁] at h
      refine Subgroup.closure_mono ?_ h
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    · intro u hu
      have h := commutator_mem_of_eq hc₂ u hu
      rw [← hg₂] at h
      refine Subgroup.closure_mono ?_ h
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
  have hQ₁n := conj_mem_quatIn_of_commute hY e₁ e₂ hQ₁U hQ₂U hs₁J hs₁3 hs₁1 hs₂J hs₂3 hs₂1 hc₁
    hcomm.symm
  have hQ₂n := conj_mem_quatIn_of_commute (sup_comm J₁ J₂ ▸ hY) e₂ e₁ hQ₂U hQ₁U hs₂J hs₂3 hs₂1
    hs₁J hs₁3 hs₁1 hc₂ hcomm
  have hdich : quatIn e₁ = quatIn e₂ ∨ ∀ x ∈ quatIn e₁ ⊓ quatIn e₂, x ^ 2 = 1 := by
    by_cases h : ∀ x ∈ quatIn e₁ ⊓ quatIn e₂, x ^ 2 = 1
    · exact Or.inr h
    · left
      obtain ⟨x, hx, hx2⟩ : ∃ x ∈ quatIn e₁ ⊓ quatIn e₂, x ^ 2 ≠ 1 := by
        by_contra hcon
        exact h fun x hx => by_contra fun hx2 => hcon ⟨x, hx, hx2⟩
      refine le_antisymm ?_ ?_
      · refine (quatIn_le_closure e₁ hs₁J hs₁3 hs₁1 hx.1 hx2).trans
          ((Subgroup.closure_le _).mpr ?_)
        intro w hw
        rcases hw with rfl | hw
        · exact hx.2
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          exact hQ₂n s₁ x hx.2
      · refine (quatIn_le_closure e₂ hs₂J hs₂3 hs₂1 hx.2 hx2).trans
          ((Subgroup.closure_le _).mpr ?_)
        intro w hw
        rcases hw with rfl | hw
        · exact hx.1
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          exact hQ₁n s₂ x hx.1
  rcases hdich with hQ | h2
  ·
    left
    have hmem : s₂ ∈ Subgroup.zpowers s₁ := by
      refine mem_zpowers_of_displaced_into_closure hU2 hCU hP3 hs₁S hs₂S ({x₁, y₁} : Finset Y)
        ?_ Finset.card_le_two ?_ ?_ hs₁1
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        exacts [hQ₁U hx₁, hQ₁U hy₁]
      · intro u hu
        have h := commutator_mem_of_eq hc₁ u hu
        rw [← hg₁] at h
        simpa using h
      · intro u hu
        have h := commutator_mem_of_eq hc₂ u hu
        rw [← hQ, ← hg₁] at h
        simpa using h
    have hle : J₂ ≤ J₁ :=
      calc J₂ = quatIn e₂ ⊔ Subgroup.zpowers s₂ := (quatIn_sup_zpowers e₂ hs₂J hs₂3 hs₂1).symm
        _ ≤ quatIn e₁ ⊔ Subgroup.zpowers s₁ :=
            sup_le_sup (le_of_eq hQ.symm) (Subgroup.zpowers_le.mpr hmem)
        _ = J₁ := quatIn_sup_zpowers e₁ hs₁J hs₁3 hs₁1
    have : Finite J₁ := Finite.of_equiv SL(2, ZMod 3) e₁.symm.toEquiv
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [natCard_subgroup e₁, natCard_subgroup e₂])).symm
  ·
    right
    have hcen : ∀ w ∈ quatIn e₁ ⊓ quatIn e₂, (∀ t : Y, w * t = t * w) ∧ w ^ 2 = 1 := by
      intro w hw
      refine ⟨?_, h2 w hw⟩
      by_cases hw1 : w = 1
      · intro t; rw [hw1, one_mul, mul_one]
      · have : w = z :=
          involution_unique_in e₁ (quatIn_le e₁ hw.1) hz₁ (h2 w hw) hz2 hw1 hz1
        rw [this]; exact hzc
    have hs₁Q₂ : ∀ x ∈ quatIn e₂, s₁ * x = x * s₁ :=
      commute_of_inf_central hc₁ hQ₂U hQ₂n hs₁3 hcen
    have hs₂Q₁ : ∀ x ∈ quatIn e₁, s₂ * x = x * s₂ :=
      commute_of_inf_central hc₂ hQ₁U hQ₁n hs₂3 (fun w hw => hcen w ⟨hw.2, hw.1⟩)
    have hQQ : ∀ x ∈ quatIn e₁, ∀ y ∈ quatIn e₂, x * y = y * x :=
      commute_of_centralizes (commutator_quatIn e₂ hs₂J hs₂3 hs₂1)
        (fun x hx => (hs₂Q₁ x hx).symm) hQ₁n hQ₂n (fun w hw => (hcen w hw).1)
    have hJ₂C : ∀ a : Y, (∀ q ∈ quatIn e₂, a * q = q * a) → a * s₂ = s₂ * a →
        J₂ ≤ Subgroup.centralizer ({a} : Set Y) := by
      intro a haq has
      refine (quatIn_sup_zpowers e₂ hs₂J hs₂3 hs₂1).symm.le.trans (sup_le ?_ ?_)
      · intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.mpr (haq q hq).symm
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr has.symm)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine (quatIn_sup_zpowers e₁ hs₁J hs₁3 hs₁1).symm.le.trans (sup_le ?_ ?_)
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := hJ₂C q (fun y hy => hQQ q hq y hy) (hs₂Q₁ q hq).symm hb
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro b hb
      have := hJ₂C s₁ (fun y hy => hs₁Q₂ y hy) hcomm hb
      exact Subgroup.mem_centralizer_singleton_iff.mp this

end CFSG.ClassicalInvolution.Q3.Twin
