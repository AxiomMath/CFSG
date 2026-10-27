module

public import CFSG.LargeExtraspecial.A2ModFrBLevi
public import CFSG.LargeExtraspecial.A2ModCfg

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped commutatorElement

variable (n : ℕ) {K : Type} [Field K] (b c : K)

noncomputable abbrev lr {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    spinGroup (quadMinus n K b c) :=
  (minusFrame n b c).longRoot hij s t (.ofAdd 1)

section CharTwo

variable {n b c}

omit [Field K] in
theorem neg_one_eq_one_of_two_eq_zero [Field K] (h2 : (2 : K) = 0) : (-1 : K) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]

theorem lr_swap (h2 : (2 : K) = 0) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    lr n b c hij s t = lr n b c hij.symm t s := by
  rw [lr, HypFrame.longRoot_swap, neg_one_eq_one_of_two_eq_zero h2]

theorem lr_mul_self (h2 : (2 : K) = 0) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    lr n b c hij s t * lr n b c hij s t = 1 := by
  rw [lr, ← map_mul, ← ofAdd_add, one_add_one_eq_two, h2, ofAdd_zero, map_one]

theorem lr_inv (h2 : (2 : K) = 0) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    (lr n b c hij s t)⁻¹ = lr n b c hij s t :=
  inv_eq_of_mul_eq_one_right (lr_mul_self h2 hij s t)

theorem commutator_lr {i j k : Fin (n - 1)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (s t u : Bool) : ⁅lr n b c hij s t, lr n b c hjk (!t) u⁆ = lr n b c hik s u := by
  rw [lr, lr, HypFrame.commutator_longRoot_longRoot, mul_one]

theorem mul_mul_inv_eq_commutatorElement_mul {G : Type*} [Group G] (x y : G) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def, inv_mul_cancel_right]

theorem lr_conj_shortWeyl (h2 : (2 : K) = 0) (l : Fin (n - 1)) {k m : Fin (n - 1)}
    (hkm : k ≠ m) (u v : Bool) :
    (minusFrame n b c).shortWeyl l true * lr n b c hkm u v *
        ((minusFrame n b c).shortWeyl l true)⁻¹ =
      lr n b c hkm (shortWeylBool l k u) (shortWeylBool l m v) := by
  have hs : ∀ p : Fin (n - 1), (longWeylSign l p : K) = 1 := fun p => by
    by_cases hp : p = l
    · rw [hp, longWeylSign_self, neg_one_eq_one_of_two_eq_zero h2]
    · exact longWeylSign_of_ne hp
  rw [lr, OddFrame.shortWeyl_conj_longRoot, hs, hs, one_mul, one_mul]

end CharTwo

theorem leviZ_elemTv_eq_lr [Finite K] {b c : K} (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) {i j : Fin (n - 1)}
    (hij : i ≠ j) : leviZ n b c hn hirr hK (elemTv i j) = lr n b c hij true false :=
  leviZ_elemTv n hn hirr hK hij

section Members

variable {n b c} {X : Type} [Group X] {D : Set X}

variable (Ψ : spinGroup (quadMinus n K b c) →* X) (hcls : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D)
include hcls

theorem map_conj_mem {x : spinGroup (quadMinus n K b c)} (hx : Ψ x ∈ D)
    (g : spinGroup (quadMinus n K b c)) : Ψ (g * x * g⁻¹) ∈ D := by
  rw [map_mul, map_mul, map_inv]
  exact hcls _ hx _

theorem map_mem_of_isConj {x y : spinGroup (quadMinus n K b c)} (hx : Ψ x ∈ D)
    (hxy : IsConj x y) : Ψ y ∈ D := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  exact map_conj_mem Ψ hcls hx g

variable [Finite K] (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
include hn hirr hK

theorem map_lr_mem {i₀ j₀ : Fin (n - 1)} (h₀ : i₀ ≠ j₀) (hmem : Ψ (lr n b c h₀ true false) ∈ D)
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) : Ψ (lr n b c hij s t) ∈ D := by
  have h2 := two_eq_zero_of_card hK
  have hTF : ∀ {i j : Fin (n - 1)} (hij : i ≠ j), Ψ (lr n b c hij true false) ∈ D := by
    intro i j hij
    have hc : IsConj (elemTv i₀ j₀) (elemTv i j) :=
      isConj_tv (Pi.single_ne_zero_iff.mpr one_ne_zero) (Pi.single_ne_zero_iff.mpr one_ne_zero)
        (single_dotProduct_single_of_ne h₀) (Pi.single_ne_zero_iff.mpr one_ne_zero)
        (Pi.single_ne_zero_iff.mpr one_ne_zero) (single_dotProduct_single_of_ne hij)
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    have hc' : IsConj (lr n b c h₀ true false) (lr n b c hij true false) := by
      refine isConj_iff.mpr ⟨leviZ n b c hn hirr hK g, ?_⟩
      rw [← leviZ_elemTv_eq_lr n hn hirr hK h₀, ← leviZ_elemTv_eq_lr n hn hirr hK hij,
        ← map_inv, ← map_mul, ← map_mul, hg]
    exact map_mem_of_isConj Ψ hcls hmem hc'
  cases s <;> cases t
  · have h := map_conj_mem Ψ hcls (hTF hij) ((minusFrame n b c).shortWeyl i true)
    have e1 : shortWeylBool i i true = false := by simp [shortWeylBool]
    have e2 : shortWeylBool i j false = false := by simp [shortWeylBool, hij.symm]
    rwa [lr_conj_shortWeyl h2, e1, e2] at h
  · rw [lr_swap h2]
    exact hTF hij.symm
  · exact hTF hij
  · have h := map_conj_mem Ψ hcls (hTF hij) ((minusFrame n b c).shortWeyl j true)
    have e1 : shortWeylBool j i true = true := by simp [shortWeylBool, hij]
    have e2 : shortWeylBool j j false = true := by simp [shortWeylBool]
    rwa [lr_conj_shortWeyl h2, e1, e2] at h

end Members

section Node

variable {n} (hn : 4 ≤ n)

abbrev iB : Fin (n - 1) := ⟨n - 2, by omega⟩

abbrev iA : Fin (n - 1) := ⟨n - 3, by omega⟩

abbrev iC : Fin (n - 1) := ⟨n - 4, by omega⟩

theorem iA_ne_iB : iA hn ≠ iB hn := by simp only [ne_eq, Fin.mk.injEq]; omega
theorem iC_ne_iA : iC hn ≠ iA hn := by simp only [ne_eq, Fin.mk.injEq]; omega
theorem iC_ne_iB : iC hn ≠ iB hn := by simp only [ne_eq, Fin.mk.injEq]; omega

noncomputable abbrev nodeA : spinGroup (quadMinus n K b c) :=
  lr n b c (iA_ne_iB hn) true true

noncomputable abbrev nodeB : spinGroup (quadMinus n K b c) :=
  lr n b c (iA_ne_iB hn) false false

variable {b c} [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)

theorem nodeA_commute {i j : Fin (n - 1)} (hji : j.val + 1 = i.val) :
    Commute (nodeA b c hn) (leviZ n b c hn hirr hK (elemTv i j)) := by
  have h2 := two_eq_zero_of_card hK
  have hij : i ≠ j := fin_ne_of_val_ne (by omega)
  rw [leviZ_elemTv_eq_lr n hn hirr hK hij]
  by_cases hiB : i = iB hn
  · subst hiB
    obtain rfl : j = iA hn := Fin.ext (by simp only at hji ⊢; omega)
    rw [nodeA, lr_swap h2]
    exact HypFrame.commute_longRoot_longRoot_left _ _ _ _ _ _ _ _
  by_cases hiA : i = iA hn
  · subst hiA
    exact HypFrame.commute_longRoot_longRoot_left _ _ _ _ _ _ _ _
  have hjA : j ≠ iA hn := fun h => hiB (Fin.ext (by subst h; simp only at hji ⊢; omega))
  have hjB : j ≠ iB hn := fun h => by
    have := i.isLt
    subst h
    simp only at hji
    omega
  exact HypFrame.commute_longRoot_longRoot_of_disjoint _ _ _ (Ne.symm hiA) (Ne.symm hjA)
    (Ne.symm hiB) (Ne.symm hjB) _ _ _ _ _ _

theorem nodeB_commute {i j : Fin (n - 1)} (hij' : i.val + 1 = j.val) :
    Commute (nodeB b c hn) (leviZ n b c hn hirr hK (elemTv i j)) := by
  have h2 := two_eq_zero_of_card hK
  have hij : i ≠ j := fin_ne_of_val_ne (by omega)
  rw [leviZ_elemTv_eq_lr n hn hirr hK hij]
  by_cases hjB : j = iB hn
  · subst hjB
    obtain rfl : i = iA hn := Fin.ext (by simp only at hij' ⊢; omega)
    exact HypFrame.commute_longRoot_longRoot_right _ _ _ _ _ _ _ _
  by_cases hjA : j = iA hn
  · subst hjA
    rw [nodeB, lr_swap h2]
    exact HypFrame.commute_longRoot_longRoot_right _ _ _ _ _ _ _ _
  have hiA : i ≠ iA hn := fun h => hjB (Fin.ext (by subst h; simp only at hij' ⊢; omega))
  have hiB : i ≠ iB hn := fun h => by
    have := j.isLt
    subst h
    simp only at hij'
    omega
  exact HypFrame.commute_longRoot_longRoot_of_disjoint _ _ _ (Ne.symm hiA) (Ne.symm hjA)
    (Ne.symm hiB) (Ne.symm hjB) _ _ _ _ _ _

omit [Finite K] in
theorem nodeA_mul_eq (h2 : (2 : K) = 0) :
    nodeA b c hn * lr n b c (iC_ne_iA hn).symm true false =
      lr n b c (iC_ne_iB hn).symm true true * lr n b c (iC_ne_iA hn).symm true false *
        (lr n b c (iC_ne_iB hn).symm true true)⁻¹ := by
  have hcomm := commutator_lr (b := b) (c := c) (iC_ne_iB hn).symm (iC_ne_iA hn)
    (iA_ne_iB hn).symm true true true
  rw [Bool.not_true, lr_swap h2 (iC_ne_iA hn) false true,
    lr_swap h2 (iA_ne_iB hn).symm true true] at hcomm
  rw [mul_mul_inv_eq_commutatorElement_mul, hcomm]

omit [Finite K] in
theorem nodeB_mul_eq (h2 : (2 : K) = 0) :
    nodeB b c hn * lr n b c (iC_ne_iA hn) true false =
      lr n b c (iC_ne_iB hn).symm false false * lr n b c (iC_ne_iA hn) true false *
        (lr n b c (iC_ne_iB hn).symm false false)⁻¹ := by
  have hcomm := commutator_lr (b := b) (c := c) (iC_ne_iB hn).symm (iC_ne_iA hn)
    (iA_ne_iB hn).symm false false false
  rw [Bool.not_false, lr_swap h2 (iA_ne_iB hn).symm false false] at hcomm
  rw [mul_mul_inv_eq_commutatorElement_mul, hcomm]

variable {X : Type} [Group X] {D : Set X} (Ψ : spinGroup (quadMinus n K b c) →* X)
  (hcls : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D)
  (hD : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool), Ψ (lr n b c hij s t) ∈ D)
include hcls hD

theorem isLeviNode :
    IsLeviNode D (Ψ.comp (leviZ n b c hn hirr hK)) (Ψ (nodeA b c hn)) (Ψ (nodeB b c hn)) where
  map_mem g hg := by
    obtain ⟨v, φ, hv, hφ, h, rfl⟩ := mem_transvectionSet.mp hg
    have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp
    have hc : IsConj (elemTv (⟨0, by omega⟩ : Fin (n - 1)) ⟨1, by omega⟩) (tv v φ) :=
      isConj_tv (Pi.single_ne_zero_iff.mpr one_ne_zero) (Pi.single_ne_zero_iff.mpr one_ne_zero)
        (single_dotProduct_single_of_ne h01) hv hφ h
    have hc' := MonoidHom.map_isConj (leviZ n b c hn hirr hK) hc
    rw [leviZ_elemTv_eq_lr n hn hirr hK h01] at hc'
    exact map_mem_of_isConj Ψ hcls (hD h01 true false) hc'
  mem_left := hD _ _ _
  mem_right := hD _ _ _
  commute_left i j hji := (nodeA_commute hn hirr hK hji).map Ψ
  commute_right i j hij := (nodeB_commute hn hirr hK hij).map Ψ
  mul_mem_left i j hi hj := by
    obtain rfl : i = iA hn := Fin.ext (by simp only; omega)
    obtain rfl : j = iC hn := Fin.ext (by simp only; omega)
    rw [MonoidHom.comp_apply, leviZ_elemTv_eq_lr n hn hirr hK (iC_ne_iA hn).symm, ← map_mul,
      nodeA_mul_eq hn (two_eq_zero_of_card hK)]
    exact map_conj_mem Ψ hcls (hD _ _ _) _
  mul_mem_right i j hi hj := by
    obtain rfl : i = iC hn := Fin.ext (by simp only; omega)
    obtain rfl : j = iA hn := Fin.ext (by simp only; omega)
    rw [MonoidHom.comp_apply, leviZ_elemTv_eq_lr n hn hirr hK (iC_ne_iA hn), ← map_mul,
      nodeB_mul_eq hn (two_eq_zero_of_card hK)]
    exact map_conj_mem Ψ hcls (hD _ _ _) _

end Node

end CFSG.LargeExtraspecial.A2Mod.FrB
