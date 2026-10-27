module

public import CFSG.CGT.T75O.Cfg
public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.CGT.Timmesfeld75.Sec57Conj

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem commutator_mul_mul {a a' r r' : G} (h1 : Commute a r) (h2 : Commute a a')
    (h3 : Commute a r') (h4 : Commute a' r) (h5 : Commute a' r') :
    ⁅a * r, a' * r'⁆ = ⁅r, r'⁆ := by
  have c1 : Commute a (r * a' * r' * r⁻¹) :=
    (((h1.mul_right h2).mul_right h3).mul_right h1.inv_right)
  have c2 : Commute a' (r * r' * r⁻¹ * r'⁻¹) :=
    ((((h4.mul_right h5).mul_right h4.inv_right).mul_right h5.inv_right))
  have e1 : ⁅a * r, a' * r'⁆ = (a * (r * a' * r' * r⁻¹) * a⁻¹) * (r'⁻¹ * a'⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1, c1.eq, mul_inv_cancel_right, show r * a' = a' * r from h4.symm.eq]
  have e2 : a' * r * r' * r⁻¹ * (r'⁻¹ * a'⁻¹) = a' * (r * r' * r⁻¹ * r'⁻¹) * a'⁻¹ := by group
  rw [e2, c2.eq, mul_inv_cancel_right]
  simp only [commutatorElement_def]

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem mul_comm_T {x y : G} (hx : x ∈ T) (hy : y ∈ T) : x * y = y * x :=
  elemAbelian_mul_comm c.hy.pair.wc.1 hx hy

theorem mul_self_T {x : G} (hx : x ∈ T) : x * x = 1 :=
  elemAbelian_mul_self c.hy.pair.wc.1 hx

theorem conj_comm_cases {a e x : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) (hex : x * a * x⁻¹ = e)
    (hcomm : e * a = a * e) :
    e ∈ secA T T₁ ∨ (IsUIdx T T₁ x ∧ e ∈ conjSubgroup x (secA T T₁)) := by
  have := c.hy.finite
  have hN : e ∈ Subgroup.normalizer (T : Set G) :=
    c.hy.pair.wc.centralizer_le_normalizer (secA_le_left ha) ha1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have heA' : e ∈ conjSubgroup x (secA T T₁) := by
    rw [← hex]
    exact conj_mem_conjSubgroup x ha
  by_cases hxT : conjSubgroup x T = T
  · left
    have hxN : x ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hxT
    rwa [conjSubgroup_secA hxN] at heA'
  · right
    have he1 : e ≠ 1 := by
      rintro rfl
      apply ha1
      have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [this, hex]
      group
    have heT' : e ∈ conjSubgroup x T := by
      rw [← hex]
      exact conj_mem_conjSubgroup x (secA_le_left ha)
    have hL : normIn (conjSubgroup x T) T ≠ ⊥ := by
      intro hbot
      have hmem : e ∈ normIn (conjSubgroup x T) T := mem_normIn.2 ⟨heT', hN⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact he1 hmem
    have hle := conjSubgroup_secA_le_normIn c.hy.pair c.hS hxT hL
    exact ⟨c.hplus x (fun y hy => (mem_normIn.1 (hle hy)).2) hxT, heA'⟩

theorem comm_of_mem_normalizer_conj {e : G} (he : e ∈ classD T) (k : G)
    (hek : e ∈ Subgroup.normalizer ((conjSubgroup k T : Subgroup G) : Set G)) :
    ∀ y ∈ conjSubgroup k (secA T T₁), e * y = y * e := by
  have := c.hy.finite
  have h53 := secA_le_centralizer_normD (c.hy.pair.conjSubgroup_pair k) (c.hS.conj k)
  rw [secA_conjSubgroup_eq] at h53
  intro y hy
  exact Subgroup.mem_centralizer_iff.1 (h53 hy) e ⟨mem_classD_conjSubgroup he k, hek⟩

theorem comm_all_of_comm_one {e y : G} (he : e ∈ classD T) (k : G)
    (hy : y ∈ conjSubgroup k (secA T T₁)) (hy1 : y ≠ 1) (hey : e * y = y * e) :
    ∀ z ∈ conjSubgroup k (secA T T₁), e * z = z * e := by
  have hyT : y ∈ conjSubgroup k T := conjSubgroup_mono secA_le_left hy
  have hwc : IsWC (conjSubgroup k T) := c.hy.pair.wc.conj k
  exact c.comm_of_mem_normalizer_conj he k
    (hwc.centralizer_le_normalizer hyT hy1 (Subgroup.mem_centralizer_singleton_iff.2 hey))

theorem secR₁_le_centralizer : secR₁ T T₁ ≤ Subgroup.centralizer (secA T T₁ : Set G) := by
  have := c.hy.finite
  refine iSup₂_le fun h hh y hy => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact secA_comm_conjSubgroup_secA c.hy.pair c.hS hh.1 (hh.normIn_conj_ne_bot c.hy.pair) a ha y hy

theorem secA_comm_secR₁ {a x : G} (ha : a ∈ secA T T₁) (hx : x ∈ secR₁ T T₁) : a * x = x * a :=
  Subgroup.mem_centralizer_iff.1 (c.secR₁_le_centralizer hx) a ha

theorem secA_comm_sup {a m : G} (ha : a ∈ secA T T₁) (hm : m ∈ secA T T₁ ⊔ secR₁ T T₁) :
    a * m = m * a := by
  have hle : secA T T₁ ⊔ secR₁ T T₁ ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.mul_comm_T (secA_le_left hx) (secA_le_left ha)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (c.secA_comm_secR₁ ha hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm

theorem secA_le_normalizer_secR₁ : secA T T₁ ≤ Subgroup.normalizer (secR₁ T T₁ : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ z ∈ secR₁ T T₁, a * z * a⁻¹ = z := fun z hz => by
    rw [c.secA_comm_secR₁ ha hz, mul_inv_cancel_right]
  have hcomm' : ∀ z ∈ secR₁ T T₁, a⁻¹ * z * a⁻¹⁻¹ = z := fun z hz => by
    have := c.secA_comm_secR₁ ((secA T T₁).inv_mem ha) hz
    rw [this, mul_inv_cancel_right]
  constructor
  · intro hy
    rw [hcomm y hy]
    exact hy
  · intro hy
    have h2 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = a * y * a⁻¹ := hcomm' _ hy
    have h3 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
    rw [h3] at h2
    rw [h2]
    exact hy

theorem isPGroup_sup : IsPGroup 2 ↥(secA T T₁ ⊔ secR₁ T T₁) := by
  have hA : IsPGroup 2 ↥(secA T T₁) :=
    (isPGroup_two_of_isElemAbelian c.hy.pair.wc.1).to_le secA_le_left
  exact IsPGroup.to_sup_of_normal_right' hA c.h2 c.secA_le_normalizer_secR₁

theorem commutator_sup_mem {x y : G} (hx : x ∈ secA T T₁ ⊔ secR₁ T T₁)
    (hy : y ∈ secA T T₁ ⊔ secR₁ T T₁) : ⁅x, y⁆ ∈ secA T T₁ := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (secA T T₁) (secR₁ T T₁)
    c.secA_le_normalizer_secR₁
  have hx' : x ∈ (secA T T₁ : Set G) * (secR₁ T T₁ : Set G) := by
    rw [← hmul]
    exact hx
  have hy' : y ∈ (secA T T₁ : Set G) * (secR₁ T T₁ : Set G) := by
    rw [← hmul]
    exact hy
  obtain ⟨a, ha, r, hr, rfl⟩ := hx'
  obtain ⟨a', ha', r', hr', rfl⟩ := hy'
  have e := commutator_mul_mul (a := a) (a' := a') (r := r) (r' := r')
    (c.secA_comm_secR₁ ha hr) (c.mul_comm_T (secA_le_left ha) (secA_le_left ha'))
    (c.secA_comm_secR₁ ha hr') (c.secA_comm_secR₁ ha' hr) (c.secA_comm_secR₁ ha' hr')
  rw [e]
  exact c.hR' r hr r' hr'

theorem class_two_of_le_sup {W : Subgroup G} (hW : W ≤ secA T T₁ ⊔ secR₁ T T₁) :
    ⁅⁅W, W⁆, W⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro z hz y hy
  have hzA : z ∈ secA T T₁ :=
    (Subgroup.commutator_le.2 fun x hx y hy => c.commutator_sup_mem (hW hx) (hW hy)) hz
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact c.secA_comm_sup hzA (hW hy)

theorem conjCent_subset {t : G} (ht : t ∈ secA T T₁) (ht1 : t ≠ 1) :
    CorB.conjCent t ⊆ (secA T T₁ ⊔ secR₁ T T₁ : Subgroup G) := by
  rintro τ ⟨hcomm, hconj⟩
  obtain ⟨x, hx⟩ := isConj_iff.1 hconj
  rcases c.conj_comm_cases ht ht1 hx hcomm with h | ⟨hu, hτ⟩
  · exact Subgroup.mem_sup_left h
  · refine Subgroup.mem_sup_right ?_
    exact (le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁))
      x hu) hτ

end Cfg56

end CFSG.CGT.T75O
