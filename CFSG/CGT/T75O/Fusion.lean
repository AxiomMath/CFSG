module

public import CFSG.CGT.T75O.Comm

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

omit [Group G] in
theorem conj_ne_one' {G : Type} [Group G] {a x e : G} (hex : x * a * x⁻¹ = e) (ha1 : a ≠ 1) :
    e ≠ 1 := by
  rintro rfl
  apply ha1
  have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
  rw [this, hex]
  group

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

omit c in
theorem secA_conj_le_secR₁ {h : G} (hh : IsUIdx T T₁ h) :
    conjSubgroup h (secA T T₁) ≤ secR₁ T T₁ :=
  le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) h hh

theorem isConj_of_mem_secA {a b : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) (hb : b ∈ secA T T₁)
    (hb1 : b ≠ 1) : IsConj a b := by
  obtain ⟨g, hg⟩ := c.exists_isUIdx
  obtain ⟨K, -, hK⟩ := c.torus_transitive hg
  obtain ⟨k, -, hk⟩ := hK a ha ha1 b hb hb1
  exact isConj_iff.2 ⟨k, hk⟩

theorem exists_nonneighbour {x : G} (hx : IsUIdx T T₁ x) {τ : G}
    (hτ : τ ∈ conjSubgroup x (secA T T₁)) (hτ1 : τ ≠ 1) :
    ∃ h : G, IsUIdx T T₁ h ∧ ∀ y ∈ conjSubgroup h (secA T T₁), y * τ = τ * y → y = 1 := by
  obtain ⟨b, hb, r, hr, hbr⟩ :
      ∃ b ∈ conjSubgroup x (secA T T₁), ∃ r ∈ secR₁ T T₁, b * r ≠ r * b := by
    by_contra hcon
    apply c.hnc x hx
    intro a ha r hr
    by_contra hne
    exact hcon ⟨a, ha, r, hr, hne⟩
  obtain ⟨h, hh, y, hy, hby⟩ :
      ∃ h : G, IsUIdx T T₁ h ∧ ∃ y ∈ conjSubgroup h (secA T T₁), b * y ≠ y * b := by
    by_contra hcon
    apply hbr
    have hle : secR₁ T T₁ ≤ Subgroup.centralizer ({b} : Set G) := by
      refine iSup₂_le fun h hh y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_contra hne
      exact hcon ⟨h, hh, y, hy, fun e => hne e.symm⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hr)).symm
  refine ⟨h, hh, fun y' hy' hcomm => ?_⟩
  by_contra hy'1
  have hτD : τ ∈ classD T :=
    mem_classD_of_mem_conjSubgroup (conjSubgroup_mono secA_le_left hτ) hτ1
  have h1 := c.comm_all_of_comm_one hτD h hy' hy'1 hcomm.symm y hy
  have hy1 : y ≠ 1 := fun e => hby (by rw [e]; simp)
  have hyD : y ∈ classD T :=
    mem_classD_of_mem_conjSubgroup (conjSubgroup_mono secA_le_left hy) hy1
  have h2 := c.comm_all_of_comm_one hyD x hτ hτ1 h1.symm b hb
  exact hby h2.symm

theorem fusion_pairing {x h : G} (hx : IsUIdx T T₁ x) (hh : IsUIdx T T₁ h) {τ : G}
    (hτ : τ ∈ conjSubgroup x (secA T T₁))
    (hnb : ∀ y ∈ conjSubgroup h (secA T T₁), y * τ = τ * y → y = 1) :
    ∀ a ∈ secA T T₁, ∃ y ∈ conjSubgroup h (secA T T₁), y * τ * y⁻¹ = a * τ := by
  have := c.hy.finite
  let φ : ↥(conjSubgroup h (secA T T₁)) → ↥(secA T T₁) := fun y =>
    ⟨(y : G) * τ * (y : G)⁻¹ * τ⁻¹, by
      have := c.hR' (y : G) (secA_conj_le_secR₁ hh y.2) τ (secA_conj_le_secR₁ hx hτ)
      simpa [commutatorElement_def] using this⟩
  have hinj : Function.Injective φ := by
    intro y y' hyy
    have h1 : (y : G) * τ * (y : G)⁻¹ * τ⁻¹ = (y' : G) * τ * (y' : G)⁻¹ * τ⁻¹ :=
      congrArg Subtype.val hyy
    have h2 : (y : G) * τ * (y : G)⁻¹ = (y' : G) * τ * (y' : G)⁻¹ := mul_right_cancel h1
    have h3 : ((y' : G)⁻¹ * (y : G)) * τ = τ * ((y' : G)⁻¹ * (y : G)) := by
      calc ((y' : G)⁻¹ * (y : G)) * τ = (y' : G)⁻¹ * ((y : G) * τ * (y : G)⁻¹) * (y : G) := by
            group
        _ = (y' : G)⁻¹ * ((y' : G) * τ * (y' : G)⁻¹) * (y : G) := by rw [h2]
        _ = τ * ((y' : G)⁻¹ * (y : G)) := by group
    have h4 : (y' : G)⁻¹ * (y : G) ∈ conjSubgroup h (secA T T₁) :=
      (conjSubgroup h (secA T T₁)).mul_mem ((conjSubgroup h (secA T T₁)).inv_mem y'.2) y.2
    have h5 := hnb _ h4 h3
    exact Subtype.ext (inv_mul_eq_one.1 h5).symm
  have hcard : Nat.card ↥(secA T T₁) ≤ Nat.card ↥(conjSubgroup h (secA T T₁)) :=
    (card_conjSubgroup h (secA T T₁)).ge
  have hbij := hinj.bijective_of_nat_card_le hcard
  intro a ha
  obtain ⟨y, hy⟩ := hbij.2 ⟨a, ha⟩
  refine ⟨y, y.2, ?_⟩
  have hy' : (y : G) * τ * (y : G)⁻¹ * τ⁻¹ = a := congrArg Subtype.val hy
  calc (y : G) * τ * (y : G)⁻¹ = ((y : G) * τ * (y : G)⁻¹ * τ⁻¹) * τ := by group
    _ = a * τ := by rw [hy']

theorem fusion {t : G} (ht : t ∈ secA T T₁) (ht1 : t ≠ 1) :
    ∀ τ : G, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ) := by
  intro τ hcomm hconj hne
  obtain ⟨x, hx⟩ := isConj_iff.1 hconj
  rcases c.conj_comm_cases ht ht1 hx hcomm with hτA | ⟨hu, hτ⟩
  · have htτ : t * τ ∈ secA T T₁ := (secA T T₁).mul_mem ht hτA
    have htτ1 : t * τ ≠ 1 := by
      intro h
      apply hne
      have htt : t * t = 1 := c.mul_self_T (secA_le_left ht)
      calc τ = t * (t * τ) := by rw [← mul_assoc, htt, one_mul]
        _ = t := by rw [h, mul_one]
    exact c.isConj_of_mem_secA ht ht1 htτ htτ1
  · have hτ1 : τ ≠ 1 := conj_ne_one' hx ht1
    obtain ⟨h, hh, hnb⟩ := c.exists_nonneighbour hu hτ hτ1
    obtain ⟨y, -, hyτ⟩ := c.fusion_pairing hu hh hτ hnb t ht
    exact hconj.trans (isConj_iff.2 ⟨y, hyτ⟩)

end Cfg56

end CFSG.CGT.T75O
