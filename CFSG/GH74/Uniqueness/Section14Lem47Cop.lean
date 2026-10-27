module

public import CFSG.GH74.Uniqueness.Section14Tools
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec147

section Transport

variable {X : Type*} [Group X]

theorem map_subtype_top (H : Subgroup X) : (⊤ : Subgroup ↥H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_fixedPointSubgroup_conj {A H : Subgroup X} [MulDistribMulAction ↥A ↥H]
    (hsmul : ∀ (a : ↥A) (y : ↥H), ((a • y : ↥H) : X) = a * y * (a : X)⁻¹) (b : ↥A) :
    (CFSG.fixedPointSubgroup (zpowers b) ↥H).map H.subtype =
      centralizer ({(b : X)} : Set X) ⊓ H := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hy' : (b : X) * y * (b : X)⁻¹ = y := by rw [← hsmul, hy]
    refine ⟨?_, y.2⟩
    calc (y : X) * b = ((b : X) * y * (b : X)⁻¹) * b := by rw [hy']
      _ = b * y := by group
  · rintro ⟨hxc, hxH⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
    apply Subtype.ext
    rw [hsmul]
    change (b : X) * x * (b : X)⁻¹ = x
    rw [← hxc]
    group

end Transport

section Coprime

variable {X : Type*} [Group X] [Finite X]

theorem exists_mixed_not_le {S T : Subgroup X} {x y : X} {p : ℕ} (hp : p.Prime)
    (hx : orderOf x = p) (hy : orderOf y = p) (hxy : x * y = y * x)
    (hint : zpowers x ⊓ zpowers y = ⊥)
    (hxS : x ∈ normalizer (S : Set X)) (hyS : y ∈ normalizer (S : Set X))
    (hpS : ¬ p ∣ Nat.card S) (hST : ¬ S ≤ T)
    (hX : ∀ a ∈ zpowers x, a ≠ 1 → centralizer ({a} : Set X) ⊓ S ≤ T)
    (hY : ∀ a ∈ zpowers y, a ≠ 1 → centralizer ({a} : Set X) ⊓ S ≤ T) :
    ∃ a ∈ zpowers x, a ≠ 1 ∧ ∃ b ∈ zpowers y, b ≠ 1 ∧
      ¬ (centralizer ({a * b} : Set X) ⊓ S ≤ T) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hyp : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have : CFSG.IsElementaryAbelian p (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have : CFSG.IsElementaryAbelian p (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
  have hyc : zpowers y ≤ centralizer (zpowers x : Set X) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun h hh => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (hxy : Commute x y) k)
  have hxc : zpowers x ≤ centralizer (zpowers y : Set X) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun h hh => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (hxy.symm : Commute y x) k)
  have : CFSG.IsElementaryAbelian p ↥(zpowers x ⊔ zpowers y) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hyc
  have hxN : zpowers x ≤ normalizer (zpowers y : Set X) := hxc.trans (centralizer_le_normalizer _)
  have hcard : Nat.card ↥(zpowers x ⊔ zpowers y) = p ^ 2 := by
    have h := card_sup_mul_card_inf' (A := zpowers y) (C := zpowers x) hxN
    rw [inf_comm, hint, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hx,
      hy] at h
    rw [h, sq]
  have hES : zpowers x ⊔ zpowers y ≤ normalizer (S : Set X) :=
    sup_le (zpowers_le.mpr hxS) (zpowers_le.mpr hyS)
  let _ : MulDistribMulAction ↥(zpowers x ⊔ zpowers y) ↥S :=
    MulDistribMulAction.compHom ↥S ((conjAut S).comp (Subgroup.inclusion hES))
  have hsmul : ∀ (a : ↥(zpowers x ⊔ zpowers y)) (s : ↥S),
      ((a • s : ↥S) : X) = (a : X) * s * (a : X)⁻¹ := fun a s => rfl
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p)
    (A := ↥(zpowers x ⊔ zpowers y)) (H := ↥S) (by rw [hcard]) hpS
  have hmap := congrArg (Subgroup.map S.subtype) hgen
  simp only [Subgroup.map_iSup, map_fixedPointSubgroup_conj hsmul, map_subtype_top] at hmap
  by_contra hcon
  push Not at hcon
  apply hST
  rw [← hmap]
  refine iSup₂_le fun a ha => ?_
  have haE : (a : X) ∈ zpowers x ⊔ zpowers y := a.2
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hxN] at haE
  obtain ⟨a₁, ha₁, a₂, ha₂, hae⟩ := haE
  have hae' : a₁ * a₂ = (a : X) := hae
  have ha1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
  by_cases h1 : a₁ = 1
  · rw [h1, one_mul] at hae'
    rw [← hae']
    exact hY a₂ ha₂ (by rw [hae']; exact ha1)
  by_cases h2 : a₂ = 1
  · rw [h2, mul_one] at hae'
    rw [← hae']
    exact hX a₁ ha₁ (by rw [hae']; exact ha1)
  rw [← hae']
  exact hcon a₁ ha₁ h1 a₂ ha₂ h2

end Coprime

end Sec147

end CFSG.GH74.Uniqueness
