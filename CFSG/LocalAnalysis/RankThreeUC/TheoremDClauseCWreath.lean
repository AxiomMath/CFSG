module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCDefs
public import CFSG.LocalAnalysis.RankThreeUC.WreathQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private abbrev M3 : Type := Multiplicative (ZMod 3)

local instance instDecEqWreath : DecidableEq WreathThree := fun a b =>
  decidable_of_iff
    (RegularWreathProduct.equivProd (Multiplicative (ZMod 3)) (Multiplicative (ZMod 3)) a =
      RegularWreathProduct.equivProd (Multiplicative (ZMod 3)) (Multiplicative (ZMod 3)) b)
    ⟨fun h => (RegularWreathProduct.equivProd _ _).injective h, fun h => by rw [h]⟩

local instance instFintypeWreath : Fintype WreathThree :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Multiplicative (ZMod 3))
    (Multiplicative (ZMod 3))).symm

private def topEl : WreathThree := ⟨fun _ => 1, Multiplicative.ofAdd 1⟩

private def baseEl : WreathThree :=
  ⟨fun x => if x = 1 then Multiplicative.ofAdd 1 else 1, 1⟩

private def piHom : WreathThree →* M3 × M3 where
  toFun w := (∏ x : M3, w.left x, w.right)
  map_one' := by
    ext
    · simp
    · rfl
  map_mul' a b := by
    refine Prod.ext ?_ rfl
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft a.right⁻¹) _ _ (fun x => rfl)


private theorem topEl_pow : topEl ^ 3 = 1 := by decide +kernel

private theorem baseEl_pow : baseEl ^ 3 = 1 := by decide +kernel

private theorem comm_ne_one : ⁅topEl, ⁅topEl, baseEl⁆⁆ ≠ 1 := by decide +kernel

private theorem comm_pow : ⁅topEl, ⁅topEl, baseEl⁆⁆ ^ 3 = 1 := by decide +kernel

private theorem topEl_right : topEl.right ≠ 1 := by decide +kernel

private theorem fact_left : ∀ x : WreathThree, (∏ y : M3, x.left y) ≠ 1 →
    ⁅topEl, x⁆ ≠ 1 ∧ ⁅topEl, x⁆ ≠ ⁅topEl, ⁅topEl, baseEl⁆⁆ ∧
    ⁅topEl, x⁆ ≠ (⁅topEl, ⁅topEl, baseEl⁆⁆)⁻¹ ∧ ⁅topEl, x⁆ ^ 3 = 1 ∧
    ⁅topEl, ⁅topEl, baseEl⁆⁆ * ⁅topEl, x⁆ = ⁅topEl, x⁆ * ⁅topEl, ⁅topEl, baseEl⁆⁆ := by
  decide +kernel

private theorem fact_right : ∀ x : WreathThree, x.right ≠ 1 →
    ⁅baseEl, x⁆ ≠ 1 ∧ ⁅baseEl, x⁆ ≠ ⁅topEl, ⁅topEl, baseEl⁆⁆ ∧
    ⁅baseEl, x⁆ ≠ (⁅topEl, ⁅topEl, baseEl⁆⁆)⁻¹ ∧ ⁅baseEl, x⁆ ^ 3 = 1 ∧
    ⁅topEl, ⁅topEl, baseEl⁆⁆ * ⁅baseEl, x⁆ = ⁅baseEl, x⁆ * ⁅topEl, ⁅topEl, baseEl⁆⁆ := by
  decide +kernel

private theorem pair_pow_three : ∀ g : M3 × M3, g ^ 3 = 1 := by decide +kernel

private theorem not_cyclic_pair : ∀ g : M3 × M3, ∃ a : M3 × M3, ∀ k : Fin 3, a ≠ g ^ (k : ℕ) := by
  decide +kernel

private theorem exists_not_pow (g : M3 × M3) : ∃ a : M3 × M3, ∀ k : ℕ, a ≠ g ^ k := by
  obtain ⟨a, ha⟩ := not_cyclic_pair g
  refine ⟨a, fun k hk => ?_⟩
  rw [pow_eq_pow_mod k (pair_pow_three g)] at hk
  exact ha ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ hk

private theorem piHom_surj : Function.Surjective piHom := by
  intro a
  refine ⟨⟨fun x => if x = 1 then a.1 else 1, a.2⟩, ?_⟩
  refine Prod.ext ?_ rfl
  show ∏ x : M3, (if x = 1 then a.1 else 1) = a.1
  simp

private theorem wreath_core (H : Subgroup WreathThree) (hn : H.Normal)
    (hcyc : ∃ g : WreathThree, ∀ γ : WreathThree, ∃ k : ℕ, ∃ h ∈ H, γ = g ^ k * h) :
    (∀ a b : WreathThree, ⁅a, b⁆ ∈ H) ∧ ∃ x ∈ H, piHom x ≠ 1 := by
  obtain ⟨g, hg⟩ := hcyc
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨i, h₁, hh₁, rfl⟩ := hg a
    obtain ⟨j, h₂, hh₂, rfl⟩ := hg b
    rw [← QuotientGroup.eq_one_iff (N := H), ← QuotientGroup.mk'_apply, map_commutatorElement]
    have h1 : QuotientGroup.mk' H h₁ = 1 := (QuotientGroup.eq_one_iff h₁).mpr hh₁
    have h2 : QuotientGroup.mk' H h₂ = 1 := (QuotientGroup.eq_one_iff h₂).mpr hh₂
    rw [map_mul, map_mul, h1, h2, mul_one, mul_one, map_pow, map_pow]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((Commute.refl _).pow_pow i j).eq
  · by_contra hcon
    push Not at hcon
    obtain ⟨a, ha⟩ := exists_not_pow (piHom g)
    obtain ⟨w, hw⟩ := piHom_surj a
    obtain ⟨k, h, hh, rfl⟩ := hg w
    rw [map_mul, map_pow, hcon h hh, mul_one] at hw
    exact ha k hw.symm

private def emb (P : Subgroup G) (e : P ≃* WreathThree) : WreathThree →* G :=
  P.subtype.comp e.symm.toMonoidHom

private theorem emb_injective (P : Subgroup G) (e : P ≃* WreathThree) :
    Function.Injective (emb P e) :=
  P.subtype_injective.comp e.symm.injective

private theorem emb_mem (P : Subgroup G) (e : P ≃* WreathThree) (w : WreathThree) :
    emb P e w ∈ P :=
  (e.symm w).2

private theorem transfer {P H : Subgroup G} (e : P ≃* WreathThree)
    (hHn : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H) (hcyc : CyclicMod P H) :
    (H.comap (emb P e)).Normal ∧
      ∃ g : WreathThree, ∀ γ : WreathThree, ∃ k : ℕ, ∃ h ∈ H.comap (emb P e), γ = g ^ k * h := by
  refine ⟨⟨fun n hn w => ?_⟩, ?_⟩
  · have : emb P e n ∈ H := hn
    show emb P e (w * n * w⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv]
    exact hHn _ (emb_mem P e w) _ this
  · obtain ⟨g, hgP, hg⟩ := hcyc
    refine ⟨e ⟨g, hgP⟩, fun γ => ?_⟩
    obtain ⟨k, h, hhH, hγ⟩ := hg (emb P e γ) (emb_mem P e γ)
    have hge : emb P e (e ⟨g, hgP⟩) = g := by simp [emb]
    refine ⟨k, (e ⟨g, hgP⟩ ^ k)⁻¹ * γ, ?_, by group⟩
    show emb P e ((e ⟨g, hgP⟩ ^ k)⁻¹ * γ) ∈ H
    rw [map_mul, map_inv, map_pow, hge, hγ, inv_mul_cancel_left]
    exact hhH

theorem exists_three_element_nontrivial_commutator {P H C : Subgroup G} (e : P ≃* WreathThree)
    (hHn : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H) (hcyc : CyclicMod P H)
    (hC : NoRankTwoThree C) : ∃ y ∈ P, y ^ 3 = 1 ∧ ∃ x ∈ H, ⁅y, x⁆ ∉ C := by
  obtain ⟨hHw, hcycw⟩ := transfer e hHn hcyc
  obtain ⟨hcomm, x₀, hx₀, hx₀1⟩ := wreath_core (H.comap (emb P e)) hHw hcycw
  by_contra hcon
  push Not at hcon
  have key : ∀ w : WreathThree, w ^ 3 = 1 → ∀ x ∈ H.comap (emb P e),
      ⁅emb P e w, emb P e x⁆ ∈ C := fun w hw x hx =>
    hcon _ (emb_mem P e w) (by rw [← map_pow, hw, map_one]) _ hx
  have hinj := emb_injective P e
  have hc1 : emb P e ⁅topEl, ⁅topEl, baseEl⁆⁆ ∈ C := by
    rw [map_commutatorElement]
    exact key topEl topEl_pow _ (hcomm topEl baseEl)
  have hmain : ∀ c₂ : WreathThree, emb P e c₂ ∈ C → c₂ ≠ 1 → c₂ ≠ ⁅topEl, ⁅topEl, baseEl⁆⁆ →
      c₂ ≠ (⁅topEl, ⁅topEl, baseEl⁆⁆)⁻¹ → c₂ ^ 3 = 1 →
      ⁅topEl, ⁅topEl, baseEl⁆⁆ * c₂ = c₂ * ⁅topEl, ⁅topEl, baseEl⁆⁆ → False := by
    intro c₂ h2 h21 h2a h2b h23 h2c
    refine hC _ hc1 _ h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, h2c, map_mul]
    · rw [← map_pow, comm_pow, map_one]
    · rw [← map_pow, h23, map_one]
    · exact fun h => comm_ne_one (hinj (by rw [h, map_one]))
    · exact fun h => h21 (hinj (by rw [h, map_one]))
    · exact fun h => h2a (hinj h)
    · exact fun h => h2b (hinj (by rw [h, map_inv]))
  have hx₀' : (∏ y : M3, x₀.left y) ≠ 1 ∨ x₀.right ≠ 1 := by
    by_contra h
    push Not at h
    exact hx₀1 (Prod.ext h.1 h.2)
  rcases hx₀' with h | h
  · obtain ⟨f1, f2, f3, f4, f5⟩ := fact_left x₀ h
    refine hmain ⁅topEl, x₀⁆ ?_ f1 f2 f3 f4 f5
    rw [map_commutatorElement]
    exact key topEl topEl_pow x₀ hx₀
  · obtain ⟨f1, f2, f3, f4, f5⟩ := fact_right x₀ h
    refine hmain ⁅baseEl, x₀⁆ ?_ f1 f2 f3 f4 f5
    rw [map_commutatorElement]
    exact key baseEl baseEl_pow x₀ hx₀

theorem exists_order_three_not_mem_thompsonSubgroup_commutator_ne_one [Finite G]
    {P H : Subgroup G} (e : P ≃* WreathThree)
    (hHn : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H) (hcyc : CyclicMod P H) :
    ∃ s ∈ P, orderOf s = 3 ∧ s ∉ thompsonSubgroup P ∧ ∃ x ∈ H, ⁅s, x⁆ ≠ 1 := by
  obtain ⟨hHw, hcycw⟩ := transfer e hHn hcyc
  obtain ⟨hcomm, -⟩ := wreath_core (H.comap (emb P e)) hHw hcycw
  have hinj := emb_injective P e
  have htop1 : topEl ≠ 1 := fun h => topEl_right (by rw [h]; rfl)
  refine ⟨emb P e topEl, emb_mem P e topEl, ?_, fun hy => ?_, emb P e ⁅topEl, baseEl⁆,
    hcomm topEl baseEl, ?_⟩
  · rw [orderOf_injective _ hinj, orderOf_eq_prime topEl_pow htop1]
  · obtain ⟨a, ha, haσ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.thompsonSubgroup_le_map_ker e hy
    obtain rfl : a = topEl := hinj haσ
    exact topEl_right ha
  · rw [← map_commutatorElement]
    exact fun h => comm_ne_one (hinj (by rw [h, map_one]))

theorem card_eq_eighty_one_of_equiv {P : Subgroup G} (e : P ≃* WreathThree) :
    Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

end CFSG.LocalAnalysis.RankThreeUC
