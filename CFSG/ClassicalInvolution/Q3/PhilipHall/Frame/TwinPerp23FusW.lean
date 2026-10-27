module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusLie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711Cor
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93WO2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf19AE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

theorem eq_or_inv_of_mem_zpowers {X : Type} [Group X] {a b : X} (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1)
    (hb : b ∈ Subgroup.zpowers a) (hb2 : b ^ 2 ≠ 1) : b = a ∨ b = a⁻¹ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hord : orderOf a = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a) (by simpa using ha2)
      (by simpa using ha4)
    simpa using this
  have hmod : a ^ (i % (orderOf a : ℤ)) = a ^ i := zpow_mod_orderOf a i
  rw [hord] at hmod
  rw [← hmod] at hb2 ⊢
  have hi : i % ((4 : ℕ) : ℤ) = 0 ∨ i % ((4 : ℕ) : ℤ) = 1 ∨ i % ((4 : ℕ) : ℤ) = 2 ∨
      i % ((4 : ℕ) : ℤ) = 3 := by omega
  rcases hi with h | h | h | h <;> rw [h] at hb2 ⊢
  · exact absurd (by simp) hb2
  · left; simp
  · exfalso
    apply hb2
    calc (a ^ (((2 : ℕ) : ℤ))) ^ 2 = a ^ 4 := by group
      _ = 1 := ha4
  · right
    calc a ^ (((3 : ℕ) : ℤ)) = a ^ 4 * a⁻¹ := by group
      _ = a⁻¹ := by rw [ha4, one_mul]


section W

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem wshape_false (h : PerpHypS n Y R S t) {c : Y} {J J' Q Q' : Subgroup Y} {w : Y}
    (hT : LayerTwins Y R c J J' Q Q' w) (h2 : ∀ L ∈ TwinDisc.secFam (Om R) c, IsPGroup 2 ↥L)
    (hV : ∃ V : Subgroup (SecQ R c), WSet (TwinDisc.secFam (Om R) c) = {V}) {x : Y}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set Y)) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hmove : ∀ q ∈ Q, q ^ 2 ≠ 1 → x * q * x⁻¹ ≠ q ∧ x * q * x⁻¹ ≠ q⁻¹) : False := by
  classical
  obtain ⟨V, hV⟩ := hV
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hT.hc2
  have hS := p23_q8Section h hT.hc2
  have hΦ : HypOmegaGen (TwinDisc.secFam (Om R) c) := hS.hyp
  have hVmem : V ∈ WSet (TwinDisc.secFam (Om R) c) := by rw [hV]; exact Set.mem_singleton V
  have hVn : ∀ y : SecQ R c, conjSub y V = V := fun y => by
    have h1 := WSet.conj hΦ.conjInvariant hVmem y
    rw [hV] at h1
    exact h1
  haveI hVnormal : V.Normal := TwinSec711.normal_of_conj_eq hVn
  obtain ⟨σ, hσ⟩ : ∃ σ : MulAut (SecQ R c), σ = TwinDisc.secAct hΩ hc2'
      (⟨x, hxc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : MulAut (SecQ R c), σ' = TwinDisc.secAct hΩ hc2'
      (⟨x⁻¹, Subgroup.inv_mem _ hxc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) := ⟨_, rfl⟩
  have hperm1 : ∀ L ∈ TwinDisc.secFam (Om R) c, L.map σ.toMonoidHom ∈ TwinDisc.secFam (Om R) c := by
    intro L hL'
    obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hL'
    rw [hσ, TwinDisc.secAct_map_secImg hΩ hc2' ⟨x, hxc⟩]
    exact TwinDisc.secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxc hJ₁)
  have hperm2 : ∀ L ∈ TwinDisc.secFam (Om R) c, L.map σ'.toMonoidHom ∈ TwinDisc.secFam (Om R) c := by
    intro L hL'
    obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hL'
    have hxi : x⁻¹ ∈ Subgroup.centralizer ({c} : Set Y) := Subgroup.inv_mem _ hxc
    rw [hσ', TwinDisc.secAct_map_secImg hΩ hc2' ⟨x⁻¹, hxi⟩]
    exact TwinDisc.secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxi hJ₁)
  have hσσ' : σ' = σ.symm := by
    have h1 : σ * σ' = 1 := by
      rw [hσ, hσ', ← map_mul]
      have : (⟨x, hxc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) *
          ⟨x⁻¹, Subgroup.inv_mem _ hxc⟩ = 1 := Subtype.ext (mul_inv_cancel x)
      rw [this, map_one]
    exact eq_inv_of_mul_eq_one_right h1
  have hσV : V.map σ.toMonoidHom = V := by
    have h1 := TwinPerpV3.Pf93.map_mem_WSet_equiv σ hperm1
      (fun L hL => by rw [← hσσ']; exact hperm2 L hL) hVmem
    rw [hV] at h1
    exact h1
  set C := Subgroup.centralizer ({c} : Set Y) with hC'
  set H := TwinDisc.coreHull (Om R) c with hH
  set N := classicalInvolutionOddCore ↥H with hN
  set π := QuotientGroup.mk' N with hπ
  set A : Subgroup ↥H := (Q.subgroupOf C).subgroupOf H with hA
  have hJb : TwinDisc.secImg (Om R) c J ∈ TwinDisc.secFam (Om R) c :=
    TwinDisc.secImg_mem_secFam hT.hJ
  set Jb := TwinDisc.secImg (Om R) c J with hJbdef
  have hJb2 : IsPGroup 2 ↥Jb := h2 _ hJb
  have hAmap : A.map π = Jb := map_syl_eq_secImg hc2' hT.hJ hT.hQ hT.hQc hJb2
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hA2 : IsPGroup 2 ↥A :=
    (hT.hQ.2.1.comap_of_injective C.subtype C.subtype_injective).comap_of_injective
      H.subtype H.subtype_injective
  have hAN : A ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hA2 le_rfl
      (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hinj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, π a₁ = π a₂ → a₁ = a₂ := by
    intro a₁ h₁ a₂ h₂ he
    have h1 : a₁⁻¹ * a₂ ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem h₁) h₂, QuotientGroup.eq.mp he⟩
    rw [hAN, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hact : ∀ b ∈ A, ∃ b' ∈ A, σ (π b) = π b' ∧
      (((b' : ↥H) : ↥C) : Y) = x * (((b : ↥H) : ↥C) : Y) * x⁻¹ := by
    intro b hb
    have hbQ : (((b : ↥H) : ↥C) : Y) ∈ Q :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hb)
    have hb'val : ((((C25Y.conjOnSub H (conjSub_coreHull hΩ hc2' (⟨x, hxc⟩ : ↥C)) b : ↥H) : ↥C) : Y)) =
        x * (((b : ↥H) : ↥C) : Y) * x⁻¹ :=
      congrArg (fun z : ↥C => (z : Y)) (TwinDisc.coe_secAct_mk hΩ hc2' (⟨x, hxc⟩ : ↥C) b)
    refine ⟨C25Y.conjOnSub H (conjSub_coreHull hΩ hc2' (⟨x, hxc⟩ : ↥C)) b, ?_, ?_, hb'val⟩
    swap
    · rw [hσ]; exact TwinDisc.secAct_mk hΩ hc2' (⟨x, hxc⟩ : ↥C) b
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
      (by rw [hb'val]; exact hxQ _ hbQ))
  obtain ⟨η, hη, hVeq⟩ := id hVmem
  have hV2 : IsPGroup 2 ↥V := Thompson.isPGroup_of_mem_WSet hVmem
  have hJVn : Jb ≤ Subgroup.normalizer (V : Set (SecQ R c)) := by
    rw [Subgroup.normalizer_eq_top (H := V)]
    exact le_top
  have hsup : IsPGroup 2 ↥(Jb ⊔ V) := hJb2.to_sup_of_normal_right' hV2 hJVn
  obtain ⟨S', hS'⟩ := hsup.exists_le_sylow
  have hVS' : V ≤ (S' : Subgroup (SecQ R c)) := le_sup_right.trans hS'
  have hηS : ∀ U ∈ η, U ≤ (S' : Subgroup (SecQ R c)) := fun U hU =>
    ((by rw [hVeq]; exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) U hU) : U ≤ V).trans hVS'
  have hmem := TwinSec711.member_inf_mem_eta hΦ hη hηS hJb
    ⟨le_rfl, hJb2, fun V' h1 _ h3 => le_antisymm h1 h3⟩ (le_sup_left.trans hS')
  rw [← hVeq] at hmem
  obtain ⟨R', hR', hUR', hcyc, hidx⟩ := TwinSec711.mem_USet_of_mem_etaG hη hmem
  obtain ⟨L₀, hL₀, hRL⟩ := exists_isSylow2In_of_mem_RSet hR'
  obtain ⟨eR⟩ := hS.q8 L₀ hL₀ R' hRL
  have hR'card : Nat.card ↥R' = 8 := by
    rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hUcard : Nat.card ↥(Jb ⊓ V) = 4 := by
    have h1 := Subgroup.card_mul_index ((Jb ⊓ V).subgroupOf R')
    have h2 : ((Jb ⊓ V).subgroupOf R').index = 2 := hidx
    rw [h2, hR'card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR').toEquiv] at h1
    omega
  obtain ⟨gen, hgen⟩ := hcyc.exists_generator
  have hgenord : orderOf gen = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hUcard]
  set a : SecQ R c := ((gen : ↥(Jb ⊓ V)) : SecQ R c) with ha
  have haU : a ∈ Jb ⊓ V := gen.2
  have ha4 : a ^ 4 = 1 := by
    have := pow_orderOf_eq_one gen
    rw [hgenord] at this
    simpa using congrArg (fun z : ↥(Jb ⊓ V) => (z : SecQ R c)) this
  have ha2 : a ^ 2 ≠ 1 := by
    intro h1
    have : orderOf gen ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [hgenord] at this
    omega
  have hazp : ∀ z ∈ Jb ⊓ V, z ∈ Subgroup.zpowers a := by
    intro z hz
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩
  obtain ⟨b, hbA, hba⟩ : ∃ b ∈ A, π b = a := by
    have : a ∈ A.map π := hAmap ▸ haU.1
    obtain ⟨b, hb, e⟩ := this
    exact ⟨b, hb, e⟩
  obtain ⟨b', hb'A, hσb, hb'val⟩ := hact b hbA
  have hσaU : σ a ∈ Jb ⊓ V := by
    refine ⟨?_, ?_⟩
    · rw [← hba, hσb, ← hAmap]
      exact ⟨b', hb'A, rfl⟩
    · have : σ a ∈ V.map σ.toMonoidHom := ⟨a, haU.2, rfl⟩
      rwa [hσV] at this
  have hσa2 : (σ a) ^ 2 ≠ 1 := by
    intro h1
    apply ha2
    have : σ (a ^ 2) = σ 1 := by rw [map_pow, h1, map_one]
    exact σ.injective this
  rcases eq_or_inv_of_mem_zpowers ha4 ha2 (hazp _ hσaU) hσa2 with h1 | h1
  ·
    have hb'b : b' = b := hinj _ hb'A _ hbA (by rw [← hσb, hba]; exact h1)
    have hbQ : (((b : ↥H) : ↥C) : Y) ∈ Q :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hbA)
    have hq2 : (((b : ↥H) : ↥C) : Y) ^ 2 ≠ 1 := by
      intro h3
      apply ha2
      have h4 : b ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using h3))
      rw [← hba, ← map_pow, h4, map_one]
    exact (hmove _ hbQ hq2).1 (by rw [← hb'val, hb'b])
  ·
    have hb'b : b' = b⁻¹ := hinj _ hb'A _ (A.inv_mem hbA) (by rw [← hσb, map_inv, hba]; exact h1)
    have hbQ : (((b : ↥H) : ↥C) : Y) ∈ Q :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hbA)
    have hq2 : (((b : ↥H) : ↥C) : Y) ^ 2 ≠ 1 := by
      intro h3
      apply ha2
      have h4 : b ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using h3))
      rw [← hba, ← map_pow, h4, map_one]
    exact (hmove _ hbQ hq2).2 (by rw [← hb'val, hb'b]; rfl)

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
