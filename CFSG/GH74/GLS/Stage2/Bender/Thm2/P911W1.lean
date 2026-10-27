module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der615
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Comp
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section W1

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

private theorem mem_Op_of_centralizes (hC : Ctx9 G z k S M p) {x : G} (hxM : x ∈ M)
    (hx : x ∈ centralizer ((Op p M : Subgroup G) : Set G)) : x ∈ Op p M := by
  have hD : generalizedFitting ↥M = pCore p ↥M := (Fs_eq_Op_iff M p).mp hC.fstar
  have hx' : (⟨x, hxM⟩ : ↥M) ∈ centralizer ((generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hD] at hy
    have hmem : (y : G) ∈ Op p M := ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx _ hmem)
  have h3 := CFSG.centralizer_generalizedFitting_le ↥M hx'
  rw [hD] at h3
  exact ⟨_, h3, rfl⟩

omit [Finite G] in
private theorem le_Cen_of_le_centralizer {J₁ X₂ : Subgroup G} (hzJ : z ∈ J₁)
    (hX₂J : X₂ ≤ centralizer (J₁ : Set G)) : X₂ ≤ Cen z := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hX₂J hx) z hzJ).symm

omit [Finite G] in
private theorem mem_centralizer_of_le_centralizer {J₁ X₂ : Subgroup G} {c : G} (hc : c ∈ J₁)
    (hX₂J : X₂ ≤ centralizer (J₁ : Set G)) : c ∈ centralizer (X₂ : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    (Subgroup.mem_centralizer_iff.mp (hX₂J hx) c hc).symm

private theorem mem_normalizer_cap {X₂ : Subgroup G} {c : G} (hcM : c ∈ M)
    (hcX : c ∈ centralizer (X₂ : Set G)) :
    c ∈ normalizer ((Op p M ⊓ centralizer (X₂ : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf (le_normalizer_Op' p M hcM)
    (mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ hcX))

private theorem comm_cap_ne_bot (hC : Ctx9 G z k S M p) {X₂ : Subgroup G} (hX₂p : IsPGroup p ↥X₂)
    (hX₂Cen : X₂ ≤ Cen z) :
    ⁅Op p M ⊓ centralizer (X₂ : Set G), zpowers z⁆ ≠ ⊥ := by
  intro hbot
  have hp := hC.prime
  have hzM : z ∈ M := hC.z_mem
  have hzP : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op' p M hzM
  have hCz : Op p M ⊓ centralizer (X₂ : Set G) ≤ Cen z := commutator_zpowers_eq_bot_iff.mp hbot
  have hcop : Nat.Coprime p (Nat.card ↥(zpowers z)) := by
    rw [Nat.card_zpowers, hC.orderOf_z]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hC.odd
  have hAB : ∀ a ∈ zpowers z, ∀ b ∈ X₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.mp (hX₂Cen hb)
    exact (Commute.zpow_left (show Commute z b from hbz.symm) n).eq
  have hfix :
      zpowers z ≤ centralizer ((Op p M ⊓ centralizer (X₂ : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mp (hCz hc)
  have hcenP : zpowers z ≤ centralizer ((Op p M : Subgroup G) : Set G) :=
    ig_11_7_thm G p hp (zpowers z) X₂ (Op p M) hC.P_pgroup hX₂p hcop
      (Subgroup.zpowers_le.mpr hzP) ((hX₂Cen.trans hC.cen_le).trans (le_normalizer_Op' p M)) hAB
      hfix
  have hzO : z ∈ Op p M := mem_Op_of_centralizes hC hzM (hcenP (Subgroup.mem_zpowers z))
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hC.P_pgroup ⟨z, hzO⟩
  rw [Subgroup.orderOf_mk, hC.orderOf_z] at hm
  exact hC.odd ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hm.symm).1

private theorem conj_mem_of_odd {J₁ N₁ : Subgroup G}
    (hcard : Nat.card (CFSG.LocalCores.ComponentIndex ↥N₁) ≤ 2)
    (hJN : IsComponent (J₁.subgroupOf N₁)) (hJN₁ : J₁ ≤ N₁) {c : G} (hcN : c ∈ N₁)
    (hodd : Odd (orderOf c)) {j : G} (hj : j ∈ J₁) : c * j * c⁻¹ ∈ J₁ := by
  have h1 := mem_normalizer_of_odd_orderOf hcard (a := (⟨c, hcN⟩ : ↥N₁))
    (by rwa [Subgroup.orderOf_mk]) hJN
  have h2 := (Subgroup.mem_normalizer_iff.mp h1 ⟨j, hJN₁ hj⟩).mp (Subgroup.mem_subgroupOf.mpr hj)
  exact Subgroup.mem_subgroupOf.mp h2

theorem exists_W₁ {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    (hC : Ctx9 G z k S M p) {J₁ N₁ X₂ : Subgroup G} (hN₁ : N₁ ≠ ⊤) (hzJ : z ∈ J₁)
    (hJN : IsComponent (J₁.subgroupOf N₁)) (hJN₁ : J₁ ≤ N₁) (hX₂p : IsPGroup p ↥X₂)
    (hX₂0 : X₂ ≠ ⊥) (hX₂J : X₂ ≤ centralizer (J₁ : Set G))
    (hX₂N : normalizer (X₂ : Set G) ≤ N₁) :
    ∃ W₁ : Subgroup G, W₁ ≠ ⊥ ∧ IsPGroup p ↥W₁ ∧ W₁ ≤ J₁ ∧ ⁅W₁, zpowers z⁆ = W₁ ∧
      ∀ c ∈ J₁, c * z = z * c → c ∈ normalizer (W₁ : Set G) := by
  have _ := hN₁
  have _ := hX₂0
  have hp := hC.prime
  have hX₂Cen : X₂ ≤ Cen z := le_Cen_of_le_centralizer hzJ hX₂J
  have hzX : z ∈ centralizer (X₂ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hX₂Cen hx)
  have hzC : z ∈ normalizer ((Op p M ⊓ centralizer (X₂ : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_cap hC.z_mem hzX
  have hle : ⁅Op p M ⊓ centralizer (X₂ : Set G), zpowers z⁆ ≤ Op p M ⊓ centralizer (X₂ : Set G) :=
    commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzC)
  refine ⟨⁅Op p M ⊓ centralizer (X₂ : Set G), zpowers z⁆, comm_cap_ne_bot hC hX₂p hX₂Cen,
    hC.P_pgroup.to_le (hle.trans inf_le_left), ?_,
    commutator_zpowers_idem hC.orderOf_z hp hC.odd (hC.P_pgroup.to_le inf_le_left) hzC, ?_⟩
  · have hcard : Nat.card (CFSG.LocalCores.ComponentIndex ↥N₁) ≤ 2 :=
      card_componentIndex_le_two (SectionalTwoRankLE.subgroup N₁ hC.ctx.std.gen4)
    rw [Subgroup.commutator_le]
    intro c hc w hw
    have hcN : c ∈ N₁ := hX₂N (Subgroup.centralizer_le_normalizer _ hc.2)
    obtain ⟨m, hm⟩ := exists_orderOf_pow_of_mem_Op hp hc.1
    have hodd : Odd (orderOf c) := by
      rw [hm]
      exact (hp.odd_of_ne_two hC.odd).pow
    have hwJ : w ∈ J₁ := Subgroup.zpowers_le.mpr hzJ hw
    rw [commutatorElement_def]
    exact J₁.mul_mem (conj_mem_of_odd hcard hJN hJN₁ hcN hodd hwJ) (J₁.inv_mem hwJ)
  · intro c hcJ hcz
    have hcCen : c ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hcz
    exact le_normalizer_commutator_zpowers
      (mem_normalizer_cap (hC.cen_le hcCen) (mem_centralizer_of_le_centralizer hcJ hX₂J)) hcCen

end W1

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
