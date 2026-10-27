module

public import CFSG.ClassicalInvolution.Balance.PassTwoLocal
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Balance

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Comm

theorem comm_mem_oddCoreIn_of_ne_comp (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData p f (locQuot Ω u) (locFamily Ω u)} {i j : Fin D.card} (hij : i ≠ j)
    {N N' : Subgroup G} (hN : N ∈ compMembers Ω u D i) (hN' : N' ∈ compMembers Ω u D j)
    {a b : G} (ha : a ∈ N) (hb : b ∈ N') :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
  have haY : a ∈ locLayer Ω u := le_centralizingLayer hN.1 ha
  have hbY : b ∈ locLayer Ω u := le_centralizingLayer hN'.1 hb
  have hc := commutes_range D hij (locMk Ω u ⟨a, haY⟩)
    (hN.2 ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩) (locMk Ω u ⟨b, hbY⟩)
    (hN'.2 ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)
  have hd : (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹ : ↥(locLayer Ω u)) ∈
      classicalInvolutionOddCore ↥(locLayer Ω u) := by
    rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω u))]
    change locMk Ω u (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hc
  have := map_inclusion_oddCore_le (a := u) hΩ ⟨_, hd, rfl⟩
  exact ⟨_, this, rfl⟩

@[expose] def commModOdd (u : G) (X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.centralizer ({u} : Set G) ∧ ∀ y ∈ X,
    g * y * g⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G))}
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hg₁ hg₂, fun y hy => ?_⟩
    have e : g₁ * g₂ * y * (g₁ * g₂)⁻¹ * y⁻¹ =
        (g₁ * (g₂ * y * g₂⁻¹ * y⁻¹) * g₁⁻¹) * (g₁ * y * g₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_oddCoreIn hg₁ (h₂ y hy)) (h₁ y hy)
  one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, h⟩
    refine ⟨Subgroup.inv_mem _ hg, fun y hy => ?_⟩
    have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ = (g⁻¹ * (g * y * g⁻¹ * y⁻¹) * g⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (conj_mem_oddCoreIn (Subgroup.inv_mem _ hg) (h y hy))

theorem le_commModOdd_of_ne_comp (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData p f (locQuot Ω u) (locFamily Ω u)} {i : Fin D.card} {X : Subgroup G}
    (hX : X ∈ compMembers Ω u D i) {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ L ∈ 𝒮, L ∈ centralizingMembers Ω {u} ∧ ∀ j, L ∈ compMembers Ω u D j → j ≠ i)
    (hle : ∀ L ∈ 𝒮, ∃ j, L ∈ compMembers Ω u D j) :
    (⨆ L ∈ 𝒮, L) ≤ commModOdd u X := by
  refine iSup₂_le fun L hL g hg => ?_
  obtain ⟨j, hj⟩ := hle L hL
  refine ⟨(h𝒮 L hL).1.2 hg, fun y hy => ?_⟩
  exact comm_mem_oddCoreIn_of_ne_comp hΩ ((h𝒮 L hL).2 j hj) hj hX hg hy

end Comm

section Layer

theorem oddCoreIn_inf_layer_le (u : G) {x : G}
    (hxO : x ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G))) (hxY : x ∈ locLayer Ω u) :
    (⟨x, hxY⟩ : ↥(locLayer Ω u)) ∈ classicalInvolutionOddCore ↥(locLayer Ω u) := by
  have hYC : locLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) :=
    centralizingLayer_le_centralizer Ω {u}
  let S : Subgroup G := oddCoreIn (Subgroup.centralizer ({u} : Set G)) ⊓ locLayer Ω u
  have hSY : S ≤ locLayer Ω u := inf_le_right
  have hnorm : locLayer Ω u ≤ Subgroup.normalizer (S : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨hs1, hs2⟩
      exact ⟨conj_mem_oddCoreIn (hYC hy) hs1,
        (locLayer Ω u).mul_mem ((locLayer Ω u).mul_mem hy hs2) ((locLayer Ω u).inv_mem hy)⟩
    · rintro ⟨hs1, hs2⟩
      have e : s = y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ := by group
      rw [e]
      exact ⟨conj_mem_oddCoreIn (Subgroup.inv_mem _ (hYC hy)) hs1,
        (locLayer Ω u).mul_mem ((locLayer Ω u).mul_mem ((locLayer Ω u).inv_mem hy) hs2)
          ((locLayer Ω u).inv_mem ((locLayer Ω u).inv_mem hy))⟩
  have hodd : Odd (Nat.card S) :=
    (odd_card_oddCoreIn (Subgroup.centralizer ({u} : Set G))).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hle := le_oddCoreIn_of_normalizes hSY hnorm hodd ⟨hxO, hxY⟩
  obtain ⟨d, hd, hdx⟩ := hle
  have : d = ⟨x, hxY⟩ := Subtype.ext hdx
  rw [← this]
  exact hd

theorem conjSub_mem_compMembers_of_oddCoreIn (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData p f (locQuot Ω u) (locFamily Ω u)} {i : Fin D.card} {N : Subgroup G}
    (hN : N ∈ compMembers Ω u D i) {n : G}
    (hn : n ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G))) :
    conjSub n N ∈ compMembers Ω u D i := by
  have hnC : n ∈ Subgroup.centralizer ({u} : Set G) := oddCoreIn_le _ hn
  refine ⟨⟨hΩ n N hN.1.1, ?_⟩, ?_⟩
  · intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := hN.1.2 hy
    have e : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC h1) (Subgroup.inv_mem _ hnC)
  · refine le_trans ?_ hN.2
    rintro _ ⟨a, ha, rfl⟩
    have haN : (a : G) ∈ conjSub n N := Subgroup.mem_subgroupOf.mp ha
    rw [mem_conjSub_iff] at haN
    have hy₀Y : n⁻¹ * (a : G) * n ∈ locLayer Ω u := le_centralizingLayer hN.1 haN
    refine ⟨⟨n⁻¹ * (a : G) * n, hy₀Y⟩, Subgroup.mem_subgroupOf.mpr haN, ?_⟩
    show locMk Ω u ⟨n⁻¹ * (a : G) * n, hy₀Y⟩ = locMk Ω u a
    refine QuotientGroup.eq.mpr ?_
    have haC : (a : G) ∈ Subgroup.centralizer ({u} : Set G) :=
      centralizingLayer_le_centralizer Ω {u} a.2
    have hmem : (n⁻¹ * (a : G) * n)⁻¹ * (a : G) ∈
        oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
      have e : (n⁻¹ * (a : G) * n)⁻¹ * (a : G) = n⁻¹ * ((a : G)⁻¹ * n * (a : G)⁻¹⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn)
        (conj_mem_oddCoreIn (Subgroup.inv_mem _ haC) hn)
    exact oddCoreIn_inf_layer_le u hmem
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy₀Y) a.2)

end Layer

end CFSG.ClassicalInvolution.RouteD.Exotic
