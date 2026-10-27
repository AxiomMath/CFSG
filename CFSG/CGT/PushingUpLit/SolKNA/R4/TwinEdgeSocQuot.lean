module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocle
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThm4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin
open scoped commutatorElement

section Transport

variable {G A : Type} [Group G] [Group A]

@[expose] noncomputable def soc_mapEquiv (φ : G →* A) {P : Subgroup G}
    (hφ : ∀ x ∈ P, φ x = 1 → x = 1) : ↥P ≃* ↥(P.map φ) :=
  (MonoidHom.ofInjective (f := φ.comp P.subtype) (by
      intro x y hxy
      apply Subtype.ext
      have h2 : φ ((x : G) * (y : G)⁻¹) = 1 := by
        have : φ (x : G) = φ (y : G) := hxy
        rw [map_mul, map_inv, this, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hφ _ (P.mul_mem x.2 (P.inv_mem y.2)) h2))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem soc_natCard_map (φ : G →* A) {P : Subgroup G} (hφ : ∀ x ∈ P, φ x = 1 → x = 1) :
    Nat.card ↥(P.map φ) = Nat.card ↥P :=
  (Nat.card_congr (soc_mapEquiv φ hφ).toEquiv).symm

theorem soc_isCyclic_map (φ : G →* A) {P : Subgroup G} (hφ : ∀ x ∈ P, φ x = 1 → x = 1) :
    IsCyclic ↥(P.map φ) ↔ IsCyclic ↥P :=
  (soc_mapEquiv φ hφ).isCyclic.symm

theorem soc_isSylow2In_map (φ : G →* A) {N P : Subgroup G} (hφ : ∀ x ∈ N, φ x = 1 → x = 1)
    (h : IsSylow2In P N) : IsSylow2In (P.map φ) (N.map φ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map φ, fun V hVN hV2 hle => ?_⟩
  set V' : Subgroup G := V.comap φ ⊓ N with hV'
  have hV'N : V' ≤ N := inf_le_right
  have hPV' : P ≤ V' := fun x hx => ⟨hle (Subgroup.mem_map_of_mem φ hx), h.1 hx⟩
  have hV'2 : IsPGroup 2 ↥V' := by
    let ψ : ↥V' →* ↥V := (φ.comp V'.subtype).codRestrict V (fun x => x.2.1)
    refine hV2.of_injective ψ ?_
    intro x y hxy
    have h1 : φ (x : G) = φ (y : G) := congrArg Subtype.val hxy
    apply Subtype.ext
    have h2 : φ ((x : G) * (y : G)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hφ _ (N.mul_mem (hV'N x.2) (N.inv_mem (hV'N y.2))) h2)
  have hVP : V ≤ P.map φ := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := hVN hv
    have : n ∈ V' := ⟨hv, hn⟩
    rw [h.2.2 V' hV'N hV'2 hPV'] at this
    exact Subgroup.mem_map_of_mem φ (by simpa using this)
  exact le_antisymm hVP hle

end Transport

section Cyc4

variable {A : Type} [Group A]

theorem soc_cyc4_apply (T : Subgroup A) (hF : SocleCyc4 ↥T) {z : A} (hzT : z ∈ T)
    (hz : orderOf z = 2) {N₁ N₂ P₁ P₂ : Subgroup A} (hN₁T : N₁ ≤ T) (hN₂T : N₂ ≤ T)
    (hc₁ : N₁ ≤ Subgroup.centralizer {z}) (hc₂ : N₂ ≤ Subgroup.centralizer {z})
    (hn₁ : ∀ y ∈ T, y ∈ Subgroup.centralizer {z} → y ∈ Subgroup.normalizer (N₁ : Set A))
    (hn₂ : ∀ y ∈ T, y ∈ Subgroup.centralizer {z} → y ∈ Subgroup.normalizer (N₂ : Set A))
    (hS₁ : IsSylow2In P₁ N₁) (hS₂ : IsSylow2In P₂ N₂) (hcy₁ : IsCyclic ↥P₁)
    (hcy₂ : IsCyclic ↥P₂) (h4₁ : 4 ≤ Nat.card ↥P₁) (h4₂ : 4 ≤ Nat.card ↥P₂) :
    ∃ u ∈ P₁ ⊓ P₂, orderOf u = 4 := by
  have hz' : orderOf (⟨z, hzT⟩ : ↥T) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hcent : ∀ {N : Subgroup A}, N ≤ Subgroup.centralizer {z} →
      N.subgroupOf T ≤ Subgroup.centralizer {(⟨z, hzT⟩ : ↥T)} := by
    intro N hN n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hN (Subgroup.mem_subgroupOf.mp hn))
  have hnorm : ∀ {N : Subgroup A}, N ≤ T →
      (∀ y ∈ T, y ∈ Subgroup.centralizer {z} → y ∈ Subgroup.normalizer (N : Set A)) →
      Subgroup.centralizer {(⟨z, hzT⟩ : ↥T)} ≤ Subgroup.normalizer ((N.subgroupOf T : Subgroup ↥T) :
        Set ↥T) := by
    intro N hNT hn y hy
    have hy' : (y : A) ∈ Subgroup.centralizer {z} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      exact congrArg Subtype.val hy
    exact (mem_normalizer_subgroupOf_iff hNT).mp (hn y y.2 hy')
  have hcyc : ∀ {P : Subgroup A}, P ≤ T → IsCyclic ↥P → IsCyclic ↥(P.subgroupOf T) := fun hPT h =>
    (Subgroup.subgroupOfEquivOfLe hPT).isCyclic.mpr h
  have hcard : ∀ {P : Subgroup A}, P ≤ T → Nat.card ↥(P.subgroupOf T) = Nat.card ↥P := fun hPT =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv
  obtain ⟨u, hu, hou⟩ := hF ⟨z, hzT⟩ hz' (N₁.subgroupOf T) (N₂.subgroupOf T) (P₁.subgroupOf T)
    (P₂.subgroupOf T) (hcent hc₁) (hcent hc₂) (hnorm hN₁T hn₁) (hnorm hN₂T hn₂)
    (hS₁.subgroupOf hN₁T) (hS₂.subgroupOf hN₂T) (hcyc (hS₁.1.trans hN₁T) hcy₁)
    (hcyc (hS₂.1.trans hN₂T) hcy₂) (by rw [hcard (hS₁.1.trans hN₁T)]; exact h4₁)
    (by rw [hcard (hS₂.1.trans hN₂T)]; exact h4₂)
  exact ⟨(u : A), Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu).1, (Subgroup.mem_inf.mp hu).2⟩, by
    rw [← Subgroup.orderOf_coe] at hou; exact hou⟩

end Cyc4

section Comm2

variable {r : ℕ} {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem F2ConfigR.soc_commutator_le_of_comm2 (hc : F2ConfigR r J L L₀)
    (hF : SocleComm2 ↥(socleOf L₀)) {P : Subgroup G} (hP : IsPGroup 2 ↥P) :
    ⁅P, P⁆ ≤ L₀ ⊔ Subgroup.center G := by
  haveI := hc.normal
  have h := hF (G ⧸ Subgroup.center G) (socleOf L₀) inferInstance ⟨MulEquiv.refl _⟩
    (centralizer_socle_eq_bot hc.isComp.1 hc.centralizerEq)
    (P.map (QuotientGroup.mk' (Subgroup.center G))) (hP.map _)
  rw [← Subgroup.map_commutator] at h
  intro x hx
  obtain ⟨l, hl, hlx⟩ := h (Subgroup.mem_map_of_mem _ hx)
  have hlx' : l⁻¹ * x ∈ Subgroup.center G := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlx
    exact hlx
  have : x = l * (l⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hl hlx'

end Comm2

end CFSG.CGT.PushingUpLit.SolKNA.R4
