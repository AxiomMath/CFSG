module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Nrm
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2V8

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Max

open CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2I301
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed
  CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Nrm CFSG.LocalAnalysis.GLTheoremA.H301B.Co2V8
open CFSG.Sporadic.Co2Schreier hiding dP

theorem mem_zpowers_of_qπ_eq_zero
    (x : locQ.subgroupOf locC) (h : qπ x = 0) :
    ((x : locC) : Equiv.Perm (Fin 2300)) ∈ Subgroup.zpowers locZ := by
  rw [qπ_eq_zero_iff, center_qc] at h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [← hn]
  exact (map_zpow (locC.subtype.comp (locQ.subgroupOf locC).subtype) zQc n).symm

theorem locQ_le_of_normalized
    {T : Subgroup (Equiv.Perm (Fin 2300))} (hTQ : T ≤ locQ)
    (hz : ∃ t ∈ T, t ∉ Subgroup.zpowers locZ) (hzT : Subgroup.zpowers locZ ≤ T)
    (c₁ c₂ c₃ : locC) (h₁ : (c₁ : Equiv.Perm (Fin 2300)) = k1P)
    (h₂ : (c₂ : Equiv.Perm (Fin 2300)) = k2P) (h₃ : (c₃ : Equiv.Perm (Fin 2300)) = dP)
    (n₁ : ∀ t ∈ T, (c₁ : Equiv.Perm (Fin 2300)) * t * (c₁ : Equiv.Perm (Fin 2300))⁻¹ ∈ T)
    (n₂ : ∀ t ∈ T, (c₂ : Equiv.Perm (Fin 2300)) * t * (c₂ : Equiv.Perm (Fin 2300))⁻¹ ∈ T)
    (n₃ : ∀ t ∈ T, (c₃ : Equiv.Perm (Fin 2300)) * t * (c₃ : Equiv.Perm (Fin 2300))⁻¹ ∈ T) :
    locQ ≤ T := by
  let W : Submodule (ZMod 2) QV :=
    { carrier := {v | ∃ x : locQ.subgroupOf locC,
        ((x : locC) : Equiv.Perm (Fin 2300)) ∈ T ∧ qπ x = v}
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, T.mul_mem hx hy, qπ_mul x y⟩
      zero_mem' := ⟨1, T.one_mem, qπ_one⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · rw [zero_smul]
          exact ⟨1, T.one_mem, qπ_one⟩
        · rw [one_smul]
          exact ⟨x, hx, rfl⟩ }
  have inv : ∀ c : locC,
      (∀ t ∈ T, (c : Equiv.Perm (Fin 2300)) * t * (c : Equiv.Perm (Fin 2300))⁻¹ ∈ T) →
      ∀ w ∈ W, conjEnd (Q := locQ.subgroupOf locC) c w ∈ W := by
    rintro c hc _ ⟨x, hx, rfl⟩
    refine ⟨MulAut.conjNormal c x, ?_, (conjEnd_qπ c x).symm⟩
    rw [coe_conjNormal_qc]
    exact hc _ hx
  have hW : W ≠ ⊥ := by
    obtain ⟨t, htT, htz⟩ := hz
    intro hbot
    have hmem : qπ (toQc t (hTQ htT)) ∈ W := ⟨toQc t (hTQ htT), htT, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact htz (mem_zpowers_of_qπ_eq_zero _ hmem)
  have htop : W = ⊤ := (v8_irreducible c₁ c₂ c₃ h₁ h₂ h₃ W (inv c₁ n₁) (inv c₂ n₂)
    (inv c₃ n₃)).resolve_left hW
  intro g hg
  obtain ⟨x, hx, hqx⟩ : qπ (toQc g hg) ∈ W := htop ▸ Submodule.mem_top
  have h0 : qπ (x⁻¹ * toQc g hg) = 0 := by
    rw [qπ_mul, qπ_inv, hqx, neg_add_cancel]
  have hz' := hzT (mem_zpowers_of_qπ_eq_zero _ h0)
  have hg' : g = ((x : locC) : Equiv.Perm (Fin 2300)) *
      (((x⁻¹ * toQc g hg : locQ.subgroupOf locC) : locC) : Equiv.Perm (Fin 2300)) := by
    change g = ((x : locC) : Equiv.Perm (Fin 2300)) * (((x : locC) : Equiv.Perm (Fin 2300))⁻¹ * g)
    group
  rw [hg']
  exact T.mul_mem hx hz'

theorem eq_locQ_of_gt_locZ
    (R : Subgroup (Equiv.Perm (Fin 2300))) (hRP : R ≤ co2P) (hR : IsPGroup 2 R)
    (hlt : Subgroup.zpowers locZ < R)
    (h1 : k1P ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 2300))))
    (h2 : k2P ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 2300))))
    (h3 : dP ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 2300)))) : R = locQ := by
  have hg := gens_mem_locC
  have hnT : ∀ c ∈ locC, c ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 2300))) →
      ∀ t ∈ R ⊓ locC, c * t * c⁻¹ ∈ R ⊓ locC := by
    intro c hc hcR t ht
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hcR t).1 (Subgroup.mem_inf.1 ht).1,
      locC.mul_mem (locC.mul_mem hc (Subgroup.mem_inf.1 ht).2) (locC.inv_mem hc)⟩
  have nT : ∀ c ∈ locC, c ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 2300))) →
      c ∈ Subgroup.normalizer ((R ⊓ locC : Subgroup (Equiv.Perm (Fin 2300))) :
        Set (Equiv.Perm (Fin 2300))) := by
    intro c hc hcR
    rw [Subgroup.mem_normalizer_iff]
    refine fun t => ⟨hnT c hc hcR t, fun ht => ?_⟩
    simpa [mul_assoc] using hnT c⁻¹ (locC.inv_mem hc) (Subgroup.inv_mem _ hcR) _ ht
  have hTq : R ⊓ locC ≤ locQ := le_locQ_of_normalized inf_le_right hR.to_inf_left
    (nT _ hg.2.2.2.2.1 h1) (nT _ hg.2.2.2.2.2 h2) (nT _ hg.1 h3)
  obtain ⟨x, hxR, hxC, hxz⟩ := exists_mem_locC_of_gt_locZ hRP hR hlt
  have hzT : Subgroup.zpowers locZ ≤ R ⊓ locC := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hlt.le (Subgroup.mem_zpowers _), locQ_le_C locZ_mem_Q⟩
  have hQT : locQ ≤ R ⊓ locC := locQ_le_of_normalized hTq ⟨x, Subgroup.mem_inf.2 ⟨hxR, hxC⟩, hxz⟩
    hzT ⟨k1P, hg.2.2.2.2.1⟩ ⟨k2P, hg.2.2.2.2.2⟩ ⟨dP, hg.1⟩ rfl rfl rfl (hnT _ hg.2.2.2.2.1 h1)
    (hnT _ hg.2.2.2.2.2 h2) (hnT _ hg.1 h3)
  have hQR : locQ ≤ R := hQT.trans inf_le_left
  refine le_antisymm (fun r hr => ?_) hQR
  by_contra hrQ
  obtain ⟨y, hyR, hyC, hyQ⟩ := exists_mem_locC_of_not_le_locQ hRP hR hQR fun h => hrQ (h hr)
  exact hyQ (hTq (Subgroup.mem_inf.2 ⟨hyR, hyC⟩))

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Max

end
