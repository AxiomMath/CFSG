module

public import CFSG.LocalAnalysis.Asc75.Claim
public import CFSG.LocalAnalysis.Asc75.Fixed

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

theorem conjugate_inv_eq_map (Y : Subgroup G) (c : G) :
    conjugate Y c⁻¹ = Y.map (MulAut.conj c).toMonoidHom := by
  unfold conjugate
  rw [inv_inv]


theorem exists_conj_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (K : Subgroup G) (S : Sylow p G)
    (hSK : (S : Subgroup G) ≤ K) (W : Subgroup G) (hWK : W ≤ K) (hW : IsPGroup p W) :
    ∃ c ∈ K, W.map (MulAut.conj c).toMonoidHom ≤ S := by
  let S' : Sylow p K := S.subtype hSK
  have hW' : IsPGroup p (W.subgroupOf K) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  obtain ⟨P, hP⟩ := hW'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S'
  refine ⟨(g : G), g.property, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hwP : (⟨w, hWK hw⟩ : K) ∈ (P : Subgroup K) := hP hw
  have hmem : MulAut.conj g (⟨w, hWK hw⟩ : K) ∈ ((g • P : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hwP
  rw [hg] at hmem
  have hmem' : MulAut.conj g (⟨w, hWK hw⟩ : K) ∈ (S : Subgroup G).subgroupOf K := by
    rw [← Sylow.coe_subtype S hSK]
    exact hmem
  exact hmem'

section Unique

variable [Finite G] {S A₁ A₂ H : Subgroup G}

@[expose] noncomputable def Hyp.sylowG (h : Hyp S A₁ A₂ H) : Sylow 2 G := h.pgroup.toSylow h.odd_index

theorem Hyp.coe_sylowG (h : Hyp S A₁ A₂ H) : (h.sylowG : Subgroup G) = S := rfl

omit [Finite G] in
theorem isPGroup_conjugate {X : Subgroup G} (hX : IsPGroup 2 X) (g : G) :
    IsPGroup 2 (conjugate X g) := by
  unfold conjugate
  exact hX.map _

theorem Hyp.fixedOnly (h : Hyp S A₁ A₂ H) {X : Subgroup G} (hX : X ≤ A₁ ∨ X ≤ A₂)
    (h4 : 4 ≤ Nat.card X) : FixedOnly H X := by
  have hXS : X ≤ S := by
    rcases hX with hX | hX
    · exact hX.trans h.le₁
    · exact hX.trans h.le₂
  refine ⟨?_, fun g hg => ?_⟩
  · rcases hX with hX | hX
    · exact hX.trans h.le_H₁
    · exact hX.trans h.le_H₂
  · have hp : IsPGroup 2 (conjugate X g) := isPGroup_conjugate (h.pgroup.to_le hXS) g
    obtain ⟨c, hcH, hc⟩ := exists_conj_le_sylow (p := 2) H h.sylowG
      h.S_le_H (conjugate X g) hg hp
    have hle : conjugate X (g * c⁻¹) ≤ nU S A₁ A₂ := by
      rw [conjugate_mul, conjugate_inv_eq_map]
      intro y hy
      exact ⟨hc hy, h.S_le_stab (hc hy)⟩
    have hgc : g * c⁻¹ ∈ H := (h.claim hX h4 hle).1
    have e : g = (g * c⁻¹) * c := by group
    rw [e]
    exact H.mul_mem hgc hcH

theorem Hyp.normalizer_le_H (h : Hyp S A₁ A₂ H) {X : Subgroup G} (hX : X ≤ A₁ ∨ X ≤ A₂)
    (h4 : 4 ≤ Nat.card X) : Subgroup.normalizer (X : Set G) ≤ H :=
  (fixedOnly_iff.1 (h.fixedOnly hX h4)).2.1

end Unique

end CFSG.Asc75
