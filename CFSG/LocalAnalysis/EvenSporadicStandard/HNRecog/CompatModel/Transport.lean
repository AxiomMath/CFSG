module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section4

theorem coe_symm_comm {G : Type} [Group G] {H : Subgroup G} (Ψ : ↥H ≃* ↥P1408) {p q : ↥P1408}
    (h : p * q = q * p) : (Ψ.symm p : G) * (Ψ.symm q : G) = (Ψ.symm q : G) * (Ψ.symm p : G) := by
  have := congrArg (fun r => (Ψ.symm r : G)) h
  simpa only [map_mul, Subgroup.coe_mul] using this

theorem invIn_Gxy_of_model {G : Type} [Group G] {x b : G} (hbx : b ∈ Gx x)
    (Ψ : ↥(Gx x) ≃* ↥P1408) (hΨx : Ψ (GxSelf x) = pA) (hΨb : Ψ ⟨b, hbx⟩ = pB) {c : ↥P1408}
    (ho : orderOf c = 2) (hc : c * pB = pB * c) (h1 : c ≠ pA) (h2 : c ≠ pB) (h3 : c ≠ pA * pB) :
    (Ψ.symm c : G) ∈ InvIn (Gxy x b) ∧ (Ψ.symm c : G) ≠ x ∧ (Ψ.symm c : G) ≠ b ∧
      (Ψ.symm c : G) ≠ x * b := by
  have hΨb' : Ψ.symm pB = ⟨b, hbx⟩ := (MulEquiv.symm_apply_eq Ψ).2 hΨb.symm
  have hcomm : (Ψ.symm c : G) * b = b * (Ψ.symm c : G) := by
    have := coe_symm_comm Ψ hc
    rwa [hΨb'] at this
  refine ⟨⟨mem_Gxy.2 ⟨(Ψ.symm c).2, mem_Gx.2 hcomm.symm⟩, ?_⟩, fun e => h1 ?_, fun e => h2 ?_,
    fun e => h3 ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ho
  · have : Ψ.symm c = GxSelf x := Subtype.ext e
    exact ((MulEquiv.symm_apply_eq Ψ).1 this).trans hΨx
  · have : Ψ.symm c = ⟨b, hbx⟩ := Subtype.ext e
    exact ((MulEquiv.symm_apply_eq Ψ).1 this).trans hΨb
  · have : Ψ.symm c = GxSelf x * ⟨b, hbx⟩ := Subtype.ext e
    rw [(MulEquiv.symm_apply_eq Ψ).1 this, map_mul, hΨx, hΨb]

theorem closure_Gxy_eq {G : Type} [Group G] {x : G} (Ψ : ↥(Gx x) ≃* ↥P1408) {c₁ c₂ : ↥P1408}
    (hcl : Subgroup.closure ((Subgroup.centralizer ({c₁} : Set ↥P1408) : Set ↥P1408) ∪
      (Subgroup.centralizer ({c₂} : Set ↥P1408) : Set ↥P1408)) = ⊤) :
    Subgroup.closure ((Gxy x (Ψ.symm c₁ : G) : Set G) ∪ (Gxy x (Ψ.symm c₂ : G) : Set G)) =
      Gx x := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (hg | hg)
    · exact (mem_Gxy.1 hg).1
    · exact (mem_Gxy.1 hg).1
  · intro g hg
    let f : ↥P1408 →* G := (Gx x).subtype.comp Ψ.symm.toMonoidHom
    have hle : Subgroup.closure ((Subgroup.centralizer ({c₁} : Set ↥P1408) : Set ↥P1408) ∪
        (Subgroup.centralizer ({c₂} : Set ↥P1408) : Set ↥P1408)) ≤
        (Subgroup.closure ((Gxy x (Ψ.symm c₁ : G) : Set G) ∪
          (Gxy x (Ψ.symm c₂ : G) : Set G))).comap f := by
      refine (Subgroup.closure_le _).2 ?_
      rintro p (hp | hp)
      · exact Subgroup.subset_closure (Or.inl (mem_Gxy.2 ⟨(Ψ.symm p).2, mem_Gx.2
          (coe_symm_comm Ψ (Subgroup.mem_centralizer_singleton_iff.1 hp).symm)⟩))
      · exact Subgroup.subset_closure (Or.inr (mem_Gxy.2 ⟨(Ψ.symm p).2, mem_Gx.2
          (coe_symm_comm Ψ (Subgroup.mem_centralizer_singleton_iff.1 hp).symm)⟩))
    have hmem : Ψ ⟨g, hg⟩ ∈ Subgroup.closure ((Subgroup.centralizer ({c₁} : Set ↥P1408) :
        Set ↥P1408) ∪ (Subgroup.centralizer ({c₂} : Set ↥P1408) : Set ↥P1408)) := by
      rw [hcl]
      exact Subgroup.mem_top _
    have h2 := hle hmem
    simpa [f] using h2

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
