module

public import CFSG.ClassicalInvolution.Solomon73.YamakiZRig

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

variable {G : Type*} [Group G]

private def conjOfNormalizer (T : Subgroup G) {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    ↥T ≃* ↥T where
  toFun x := ⟨n * x * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn x).mp x.2⟩
  invFun x := ⟨n⁻¹ * x * n, (Subgroup.mem_normalizer_iff''.mp hn x).mp x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conj_eq_of_mem_normalizer_of_rigid (T : Subgroup G) (θ : ↥T ≃* ↥S0) {e : G}
    (heT : e ∈ T) (hθe : θ ⟨e, heT⟩ = ⟨alpha, alpha_mem_S0⟩) {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) : n * e * n⁻¹ = e := by
  set c := conjOfNormalizer T hn
  have h := mulEquiv_S0_alpha (θ.symm.trans (c.trans θ))
  simp only [MulEquiv.trans_apply] at h
  have h1 : θ.symm ⟨alpha, alpha_mem_S0⟩ = ⟨e, heT⟩ := by
    rw [MulEquiv.symm_apply_eq]; exact hθe.symm
  rw [h1] at h
  have h2 : θ (c ⟨e, heT⟩) = θ ⟨e, heT⟩ := by rw [h, hθe]
  have h3 := θ.injective h2
  exact congrArg Subtype.val h3

theorem eq_of_maximal_in_centralizer [Finite G] (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (θ : ↥T ≃* ↥S0) {e : G} (heT : e ∈ T)
    (hθe : θ ⟨e, heT⟩ = ⟨alpha, alpha_mem_S0⟩)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {e} → T ≤ Q → Q = T) :
    T = (S : Subgroup G) := by
  by_contra hne
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  set T' : Subgroup ↥(S : Subgroup G) := T.subgroupOf (S : Subgroup G)
  have hlt : T' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    refine le_antisymm hTS fun x hx => ?_
    have : (⟨x, hx⟩ : ↥(S : Subgroup G)) ∈ T' := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hnc := (Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup G))) T' hlt
  obtain ⟨s, hsN, hsT'⟩ := SetLike.exists_of_lt hnc
  have hsN' : (s : G) ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := (Subgroup.mem_normalizer_iff.mp hsN ⟨g, hTS hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hg
      have hgS : g ∈ (S : Subgroup G) := by
        have h1 : (s : G) * g * (s : G)⁻¹ ∈ (S : Subgroup G) := hTS hg
        have h2 := (S : Subgroup G).mul_mem
          ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem s.2) h1) s.2
        have h3 : (s : G)⁻¹ * ((s : G) * g * (s : G)⁻¹) * (s : G) = g := by group
        rwa [h3] at h2
      have h1 := (Subgroup.mem_normalizer_iff.mp hsN ⟨g, hgS⟩).mpr (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp h1
  have hsC : (s : G) ∈ Subgroup.centralizer {e} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := conj_eq_of_mem_normalizer_of_rigid T θ heT hθe hsN'
    calc (s : G) * e = ((s : G) * e * (s : G)⁻¹) * (s : G) := by group
      _ = e * (s : G) := by rw [this]
  have hTC : T ≤ Subgroup.centralizer {e} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := Subgroup.mem_center_iff.mp (alpha_mem_center_S0) (θ ⟨x, hx⟩)
    have h1 : θ ⟨x, hx⟩ * θ ⟨e, heT⟩ = θ ⟨e, heT⟩ * θ ⟨x, hx⟩ := by rw [hθe]; exact hc
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (θ.injective h1)
  have hQS : T ⊔ Subgroup.zpowers (s : G) ≤ (S : Subgroup G) :=
    sup_le hTS (Subgroup.zpowers_le.mpr s.2)
  have hQp : IsPGroup 2 (T ⊔ Subgroup.zpowers (s : G) : Subgroup G) := S.isPGroup'.to_le hQS
  have hQC : T ⊔ Subgroup.zpowers (s : G) ≤ Subgroup.centralizer {e} :=
    sup_le hTC (Subgroup.zpowers_le.mpr hsC)
  have hQT := hmax _ hQp hQC le_sup_left
  have hsT : (s : G) ∈ T := by
    have : (s : G) ∈ T ⊔ Subgroup.zpowers (s : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [hQT] at this
  exact hsT' (Subgroup.mem_subgroupOf.mpr hsT)

end CFSG.ClassicalInvolution.Sp62Rec
