module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Statements

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def conjEquiv (M : Subgroup G) (g : G) : ↥M ≃* ↥(rightConjugate M g) :=
  (MulAut.conj g⁻¹).subgroupMap M

omit [Finite G] in
theorem subgroupOf_rightConjugate {M J : Subgroup G} (g : G) :
    (rightConjugate J g).subgroupOf (rightConjugate M g) =
      (J.subgroupOf M).map (conjEquiv M g).toMonoidHom := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
  have key : (((conjEquiv M g).symm ⟨y, hy⟩ : ↥M) : G) = g * y * g⁻¹ := by
    have h1 : (conjEquiv M g) ⟨g * y * g⁻¹, (mem_rightConjugate_iff M g y).1 hy⟩ = ⟨y, hy⟩ := by
      apply Subtype.ext
      show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
      group
    have h2 := (conjEquiv M g).symm_apply_apply
      ⟨g * y * g⁻¹, (mem_rightConjugate_iff M g y).1 hy⟩
    rw [h1] at h2
    exact congrArg Subtype.val h2
  rw [Subgroup.mem_subgroupOf, key]
  exact mem_rightConjugate_iff J g y

namespace CE

variable {M J : Subgroup G}

theorem transport (c : CE G M J) (g : G) :
    CE G (rightConjugate M g) (rightConjugate J g) := by
  have hmax : IsMaximalTwoLocal (rightConjugate M g) :=
    isMaximalTwoLocal_map_conj c.maxLocal g⁻¹
  have hle : rightConjugate J g ≤ rightConjugate M g := Subgroup.map_mono c.le
  exact
    { simple := c.simple
      charTwo := c.charTwo
      maxLocal := hmax
      le := hle
      subnormal := by
        have h : ((J.subgroupOf M).map (conjEquiv M g).toMonoidHom).IsSubnormal :=
          c.subnormal.map (conjEquiv M g).surjective
        rwa [← subgroupOf_rightConjugate g] at h
      block := c.block.conj g
      unique := by
        ext M'
        simp only [maximalTwoLocalsContaining, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hM', hsub⟩
          have hmax' : IsMaximalTwoLocal (rightConjugate M' g⁻¹) := by
            have := isMaximalTwoLocal_map_conj hM' g
            simpa [rightConjugate] using this
          have hJle : (J : Set G) ⊆ (rightConjugate M' g⁻¹ : Subgroup G) := by
            intro x hx
            rw [SetLike.mem_coe, mem_rightConjugate_iff]
            refine hsub ?_
            rw [SetLike.mem_coe, mem_rightConjugate_iff]
            have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
            rw [e]
            exact hx
          have hmem : rightConjugate M' g⁻¹ ∈ maximalTwoLocalsContaining (J : Set G) :=
            ⟨hmax', hJle⟩
          rw [c.unique, Set.mem_singleton_iff] at hmem
          calc M' = rightConjugate (rightConjugate M' g⁻¹) g := by
                rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
            _ = rightConjugate M g := by rw [hmem]
        · rintro rfl
          exact ⟨hmax, fun x hx => hle hx⟩
      notNormal := by
        intro hn
        apply c.notNormal
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer c.le]
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle] at hn
        intro m hm
        have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
        have h1 : g⁻¹ * m * g ∈ rightConjugate M g := by
          rw [mem_rightConjugate_iff, e]
          exact hm
        have h2 := hn h1
        rw [mem_normalizer_rightConjugate, e] at h2
        exact h2 }

end CE

omit [Finite G] in
theorem ZData.transport {J : Subgroup G} {z₀ : G} (h : ZData J z₀) (g : G) :
    ZData (rightConjugate J g) (g⁻¹ * z₀ * g) where
  mem := by
    have e : g * (g⁻¹ * z₀ * g) * g⁻¹ = z₀ := by group
    rw [mem_rightConjugate_iff, e]
    exact h.mem
  central := by
    intro j hj
    rw [mem_rightConjugate_iff] at hj
    have h1 := h.central _ hj
    calc g⁻¹ * z₀ * g * j = g⁻¹ * (z₀ * (g * j * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * j * g⁻¹) * z₀) * g := by rw [h1]
      _ = j * (g⁻¹ * z₀ * g) := by group
  sq := by
    calc g⁻¹ * z₀ * g * (g⁻¹ * z₀ * g) = g⁻¹ * (z₀ * z₀) * g := by group
      _ = 1 := by rw [h.sq]; group
  ne_one := by
    intro h1
    apply h.ne_one
    have e : g * (g⁻¹ * z₀ * g) * g⁻¹ = z₀ := by group
    rw [h1] at e
    simpa using e.symm

omit [Finite G] in
theorem TwoOrbit.transport {M J : Subgroup G} (h : TwoOrbit M J) (g : G) :
    TwoOrbit (rightConjugate M g) (rightConjugate J g) := by
  obtain ⟨J', hne, hall⟩ := h
  refine ⟨rightConjugate J' g, fun h' => hne (rightConjugate_inj'.1 h'), ?_⟩
  intro m' hm'
  rw [mem_rightConjugate_iff] at hm'
  have key : ∀ A : Subgroup G, rightConjugate (rightConjugate A g) m' =
      rightConjugate (rightConjugate A (g * m' * g⁻¹)) g := fun A => by
    rw [rightConjugate_mul, rightConjugate_mul]
    congr 1
    group
  rcases hall _ hm' with h1 | h1
  · left
    rw [key, h1]
  · right
    rw [key, h1]

end CFSG.CGT.PushingUpLit.LIT.Foote
