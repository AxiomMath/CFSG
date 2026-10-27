module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer

theorem exists_mulEquiv_prod_centralizer {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hZ : Subgroup.center N = ⊥) (hinner : ∀ φ : MulAut N, ∃ n : N, φ = MulAut.conj n) :
    ∃ ψ : G ≃* N × Subgroup.centralizer (N : Set G), ∀ p, ψ.symm p = (p.1 : G) * p.2 := by
  set C := Subgroup.centralizer (N : Set G) with hC
  have hcomm : ∀ (n : N) (c : C), Commute (N.subtype n) (C.subtype c) := fun n c =>
    (Subgroup.mem_centralizer_iff.mp c.2 n n.2)
  let f : N × C →* G := MonoidHom.noncommCoprod N.subtype C.subtype hcomm
  have hf : ∀ p : N × C, f p = (p.1 : G) * p.2 := fun _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨n, c⟩ h1
      rw [hf] at h1
      have hnc : (n : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hn : n ∈ Subgroup.center N := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        change (y : G) * n = n * y
        have hyc : (y : G) * c = c * y := Subgroup.mem_centralizer_iff.mp c.2 y y.2
        rw [hnc]
        calc (y : G) * (c : G)⁻¹ = (c : G)⁻¹ * ((c : G) * y) * (c : G)⁻¹ := by group
          _ = (c : G)⁻¹ * ((y : G) * c) * (c : G)⁻¹ := by rw [hyc]
          _ = (c : G)⁻¹ * y := by group
      rw [hZ, Subgroup.mem_bot] at hn
      have hc : c = 1 := by
        apply Subtype.ext
        have : (c : G)⁻¹ = 1 := by rw [← hnc, hn]; rfl
        rw [inv_eq_one] at this
        exact this
      rw [hn, hc]
      rfl
    · intro g
      obtain ⟨n, hn⟩ := hinner (MulAut.conjNormal g)
      have hgc : (n : G)⁻¹ * g ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : G)) hn
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h1
        calc x * ((n : G)⁻¹ * g) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * g := by group
          _ = (n : G)⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]
          _ = (n : G)⁻¹ * g * x := by group
      refine ⟨(n, ⟨(n : G)⁻¹ * g, hgc⟩), ?_⟩
      rw [hf]
      change (n : G) * ((n : G)⁻¹ * g) = g
      group
  exact ⟨(MulEquiv.ofBijective f hbij).symm, fun p => rfl⟩

variable {X : Type} [Group X]

theorem threeResidualJoin_eq_top_of_center_eq_bot {d : X} (hZ : Subgroup.center X = ⊥)
    (hW : threeResidualQuot d = ⊤) : threeResidualJoin d = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (QuotientGroup.mk x : X ⧸ Subgroup.center X) ∈ threeResidualQuot d :=
    hW ▸ Subgroup.mem_top _
  obtain ⟨w, hw, hwx⟩ := hx
  have h1 : w⁻¹ * x ∈ Subgroup.center X := QuotientGroup.eq.mp hwx
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
  rw [← h1]
  exact hw

end CFSG.GroupTheory.ThreeTranspositions
