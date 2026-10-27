module

public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Kit

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem isComponentOf_centralizer_of_glaPComponent {X : Type} [Group X] {K J : Subgroup X}
    {a : X} (hK : CFSG.Open.IsComponentOf K ⊤)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hq : CFSG.Open.IsQuasisimple ↥J) :
    CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set X)) := by
  have h1 : CFSG.Open.IsSubnormal (K ⊓ Subgroup.centralizer ({a} : Set X))
      (Subgroup.centralizer ({a} : Set X)) := by
    have := CFSG.Open.IsSubnormal.inf hK.2.1 (Subgroup.centralizer ({a} : Set X))
    rwa [top_inf_eq] at this
  exact ⟨hJ.1.trans inf_le_right, hJ.2.1.trans h1, hq⟩

theorem gLBConj_mul {X : Type*} [Group X] (g h : X) (H : Subgroup X) :
    GLBConj (g * h) H = GLBConj h (GLBConj g H) := by
  ext x
  simp only [mem_gLBConj]
  have : g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ := by group
  rw [this]

theorem gLBConj_one' {X : Type*} [Group X] (H : Subgroup X) : GLBConj 1 H = H := by
  ext x
  simp [mem_gLBConj]

theorem glaPComponent_gLBConj_centralizer {X : Type*} [Group X] [Finite X] {K J : Subgroup X}
    {a b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) (hba : b * a = a * b)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) (GLBConj b J) := by
  have h := glaPComponent_gLBConj hJ b
  have heq : GLBConj b (K ⊓ Subgroup.centralizer ({a} : Set X)) =
      K ⊓ Subgroup.centralizer ({a} : Set X) := by
    ext x
    rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    have hK : b * x * b⁻¹ ∈ K ↔ x ∈ K := (Subgroup.mem_normalizer_iff.1 hb x).symm
    rw [hK]
    refine and_congr_right fun _ => ?_
    have hba' : b⁻¹ * a = a * b⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * a) * b⁻¹ := by rw [hba]
        _ = a * b⁻¹ := by group
    constructor
    · intro hx
      have h1 : b * (x * a) * b⁻¹ = b * (a * x) * b⁻¹ := by
        calc b * (x * a) * b⁻¹ = (b * x * b⁻¹) * a := by
              calc b * (x * a) * b⁻¹ = b * x * (a * b⁻¹) := by group
                _ = b * x * (b⁻¹ * a) := by rw [hba']
                _ = (b * x * b⁻¹) * a := by group
          _ = a * (b * x * b⁻¹) := hx
          _ = b * (a * x) * b⁻¹ := by
              calc a * (b * x * b⁻¹) = (a * b) * x * b⁻¹ := by group
                _ = (b * a) * x * b⁻¹ := by rw [hba]
                _ = b * (a * x) * b⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h1)
    · intro hx
      calc (b * x * b⁻¹) * a = b * (x * a) * b⁻¹ := by
            calc (b * x * b⁻¹) * a = b * x * (b⁻¹ * a) := by group
              _ = b * x * (a * b⁻¹) := by rw [hba']
              _ = b * (x * a) * b⁻¹ := by group
        _ = b * (a * x) * b⁻¹ := by rw [hx]
        _ = a * (b * x * b⁻¹) := by
            calc b * (a * x) * b⁻¹ = (b * a) * x * b⁻¹ := by group
              _ = (a * b) * x * b⁻¹ := by rw [hba]
              _ = a * (b * x * b⁻¹) := by group
  rwa [heq] at h

theorem mem_normalizer_of_card_le_two {X : Type*} [Group X] {B : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian 3 B) {𝒥 : Set (Subgroup X)}
    (h3 : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∀ J₃ ∈ 𝒥, J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃)
    (hst : ∀ b ∈ B, ∀ J ∈ 𝒥, GLBConj b J ∈ 𝒥) {b : X} (hb : b ∈ B) {J : Subgroup X}
    (hJ : J ∈ 𝒥) : b ∈ Subgroup.normalizer (J : Set X) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have hb3 : b * b * b = 1 := by
    have := hB.2 b hb
    rw [pow_three'] at this
    exact this
  by_contra hne
  have hJ1 : GLBConj b J ∈ 𝒥 := hst b hb J hJ
  have hJ2 : GLBConj b (GLBConj b J) ∈ 𝒥 := hst b hb _ hJ1
  have hb3' : b * (b * b) = 1 := by rw [← mul_assoc]; exact hb3
  have h111 : GLBConj b (GLBConj b (GLBConj b J)) = J := by
    rw [← gLBConj_mul, ← gLBConj_mul, hb3', gLBConj_one']
  rcases h3 J hJ _ hJ1 _ hJ2 with h | h | h
  · exact hne h.symm
  · apply hne
    calc GLBConj b J = GLBConj b (GLBConj b (GLBConj b J)) := congrArg (GLBConj b) h
      _ = J := h111
  · apply hne
    calc GLBConj b J = GLBConj b (GLBConj b J) := h
      _ = GLBConj b (GLBConj b (GLBConj b J)) := congrArg (GLBConj b) h
      _ = J := h111

theorem isStronglyLocallyOneBalanced_of_centralizes {X : Type*} [Group X] {p : ℕ}
    {B J : Subgroup X} {b : X}
    (h : ∀ S : Subgroup X,
      S ≤ Subgroup.normalizer (J : Set X) ⊓ Subgroup.centralizer ({b} : Set X) →
      Nat.Coprime p (Nat.card S) →
        B ⊓ Subgroup.normalizer (J : Set X) ≤ Subgroup.normalizer (S : Set X) →
          S ≤ Subgroup.centralizer (J : Set X)) :
    IsStronglyLocallyOneBalanced p B b J := by
  intro S hS hcop hBS
  refine Subgroup.commutator_le.2 (fun x hx s hs => ?_)
  have hcomm : x * s = s * x := Subgroup.mem_centralizer_iff.1 (h S hS hcop hBS hs) x hx
  rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
  exact Subgroup.one_mem _

end KSF4Kit

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
