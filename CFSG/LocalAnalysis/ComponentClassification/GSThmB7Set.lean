module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

@[expose] def Prop62Output (h h' : Hyp52 X) (y : X) : Prop :=
  h'.a = h.a ∧ h'.J = h.J ∧ h'.B = h.B ∧ h'.K = h.K ∧
    (∃ c ∈ centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X),
      h'.S = conjugate h.S c ∧ h'.x = c⁻¹ * h.x * c) ∧
    h'.Q = h.Q ∧ h'.Q ≤ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ∧
    y ∈ normalizer (h'.Q : Set X) ∧ y ∈ h'.P ∧ y ∉ h'.T ∧ y ^ 2 ∈ h'.T ∧
    (h'.S ⊓ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ≤
        normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ⊓
          centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X) ∧
      ∃ R : Sylow 2 ↥(normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ⊓
          centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X)),
        (R : Subgroup _) =
          (h'.S ⊓ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X)).subgroupOf
            (normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ⊓
              centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X))) ∧
    h'.Lemma61Shape y

end Seven

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

theorem table517_of_ne (hT : h.Table517) (hKa : conjugate h.K h.a ≠ h.K) :
    Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2 ∧
      ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
          Nonempty (h.K ⧸ Open.fusionZStar h.K ≃* alternatingGroup (Fin n))) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (h.K ⧸ Open.fusionZStar h.K) .PSL 2 p f) := by
  rcases hT with ⟨-, hZ, ht⟩ | hT | hT | hT
  · refine ⟨hZ, ht.imp (fun ⟨n, hn, _, hK⟩ => ⟨n, hn, hK⟩) ?_⟩
    exact fun ⟨p, f, hp, hp2, hf, h5, _, hK⟩ => ⟨p, f, hp, hp2, hf, h5, hK⟩
  · obtain ⟨-, -, -, -, -, -, -, hKa', -⟩ := hT
    exact absurd hKa' hKa
  · exact absurd hT.2.1 hKa
  · obtain ⟨-, -, -, -, -, -, hKa', -⟩ := hT
    exact absurd hKa' hKa

end Hyp52

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem V_le_Lay (hS : SchreierFor Blueprint.Catalog) [IsSimpleGroup X]
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (h : Hyp52 X) (y : X) (hB0 : B0 h y ≠ ⊥) : h.V ≤ Lay h y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsch : ∀ M : Subgroup X, M ≠ ⊤ → LBalance.SchreierSections ↥M := fun M hM =>
    schreierSections_of_isKGroupCat hS (isKGroupCat_of_ne_top' hK hM)
  have hNt : ∀ A' : Subgroup X, A' ≠ ⊥ → IsPGroup 2 A' → normalizer (A' : Set X) ≠ ⊤ :=
    fun A' h1 h2 => normalizer_ne_top_of_simple hnonab h1 h2
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) h.B h.isPGroup_B
  have h2 := lBalancePLayer_centralizer_le_of_le hsch hNt h.isPGroup_B (B0 h y) inf_le_left hB0
  have h3 := h1.trans h2
  rwa [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h3

theorem mem_normalizer_T_of {h : Hyp52 X} {y : X} (hyP : y ∈ h.P)
    (hyQ : y ∈ normalizer (h.Q : Set X)) : y ∈ normalizer (h.T : Set X) := by
  have hyS : y ∈ h.S := (mem_inf.mp hyP).1
  have hyN : y ∈ normalizer (h.P : Set X) := by
    rw [mem_normalizer_iff]
    intro w
    refine ⟨fun hw => h.conj_mem_P hyS hw, fun hw => ?_⟩
    have := h.conj_mem_P (inv_mem hyS) hw
    rwa [show y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w by group] at this
  exact mem_normalizer_inf hyQ hyN

end Seven

end CFSG.ComponentClassification.GSThmB
