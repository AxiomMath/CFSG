module

public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG.ClassicalInvolution.Q3.AE
open Wr

@[expose] def e29Sigma0 : Equiv.Perm (Fin 8) :=
  Equiv.swap 2 6 * Equiv.swap 2 4 * (Equiv.swap 3 7 * Equiv.swap 3 5)

theorem e29Sigma0_spec : (∀ s ∈ affinePlanes, s.map e29Sigma0.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma0⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 2, 4, 6} : Finset (Fin 8)), e29Sigma0 x ∈ ({0, 2, 4, 6} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 2, 4, 6} : Finset (Fin 8)), e29Sigma0 x ≠ x) ∧
    (∀ x ∈ ({1, 3, 5, 7} : Finset (Fin 8)), e29Sigma0 x ∈ ({1, 3, 5, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({1, 3, 5, 7} : Finset (Fin 8)), e29Sigma0 x ≠ x) ∧
    e29Sigma0 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma0 = 1 := by
  decide +kernel

@[expose] def e29Sigma1 : Equiv.Perm (Fin 8) :=
  Equiv.swap 1 5 * Equiv.swap 1 4 * (Equiv.swap 3 7 * Equiv.swap 3 6)

theorem e29Sigma1_spec : (∀ s ∈ affinePlanes, s.map e29Sigma1.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma1⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 1, 4, 5} : Finset (Fin 8)), e29Sigma1 x ∈ ({0, 1, 4, 5} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 1, 4, 5} : Finset (Fin 8)), e29Sigma1 x ≠ x) ∧
    (∀ x ∈ ({2, 3, 6, 7} : Finset (Fin 8)), e29Sigma1 x ∈ ({2, 3, 6, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({2, 3, 6, 7} : Finset (Fin 8)), e29Sigma1 x ≠ x) ∧
    e29Sigma1 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma1 = 1 := by
  decide +kernel

@[expose] def e29Sigma2 : Equiv.Perm (Fin 8) :=
  Equiv.swap 2 6 * Equiv.swap 2 5 * (Equiv.swap 3 7 * Equiv.swap 3 4)

theorem e29Sigma2_spec : (∀ s ∈ affinePlanes, s.map e29Sigma2.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma2⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 3, 4, 7} : Finset (Fin 8)), e29Sigma2 x ∈ ({0, 3, 4, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 3, 4, 7} : Finset (Fin 8)), e29Sigma2 x ≠ x) ∧
    (∀ x ∈ ({1, 2, 5, 6} : Finset (Fin 8)), e29Sigma2 x ∈ ({1, 2, 5, 6} : Finset (Fin 8))) ∧
    (∃ x ∈ ({1, 2, 5, 6} : Finset (Fin 8)), e29Sigma2 x ≠ x) ∧
    e29Sigma2 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma2 = 1 := by
  decide +kernel

@[expose] def e29Sigma3 : Equiv.Perm (Fin 8) :=
  Equiv.swap 1 3 * Equiv.swap 1 2 * (Equiv.swap 5 7 * Equiv.swap 5 6)

theorem e29Sigma3_spec : (∀ s ∈ affinePlanes, s.map e29Sigma3.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma3⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 1, 2, 3} : Finset (Fin 8)), e29Sigma3 x ∈ ({0, 1, 2, 3} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 1, 2, 3} : Finset (Fin 8)), e29Sigma3 x ≠ x) ∧
    (∀ x ∈ ({4, 5, 6, 7} : Finset (Fin 8)), e29Sigma3 x ∈ ({4, 5, 6, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({4, 5, 6, 7} : Finset (Fin 8)), e29Sigma3 x ≠ x) ∧
    e29Sigma3 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma3 = 1 := by
  decide +kernel

@[expose] def e29Sigma4 : Equiv.Perm (Fin 8) :=
  Equiv.swap 2 7 * Equiv.swap 2 5 * (Equiv.swap 3 6 * Equiv.swap 3 4)

theorem e29Sigma4_spec : (∀ s ∈ affinePlanes, s.map e29Sigma4.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma4⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 2, 5, 7} : Finset (Fin 8)), e29Sigma4 x ∈ ({0, 2, 5, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 2, 5, 7} : Finset (Fin 8)), e29Sigma4 x ≠ x) ∧
    (∀ x ∈ ({1, 3, 4, 6} : Finset (Fin 8)), e29Sigma4 x ∈ ({1, 3, 4, 6} : Finset (Fin 8))) ∧
    (∃ x ∈ ({1, 3, 4, 6} : Finset (Fin 8)), e29Sigma4 x ≠ x) ∧
    e29Sigma4 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma4 = 1 := by
  decide +kernel

@[expose] def e29Sigma5 : Equiv.Perm (Fin 8) :=
  Equiv.swap 1 7 * Equiv.swap 1 6 * (Equiv.swap 3 5 * Equiv.swap 3 4)

theorem e29Sigma5_spec : (∀ s ∈ affinePlanes, s.map e29Sigma5.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma5⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 1, 6, 7} : Finset (Fin 8)), e29Sigma5 x ∈ ({0, 1, 6, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 1, 6, 7} : Finset (Fin 8)), e29Sigma5 x ≠ x) ∧
    (∀ x ∈ ({2, 3, 4, 5} : Finset (Fin 8)), e29Sigma5 x ∈ ({2, 3, 4, 5} : Finset (Fin 8))) ∧
    (∃ x ∈ ({2, 3, 4, 5} : Finset (Fin 8)), e29Sigma5 x ≠ x) ∧
    e29Sigma5 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma5 = 1 := by
  decide +kernel

@[expose] def e29Sigma6 : Equiv.Perm (Fin 8) :=
  Equiv.swap 2 7 * Equiv.swap 2 4 * (Equiv.swap 3 6 * Equiv.swap 3 5)

theorem e29Sigma6_spec : (∀ s ∈ affinePlanes, s.map e29Sigma6.toEmbedding ∈ affinePlanes ∧
      s.map e29Sigma6⁻¹.toEmbedding ∈ affinePlanes) ∧
    (∀ x ∈ ({0, 3, 5, 6} : Finset (Fin 8)), e29Sigma6 x ∈ ({0, 3, 5, 6} : Finset (Fin 8))) ∧
    (∃ x ∈ ({0, 3, 5, 6} : Finset (Fin 8)), e29Sigma6 x ≠ x) ∧
    (∀ x ∈ ({1, 2, 4, 7} : Finset (Fin 8)), e29Sigma6 x ∈ ({1, 2, 4, 7} : Finset (Fin 8))) ∧
    (∃ x ∈ ({1, 2, 4, 7} : Finset (Fin 8)), e29Sigma6 x ≠ x) ∧
    e29Sigma6 ^ 3 = 1 ∧ Equiv.Perm.sign e29Sigma6 = 1 := by
  decide +kernel

theorem e29_yElt {α : Finset (Fin 8)} (hα : α ∈ CFSG.ClassicalInvolution.Q3.AE.e29Sets)
    (h : α.card = 4) :
    ∃ y ∈ CFSG.ClassicalInvolution.Q3.AE.e29Sub, y ^ 3 = 1 ∧
      y * CFSG.ClassicalInvolution.Q3.AE.zBar α h = CFSG.ClassicalInvolution.Q3.AE.zBar α h * y ∧
      (∀ b, ∀ x ∈ CFSG.ClassicalInvolution.Q3.AE.memBar α h b,
        y * x * y⁻¹ ∈ CFSG.ClassicalInvolution.Q3.AE.memBar α h b) ∧
      (∀ b, ∃ x ∈ CFSG.ClassicalInvolution.Q3.AE.memBar α h b, y * x ≠ x * y) := by
  have key : ∀ σ : Equiv.Perm (Fin 8), (∀ s ∈ affinePlanes, s.map σ.toEmbedding ∈ affinePlanes ∧
      s.map σ⁻¹.toEmbedding ∈ affinePlanes) → Equiv.Perm.sign σ = 1 →
      (∀ x ∈ α, σ x ∈ α) → σ ^ 3 = 1 → (∃ x ∈ α, σ x ≠ x) →
      ∃ y ∈ e29Sub, y ^ 3 = 1 ∧ y * zBar α h = zBar α h * y ∧
        (∀ b, ∀ x ∈ memBar α h b, y * x * y⁻¹ ∈ memBar α h b) ∧
        (∀ b, ∃ x ∈ memBar α h b, y * x ≠ x * y) := by
    intro σ hm hsg hs h3 hmv
    obtain ⟨h1, h2, h3', h4⟩ := yElt_of_perm (by norm_num) h hs h3 hmv
    exact ⟨mkQ 8 (ofPerm σ), ⟨_, ofPerm_mem_aeSubOver hm hsg, rfl⟩, h1, h2, h3', h4⟩
  have hα' : α ∈ affinePlanes := hα
  simp only [affinePlanes, List.mem_cons, List.mem_nil_iff, or_false] at hα'
  rcases hα' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma0_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma0_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma1_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma1_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma2_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma2_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma3_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma3_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma4_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma4_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma5_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma5_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, hmv, -, -, h3, hsg⟩ := e29Sigma6_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, -, -, hs, hmv, h3, hsg⟩ := e29Sigma6_spec
    exact key _ hm hsg hs h3 hmv

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
