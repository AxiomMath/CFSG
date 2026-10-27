module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4StrongFinal

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] (Q : Subgroup G) (g : G)
    (h : Q.map (MulAut.conj g).toMonoidHom = Q) : g ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  conv_rhs => rw [← h]
  rw [Subgroup.mem_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := (MulAut.conj g).injective hyx
    rwa [← this]

theorem card_map_conj {G : Type*} [Group G] (Q : Subgroup G) (g : G) :
    Nat.card (Q.map (MulAut.conj g).toMonoidHom) = Nat.card Q :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_map_conj_iff_J4 {G : Type*} [Group G] (Q : Subgroup G) (g w : G) :
    w ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ Q := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ * (g * y * g⁻¹) * g ∈ Q
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]; exact hy
  · intro h
    exact ⟨_, h, by show g * (g⁻¹ * w * g) * g⁻¹ = w; group⟩


theorem TI_Q11 (g : J) (hg : g ∉ Subgroup.normalizer (Q11 : Set J)) :
    (Q11 : Subgroup J) ⊓ Q11.map (MulAut.conj g).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwQ, hwQ'⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  have hcard : Nat.card (Q11.map (MulAut.conj g).toMonoidHom) = 11 ^ 3 := by
    rw [@card_map_conj J (Subgroup.toGroup J) Q11 g, card_Q11]
  by_cases hwz : w ∈ Subgroup.zpowers qz
  ·
    have hy := (@mem_map_conj_iff_J4 J (Subgroup.toGroup J) Q11 g w).1 hwQ'
    by_cases hyz : g⁻¹ * w * g ∈ Subgroup.zpowers qz
    · have hy1 : g⁻¹ * w * g ≠ 1 := by
        intro h1
        apply hw1
        have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        rw [this, h1]; group
      have h1 := @zpowers_eq_of_mem_of_ne_one J (Subgroup.toGroup J) _ _ _ orderOf_qz hyz hy1
      have h2 := @zpowers_eq_of_mem_of_ne_one J (Subgroup.toGroup J) _ _ _ orderOf_qz hwz hw1
      apply hg
      have hnorm : g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers qz : Subgroup J) : Set J) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have e : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by group
        rw [e]
        have := @mem_zpowers_conj_iff J (Subgroup.toGroup J) g (g⁻¹ * w * g) x
        rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at this
        rwa [h2, h1] at this
      have := inv_mem hnorm
      rw [inv_inv] at this
      rw [← normalizer_zpowers_qz_eq_J4]
      exact this
    · have h12 := fixDim_of_mem_Q11 card_centralizer_qx_le hy hyz
      have h2 := fixDim_of_mem_zpowers_qz hwz hw1
      have := fixDim_conj g (g⁻¹ * w * g)
      rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at this
      omega
  · have hQ'Q := eq_Q11_of_mem card_centralizer_qx_le _ hcard hwQ hwz hwQ'
    exact hg (@mem_normalizer_of_map_conj_eq J (Subgroup.toGroup J) Q11 g hQ'Q)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
