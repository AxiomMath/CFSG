module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Centralizer
public import CFSG.ClassicalInvolution.WeakCT.TwistedFrame

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

section Abstract

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem torus_agree_abstract_one (hK : 3 ≤ Nat.card K) {θ₂ : SL(3, K) →* X}
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, K)) {T A : Subgroup X}
    (hTM : T ≤ (B23 K).map θ₂) (hAT : ∀ a ∈ A, ∀ t ∈ T, a * t = t * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ (D12 K).map θ₂, a * c = c * a)
    (hT : ∀ m ∈ (B23 K).map θ₂, (∀ a ∈ A, a * m = m * a) → m ∈ T)
    (hcyc : IsCyclic T) (hcard : Nat.card T = Nat.card (diagTorus2 K)) :
    T = (D23 K).map θ₂ := by
  have hTfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have : Finite ((D23 K).map θ₂) := finite_map_subgroup _ _
  have hcard₂ : Nat.card ((D12 K).map θ₂) = Nat.card (diagTorus2 K) := by
    rw [map_D12]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₂ _ (by omega))
  have hcard₃ : Nat.card ((D23 K).map θ₂) = Nat.card (diagTorus2 K) := by
    rw [map_D23]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₂ _ (by omega))
  have hle : T ≤ (D23 K).map θ₂ := by
    refine le_of_centralizer_of_card_lt (M := (B23 K).map θ₂) (A := A) (C := (D12 K).map θ₂)
      hTM hAT hAC ?_ hT ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨m, hm, rfl⟩
      exact ⟨c * m * c⁻¹, D12_conj_mem_B23 hc hm, by simp⟩
    · rw [hcard₂]
      calc Nat.card (MulAut T) < Nat.card T := card_mulAut_lt _ (by
            rw [hcard]; exact one_lt_card_diagTorus2 hK)
        _ = Nat.card (diagTorus2 K) := hcard
    · rintro _ ⟨d, hd, rfl⟩ hd1 _ ⟨m, ⟨A', rfl⟩, rfl⟩ hdm
      obtain ⟨t, rfl⟩ := mem_D12_iff.mp hd
      have ht : t ≠ 1 := fun h => by
        subst h
        exact hd1 (by simp)
      have hA := mem_diagTorus2_of_map_commute_one h₂ ht (A := A') hdm.symm
      exact ⟨_, ⟨A', hA, rfl⟩, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₃, hcard])

theorem torus_agree_abstract (hK : 3 ≤ Nat.card K) (t : Fin 2) {θ₂ : SL(3, K) →* X}
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, K)) {T A : Subgroup X}
    (hTM : T ≤ (Bs K t).map θ₂) (hAT : ∀ a ∈ A, ∀ t' ∈ T, a * t' = t' * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ (Ds K t.rev).map θ₂, a * c = c * a)
    (hT : ∀ m ∈ (Bs K t).map θ₂, (∀ a ∈ A, a * m = m * a) → m ∈ T)
    (hcyc : IsCyclic T) (hcard : Nat.card T = Nat.card (diagTorus2 K)) :
    T = (Ds K t).map θ₂ := by
  fin_cases t
  ·
    have hker := ker_comp_mulEquiv_le_center h₂ (MulAut.conj (swapSL : SL(3, K)))
    have := torus_agree_abstract_one hK hker (T := T) (A := A)
      (by rw [show B23 K = Bs K 1 from rfl, map_flip_Bs]; exact hTM) hAT
      (by
        intro a ha c hc
        rw [show D12 K = Ds K 0 from rfl, map_flip_Ds] at hc
        exact hAC a ha c hc)
      (by rw [show B23 K = Bs K 1 from rfl, map_flip_Bs]; exact hT) hcyc hcard
    rw [show D23 K = Ds K 1 from rfl, map_flip_Ds] at this
    exact this
  · exact torus_agree_abstract_one hK h₂ hTM hAT hAC hT hcyc hcard

end Abstract

section Agree

variable {F E : Type} [Field F] [Field E] {G : Type} [Group G] {X : Type} [Group X]

theorem torus_agree_long [Finite F] (P : TwistedB2Model F E G) (hν : ∃ t, P.nu t ≠ 1)
    (hF : 3 ≤ Nat.card F) (t : Fin 2)
    {θ₁ : G →* X} {θ₂ : SL(3, F) →* X} (hl : Function.Injective (θ₁.comp P.lb))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp P.lb).range = (Bs F t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp P.sb).range, ∀ y ∈ (Bs F t.rev).map θ₂, x * y = y * x) :
    (diagTorus2 F).map (θ₁.comp P.lb) = (Ds F t).map θ₂ := by
  have hcyc : IsCyclic ((diagTorus2 F).map (θ₁.comp P.lb)) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ hl)).1 isCyclic_diagTorus2
  refine torus_agree_abstract (A := (diagTorus2 E).map (θ₁.comp P.sb)) hF t h₂ ?_ ?_ ?_ ?_ hcyc
    (Subgroup.card_map_of_injective hl)
  · rw [← hM]
    exact Subgroup.map_le_range _ _
  · rintro _ ⟨_, ⟨t', rfl⟩, rfl⟩ _ ⟨_, ⟨s, rfl⟩, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul]
    exact congrArg θ₁ (P.torus_comm s t').symm.eq
  · intro a ha c hc
    have hDB : ∀ s : Fin 2, Ds F s ≤ Bs F s := fun s => Subgroup.map_le_range _ _
    exact hcomm a (Subgroup.map_le_range _ _ ha) c (Subgroup.map_mono (hDB _) hc)
  · intro m hm hcentral
    exact P.centralizer_long hν hl (hM ▸ hm) hcentral

theorem torus_agree_short [Finite E] (P : TwistedB2Model F E G) (hμ : ∃ s, P.mu s ≠ 1)
    (hE : 3 ≤ Nat.card E) (t : Fin 2)
    {θ₁ : G →* X} {θ₂ : SL(3, E) →* X} (hs : Function.Injective (θ₁.comp P.sb))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, E))
    (hM : (θ₁.comp P.sb).range = (Bs E t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp P.lb).range, ∀ y ∈ (Bs E t.rev).map θ₂, x * y = y * x) :
    (diagTorus2 E).map (θ₁.comp P.sb) = (Ds E t).map θ₂ :=
  torus_agree_long P.swap hμ hE t hs h₂ hM hcomm

end Agree

section Frame

variable {F E : Type} [Field F] [Field E] {G : Type} [Group G] {X : Type} [Group X] {r : ℕ}
  {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r}

theorem exists_frame_of_tree_long [Finite F] (P : TwistedB2Model F E G) (hν : ∃ t, P.nu t ≠ 1)
    (hF : 4 ≤ Nat.card F)
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F W (U i) (U j))
    {θ₁ : G →* X} (hl : Function.Injective (θ₁.comp P.lb)) (hU : (θ₁.comp P.lb).range = U k₀)
    (hV : ∀ q, (adj k₀ q ∨ adj q k₀) → ∀ x ∈ (θ₁.comp P.sb).range, ∀ y ∈ U q, x * y = y * x) :
    ∃ ρ : Fin r → SL(2, F) →* X, ρ k₀ = θ₁.comp P.lb ∧
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      ∀ i j, adj i j → ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j := by
  refine exists_frame_of_tree_root hF hT hroot hcomm hpair hl hU
    (fun q hq θ hθ h0 h1 => ?_) (fun q hq θ hθ h1 h0 => ?_)
  · refine (torus_agree_long P hν (by omega) 0 hl hθ (by rw [hU, h0]) fun x hx y hy => ?_).symm
    rw [show (0 : Fin 2).rev = 1 from rfl, h1] at hy
    exact hV q (Or.inl hq) x hx y hy
  · refine (torus_agree_long P hν (by omega) 1 hl hθ (by rw [hU, h1]) fun x hx y hy => ?_).symm
    rw [show (1 : Fin 2).rev = 0 from rfl, h0] at hy
    exact hV q (Or.inr hq) x hx y hy

theorem exists_frame_of_tree_short [Finite E] (P : TwistedB2Model F E G) (hμ : ∃ s, P.mu s ≠ 1)
    (hE : 4 ≤ Nat.card E)
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair E W (U i) (U j))
    {θ₁ : G →* X} (hs : Function.Injective (θ₁.comp P.sb)) (hU : (θ₁.comp P.sb).range = U k₀)
    (hV : ∀ q, (adj k₀ q ∨ adj q k₀) → ∀ x ∈ (θ₁.comp P.lb).range, ∀ y ∈ U q, x * y = y * x) :
    ∃ ρ : Fin r → SL(2, E) →* X, ρ k₀ = θ₁.comp P.sb ∧
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      ∀ i j, adj i j → ∃ ψ : SL(3, E) →* X, ψ.comp (blk E 0) = ρ i ∧ ψ.comp (blk E 1) = ρ j :=
  exists_frame_of_tree_long P.swap hμ hE hT hroot hcomm hpair hs hU hV

end Frame

end CFSG.ClassicalInvolution.WeakCT
