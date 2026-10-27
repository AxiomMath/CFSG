module

public import CFSG.GH74.GLS.C3.Layer1.EvenMax
public import CFSG.GH74.GLS.C3.Layer2.L5C20

public section

open Subgroup CFSG

namespace CFSG.GH74.GLS

theorem isConj_mulEquiv_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a b : A) :
    IsConj (e a) (e b) ↔ IsConj a b := by
  rw [isConj_iff, isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    apply e.injective
    simpa using hc
  · rintro ⟨c, hc⟩
    refine ⟨e c, ?_⟩
    rw [← hc]
    simp

theorem centralizer_singleton_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nonempty (↥(centralizer ({a} : Set A)) ≃* ↥(centralizer ({e a} : Set B))) := by
  have h : (centralizer ({a} : Set A)).map e.toMonoidHom = centralizer ({e a} : Set B) := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hc' : c ∈ centralizer ({a} : Set A) := hc
      rw [mem_centralizer_singleton_iff] at hc'
      rw [MulEquiv.coe_toMonoidHom, mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
    · intro hb
      refine ⟨e.symm b, ?_, by simp⟩
      show e.symm b ∈ centralizer ({a} : Set A)
      rw [mem_centralizer_singleton_iff] at hb ⊢
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hb
  exact ⟨(MulEquiv.subgroupMap e (centralizer ({a} : Set A))).trans (MulEquiv.subgroupCongr h)⟩

theorem SameCentralizerOfInvolutionPattern.of_mulEquiv {G A B : Type*} [Group G] [Finite G]
    [Group A] [Finite A] [Group B] [Finite B] (h : SameCentralizerOfInvolutionPattern G A)
    (e : A ≃* B) : SameCentralizerOfInvolutionPattern G B := by
  obtain ⟨S, S', φ, hconj, hcent⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  let S'' : Sylow 2 B := S'.mapSurjective hsurj
  have hS'' : (S'' : Subgroup B) = (S' : Subgroup A).map e.toMonoidHom :=
    Sylow.coe_mapSurjective hsurj S'
  let ψ : ↥(S' : Subgroup A) ≃* ↥(S'' : Subgroup B) :=
    (MulEquiv.subgroupMap e (S' : Subgroup A)).trans (MulEquiv.subgroupCongr hS''.symm)
  have hψ : ∀ s : ↥(S' : Subgroup A), ((ψ s : ↥(S'' : Subgroup B)) : B) = e (s : A) := fun s => rfl
  refine ⟨S, S'', φ.trans ψ, ?_, ?_⟩
  · intro u v hu hv
    have h1 := hconj u v hu hv
    have : ((φ.trans ψ) u : B) = e ((φ u : ↥(S' : Subgroup A)) : A) := rfl
    have h2 : ((φ.trans ψ) v : B) = e ((φ v : ↥(S' : Subgroup A)) : A) := rfl
    rw [this, h2, isConj_mulEquiv_iff]
    exact h1
  · intro u hu
    obtain ⟨c⟩ := hcent u hu
    obtain ⟨d⟩ := centralizer_singleton_mulEquiv e ((φ u : ↥(S' : Subgroup A)) : A)
    exact ⟨c.trans d⟩


@[expose] def B_even_alt_config : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q N : Subgroup G), EvenSel x K T Q → IsStandardSubgroup K →
      gammaK 2 Q 1 ≤ normalizer (K : Set G) → normalizer (K : Set G) < N → N ≠ ⊤ →
      ∀ n ∈ ({5, 6} : Finset ℕ), Nonempty (↥K ≃* alternatingGroup (Fin n)) →
        Nonempty (↥N ≃* alternatingGroup (Fin (n + 4))) →
        ∃ (S : Subgroup G) (a : G), IsAConfig n x K T Q S a

theorem b_even_N_alt_of_config
    (h : B_even_alt_config) : B_even_N_alt := by
  intro G _ _ hG hE hV x K T Q N hs hstd hgam hMN hN n hn hKn hNn
  obtain ⟨S, a, hcfg⟩ := h G hG hE hV x K T Q N hs hstd hgam hMN hN n hn hKn hNn
  have hn' : n ∈ ({5, 6, 7} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn ⊢
    omega
  have hA := s_layerII_proved G hG n hn' ⟨x, K, T, Q, S, a, hcfg⟩
  obtain ⟨e⟩ := hNn
  exact hA.1.of_mulEquiv e.symm

end CFSG.GH74.GLS
