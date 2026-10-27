module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Cover
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup

theorem cover_unique_sub {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (ρ : ↥K →* Equiv.Perm (Fin 11)) (hrange : ρ.range ≤ alternatingGroup (Fin 11))
    (hker : ρ.ker ≤ Subgroup.center ↥K) (hker2 : Nat.card ρ.ker = 2)
    {A : Subgroup X} (hAK : A ≤ K) (hA : Nat.card ↥A = 2 ^ 8)
    {W W' : Subgroup X} (hWK : W ≤ K) (hW'K : W' ≤ K)
    (hW : IsPGroup 3 ↥W) (hW' : IsPGroup 3 ↥W') (h1 : W ≠ ⊥) (h1' : W' ≠ ⊥)
    (hn : A ≤ Subgroup.normalizer (W : Set X)) (hn' : A ≤ Subgroup.normalizer (W' : Set X)) :
    W = W' ∧ Nat.card ↥W = 3 := by
  have hbot : ∀ {U : Subgroup X}, U ≤ K → U ≠ ⊥ → U.subgroupOf K ≠ ⊥ := by
    intro U hU hne h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hU, h, Subgroup.map_bot]
  have hnorm : ∀ {U : Subgroup X}, A ≤ normalizer (U : Set X) →
      A.subgroupOf K ≤ normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    intro U hU s hs
    rw [mem_normalizer_iff]
    intro w
    have hs' : (s : X) ∈ normalizer (U : Set X) := hU (Subgroup.mem_subgroupOf.1 hs)
    have := mem_normalizer_iff.1 hs' (w : X)
    simpa [Subgroup.mem_subgroupOf] using this
  have hAc : Nat.card ↥(A.subgroupOf K) = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA]
  obtain ⟨hWW, hW3⟩ := cover_unique ρ hrange hker hker2 hAc (hW.comap_subtype (K := K))
    (hW'.comap_subtype (K := K)) (hbot hWK h1) (hbot hW'K h1') (hnorm hn) (hnorm hn')
  refine ⟨?_, ?_⟩
  · have := Subgroup.subgroupOf_inj.1 hWW
    rwa [inf_of_le_left hWK, inf_of_le_left hW'K] at this
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv]
    exact hW3

theorem ly_centralizer_cover_unique
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Ly))
    {τ : X} (hτ : orderOf τ = 2)
    {A : Subgroup X} (hAK : A ≤ Subgroup.centralizer ({τ} : Set X)) (hA : Nat.card ↥A = 2 ^ 8)
    {W W' : Subgroup X} (hWK : W ≤ Subgroup.centralizer ({τ} : Set X))
    (hW'K : W' ≤ Subgroup.centralizer ({τ} : Set X))
    (hW : IsPGroup 3 ↥W) (hW' : IsPGroup 3 ↥W') (h1 : W ≠ ⊥) (h1' : W' ≠ ⊥)
    (hn : A ≤ Subgroup.normalizer (W : Set X)) (hn' : A ≤ Subgroup.normalizer (W' : Set X)) :
    W = W' ∧ Nat.card ↥W = 3 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple hX τ hτ
  let ρ : ↥(Subgroup.centralizer ({τ} : Set X)) →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp
      (e.toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center ↥(Subgroup.centralizer ({τ} : Set X)))))
  have hker : ρ.ker = Subgroup.center ↥(Subgroup.centralizer ({τ} : Set X)) := by
    ext x
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← Subgroup.coe_one, Subtype.coe_inj, MulEquiv.coe_toMonoidHom, e.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hrange : ρ.range ≤ alternatingGroup (Fin 11) := by
    rintro _ ⟨x, rfl⟩
    exact (e (QuotientGroup.mk' _ x)).2
  exact cover_unique_sub ρ hrange hker.le (by rw [hker]; exact hc) hAK hA hWK hW'K hW hW' h1 h1'
    hn hn'

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
