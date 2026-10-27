module

public import CFSG.GH74.GLS.LU.Local.Main
public import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

structure LUModelData (Gs : Type) [Group Gs] (q : ℕ) (ε : ℤ) (z' : Gs) (S' : Sylow 2 Gs)
    (E₁ E₂ : Subgroup Gs) (t' u' : Gs) : Prop where
  comps : LUComps Gs q z' E₁ E₂
  syl : LUSyl Gs z' S' E₁ E₂ t' u'
  eps : ε = 1 ∨ ε = -1
  mod8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8])
  A0_dvd : ((Nat.card ↥(pPrimeCore 2 ↥(Cz z')) : ℕ) : ℤ) ∣ (q : ℤ) - ε
  H_cyc : IsCyclic ↥(E₁ ⊓ centralizer ({u'} : Set Gs))
  H_card : (Nat.card ↥(E₁ ⊓ centralizer ({u'} : Set Gs)) : ℤ) = (q : ℤ) - ε

@[expose] def LUModelLeaf : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (S' : Sylow 2 Gs) (z' : Gs),
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
      ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) →
        ∃ (E₁ E₂ : Subgroup Gs) (t' u' : Gs), LUModelData Gs (p ^ f) 1 z' S' E₁ E₂ t' u') ∧
      ((p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f) →
        ∃ (E₁ E₂ : Subgroup Gs) (t' u' : Gs), LUModelData Gs (p ^ f) (-1) z' S' E₁ E₂ t' u')

section FromModel

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

theorem pull_inf_centralizer (ψ : ↥(layerTimesSylow z (S : Subgroup G)) ≃*
      ↥(layerTimesSylow z' (S' : Subgroup Gs))) (E : Subgroup Gs) {u : G}
    (hu : u ∈ layerTimesSylow z (S : Subgroup G)) {u' : Gs}
    (hψu : ((ψ ⟨u, hu⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = u') :
    pull ψ (E ⊓ centralizer ({u'} : Set Gs)) = pull ψ E ⊓ centralizer ({u} : Set G) := by
  ext x
  constructor
  · intro h
    have hx := pull_le ψ _ h
    have h' := (mem_pull ψ _ hx).mp h
    refine ⟨(mem_pull ψ _ hx).mpr h'.1, ?_⟩
    show x ∈ centralizer ({u} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h2 : ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) * u' =
        u' * ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) :=
      mem_centralizer_singleton_iff.mp h'.2
    rw [← hψu] at h2
    have h3 := (psi_eq_iff ψ (Subgroup.mul_mem _ hx hu) (Subgroup.mul_mem _ hu hx)).mp
      (by rw [psi_mul ψ hx hu, psi_mul ψ hu hx]; exact h2)
    exact h3
  · rintro ⟨h1, h2⟩
    have hx := pull_le ψ _ h1
    refine (mem_pull ψ _ hx).mpr ⟨(mem_pull ψ _ hx).mp h1, ?_⟩
    show ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
      centralizer ({u'} : Set Gs)
    rw [mem_centralizer_singleton_iff]
    have h3 : x * u = u * x := mem_centralizer_singleton_iff.mp h2
    have h4 : ((ψ ⟨x * u, Subgroup.mul_mem _ hx hu⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs)
        = ((ψ ⟨u * x, Subgroup.mul_mem _ hu hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) :=
      (psi_eq_iff ψ _ _).mpr h3
    rw [psi_mul ψ hx hu, psi_mul ψ hu hx, hψu] at h4
    exact h4

theorem setup_of_model [Finite G] [Finite Gs] {q : ℕ} {ε : ℤ} (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    (hA : IsCyclic ↥(pPrimeCore 2 ↥(Cz z)) ∧
      Nat.card ↥(pPrimeCore 2 ↥(Cz z)) ∣ Nat.card ↥(pPrimeCore 2 ↥(Cz z')))
    {E₁ E₂ : Subgroup Gs} {t' u' : Gs} (d : LUModelData Gs q ε z' S' E₁ E₂ t' u') :
    ∃ (K₁ K₂ : Subgroup G) (t u : G), LUComps G q z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧
      LUEps G q ε z K₁ u := by
  set ψ := I.ψ with hψ
  have hA0e : ↥(pPrimeCore 2 ↥(Cz z)) ≃* ↥(A0 z) :=
    (pPrimeCore 2 ↥(Cz z)).equivMapOfInjective (Cz z).subtype (Cz z).subtype_injective
  have hcyc : IsCyclic ↥(A0 z) := by
    have := hA.1
    exact isCyclic_of_surjective hA0e.toMonoidHom hA0e.surjective
  have hcomps := LUComps.transport I hz hz' hcyc d.comps d.syl.z_inv
  obtain ⟨t, u, ht, hu, hψt, hψu, hsyl⟩ := LUSyl.transport I hz hz' d.comps d.syl
  have hE₁ : E₁ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn d.comps.comp₁).trans le_sup_left
  have hHle : E₁ ⊓ centralizer ({u'} : Set Gs) ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    inf_le_left.trans hE₁
  have hH := pull_inf_centralizer ψ E₁ hu hψu
  refine ⟨pull ψ E₁, pull ψ E₂, t, u, hcomps, hsyl, ?_⟩
  refine ⟨d.eps, d.mod8, hcyc, ?_, ?_, ?_⟩
  · have h1 : Nat.card ↥(A0 z) = Nat.card ↥(pPrimeCore 2 ↥(Cz z)) :=
      (Nat.card_congr hA0e.toEquiv).symm
    rw [h1]
    exact (Int.natCast_dvd_natCast.mpr hA.2).trans d.A0_dvd
  · rw [← hH]
    have := d.H_cyc
    exact isCyclic_of_surjective (pullEquiv ψ hHle).symm.toMonoidHom (pullEquiv ψ hHle).symm.surjective
  · rw [← hH, card_pull ψ hHle]
    exact d.H_card

end FromModel

theorem luSetupLeaf_of_model
    (hM : LUModelLeaf) : LUSetupLeaf := by
  intro G _ _ hG Gs _ hcompat p f hp hp2 hq
  obtain ⟨-, S, z, S', z', hz, hz', ⟨ψ, hψS, hψfus⟩, -, hAcyc⟩ := hcompat
  let I : CompatIso G z S z' S' := ⟨ψ, hψS, hψfus⟩
  constructor
  · rintro ⟨h8, hL⟩
    have : Finite Gs := (CFSG.LieType.Catalog.lieModel_finite_simple Gs _ 4 p f hL).1
    obtain ⟨E₁, E₂, t', u', d⟩ := (hM Gs p f hp hp2 hq S' z' hz').1 ⟨h8, hL⟩
    obtain ⟨K₁, K₂, t, u, hc, hs, he⟩ :=
      setup_of_model I hz hz' (hAcyc ⟨p, f, hp, hp2, Or.inl hL⟩) d
    exact ⟨z, S, K₁, K₂, t, u, hc, hs, he⟩
  · rintro ⟨h8, hU⟩
    have : Finite Gs := (CFSG.LieType.Catalog.lieModel_finite_simple Gs _ 4 p f hU).1
    obtain ⟨E₁, E₂, t', u', d⟩ := (hM Gs p f hp hp2 hq S' z' hz').2 ⟨h8, hU⟩
    obtain ⟨K₁, K₂, t, u, hc, hs, he⟩ :=
      setup_of_model I hz hz' (hAcyc ⟨p, f, hp, hp2, Or.inr hU⟩) d
    exact ⟨z, S, K₁, K₂, t, u, hc, hs, he⟩

theorem luNeighborhood_of_model
    (hM : LUModelLeaf) (hT1 : LULocalLeaf) (h6A : LUMax6A) :
    LUNeighborhood :=
  luNeighborhood_of_6A (luSetupLeaf_of_model hM) hT1 h6A

end CFSG.GH74.GLS.LU.Local
