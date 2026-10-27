module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HS4Group
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HS4Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519.HS4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X3Aut

theorem fin_of_equiv {Γ Γ' : Type*} [Group Γ] [Group Γ'] [Finite Γ] (ψ : Γ ≃* Γ')
    (h' : ∀ P E : Subgroup Γ', IsPGroup 2 ↥P → (∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      (∀ e ∈ E, e * e = 1) → 8 ≤ Nat.card ↥E →
      4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set Γ'))) :
    ∀ P E : Subgroup Γ, IsPGroup 2 ↥P → (∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      (∀ e ∈ E, e * e = 1) → 8 ≤ Nat.card ↥E →
      4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set Γ)) := by
  intro P E hP hEn hsq h8
  have : Finite Γ' := Finite.of_equiv Γ ψ.toEquiv
  have hP' : IsPGroup 2 ↥(P.map ψ.toMonoidHom) :=
    IsPGroup.of_surjective hP (ψ.toMonoidHom.subgroupMap P) (ψ.toMonoidHom.subgroupMap_surjective P)
  have hEn' : ∀ g ∈ P.map ψ.toMonoidHom, ∀ e ∈ E.map ψ.toMonoidHom,
      g * e * g⁻¹ ∈ E.map ψ.toMonoidHom := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨g * e * g⁻¹, hEn g hg e he, by simp⟩
  have hsq' : ∀ e ∈ E.map ψ.toMonoidHom, e * e = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hsq e he, map_one]
  have h8' : 8 ≤ Nat.card ↥(E.map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact h8
  have h4 := h' _ _ hP' hEn' hsq' h8'
  have hsub : E.map ψ.toMonoidHom ⊓ Subgroup.centralizer ((P.map ψ.toMonoidHom : Subgroup Γ') :
      Set Γ') ≤ (E ⊓ Subgroup.centralizer (P : Set Γ)).map ψ.toMonoidHom := by
    rintro _ ⟨⟨z, hz, rfl⟩, hzc⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    show z ∈ Subgroup.centralizer (P : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_centralizer_iff.mp hzc (ψ g) ⟨g, hg, rfl⟩
    exact ψ.injective (by simpa using this)
  have h5 := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective ψ.injective] at h5
  omega

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G}

theorem hs4_false (h : Lv2518 N t zK) (hA6 : IsA6 N.K)
    (M2 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N i) →
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
        Nat.card ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G)))
    (hB : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G))
    (hCiK : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c ∈ Subgroup.normalizer (N.K : Set G))
    (hn : ∃ n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G), n * i ≠ i * n)
    {R0 : Subgroup G} (hR0R : R0 ≤ Rgrp2519 N i)
    (hR0norm : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G),
      c ∈ Subgroup.normalizer (N.K : Set G) → c ∈ Subgroup.normalizer (R0 : Set G))
    (hR0nc : ∀ r ∈ R0, r ≠ 1 → r ^ 2 = 1 →
      ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G)))
    (hR0exp : ∀ r ∈ Rgrp2519 N i, r * r ∈ R0)
    (hbig : 4 < Nat.card (Rgrp2519 N i)) : False := by
  obtain ⟨e⟩ := hA6
  let ψ : MulAut ↥N.K ≃* AutA6 := (MulAut.congr e).trans thetaEquiv.symm
  exact hs4_false_of_fin h (fin_of_equiv ψ fun P E hP hEn hsq h8 => fixed_ge_four hP hEn hsq h8)
    M2 hB hCiK hn hR0R hR0norm hR0nc hR0exp hbig

end Main

end CFSG.QuasithinUnique.Id2519.HS4
