module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSix

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Equiv

namespace Unc25K1.A6Model

theorem key_of_iso
    {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 6)) (P X : Subgroup K)
    (hPc : Nat.card P = 8) (hPX : P ≤ X) (hXP : X ≠ P) (hXtop : X ≠ ⊤) (γ : MulAut K)
    (τ : Perm (Fin 6))
    (hγ : ∀ k : K, ((e (γ k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      τ * ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) * τ⁻¹)
    (hγP : ∀ k : K, k ∈ P ↔ γ k ∈ P) : ∀ k : K, k ∈ X ↔ γ k ∈ X := by
  let f : K →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfk : ∀ k, f k = ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) := fun k => rfl
  have hmemmap : ∀ (Y : Subgroup K) (k : K), f k ∈ Y.map f ↔ k ∈ Y := fun Y k =>
    Subgroup.mem_map_iff_mem hf
  have hfγ : ∀ k, f (γ k) = τ * f k * τ⁻¹ := fun k => hγ k
  have hτ : ∀ p, p ∈ P.map f ↔ τ * p * τ⁻¹ ∈ P.map f := by
    intro p
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [← hfγ]
      exact ⟨γ k, (hγP k).1 hk, rfl⟩
    · intro hp
      obtain ⟨k₂, hk₂, hk₂p⟩ := hp
      have hp_even : p ∈ alternatingGroup (Fin 6) := by
        have h1 : Perm.sign (τ * p * τ⁻¹) = 1 := by
          rw [← hk₂p]
          exact Equiv.Perm.mem_alternatingGroup.1 (e k₂).2
        rw [Equiv.Perm.mem_alternatingGroup]
        rwa [Six.sign_conj] at h1
      let k₁ : K := e.symm ⟨p, hp_even⟩
      have hk₁ : f k₁ = p := by
        rw [hfk]
        simp [k₁]
      have h2 : γ k₁ = k₂ := by
        apply hf
        rw [hfγ, hk₁, hk₂p]
      exact ⟨k₁, (hγP k₁).2 (h2 ▸ hk₂), hk₁⟩
  have hPA : P.map f ≤ Six.A6s := by
    rintro _ ⟨k, -, rfl⟩
    exact (e k).2
  have hXA : X.map f ≤ Six.A6s := by
    rintro _ ⟨k, -, rfl⟩
    exact (e k).2
  have hX'ne : X.map f ≠ P.map f := fun h => hXP (Subgroup.map_injective hf h)
  have hX'top : X.map f ≠ Six.A6s := by
    intro h
    apply hXtop
    rw [eq_top_iff]
    intro k _
    have : f k ∈ X.map f := by
      rw [h]
      exact (e k).2
    exact (hmemmap X k).1 this
  have key := Six.six_key (by rw [Subgroup.card_map_of_injective hf]; exact hPc) hPA
    (Subgroup.map_mono hPX) hXA hX'ne hX'top τ hτ
  intro k
  rw [← hmemmap X k, ← hmemmap X (γ k), hfγ]
  exact key (f k)

theorem factorization_360 : (360 : ℕ).factorization 2 = 3 := by
  norm_num [Nat.factorization]

end Unc25K1.A6Model

theorem a6OuterTypes : A6OuterTypes := by
  intro G _ _ H K P X s he hKH hP hPX hXK hXP hXK' hs hsP hsX
  obtain ⟨e⟩ := he
  obtain ⟨θ, ψ, -, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  let φ : ↥K ≃* ↥A6Models.psl29 := e.trans ψ.symm
  have hsH : s ∈ H := hs.1
  have hsN : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  let γs : MulAut ↥K := conjAct K ⟨s, hsN⟩
  have hγs : ∀ k : ↥K, ((γs k : ↥K) : G) = s * (k : G) * s⁻¹ := fun k => rfl
  have hγsmem : γs ∈ autOn H K :=
    Subgroup.mem_map.2 ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.2 hsH, rfl⟩
  let Θ := Unc25K1.A6Model.thetaEquiv φ
  let B : Subgroup (Equiv.Perm (Fin 10)) :=
    ((autOn H K).map Θ.toMonoidHom).map A6Models.autA6.subtype
  have hB1 : B ≤ A6Models.autA6 := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hB2 : A6Models.psl29 ≤ B := by
    intro x hx
    let k₀ : ↥K := φ.symm ⟨x, hx⟩
    have hk₀N : (k₀ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k₀.2
    let ι : MulAut ↥K := conjAct K ⟨(k₀ : G), hk₀N⟩
    have hι : ι ∈ autOn H K :=
      Subgroup.mem_map.2 ⟨⟨(k₀ : G), hk₀N⟩, Subgroup.mem_subgroupOf.2 (hKH k₀.2), rfl⟩
    have hιk : ∀ k : ↥K, ι k = k₀ * k * k₀⁻¹ := fun k => rfl
    have hk₀φ : φ k₀ = ⟨x, hx⟩ := by simp [k₀]
    have hΘι : Θ ι = ⟨x, A6Facts.psl29_le_autA6 hx⟩ := by
      apply Unc25K1.A6Model.thetaEquiv_eq φ ι
      intro k
      rw [hιk, map_mul, map_mul, map_inv, hk₀φ]
      rfl
    exact ⟨Θ ι, ⟨ι, hι, rfl⟩, by rw [hΘι]; rfl⟩
  have hKc : Nat.card ↥K = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact Unc25K1.A6Model.card_alt6
  have hPc : Nat.card P = 8 := by
    rw [hP.card_eq, twoPart, hKc, Unc25K1.A6Model.factorization_360]
    norm_num
  have hPc' : Nat.card (P.subgroupOf K) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv]
    exact hPc
  have hB3 : ∃ σ ∈ B, σ ∉ A6Facts.s6 := by
    refine ⟨((Θ γs : ↥A6Models.autA6) : Equiv.Perm (Fin 10)), ⟨Θ γs, ⟨γs, hγsmem, rfl⟩, rfl⟩, ?_⟩
    intro hσ6
    obtain ⟨τ, hτ⟩ := Unc25K1.A6Model.s6_induces θ ψ hψθ e γs hσ6
    have hPX' : P.subgroupOf K ≤ X.subgroupOf K := fun k hk => hPX hk
    have hXP' : X.subgroupOf K ≠ P.subgroupOf K := by
      intro h
      apply hXP
      apply le_antisymm _ hPX
      intro x hx
      have hxK : x ∈ K := hXK hx
      have : (⟨x, hxK⟩ : ↥K) ∈ X.subgroupOf K := hx
      rw [h] at this
      exact this
    have hXtop : X.subgroupOf K ≠ ⊤ := by
      intro h
      apply hXK'
      apply le_antisymm hXK
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ X.subgroupOf K := by rw [h]; trivial
      exact this
    have hγP : ∀ k : ↥K, k ∈ P.subgroupOf K ↔ γs k ∈ P.subgroupOf K := by
      intro k
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hγs]
      exact Subgroup.mem_normalizer_iff.1 hsP (k : G)
    have hnorm := Unc25K1.A6Model.key_of_iso e (P.subgroupOf K) (X.subgroupOf K) hPc' hPX' hXP'
      hXtop γs τ hτ hγP
    apply hsX
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ K
    · have h1 := hnorm ⟨g, hg⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hγs] at h1
      exact h1
    · have h1 : g ∉ X := fun h => hg (hXK h)
      have h2 : s * g * s⁻¹ ∉ X := by
        intro h
        apply hg
        exact (Subgroup.mem_normalizer_iff.1 hsN g).2 (hXK h)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hclass := Unc25K1.A6Model.classify B hB1 hB2 hB3
  let E1 : ↥(autOn H K) ≃* ↥((autOn H K).map Θ.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ Θ.toMonoidHom Θ.injective
  let E2 : ↥((autOn H K).map Θ.toMonoidHom) ≃* ↥B :=
    Subgroup.equivMapOfInjective _ A6Models.autA6.subtype A6Models.autA6.subtype_injective
  rcases hclass with h | h | h
  · exact Or.inr (Or.inl ⟨(E1.trans E2).trans (MulEquiv.subgroupCongr h)⟩)
  · exact Or.inl ⟨(E1.trans E2).trans (MulEquiv.subgroupCongr h)⟩
  · exact Or.inr (Or.inr ⟨(E1.trans E2).trans (MulEquiv.subgroupCongr h)⟩)

end CFSG.QuasithinUnique
