module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29N
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Main

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.GSThmB.Catalog82A10
open CFSG.ComponentClassification.UnbalancedLayer

namespace P29.A10

@[expose] def IsEmb {H : Type} [Group H] (φ : H →* Perm (Fin 10)) : Prop :=
  Function.Injective φ ∧ alternatingGroup (Fin 10) ≤ φ.range ∧
    ∀ h, h ∈ generalizedFitting H ↔ φ h ∈ alternatingGroup (Fin 10)

theorem IsEmb.conj {H : Type} [Group H] {φ : H →* Perm (Fin 10)} (hφ : IsEmb φ)
    (τ : Perm (Fin 10)) : IsEmb ((MulAut.conj τ).toMonoidHom.comp φ) := by
  obtain ⟨hinj, hA, hfit⟩ := hφ
  refine ⟨(MulAut.conj τ).injective.comp hinj, fun a ha => ?_, fun h => ?_⟩
  · obtain ⟨h, hh⟩ :=
      hA ((inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem a ha τ⁻¹)
    refine ⟨h, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hh]
    group
  · rw [hfit, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mem_alternatingGroup, mem_alternatingGroup, map_mul, map_mul, map_inv,
      mul_comm (sign τ), mul_assoc, mul_inv_cancel, mul_one]

theorem exists_normal_form {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (e : ↥(generalizedFitting H) ≃* alternatingGroup (Fin 10)) {ι : H} (hι : orderOf ι = 2)
    {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))))
    (hJt : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) :
    pPrimeCore 2 J₁ = ⊥ ∧ ∃ φ : H →* Perm (Fin 10), IsEmb φ ∧ φ ι = sigmaTwo := by
  classical
  have : (generalizedFitting H).Normal := (LocalCores.generalized_fitting_characteristic (G := H)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hinj, hφe⟩ := exists_perm_embedding _ hC e
  have hA := alternating_le_range _ e φ hφe
  have hfit : ∀ h, h ∈ generalizedFitting H ↔ φ h ∈ alternatingGroup (Fin 10) := by
    intro h
    constructor
    · intro hh
      have h1 : φ h = (e ⟨h, hh⟩ : Perm (Fin 10)) := hφe ⟨h, hh⟩
      rw [h1]
      exact (e _).2
    · intro hh
      obtain ⟨s, hs⟩ := e.surjective ⟨φ h, hh⟩
      have h1 : φ s = φ h := by rw [hφe, hs]
      rw [← hinj h1]
      exact s.2
  have hσ : orderOf (φ ι) = 2 := by rw [orderOf_injective φ hinj, hι]
  obtain ⟨hct, hsupp, hm1⟩ := cycleType_of_orderOf_two hσ
  have hm5 : (φ ι).support.card / 2 ≤ 5 := by
    have := (φ ι).support.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hX := card_sec8 hJt
  obtain ⟨rfl, rfl, hm2⟩ := arith_sec8 hp hp2 hf hm1 hm5 (hX ▸ card_quot_dvd φ hinj hι J₁ hJC)
  have h360 : Nat.card (J₁ ⧸ pPrimeCore 2 J₁) = 360 := by rw [hX]; decide
  have hJN := map_eq_altOn φ hinj hA ι J₁ hJC hJ (by omega)
  have hT : 2 ≤ ((φ ι).support)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hJcard : Nat.card J₁ = (10 - (φ ι).support.card).factorial / 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hJN, card_altOn _ hT, Finset.card_compl,
      Fintype.card_fin]
  have hJO := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 J₁)
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 J₁)) := pPrimeCore_coprime_card
  have hm : (φ ι).support.card = 4 := by
    by_contra hne
    have h2 : (φ ι).support.card = 2 := by omega
    rw [hJcard, h2, h360] at hJO
    have h56 : Nat.card (pPrimeCore 2 J₁) = 56 := by
      norm_num [Nat.factorial] at hJO
      omega
    rw [h56] at hOcop
    norm_num at hOcop
  have hJ360 : Nat.card J₁ = 360 := by
    rw [hJcard, hm]
    decide
  have hO1 : Nat.card (pPrimeCore 2 J₁) = 1 := by
    rw [hJ360, h360] at hJO
    omega
  have hconj : IsConj (φ ι) sigmaTwo := by
    rw [isConj_iff_cycleType_eq, hct, hm, (cycleType_of_orderOf_two orderOf_sigmaTwo).1,
      card_support_sigmaTwo]
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  refine ⟨Subgroup.eq_bot_of_card_eq _ hO1, (MulAut.conj τ).toMonoidHom.comp φ,
    IsEmb.conj ⟨hinj, hA, hfit⟩ τ, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hτ

end P29.A10

open P29 P29.A10

theorem cf82Prop29A10 : CF82Prop29A10 := by
  intro H _ _ p f hp hp2 hf hC ⟨e⟩ ι hι J₁ hJC hJ hJt S₁ hS
  obtain ⟨hO, φ, hφ, hφι⟩ := exists_normal_form hp hp2 hf hC e hι hJC hJ hJt
  obtain ⟨g, hg, hS'⟩ := exists_conj_map_eq φ hφ.1 hS (P := P)
    (by rw [hφι]; exact P_le_centralizer) isPGroup_P (by rw [hφι, relIndex_P]; decide)
  set ψ := (MulAut.conj g).toMonoidHom.comp φ with hψdef
  have hψ : IsEmb ψ := hφ.conj g
  have hψι : ψ ι = sigmaTwo := by
    rw [hφι] at hg
    rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφι,
      ← mem_centralizer_iff.mp hg sigmaTwo rfl, mul_inv_cancel_right]
  have hJmap : J₁.map ψ = altOn fixTwo := by
    have h := map_eq_altOn ψ hψ.1 hψ.2.1 ι J₁ hJC hJ (by rw [hψι, card_support_sigmaTwo])
    rwa [hψι, support_sigmaTwo_compl] at h
  have hFmap : (generalizedFitting H).map ψ = alternatingGroup (Fin 10) := by
    ext a
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (hψ.2.2 h).mp hh
    · intro ha
      obtain ⟨h, rfl⟩ := hψ.2.1 ha
      exact ⟨h, (hψ.2.2 h).mpr ha, rfl⟩
  apply prop29Concl_of_model ψ hψ.1 hO
  rw [hFmap, hψι, hJmap, hS']
  exact modelConcl hψ.2.1 fun h => h ⟨e⟩

end CFSG.ComponentClassification.GSThmB
