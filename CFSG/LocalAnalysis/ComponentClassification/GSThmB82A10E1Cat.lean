module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Main

public section

namespace CFSG.ComponentClassification.GSThmB.A10E1

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10

@[expose] def e4Two : List (Perm (Fin 10)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem e4Two_comm {π π' : Perm (Fin 10)} (h : π ∈ e4Two) (h' : π' ∈ e4Two) :
    π * π' = π' * π := by
  simp only [e4Two, List.mem_cons, List.not_mem_nil, or_false] at h h'
  rcases h with rfl | rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl | rfl <;> decide

theorem pairsTwo_cases : ∀ w ∈ pairsTwo, w = (0, 2) ∨ w = (0, 3) ∨ w = (1, 2) ∨ w = (1, 3) ∨
    w = (2, 0) ∨ w = (2, 1) ∨ w = (3, 0) ∨ w = (3, 1) := by
  decide

theorem mem_e4Two {g : Perm (Fin 10)} (hfix : ∀ x ∈ fixTwo, g x = x)
    (hc : g * sigmaTwo = sigmaTwo * g) (hs : sign g = 1) : g ∈ e4Two := by
  rcases pairsTwo_cases _ (pair_mem hfix hc) with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h2⟩ := Prod.mk.inj h
  · rw [eq_of_pair_eq (h := 1) hfix (by decide) hc (by decide) (by rw [h0]; decide)
      (by rw [h2]; decide)]
    simp [e4Two]
  · rw [eq_of_pair_eq (h := swap 2 3) hfix (by decide) hc (by decide) (by rw [h0]; decide)
      (by rw [h2]; decide)] at hs
    exact absurd hs (by decide)
  · rw [eq_of_pair_eq (h := swap 0 1) hfix (by decide) hc (by decide) (by rw [h0]; decide)
      (by rw [h2]; decide)] at hs
    exact absurd hs (by decide)
  · rw [eq_of_pair_eq (h := swap 0 1 * swap 2 3) hfix (by decide) hc (by decide)
      (by rw [h0]; decide) (by rw [h2]; decide)]
    simp [e4Two]
  · rw [eq_of_pair_eq (h := swap 0 2 * swap 1 3) hfix (by decide) hc (by decide)
      (by rw [h0]; decide) (by rw [h2]; decide)]
    simp [e4Two]
  · rw [eq_of_pair_eq (h := swap 0 2 * swap 2 1 * swap 1 3) hfix (by decide) hc (by decide)
      (by rw [h0]; decide) (by rw [h2]; decide)] at hs
    exact absurd hs (by decide)
  · rw [eq_of_pair_eq (h := swap 0 3 * swap 3 1 * swap 1 2) hfix (by decide) hc (by decide)
      (by rw [h0]; decide) (by rw [h2]; decide)] at hs
    exact absurd hs (by decide)
  · rw [eq_of_pair_eq (h := swap 0 3 * swap 1 2) hfix (by decide) hc (by decide)
      (by rw [h0]; decide) (by rw [h2]; decide)]
    simp [e4Two]

theorem exists_sigmaTwo_embedding {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (hA : Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)))
    {ι : H} (hι : orderOf ι = 2) {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))))
    (hJt : IsSec8JType (J₁ ⧸ pPrimeCore 2 J₁) p f) :
    ∃ φ : H →* Perm (Fin 10), Function.Injective φ ∧ φ ι = sigmaTwo ∧
      (∀ s ∈ generalizedFitting H, sign (φ s) = 1) ∧ J₁.map φ = altOn fixTwo ∧
      pPrimeCore 2 J₁ = ⊥ := by
  classical
  obtain ⟨e⟩ := hA
  have : (generalizedFitting H).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := H)).2
  obtain ⟨φ, hinj, hφe⟩ := exists_perm_embedding _ hC e
  have hA := alternating_le_range _ e φ hφe
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
  have hObot : pPrimeCore 2 J₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ hO1
  have hconj : IsConj (φ ι) sigmaTwo := by
    rw [isConj_iff_cycleType_eq, hct, hm, (cycleType_of_orderOf_two orderOf_sigmaTwo).1,
      card_support_sigmaTwo]
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  set φ' : H →* Perm (Fin 10) := (MulAut.conj τ).toMonoidHom.comp φ with hφ'
  have hφ'apply : ∀ h : H, φ' h = τ * φ h * τ⁻¹ := fun h => rfl
  have hinj' : Function.Injective φ' := (MulAut.conj τ).injective.comp hinj
  have hA' : alternatingGroup (Fin 10) ≤ φ'.range := by
    intro a ha
    have hmem : τ⁻¹ * a * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 10) :=
      (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem a ha τ⁻¹
    obtain ⟨h, hh⟩ := hA hmem
    refine ⟨h, ?_⟩
    rw [hφ'apply, hh]
    group
  have hφ'ι : φ' ι = sigmaTwo := by rw [hφ'apply, hτ]
  refine ⟨φ', hinj', hφ'ι, fun s hs => ?_, ?_, hObot⟩
  · rw [hφ'apply, show φ s = ((e ⟨s, hs⟩ : alternatingGroup (Fin 10)) : Perm (Fin 10)) from
      hφe ⟨s, hs⟩, map_mul, map_mul, mem_alternatingGroup.mp (e ⟨s, hs⟩).2, map_inv]
    simp
  · rw [map_eq_altOn φ' hinj' hA' ι J₁ hJC hJ (by rw [hφ'ι, card_support_sigmaTwo]), hφ'ι,
      support_sigmaTwo_compl]

theorem commute_of_mem_inf {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (hA : Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)))
    {ι : H} (hι : orderOf ι = 2) {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))))
    (hJt : IsSec8JType (J₁ ⧸ pPrimeCore 2 J₁) p f) {u v : H}
    (hu : u ∈ generalizedFitting H ⊓ centralizer ({ι} : Set H) ⊓ coreActionKernel J₁)
    (hv : v ∈ generalizedFitting H ⊓ centralizer ({ι} : Set H) ⊓ coreActionKernel J₁) :
    u * v = v * u := by
  classical
  obtain ⟨φ, hinj, hφι, hφs, hJN, hO⟩ := exists_sigmaTwo_embedding hp hp2 hf hC hA hι hJC hJ hJt
  have key : ∀ r ∈ generalizedFitting H ⊓ centralizer ({ι} : Set H) ⊓ coreActionKernel J₁,
      φ r ∈ e4Two := by
    intro r hr
    obtain ⟨⟨hrF, hrC⟩, hrK⟩ := hr
    have hcomm : ∀ j ∈ J₁, r * j = j * r := by
      intro j hj
      have h1 := (mem_coreActionKernel.mp hrK).2 j hj
      rw [hO, Subgroup.map_bot, mem_bot] at h1
      calc r * j = r * j * (j⁻¹ * r⁻¹ * j * r) := by rw [h1, mul_one]
        _ = j * r := by group
    refine mem_e4Two (fix_of_commute_altOn fun n hn => ?_) ?_ (hφs r hrF)
    · rw [← hJN] at hn
      obtain ⟨j, hj, rfl⟩ := hn
      rw [← map_mul, ← map_mul, hcomm j hj]
    · have hc : ι * r = r * ι := mem_centralizer_iff.mp hrC ι rfl
      rw [← hφι, ← map_mul, ← map_mul, hc]
  apply hinj
  rw [map_mul, map_mul]
  exact e4Two_comm (key u hu) (key v hv)

end CFSG.ComponentClassification.GSThmB.A10E1
