module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Sym
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog82A10

open CFSG Subgroup Equiv Equiv.Perm
open CFSG.ComponentClassification.UnbalancedLayer

theorem card_quot_dvd {H : Type} [Group H] [Finite H] (φ : H →* Perm (Fin 10))
    (hinj : Function.Injective φ) {ι : H} (hι : orderOf ι = 2) (J : Subgroup H)
    (hJC : J ≤ centralizer ({ι} : Set H)) :
    Nat.card (J ⧸ pPrimeCore 2 J) ∣
      (10 - 2 * ((φ ι).support.card / 2)).factorial * 2 ^ ((φ ι).support.card / 2) *
        ((φ ι).support.card / 2).factorial := by
  have hσ : orderOf (φ ι) = 2 := by rw [orderOf_injective φ hinj, hι]
  rw [← card_centralizer_of_orderOf_two hσ]
  have hCmap : (centralizer ({ι} : Set H)).map φ ≤
      centralizer ({φ ι} : Set (Perm (Fin 10))) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ rfl
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc ι rfl]
  have h1 : Nat.card (centralizer ({ι} : Set H)) ∣
      Nat.card (centralizer ({φ ι} : Set (Perm (Fin 10)))) := by
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le hCmap
  exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_dvd_of_le hJC).trans h1)

theorem card_sec8 {Y : Type} [Group Y] {p f : ℕ} (h : IsSec8JType Y p f) :
    Nat.card Y = Open.ordA 1 (p ^ (2 * f)) := by
  rcases h with hL | ⟨rfl, rfl, ⟨eA⟩⟩
  · exact GH74.card_of_lieModel_PSL (by norm_num) hL
  · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem part_c {H : Type} [Group H] [Finite H] (φ : H →* Perm (Fin 10))
    (hinj : Function.Injective φ) (hA : alternatingGroup (Fin 10) ≤ φ.range) {ι : H}
    (hφι : φ ι = sigmaTwo) (J : Subgroup H) (hJC : J ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({ι} : Set H))))
    (hO : pPrimeCore 2 J = ⊥) (R : Subgroup H)
    (hR : R ≤ centralizer ({ι} : Set H) ⊓ coreActionKernel J) :
    Nat.card R ≤ 8 ∧ (Nat.card R = 8 → ∃ u ∈ R, ∃ v ∈ R, u * v ≠ v * u) := by
  have hJN := map_eq_altOn φ hinj hA ι J hJC hJ (by rw [hφι, card_support_sigmaTwo])
  rw [hφι, support_sigmaTwo_compl] at hJN
  have hD : ∀ g ∈ R.map φ, (∀ x ∈ fixTwo, g x = x) ∧ g * sigmaTwo = sigmaTwo * g := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrC, hrK⟩ := hR hr
    have hcomm : ∀ j ∈ J, r * j = j * r := by
      intro j hj
      have h1 := (mem_coreActionKernel.mp hrK).2 j hj
      rw [hO, Subgroup.map_bot, mem_bot] at h1
      calc r * j = r * j * (j⁻¹ * r⁻¹ * j * r) := by rw [h1, mul_one]
        _ = j * r := by group
    refine ⟨fix_of_commute_altOn (fun n hn => ?_), ?_⟩
    · rw [← hJN] at hn
      obtain ⟨j, hj, rfl⟩ := hn
      rw [← map_mul, ← map_mul, hcomm j hj]
    · have hc : ι * r = r * ι := mem_centralizer_iff.mp hrC ι rfl
      rw [← hφι, ← map_mul, ← map_mul, hc]
  obtain ⟨h8, hna⟩ := card_le_eight_of_le_D (R.map φ) hD
  have hcardR : Nat.card (R.map φ) = Nat.card R := Subgroup.card_map_of_injective hinj
  refine ⟨hcardR ▸ h8, fun hR8 => ?_⟩
  obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, huv⟩ := hna (hcardR.trans hR8)
  exact ⟨u, hu, v, hv, fun h => huv (by rw [← map_mul, ← map_mul, h])⟩

theorem cf82A10P : CF82A10P := by
  intro H _ _ p f hp hp2 hf hC ⟨e⟩ ι hι J hJC hJ hJt
  classical
  have : (generalizedFitting H).Normal := (LocalCores.generalized_fitting_characteristic (G := H)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hinj, hφe⟩ := exists_perm_embedding _ hC e
  have hA := alternating_le_range _ e φ hφe
  have hσ : orderOf (φ ι) = 2 := by rw [orderOf_injective φ hinj, hι]
  obtain ⟨hct, hsupp, hm1⟩ := cycleType_of_orderOf_two hσ
  have hm5 : (φ ι).support.card / 2 ≤ 5 := by
    have := (φ ι).support.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hX := card_sec8 hJt
  obtain ⟨rfl, rfl, hm2⟩ := arith_sec8 hp hp2 hf hm1 hm5 (hX ▸ card_quot_dvd φ hinj hι J hJC)
  have h360 : Nat.card (J ⧸ pPrimeCore 2 J) = 360 := by rw [hX]; decide
  have hJN := map_eq_altOn φ hinj hA ι J hJC hJ (by omega)
  have hT : 2 ≤ ((φ ι).support)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hJcard : Nat.card J = (10 - (φ ι).support.card).factorial / 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hJN, card_altOn _ hT, Finset.card_compl,
      Fintype.card_fin]
  have hJO := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 J)
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 J)) := pPrimeCore_coprime_card
  have hm : (φ ι).support.card = 4 := by
    by_contra hne
    have h2 : (φ ι).support.card = 2 := by omega
    rw [hJcard, h2, h360] at hJO
    have h56 : Nat.card (pPrimeCore 2 J) = 56 := by
      norm_num [Nat.factorial] at hJO
      omega
    rw [h56] at hOcop
    norm_num at hOcop
  have hJ360 : Nat.card J = 360 := by
    rw [hJcard, hm]
    decide
  have hO1 : Nat.card (pPrimeCore 2 J) = 1 := by
    rw [hJ360, h360] at hJO
    omega
  have hObot : pPrimeCore 2 J = ⊥ := Subgroup.eq_bot_of_card_eq _ hO1
  refine ⟨?_, ?_, ?_⟩
  · rcases hJt with hL | ⟨-, -, ⟨eA⟩⟩
    · exact hL
    · exact LieType.CurtisTits.lieModel_of_mulEquiv eA.symm lieModel_alternatingGroup_six
  · intro Q hQ hQJ
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    have hdvd : Nat.card Q ∣ 360 := hJ360 ▸ Subgroup.card_dvd_of_le hQJ
    rw [hn] at hdvd ⊢
    have hn3 : n ≤ 3 := by
      by_contra h
      push Not at h
      have h16 : 2 ^ 4 ∣ 360 := (pow_dvd_pow 2 h).trans hdvd
      norm_num at h16
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 8 := by norm_num
  · intro R _ hR
    have hconj : IsConj (φ ι) sigmaTwo := by
      rw [isConj_iff_cycleType_eq, hct, hm, (cycleType_of_orderOf_two orderOf_sigmaTwo).1,
        card_support_sigmaTwo]
    obtain ⟨φ', hinj', hA', hφ'ι⟩ := exists_conj_normal φ hinj hA hconj
    exact part_c φ' hinj' hA' hφ'ι J hJC hJ hObot R hR

end CFSG.ComponentClassification.GSThmB.Catalog82A10
