module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Main
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideA6

public section

namespace CFSG.ComponentClassification.GSThmB.A10Side

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10

theorem mem_fixTwo_iff_of_commute {g : Perm (Fin 10)} (hg : g * sigmaTwo = sigmaTwo * g)
    (x : Fin 10) : g x ∈ fixTwo ↔ x ∈ fixTwo := by
  rw [← support_sigmaTwo_compl, Finset.mem_compl, Finset.mem_compl]
  exact not_congr (Catalog82A10.mem_support_iff_of_commute hg x)

@[expose] noncomputable def restrTwo (g : Perm (Fin 10)) (hg : g * sigmaTwo = sigmaTwo * g) :
    Perm ↥fixTwo :=
  g.subtypePerm (mem_fixTwo_iff_of_commute hg)

theorem restrTwo_apply (g : Perm (Fin 10)) (hg : g * sigmaTwo = sigmaTwo * g) (x : ↥fixTwo) :
    ((restrTwo g hg x : ↥fixTwo) : Fin 10) = g x := rfl

theorem ofSubtype_conj_restrTwo (g : Perm (Fin 10)) (hg : g * sigmaTwo = sigmaTwo * g)
    (π : Perm ↥fixTwo) :
    Perm.ofSubtype (restrTwo g hg * π * (restrTwo g hg)⁻¹) = g * Perm.ofSubtype π * g⁻¹ := by
  ext x
  by_cases hx : x ∈ fixTwo
  · have hgx : g⁻¹ x ∈ fixTwo := by
      rw [← mem_fixTwo_iff_of_commute hg]
      simpa using hx
    rw [Perm.ofSubtype_apply_of_mem _ hx]
    simp only [Perm.coe_mul, Function.comp_apply]
    rw [Perm.ofSubtype_apply_of_mem _ hgx, restrTwo_apply]
    congr 2
  · have hgx : g⁻¹ x ∉ fixTwo := by
      rw [← mem_fixTwo_iff_of_commute hg]
      simpa using hx
    rw [Perm.ofSubtype_apply_of_not_mem _ hx]
    simp only [Perm.coe_mul, Function.comp_apply]
    rw [Perm.ofSubtype_apply_of_not_mem _ hgx]
    simp

@[expose] noncomputable def fixTwoEquiv : ↥fixTwo ≃ Fin 6 :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; rfl)

@[expose] noncomputable def altOnFixTwoEquiv : ↥(altOn fixTwo) ≃* alternatingGroup (Fin 6) :=
  (altOnEquiv fixTwo).symm.trans (Equiv.altCongrHom fixTwoEquiv)

theorem altOnFixTwoEquiv_conj (g : Perm (Fin 10)) (hg : g * sigmaTwo = sigmaTwo * g)
    (x : ↥(altOn fixTwo)) (hx : g * (x : Perm (Fin 10)) * g⁻¹ ∈ altOn fixTwo) :
    ((altOnFixTwoEquiv ⟨_, hx⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      fixTwoEquiv.permCongr (restrTwo g hg) *
        (altOnFixTwoEquiv x : Perm (Fin 6)) * (fixTwoEquiv.permCongr (restrTwo g hg))⁻¹ := by
  set k := (altOnEquiv fixTwo).symm x with hk
  have hxk : (x : Perm (Fin 10)) = Perm.ofSubtype (k : Perm ↥fixTwo) := by
    have h1 : altOnEquiv fixTwo k = x := by rw [hk, MulEquiv.apply_symm_apply]
    rw [← h1]
    rfl
  set r := restrTwo g hg with hr
  have hmem : r * (k : Perm ↥fixTwo) * r⁻¹ ∈ alternatingGroup ↥fixTwo := by
    rw [mem_alternatingGroup, map_mul, map_mul, map_inv, mem_alternatingGroup.mp k.2, mul_one,
      mul_inv_cancel]
  have hsymm : (altOnEquiv fixTwo).symm ⟨_, hx⟩ = ⟨r * k * r⁻¹, hmem⟩ := by
    apply (altOnEquiv fixTwo).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change g * (x : Perm (Fin 10)) * g⁻¹ = Perm.ofSubtype (r * (k : Perm ↥fixTwo) * r⁻¹)
    rw [hr, ofSubtype_conj_restrTwo, hxk]
  change ((Equiv.altCongrHom fixTwoEquiv ((altOnEquiv fixTwo).symm ⟨_, hx⟩) :
      alternatingGroup (Fin 6)) : Perm (Fin 6)) = _
  rw [hsymm]
  change fixTwoEquiv.permCongr (r * (k : Perm ↥fixTwo) * r⁻¹) =
    fixTwoEquiv.permCongr r * fixTwoEquiv.permCongr (k : Perm ↥fixTwo) *
      (fixTwoEquiv.permCongr r)⁻¹
  rw [Equiv.permCongr_mul, Equiv.permCongr_mul]
  congr 1

theorem exists_altSix_equiv {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (hA : Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)))
    {ι : H} (hι : orderOf ι = 2) {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))))
    (hJt : IsSec8JType (J₁ ⧸ pPrimeCore 2 J₁) p f) :
    ∃ e₁ : ↥J₁ ≃* alternatingGroup (Fin 6), ∀ h : normalizer (J₁ : Set H),
      (h : H) * ι = ι * h → IsSymSixType e₁ (J₁.normalizerMonoidHom h) := by
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
  have hconj : IsConj (φ ι) sigmaTwo := by
    rw [isConj_iff_cycleType_eq, hct, hm, (cycleType_of_orderOf_two orderOf_sigmaTwo).1,
      card_support_sigmaTwo]
  obtain ⟨φ', hinj', hA', hφ'ι⟩ := exists_conj_normal φ hinj hA hconj
  have hJN' : J₁.map φ' = altOn fixTwo := by
    rw [map_eq_altOn φ' hinj' hA' ι J₁ hJC hJ (by rw [hφ'ι, card_support_sigmaTwo]), hφ'ι,
      support_sigmaTwo_compl]
  set e₁ : ↥J₁ ≃* alternatingGroup (Fin 6) :=
    (J₁.equivMapOfInjective φ' hinj').trans ((MulEquiv.subgroupCongr hJN').trans
      altOnFixTwoEquiv) with he₁
  have he₁j : ∀ j : ↥J₁, e₁ j = altOnFixTwoEquiv ⟨φ' j, hJN' ▸ mem_map_of_mem φ' j.2⟩ :=
    fun j => rfl
  refine ⟨e₁, fun h hhι => ?_⟩
  have hg : φ' h * sigmaTwo = sigmaTwo * φ' h := by
    rw [← hφ'ι, ← map_mul, ← map_mul, hhι]
  refine ⟨fixTwoEquiv.permCongr (restrTwo (φ' h) hg), ?_⟩
  apply MulEquiv.ext
  intro c
  obtain ⟨j, rfl⟩ := e₁.surjective c
  have h1 : (MulAut.congr e₁ (J₁.normalizerMonoidHom h)) (e₁ j) =
      e₁ (J₁.normalizerMonoidHom h j) := by
    change e₁ (J₁.normalizerMonoidHom h (e₁.symm (e₁ j))) = _
    rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [h1, MulAut.conjNormal_apply, he₁j, he₁j]
  have hmemJ : (h : H) * j * (h : H)⁻¹ ∈ J₁ := (mem_normalizer_iff.mp h.2 j).mp j.2
  have hconjmem : φ' h * ((⟨φ' j, hJN' ▸ mem_map_of_mem φ' j.2⟩ : ↥(altOn fixTwo)) :
      Perm (Fin 10)) * (φ' h)⁻¹ ∈ altOn fixTwo := by
    have h3 : φ' ((h : H) * j * (h : H)⁻¹) ∈ altOn fixTwo := hJN' ▸ mem_map_of_mem φ' hmemJ
    simpa [map_mul, map_inv] using h3
  have h2 := altOnFixTwoEquiv_conj (φ' h) hg ⟨φ' j, hJN' ▸ mem_map_of_mem φ' j.2⟩ hconjmem
  have hsub : (⟨φ' ((J₁.normalizerMonoidHom h j : ↥J₁) : H),
      hJN' ▸ mem_map_of_mem φ' (J₁.normalizerMonoidHom h j).2⟩ : ↥(altOn fixTwo)) =
      ⟨_, hconjmem⟩ := by
    apply Subtype.ext
    change φ' ((h : H) * j * (h : H)⁻¹) = φ' h * φ' j * (φ' h)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [hsub, h2]

end CFSG.ComponentClassification.GSThmB.A10Side
