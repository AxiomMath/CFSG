module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
import CFSG.GroupTheory.SubgroupOfQuotientMapConj
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.GroupTheory.NormalizerInterval
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedOddCentralQuotient
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedDirectProductOrbit
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup
open CFSG.SignalizerFunctorTheorem.McBride
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L U H P D : Subgroup G} {𝒦 : Set (Subgroup G)}
  {Γ : Type} [Group Γ] [Finite Γ] {ψ : ↥(P ⊔ H) →* Γ}

private theorem isPIsolatedOver_normalizer_subgroupOf_sup_aux (hH : IsPGroup 2 H)
    (hHP : H ≤ normalizer (P : Set G)) (hPL : P ≤ L)
    (hLP : L ⊓ normalizer (H : Set G) ≤ P)
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L)) :
    IsPIsolatedOver 2
      (normalizer (((H.subgroupOf (P ⊔ H) : Subgroup ↥(P ⊔ H)) : Set ↥(P ⊔ H))))
      (H.subgroupOf (P ⊔ H)) := by
  have hPL' : P ⊓ normalizer (H : Set G) = L ⊓ normalizer (H : Set G) :=
    le_antisymm (le_inf (inf_le_left.trans hPL) inf_le_right) (le_inf hLP inf_le_right)
  have hassoc : (L ⊓ normalizer (H : Set G)) ⊓ H = H ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer), inf_comm]
  rw [← Subgroup.subgroupOf_normalizer_eq le_sup_right, ← Subgroup.inf_subgroupOf_left,
    isPIsolatedOver_subgroupOf_iff le_sup_right inf_le_left, sup_inf_normalizer_eq hHP,
    hPL', isPIsolatedOver_sup_iff hH inf_le_right, hassoc]
  exact hiso

omit [Finite G] [Finite Γ] in
private theorem commutator_normalizer_le_subgroupOf (hHP : H ≤ normalizer (P : Set G))
    (hker : ψ.ker = D.subgroupOf (P ⊔ H)) (hcore : pCoreOf 2 P = H ⊓ L)
    (hLevi : IsGomiLeviData L U P D 𝒦) :
    ⁅ψ.ker ⊓ normalizer (((H.subgroupOf (P ⊔ H) : Subgroup ↥(P ⊔ H)) : Set ↥(P ⊔ H))),
        normalizer (((H.subgroupOf (P ⊔ H) : Subgroup ↥(P ⊔ H)) : Set ↥(P ⊔ H)))⁆
      ≤ H.subgroupOf (P ⊔ H) := by
  rw [Subgroup.commutator_le]
  intro k hk n _
  rw [Subgroup.mem_subgroupOf]
  have hkker : k ∈ ψ.ker := hk.1
  have hknorm : k ∈ normalizer
      (((H.subgroupOf (P ⊔ H) : Subgroup ↥(P ⊔ H)) : Set ↥(P ⊔ H))) := hk.2
  have hdD : (k : G) ∈ D := by
    rw [hker] at hkker
    exact Subgroup.mem_subgroupOf.mp hkker
  have hdnH : (k : G) ∈ normalizer (H : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq le_sup_right] at hknorm
    exact Subgroup.mem_subgroupOf.mp hknorm
  obtain ⟨h, hh, p, hp, hhp⟩ : ∃ h ∈ H, ∃ p ∈ P, h * p = (n : G) := by
    have hn : (n : G) ∈ (H : Set G) * (P : Set G) := by
      have hnX : (n : G) ∈ ((H ⊔ P : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact n.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right H P hHP] at hnX
      exact hnX
    exact Set.mem_mul.mp hn
  have hcoe : ((⁅k, n⁆ : ↥(P ⊔ H)) : G) = ⁅(k : G), (n : G)⁆ :=
    map_commutatorElement (f := Subgroup.subtype (P ⊔ H)) (g₁ := k) (g₂ := n)
  rw [hcoe, ← hhp]
  have hcomm : ⁅(k : G), h * p⁆ = ⁅(k : G), h⁆ * (h * ⁅(k : G), p⁆ * h⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  have h1 : ⁅(k : G), h⁆ ∈ H := by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hdnH h).mp hh) (inv_mem hh)
  have hpcl : pCoreOf 2 P ≤ H := hcore.symm ▸ (inf_le_left : H ⊓ L ≤ H)
  have h2 : h * ⁅(k : G), p⁆ * h⁻¹ ∈ H :=
    mul_mem (mul_mem hh ((hLevi.commutator_le.trans hpcl)
      (Subgroup.commutator_mem_commutator hdD hp))) (inv_mem hh)
  exact mul_mem h1 h2

theorem isPIsolatedOver_normalizer_map_of_isGomiLeviData (hψ : Function.Surjective ψ)
    (hker : ψ.ker = D.subgroupOf (P ⊔ H)) (hH : IsPGroup 2 H)
    (hHP : H ≤ normalizer (P : Set G)) (hPL : P ≤ L) (hDP : D ≤ P)
    (hLP : L ⊓ normalizer (H : Set G) ≤ P) (hcore : pCoreOf 2 P = H ⊓ L)
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L))
    (hLevi : IsGomiLeviData L U P D 𝒦) :
    IsPIsolatedOver 2 (normalizer (((H.subgroupOf (P ⊔ H)).map ψ : Subgroup Γ) : Set Γ))
      ((H.subgroupOf (P ⊔ H)).map ψ) := by
  have h := isPIsolatedOver_normalizer_subgroupOf_sup_aux hH hHP hPL hLP hiso
  have hDX : D ≤ P ⊔ H := hDP.trans le_sup_left
  have hodd : ¬ 2 ∣ (H.subgroupOf (P ⊔ H)).relIndex ψ.ker := by
    rw [hker, Subgroup.relIndex_subgroupOf hDX, ← Subgroup.inf_relIndex_right]
    have hcore' : H ⊓ D = pCoreOf 2 P := by
      refine le_antisymm ?_ (le_inf (hcore.symm ▸ (inf_le_left : H ⊓ L ≤ H))
        hLevi.pCoreOf_le)
      calc H ⊓ D ≤ H ⊓ L := inf_le_inf_left H (hLevi.le_inf_normalizer.trans inf_le_left)
        _ = pCoreOf 2 P := hcore.symm
    rw [hcore']
    exact hLevi.not_two_dvd
  have hcent := commutator_normalizer_le_subgroupOf hHP hker hcore hLevi
  exact IsPIsolatedOver.normalizer_map_of_odd_central hψ hH.comap_subtype h hodd hcent

omit [Finite G] [Finite Γ] in
theorem map_subgroupOf_inf_map_sSup_eq_bot (hker : ψ.ker = D.subgroupOf (P ⊔ H))
    (hPL : P ≤ L) (hcore : pCoreOf 2 P = H ⊓ L) (hLevi : IsGomiLeviData L U P D 𝒦)
    (h𝒦 : 𝒦.Nonempty) :
    (H.subgroupOf (P ⊔ H)).map ψ ⊓ ((sSup 𝒦).subgroupOf (P ⊔ H)).map ψ = ⊥ := by
  obtain ⟨K₀, hK₀⟩ := h𝒦
  have hDs : D ≤ sSup 𝒦 := (hLevi.le_of_mem K₀ hK₀).trans (le_sSup hK₀)
  have hHD : H ⊓ sSup 𝒦 ≤ D := by
    calc H ⊓ sSup 𝒦 ≤ H ⊓ P := inf_le_inf_left H (sSup_le hLevi.le_parabolic)
      _ ≤ H ⊓ L := inf_le_inf_left H hPL
      _ = pCoreOf 2 P := hcore.symm
      _ ≤ D := hLevi.pCoreOf_le
  rw [← map_subgroupOf_inf hker H hDs]
  exact map_subgroupOf_eq_bot hker hHD

theorem gomiChevLevi_forall_eq_and_isPIsolatedOver (hψ : Function.Surjective ψ)
    (hker : ψ.ker = D.subgroupOf (P ⊔ H)) (hH : IsPGroup 2 H)
    (hHL : H ≤ normalizer (L : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hHP : H ≤ normalizer (P : Set G)) (hPL : P ≤ L)
    (hLP : L ⊓ normalizer (H : Set G) ≤ P) (hcore : pCoreOf 2 P = H ⊓ L)
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L))
    (hLevi : IsGomiLeviData L U P D 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦)
    (hHK : H ≤ normalizer (K : Set G)) :
    (∀ K' ∈ 𝒦, K' = K) ∧
      IsPIsolatedOver 2 ((K.subgroupOf (P ⊔ H)).map ψ ⊓
        centralizer (((H.subgroupOf (P ⊔ H)).map ψ : Subgroup Γ) : Set Γ)) ⊥ := by
  let S : Set (Subgroup Γ) := (fun K : Subgroup G => (K.subgroupOf (P ⊔ H)).map ψ) '' 𝒦
  have hN : IsDirectProduct S (((sSup 𝒦).subgroupOf (P ⊔ H)).map ψ) :=
    isDirectProduct_image hker (fun K hK => ⟨hLevi.le_of_mem K hK,
      (hLevi.le_parabolic K hK).trans le_sup_left⟩) hLevi.commutator_le_of_ne
      hLevi.inf_sSup_le
  have hPmem : ∀ p ∈ P, ∀ K ∈ 𝒦, K.map (MulAut.conj p).toMonoidHom ∈ 𝒦 := by
    intro p hp K hK
    have hpK : p ∈ normalizer (K : Set G) := hLevi.parabolic_le_normalizer K hK hp
    have hfix : K.map (MulAut.conj p).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hpK
    rw [hfix]
    exact hK
  have hHmem : ∀ h ∈ H, ∀ K ∈ 𝒦, K.map (MulAut.conj h).toMonoidHom ∈ 𝒦 :=
    fun h hh K hK => (hLevi.map_conj h ⟨⟨hHL hh, hHU hh⟩, hHP hh⟩).2 K hK
  have hSG := map_conj_mem_image_of_forall hψ (forall_map_conj_mem_of_le_sup hPmem hHmem)
  have hiso' := isPIsolatedOver_normalizer_map_of_isGomiLeviData hψ hker hH hHP hPL
    ((hLevi.le_of_mem K hK).trans (hLevi.le_parabolic K hK)) hLP hcore hiso hLevi
  have hH' : IsPGroup 2 (((H.subgroupOf (P ⊔ H)).map ψ)) := hH.comap_subtype.map ψ
  have hHN : (((H.subgroupOf (P ⊔ H)).map ψ)) ⊓ (((sSup 𝒦).subgroupOf (P ⊔ H)).map ψ) = ⊥ :=
    map_subgroupOf_inf_map_sSup_eq_bot hker hPL hcore hLevi ⟨K, hK⟩
  have hS : ∀ J ∈ S, 2 ∣ Nat.card J := by
    rintro J ⟨K', hK', rfl⟩
    rw [card_map_subgroupOf hker ((hLevi.le_parabolic K' hK').trans le_sup_left)]
    exact hLevi.two_dvd K' hK'
  refine ⟨fun K' hK' => ?_, ?_⟩
  · obtain ⟨x, hxH, hxeq⟩ := hiso'.exists_map_conj_eq_of_isDirectProduct hN hSG hH' hHN hS
      (show (K.subgroupOf (P ⊔ H)).map ψ ∈ S from ⟨K, hK, rfl⟩)
      (show (K'.subgroupOf (P ⊔ H)).map ψ ∈ S from ⟨K', hK', rfl⟩)
    have hxnorm : x ∈ normalizer ((((K.subgroupOf (P ⊔ H)).map ψ : Subgroup Γ)) : Set Γ) :=
      map_subgroupOf_le_normalizer ψ hHK hxH
    have hfix : (((K.subgroupOf (P ⊔ H)).map ψ)).map (MulAut.conj x).toMonoidHom =
        (K.subgroupOf (P ⊔ H)).map ψ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxnorm
    rw [hfix] at hxeq
    exact ((map_subgroupOf_inj hker ((hLevi.le_parabolic K hK).trans le_sup_left)
      ((hLevi.le_parabolic K' hK').trans le_sup_left) (hLevi.le_of_mem K hK)
      (hLevi.le_of_mem K' hK')).mp hxeq).symm
  · exact hiso'.inf_centralizer_of_isDirectProduct hN hSG hH' hHN
      (show (K.subgroupOf (P ⊔ H)).map ψ ∈ S from ⟨K, hK, rfl⟩)
      (hS _ ⟨K, hK, rfl⟩) (map_subgroupOf_le_normalizer ψ hHK)

end CFSG.GroupTheory
