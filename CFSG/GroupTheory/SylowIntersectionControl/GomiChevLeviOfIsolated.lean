module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviCenterless
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviQuotient
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviSingle

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

private lemma gomiChevLevi_le_normalizer_of_commutator_le {G : Type} [Group G] {P D : Subgroup G}
    (hcomm : ⁅P, D⁆ ≤ D) : P ≤ normalizer (D : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro p hp d hd
  have hc : ⁅p, d⁆ ∈ D := hcomm (Subgroup.commutator_mem_commutator hp hd)
  have hpd : p * d * p⁻¹ = ⁅p, d⁆ * d :=
    _root_.conj_eq_commutatorElement_mul (g₁ := p) (g₂ := d)
  rw [hpd]
  exact mul_mem hc hd

private lemma gomiChevLevi_aux_not_le {G : Type} [Group G] {L U H A K : Subgroup G}
    (hHA : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom = A)
    (hHL : H ≤ normalizer (L : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hAK : ¬ A ⊓ K ≤ L ⊓ normalizer (U : Set G)) {h : G} (hh : h ∈ H) :
    ¬ A ⊓ K.map (MulAut.conj h).toMonoidHom ≤ L ⊓ normalizer (U : Set G) := by
  intro hle
  apply hAK
  have hB : h ∈ normalizer (L ⊓ normalizer (U : Set G) : Subgroup G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHL hh, Subgroup.le_normalizer (hHU hh)⟩
  have hBeq : (L ⊓ normalizer (U : Set G)).map (MulAut.conj h).toMonoidHom =
      L ⊓ normalizer (U : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mp hB
  have hAeq : (A ⊓ K).map (MulAut.conj h).toMonoidHom =
      A ⊓ K.map (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.map_inf A K (MulAut.conj h).toMonoidHom (MulAut.conj h).injective, hHA h hh]
  have hle' : (A ⊓ K).map (MulAut.conj h).toMonoidHom ≤
      (L ⊓ normalizer (U : Set G)).map (MulAut.conj h).toMonoidHom := by
    rw [hAeq, hBeq]
    exact hle
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj h).injective).mp hle'

theorem gomiChevLevi_core (hIso : GomiChevIsolated) (hR1 : GomiChevRankOneOvergroups)
    (hR2 : GomiFact36Overgroups) {G : Type} [Group G] [Finite G] {L U H P D A : Subgroup G}
    {𝒦 : Set (Subgroup G)} (hU : IsSylowOf 2 U L) (hH : IsPGroup 2 H)
    (hHL : H ≤ normalizer (L : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hHP : H ≤ normalizer (P : Set G)) (hPL : P ≤ L)
    (hLP : L ⊓ normalizer (H : Set G) ≤ P) (hcore : pCoreOf 2 P = H ⊓ L)
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L))
    (hLevi : IsGomiLeviData L U P D 𝒦) (hA : IsGomiAtom L U A) (hAP : A < P)
    (hHA : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom = A) : False := by
  obtain ⟨K, hK, hAK, huniq⟩ := hLevi.existsUnique_factor A hA hAP.le
  have hDK : D ≤ K := hLevi.le_of_mem K hK
  have hKP : K ≤ P := hLevi.le_parabolic K hK
  have hDP : D ≤ P := hDK.trans hKP
  have hPD : P ≤ normalizer (D : Set G) := by
    refine gomiChevLevi_le_normalizer_of_commutator_le ?_
    rw [Subgroup.commutator_comm]
    exact hLevi.commutator_le.trans hLevi.pCoreOf_le
  have hHD : H ≤ normalizer (D : Set G) := by
    intro h hh
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (hLevi.map_conj h ⟨⟨hHL hh, hHU hh⟩, hHP hh⟩).1
  have hDnorm : (D.subgroupOf (P ⊔ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hDP.trans le_sup_left)).2 (sup_le hPD hHD)
  let ψ : ↥(P ⊔ H) →* (↥(P ⊔ H) ⧸ D.subgroupOf (P ⊔ H)) :=
    QuotientGroup.mk' (D.subgroupOf (P ⊔ H))
  have hψ : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hker : ψ.ker = D.subgroupOf (P ⊔ H) := QuotientGroup.ker_mk' _
  have hHK : H ≤ normalizer (K : Set G) := by
    intro h hh
    have hKmap : K.map (MulAut.conj h).toMonoidHom ∈ 𝒦 :=
      (hLevi.map_conj h ⟨⟨hHL hh, hHU hh⟩, hHP hh⟩).2 K hK
    have hnot := gomiChevLevi_aux_not_le hHA hHL hHU hAK hh
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hKmap hnot)
  obtain ⟨hsingle, hisoK⟩ :=
    gomiChevLevi_forall_eq_and_isPIsolatedOver hψ hker hH hHL hHU hHP hPL hLP hcore hiso hLevi
      hK hHK
  have hsSup : sSup 𝒦 = K := by
    rw [Set.eq_singleton_iff_unique_mem.2 ⟨hK, hsingle⟩, sSup_singleton]
  have hUK : U ≤ K := by rw [← hsSup]; exact hLevi.sylow_le
  have hPBK : P ≤ L ⊓ normalizer (U : Set G) ⊔ K := by rw [← hsSup]; exact hLevi.le_sup
  have hHA' : H ≤ normalizer (A : Set G) := fun h hh =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hHA h hh)
  exact gomiChevLevi_false_of_single_factor hIso hR1 hR2 hU hH hHU hHK hHA' hPL hA.1.le hAP hAK
    hLevi.le_inf_normalizer hDK hKP hPD hUK hPBK (hLevi.factor K hK) hψ hker hisoK

theorem gomiChevLevi_of_gomiChevIsolated (hIso : GomiChevIsolated)
    (hLevi : GomiChevLeviDecomposition) (hR1 : GomiChevRankOneOvergroups)
    (hR2 : GomiFact36Overgroups) : GomiChevLevi := by
  refine gomiChevLevi_of_center_eq_bot ?_
  intro G _ _ L U H hL hZ hU hH hHL hHU hBP hPL hcore hiso
  by_cases hat : IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
  · exact Or.inl hat
  · refine Or.inr fun A hA hAP => ?_
    by_contra hfix
    push Not at hfix
    obtain ⟨D, 𝒦, hLD⟩ :=
      hLevi G L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) hL hZ hU hBP hPL hat
    have hAP' : A < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
      lt_of_le_of_ne hAP (fun h => hat (h ▸ hA))
    have hHP : H ≤ normalizer
        ((L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      intro h hh
      have hN : h ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hh, hHL hh⟩
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hHL hh, Subgroup.le_normalizer hN⟩
    have hLP : L ⊓ normalizer (H : Set G) ≤
        L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
      intro x hx
      exact ⟨hx.1, Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hx.2, Subgroup.le_normalizer hx.1⟩⟩
    exact gomiChevLevi_core hIso hR1 hR2 hU hH hHL hHU hHP inf_le_left hLP hcore hiso hLD hA
      hAP' hfix

end CFSG.GroupTheory
