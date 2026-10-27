module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeF3Fact
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPInputs
public import Certificates.Certificate2020
public import Certificates.Certificate2022
public import Certificates.Certificate2110
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2114
public import Certificates.Certificate2115
public import Certificates.Certificate2116
public import Certificates.Certificate2117
public import Certificates.Certificate2118
public import Certificates.Certificate2223
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2275
public import Certificates.Certificate2276
public import Certificates.Certificate3168
public import Certificates.Certificate22701
public import Certificates.Certificate22703
public import Certificates.Certificate22704
public import Certificates.Certificate22705
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUMain
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKP

variable {X : Type} [Group X] [Finite X]

theorem exists_pair_of_equiv
    {L : Subgroup X} (e₀ : ↥L ≃* Blueprint.NativeSporadic.He) {u : X} (hu : HeldTwoA L u)
    {J : Subgroup X} (e : ↥J ≃* ↥(gsFixedLayer L u)) :
    ∃ w₁ w₂ : ↥J, w₁ * w₁ = 1 ∧ w₂ * w₂ = 1 ∧ w₁ * w₂ = w₂ * w₁ ∧ w₁ ∉ center ↥J ∧
      w₂ ∉ center ↥J ∧ w₁ * w₂ ∉ center ↥J := by
  obtain ⟨x₁, hx₁, x₂, hx₂, h1, h2, hc, n1, n2, n3⟩ := HeF3.exists_noncentral_pair e₀ hu
  set k₁ : ↥(gsFixedLayer L u) := ⟨x₁, hx₁⟩
  set k₂ : ↥(gsFixedLayer L u) := ⟨x₂, hx₂⟩
  have hcen : ∀ v : ↥J, v ∈ center ↥J →
      ((e v : ↥(gsFixedLayer L u)) : X) ∈
        (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro v hv
    refine ⟨e v, mem_center_iff.mpr fun g => ?_, rfl⟩
    rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, mem_center_iff.mp hv]
  refine ⟨e.symm k₁, e.symm k₂, ?_, ?_, ?_, fun h => n1 ?_, fun h => n2 ?_, fun h => n3 ?_⟩
  · rw [← map_mul, show k₁ * k₁ = 1 from Subtype.ext h1, map_one]
  · rw [← map_mul, show k₂ * k₂ = 1 from Subtype.ext h2, map_one]
  · rw [← map_mul, ← map_mul, show k₁ * k₂ = k₂ * k₁ from Subtype.ext hc]
  · have h' := hcen _ h
    rw [MulEquiv.apply_symm_apply] at h'
    exact h'
  · have h' := hcen _ h
    rw [MulEquiv.apply_symm_apply] at h'
    exact h'
  · have h' := hcen _ h
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact h'

theorem false_of_moved
    {L : Subgroup X} (hset : HeldEndSetting X L) {a : X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) {u : X} (hu : HeldTwoA L u)
    (hKc : IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))))
    {J : Subgroup X} (hJC : J ≤ centralizer ({u} : Set X))
    (hJc : IsComponent (J.subgroupOf (centralizer ({u} : Set X))))
    (hJK : J ≠ gsFixedLayer L u) (e : ↥J ≃* ↥(gsFixedLayer L u)) (hJa : conjugate J a ≠ J) :
    False := by
  set K := gsFixedLayer L u with hK
  set Cu := centralizer ({u} : Set X) with hCu
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haCu : a ∈ Cu := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hKC : K ≤ Cu := (gsFixedLayer_le_inf L u).trans inf_le_right
  have hKa : conjugate K a = K :=
    conjugate_eq_self (((gsFixedLayer_le_inf L u).trans inf_le_left).trans hLa)
  set Ja := conjugate J a with hJadef
  have hJaC : Ja ≤ Cu := by
    intro x hx
    rw [mem_conjugate] at hx
    have h := mul_mem (mul_mem (inv_mem haCu) (hJC hx)) haCu
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h
  have hJac : IsComponent (Ja.subgroupOf Cu) := isComponent_conjugate hJc haCu
  have hJaK : Ja ≠ K := by
    intro h
    apply hJK
    rw [← conjugate_conjugate (H := J) haa, ← hJadef, h, hKa]
  have hJJa := commute_of_components hJC hJaC hJc hJac (Ne.symm hJa)
  have hJK' := commute_of_components hJC hKC hJc hKc hJK
  have hJaK' := commute_of_components hJaC hKC hJac hKc hJaK
  have hαJ : ∀ x ∈ J, a⁻¹ * x * a⁻¹⁻¹ ∈ Ja := fun x hx => by
    rw [mem_conjugate]
    simpa [mul_assoc] using hx
  obtain ⟨w₁, w₂, h₁, h₂, hc, hn₁, hn₂, hn₃⟩ := exists_pair_of_equiv hset.2.2.2.1.some hu e
  refine false_of_hom hset ha hLa hu
    (LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC) hJc.1)
    (HeDQ.delta hJJa hαJ) ?_ ?_ ?_ h₁ h₂ hc hn₁ hn₂ hn₃
  · intro j
    rw [mem_centralizer_singleton_iff, HeDQ.delta_apply]
    have hcj := hJJa j j.2 _ (hαJ j j.2)
    simp only [hainv] at hcj ⊢
    calc (j : X) * (a * j * a) * a = (a * j * a) * j * a := by rw [hcj]
      _ = a * ((j : X) * (a * j * a)) := by group
  · intro j k hk
    rw [HeDQ.delta_apply]
    have h1 : Commute k j := (hJK' j j.2 k hk).symm
    have h2 : Commute k (a⁻¹ * j * a⁻¹⁻¹) := (hJaK' _ (hαJ j j.2) k hk).symm
    exact ((h1.mul_right h2).eq).symm
  · intro j hj
    rw [HeDQ.delta_apply] at hj
    have hjinv : (j : X)⁻¹ ∈ Ja := by
      rw [← eq_inv_of_mul_eq_one_right hj]
      exact hαJ j j.2
    refine mem_center_iff.mpr fun g => Subtype.ext ?_
    have h := hJJa g g.2 _ hjinv
    show (g : X) * j = j * g
    calc (g : X) * j = (j : X) * ((j : X)⁻¹ * g) * j := by group
      _ = (j : X) * (g * (j : X)⁻¹) * j := by rw [← h]
      _ = (j : X) * g := by group

theorem false_of_centralized
    {L : Subgroup X} (hset : HeldEndSetting X L) {a : X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) {u : X} (hu : HeldTwoA L u)
    (hKc : IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))))
    {J : Subgroup X} (hJC : J ≤ centralizer ({u} : Set X))
    (hJc : IsComponent (J.subgroupOf (centralizer ({u} : Set X))))
    (hJK : J ≠ gsFixedLayer L u) (e : ↥J ≃* ↥(gsFixedLayer L u))
    (haJ : a ∈ centralizer (J : Set X)) : False := by
  have hKC : gsFixedLayer L u ≤ centralizer ({u} : Set X) :=
    (gsFixedLayer_le_inf L u).trans inf_le_right
  have hJK' := commute_of_components hJC hKC hJc hKc hJK
  obtain ⟨w₁, w₂, h₁, h₂, hc, hn₁, hn₂, hn₃⟩ := exists_pair_of_equiv hset.2.2.2.1.some hu e
  refine false_of_hom hset ha hLa hu
    (LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC) hJc.1) J.subtype ?_ ?_ ?_
    h₁ h₂ hc hn₁ hn₂ hn₃
  · intro j
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haJ j j.2)
  · intro j k hk
    exact hJK' j j.2 k hk
  · intro j hj
    rw [show j = 1 from Subtype.ext hj]
    exact one_mem _

theorem false_of_component
    (hKI : HeldKInvariantComponentStep) {L : Subgroup X} (hset : HeldEndSetting X L) {a : X}
    (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) {u : X}
    (hu : HeldTwoA L u)
    (hKc : IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))))
    {J : Subgroup X} (hJC : J ≤ centralizer ({u} : Set X))
    (hJc : IsComponent (J.subgroupOf (centralizer ({u} : Set X))))
    (hJK : J ≠ gsFixedLayer L u) (e : ↥J ≃* ↥(gsFixedLayer L u)) : False := by
  by_cases hJa : conjugate J a = J
  · by_cases haJ : a ∈ centralizer (J : Set X)
    · exact false_of_centralized hset ha hLa hu hKc hJC hJc hJK e haJ
    · exact hKI X L hset a u J ha hLa hLc hu hKc hJC hJc hJK ⟨e⟩ hJa haJ
  · exact false_of_moved hset ha hLa hu hKc hJC hJc hJK e hJa

end HeKP

open HeKP in
theorem heldKNormalFromComponent_of_inputs
    (hKI : HeldKInvariantComponentStep) : HeldKNormalFromComponent := by
  intro X _ _ L hset u hu hKc
  obtain ⟨⟨-, -, -, -, -, ⟨a, ha, hLa, hLc⟩, -⟩, -⟩ := id hset
  set K := gsFixedLayer L u with hK
  set Cu := centralizer ({u} : Set X) with hCu
  have hKC : K ≤ Cu := (gsFixedLayer_le_inf L u).trans inf_le_right
  refine ⟨⟨fun n hn g => ?_⟩, fun K₁ hK₁C hK₁n ⟨e⟩ => ?_⟩
  ·
    set J := conjugate K ((g : X)⁻¹) with hJ
    have hgJ : ((g * n * g⁻¹ : ↥Cu) : X) ∈ J := by
      rw [hJ, mem_conjugate]
      have e1 : (g : X)⁻¹ * ((g * n * g⁻¹ : ↥Cu) : X) * (g : X)⁻¹⁻¹ = n := by
        simp only [coe_mul, coe_inv]
        group
      rw [e1]
      exact hn
    by_cases hJK : J = K
    · rw [mem_subgroupOf, ← hJK]
      exact hgJ
    · exfalso
      have hJC : J ≤ Cu := by
        intro x hx
        rw [hJ, mem_conjugate] at hx
        have h := mul_mem (mul_mem g.2 (hKC hx)) (inv_mem g.2)
        rwa [show (g : X) * ((g : X)⁻¹ * x * (g : X)⁻¹⁻¹) * (g : X)⁻¹ = x by group] at h
      have hJc : IsComponent (J.subgroupOf Cu) := isComponent_conjugate hKc (inv_mem g.2)
      have e' : ↥J ≃* ↥K :=
        (K.equivMapOfInjective (MulAut.conj ((g : X)⁻¹)⁻¹).toMonoidHom
          (MulAut.conj ((g : X)⁻¹)⁻¹).injective).symm
      exact false_of_component hKI hset ha hLa hLc hu hKc hJC hJc hJK e'
  ·
    by_contra hne
    have hq : IsQuasisimple ↥(K₁.subgroupOf Cu) :=
      LocalCores.isQuasisimple_of_mulEquiv
        ((subgroupOfEquivOfLe hKC).trans (e.symm.trans (subgroupOfEquivOfLe hK₁C).symm)) hKc.1
    exact false_of_component hKI hset ha hLa hLc hu hKc hK₁C ⟨hq, hK₁n.isSubnormal⟩ hne e

end CFSG.ComponentClassification.GrSLit
