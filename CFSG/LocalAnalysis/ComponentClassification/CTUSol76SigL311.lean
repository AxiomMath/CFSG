module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL38g

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_oddCoreIn_of_le_of_normalizes {M R X : Subgroup G} (hRM : R ≤ M)
    (hsup : R ⊔ oddCoreIn M = M) (hXR : X ≤ R) (hXodd : Nat.Coprime 2 (Nat.card X))
    (hRX : R ≤ normalizer (X : Set G)) : X ≤ oddCoreIn M := by
  set O := oddCoreIn M
  have hMO : M ≤ normalizer (O : Set G) := le_normalizer_oddCoreIn M
  have hXO : X ≤ normalizer (O : Set G) := (hXR.trans hRM).trans hMO
  have hOP : O ≤ normalizer ((O ⊔ X : Subgroup G) : Set G) := by
    have hcoe : ((O ⊔ X : Subgroup G) : Set G) = (O : Set G) * (X : Set G) :=
      coe_mul_of_right_le_normalizer_left O X hXO
    have key : ∀ o ∈ O, ∀ z ∈ O ⊔ X, o * z * o⁻¹ ∈ O ⊔ X := by
      intro o ho z hz
      have hz' : z ∈ (O : Set G) * (X : Set G) := by rw [← hcoe]; exact hz
      obtain ⟨o', ho', x, hx, rfl⟩ := hz'
      have e : o * (o' * x) * o⁻¹ = (o * o' * (x * o⁻¹ * x⁻¹)) * x := by group
      rw [e]
      refine mul_mem (mem_sup_left (mul_mem (mul_mem ho ho') ?_)) (mem_sup_right hx)
      exact (mem_normalizer_iff.mp (hXO hx) _).mp (inv_mem ho)
    intro o ho
    rw [mem_normalizer_iff]
    intro z
    refine ⟨key o ho z, fun h => ?_⟩
    have := key o⁻¹ (inv_mem ho) _ h
    rwa [show o⁻¹ * (o * z * o⁻¹) * o⁻¹⁻¹ = z by group] at this
  have hRP : R ≤ normalizer ((O ⊔ X : Subgroup G) : Set G) :=
    le_normalizer_sup (hRM.trans hMO) hRX
  have hMP : M ≤ normalizer ((O ⊔ X : Subgroup G) : Set G) := by
    rw [← hsup]
    exact sup_le hRP hOP
  have hPodd : Odd (Nat.card (O ⊔ X : Subgroup G)) :=
    odd_card_sup_of_le_normalizer hXO (Nat.coprime_two_left.mp (coprime_card_oddCoreIn M))
      (Nat.coprime_two_left.mp hXodd)
  have h := inf_le_oddCoreIn (Nat.coprime_two_left.mpr hPodd) hMP
  have hPM : O ⊔ X ≤ M := sup_le (map_subtype_le _) (hXR.trans hRM)
  rw [inf_eq_left.mpr hPM] at h
  exact le_sup_right.trans h

theorem oddCoreIn_le_coreActionKernel {H M : Subgroup G} (hM : IsTwoComponentIn M H) :
    oddCoreIn H ≤ coreActionKernel M := by
  have hON : oddCoreIn H ≤ normalizer (M : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hM.1 hM.2
  have hMO : M ≤ normalizer (oddCoreIn H : Set G) := hM.1.trans (le_normalizer_oddCoreIn H)
  have hIO : oddCoreIn H ⊓ M ≤ oddCoreIn M := inf_le_oddCoreIn (coprime_card_oddCoreIn H) hMO
  intro g hg
  refine mem_coreActionKernel.mpr ⟨hON hg, fun j hj => hIO (mem_inf.mpr ⟨?_, ?_⟩)⟩
  · have h1 := (mem_normalizer_iff.mp (hMO (inv_mem hj)) _).mp (inv_mem hg)
    rw [inv_inv] at h1
    exact mul_mem h1 hg
  · have h1 : g⁻¹ * j * g ∈ M := by
      have := (mem_normalizer_iff.mp (hON (inv_mem hg)) j).mp hj
      simpa [inv_inv] using this
    have e : j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) := by group
    rw [e]
    exact M.mul_mem (M.inv_mem hj) h1

theorem sup_oddCoreIn_le_coreActionKernel {H M M' : Subgroup G} (hM : IsTwoComponentIn M H)
    (hM' : IsTwoComponentIn M' H) (hne : M ≠ M') : M' ⊔ oddCoreIn H ≤ coreActionKernel M :=
  sup_le (Foote5.SolMax.le_coreActionKernel_of_ne hM hM' hne) (oddCoreIn_le_coreActionKernel hM)

theorem commutator_oddCoreIn_inf_centralizer_le {H M : Subgroup G} (hM : IsTwoComponentIn M H)
    {x : G} (hx2 : orderOf x = 2) (hxM : x ∈ coreActionKernel M) :
    ⁅M, oddCoreIn (H ⊓ centralizer ({x} : Set G))⁆ ≤ oddCoreIn H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := H ⊓ centralizer ({x} : Set G)
  set Y := oddCoreIn C
  have hMq := isQuasisimple_quotient_of_isPComponent hM.1 hM.2
  have hsup : (M ⊓ centralizer ({x} : Set G)) ⊔ oddCoreIn M = M := by
    have h := inf_centralizer_sup_oddCoreIn_eq
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])) (zpowers_le.mpr hxM)
    rwa [centralizer_zpowers_eq] at h
  obtain ⟨hR2, -, hRsup, -⟩ := cover_facts hMq inf_le_left hsup
  set R := oddResidualIn (M ⊓ centralizer ({x} : Set G))
  have hRM : R ≤ M := hR2.1.trans inf_le_left
  have hYC : M ⊓ centralizer ({x} : Set G) ≤ C := inf_le_inf_right _ hM.1
  have hsub : ((M ⊓ centralizer ({x} : Set G)).subgroupOf C).IsSubnormal := by
    have h0 : (M.subgroupOf H).IsSubnormal :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hM.1).mp hM.2).1
    have h1 := isSubnormal_subgroupOf_of_le (inf_le_left : C ≤ H) h0
    convert h1 using 1
    ext z
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp z.2).2⟩⟩
  have hRC : IsTwoComponentIn R C :=
    ⟨hR2.1.trans hYC, GrSLit.isPComponent_subgroupOf_of_isSubnormal hR2.1 hYC hsub hR2.2⟩
  have hYR : Y ≤ normalizer (R : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hRC.1 hRC.2
  have hRY : R ≤ normalizer (Y : Set G) := hRC.1.trans (le_normalizer_oddCoreIn C)
  have hcomm : ⁅R, Y⁆ ≤ Y ⊓ R := by
    rw [commutator_le]
    intro r hr y hy
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact Y.mul_mem ((mem_normalizer_iff.mp (hRY hr) y).mp hy) (Y.inv_mem hy)
    · rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine R.mul_mem hr ?_
      have := (mem_normalizer_iff.mp (hYR hy) (r⁻¹)).mp (inv_mem hr)
      simpa [mul_assoc] using this
  have hYRO : Y ⊓ R ≤ oddCoreIn M :=
    le_oddCoreIn_of_le_of_normalizes hRM hRsup inf_le_right
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn C))
      (fun r hr => mem_normalizer_inf (hRY hr) (le_normalizer hr))
  have hOMH : oddCoreIn M ≤ oddCoreIn H := oddCoreIn_le_of_isTwoComponentIn hM
  have hHO : H ≤ normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  obtain ⟨Kc, hKc⟩ := exists_subgroup_commutator_mem (C := H) (A := Y) hHO
  have hRK : R ≤ Kc := fun r hr => (hKc r).mpr ⟨hM.1 (hRM hr), fun y hy => by
    have h := hOMH (hYRO (hcomm (commutator_mem_commutator hr hy)))
    have e : ⁅y, r⁆ = ⁅r, y⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact inv_mem h⟩
  have hOK : oddCoreIn M ≤ Kc := fun o ho => (hKc o).mpr ⟨hM.1 (map_subtype_le _ ho), fun y hy => by
    have hyH : y ∈ H := (inf_le_left : C ≤ H) (map_subtype_le _ hy)
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hHO hyH) _).mp (hOMH ho)) (inv_mem (hOMH ho))⟩
  have hMK : M ≤ Kc := hRsup ▸ sup_le hRK hOK
  rw [commutator_le]
  intro m hm y hy
  have h := ((hKc m).mp (hMK hm)).2 y hy
  have e : ⁅m, y⁆ = ⁅y, m⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact inv_mem h

theorem commutator_oddCoreIn_inf_centralizer_zpowers_le {H M : Subgroup G}
    (hM : IsTwoComponentIn M H) {f u : G} (hf2 : orderOf f = 2) (hfM : f ∈ coreActionKernel M)
    (hu : u ∈ M ⊔ oddCoreIn H) :
    ⁅oddCoreIn (H ⊓ centralizer ({f} : Set G)), zpowers u⁆ ≤ oddCoreIn H := by
  set Y := oddCoreIn (H ⊓ centralizer ({f} : Set G))
  have hHO : H ≤ normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  have hYH : Y ≤ H := (map_subtype_le _).trans inf_le_left
  obtain ⟨Kc, hKc⟩ := exists_subgroup_commutator_mem (C := H) (A := Y) hHO
  have hMY := commutator_oddCoreIn_inf_centralizer_le hM hf2 hfM
  have hMK : M ≤ Kc := fun m hm => (hKc m).mpr ⟨hM.1 hm, fun y hy => by
    have h := hMY (commutator_mem_commutator hm hy)
    have e : ⁅y, m⁆ = ⁅m, y⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact inv_mem h⟩
  have hOK : oddCoreIn H ≤ Kc := fun o ho => (hKc o).mpr ⟨map_subtype_le _ ho, fun y hy => by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hHO (hYH hy)) _).mp ho) (inv_mem ho)⟩
  have huK : zpowers u ≤ Kc := zpowers_le.mpr ((sup_le hMK hOK) hu)
  rw [commutator_le]
  intro y hy z hz
  exact ((hKc z).mp (huK hz)).2 y hy

theorem oddCoreIn_inf_inf_le_oddCoreIn {H : Subgroup G} {f u : G} (hfH : f ∈ H) (huH : u ∈ H)
    (hf2 : orderOf f = 2) (hu2 : orderOf u = 2) (hfu : f * u = u * f)
    (hM : ∀ M : Subgroup G, IsTwoComponentIn M H →
      f ∈ coreActionKernel M ∨ u ∈ coreActionKernel M) :
    oddCoreIn (H ⊓ centralizer ({f} : Set G)) ⊓ oddCoreIn (H ⊓ centralizer ({u} : Set G)) ≤
      oddCoreIn H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Yf := oddCoreIn (H ⊓ centralizer ({f} : Set G))
  set Yu := oddCoreIn (H ⊓ centralizer ({u} : Set G))
  have hYfC : Yf ≤ H ⊓ centralizer ({f} : Set G) := map_subtype_le _
  have hYuC : Yu ≤ H ⊓ centralizer ({u} : Set G) := map_subtype_le _
  have hZH : Yf ⊓ Yu ≤ H := inf_le_left.trans (hYfC.trans inf_le_left)
  have hZodd : Odd (Nat.card (Yf ⊓ Yu : Subgroup G)) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn _))
  refine le_oddCoreIn_of_commutator_le hZH hZodd ?_ fun M hM' => ?_
  ·
    have hzf : zpowers f ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq, zpowers_le]
      exact mem_centralizer_singleton_iff.mpr hfu
    have hS2 := isPGroup_sup_of_le_centralizer
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one]))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])) hzf
    have hSH : zpowers f ⊔ zpowers u ≤ H := sup_le (zpowers_le.mpr hfH) (zpowers_le.mpr huH)
    have hZS : Yf ⊓ Yu ≤ centralizer ((zpowers f ⊔ zpowers u : Subgroup G) : Set G) := by
      refine le_centralizer_iff.mp (sup_le ?_ ?_)
      · refine le_centralizer_iff.mp ?_
        rw [centralizer_zpowers_eq]
        exact inf_le_left.trans (hYfC.trans inf_le_right)
      · refine le_centralizer_iff.mp ?_
        rw [centralizer_zpowers_eq]
        exact inf_le_right.trans (hYuC.trans inf_le_right)
    have hN : H ⊓ centralizer ((zpowers f ⊔ zpowers u : Subgroup G) : Set G) ≤
        normalizer ((Yf ⊓ Yu : Subgroup G) : Set G) := by
      intro g hg
      obtain ⟨hgH, hgS⟩ := mem_inf.mp hg
      have hgf : g ∈ centralizer ({f} : Set G) :=
        centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_left (mem_zpowers f))) hgS
      have hgu : g ∈ centralizer ({u} : Set G) :=
        centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers u))) hgS
      exact mem_normalizer_inf (le_normalizer_oddCoreIn _ ⟨hgH, hgf⟩)
        (le_normalizer_oddCoreIn _ ⟨hgH, hgu⟩)
    exact commutator_oddTwoCoreIn_le_of_normalizes hSH hS2 hZH hZodd hZS hN
  ·
    rcases hM M hM' with h | h
    · exact (Subgroup.commutator_mono le_rfl inf_le_left).trans
        (commutator_oddCoreIn_inf_centralizer_le hM' hf2 h)
    · exact (Subgroup.commutator_mono le_rfl inf_le_right).trans
        (commutator_oddCoreIn_inf_centralizer_le hM' hu2 h)

theorem theta_zpowers_le_oddCoreIn {H M₁ M₂ : Subgroup G} (hM₁ : IsTwoComponentIn M₁ H)
    (hM₂ : IsTwoComponentIn M₂ H) (hne : M₁ ≠ M₂) {f u : G} (hf2 : orderOf f = 2)
    (hu2 : orderOf u = 2) (hfu : f * u = u * f) (hf : f ∈ M₁ ⊔ oddCoreIn H)
    (hu : u ∈ M₂ ⊔ oddCoreIn H) (hOf : oddCoreIn (centralizer ({f} : Set G)) ≤ H)
    (hOu : oddCoreIn (centralizer ({u} : Set G)) ≤ H) :
    theta (zpowers u) f ≤ oddCoreIn H := by
  have hMH₁ : M₁ ⊔ oddCoreIn H ≤ H := sup_le hM₁.1 (map_subtype_le _)
  have hMH₂ : M₂ ⊔ oddCoreIn H ≤ H := sup_le hM₂.1 (map_subtype_le _)
  have hfH : f ∈ H := hMH₁ hf
  have huH : u ∈ H := hMH₂ hu
  have hfQ : f ∈ coreActionKernel M₂ := sup_oddCoreIn_le_coreActionKernel hM₂ hM₁ hne.symm hf
  have hOxle : ∀ x : G, oddCoreIn (centralizer ({x} : Set G)) ≤ H →
      oddCoreIn (centralizer ({x} : Set G)) ≤ oddCoreIn (H ⊓ centralizer ({x} : Set G)) := by
    intro x hOx
    have h := inf_le_oddCoreIn (coprime_card_oddCoreIn (centralizer ({x} : Set G)))
      (inf_le_right.trans (le_normalizer_oddCoreIn (centralizer ({x} : Set G))) :
        H ⊓ centralizer ({x} : Set G) ≤ _)
    rwa [inf_eq_left.mpr (le_inf hOx (map_subtype_le _))] at h
  have hMf : ∀ M : Subgroup G, IsTwoComponentIn M H →
      f ∈ coreActionKernel M ∨ u ∈ coreActionKernel M := by
    intro M hM
    by_cases h1 : M = M₁
    · rw [h1]
      exact Or.inr (sup_oddCoreIn_le_coreActionKernel hM₁ hM₂ hne hu)
    · exact Or.inl (sup_oddCoreIn_le_coreActionKernel hM hM₁ h1 hf)
  rw [theta, centralizer_zpowers_eq]
  refine sup_le ?_ ?_
  · exact (Subgroup.commutator_mono (hOxle f hOf) le_rfl).trans
      (commutator_oddCoreIn_inf_centralizer_zpowers_le hM₂ hf2 hfQ hu)
  · exact (inf_le_inf (hOxle f hOf) (hOxle u hOu)).trans
      (oddCoreIn_inf_inf_le_oddCoreIn hfH huH hf2 hu2 hfu hMf)

end CFSG.ComponentClassification.Sol76.Sig
