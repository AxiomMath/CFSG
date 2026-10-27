module

public import CFSG.FeitThompson.Representations.PrimeDadeLowFamilyBridgeRigidity
public import CFSG.FeitThompson.Representations.PrincipalColumnProjectionNormalizedPivot
public import CFSG.FeitThompson.Representations.TypeVTwoFamilyCoherenceJoining
public import CFSG.FeitThompson.Representations.CoherentMapOrientsEqualDegreeRows

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeDadeColumnGluing

open PrimeDadeLowFamily

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {ζ : ↥L → ℂ} {d n : ℤ} {A₀ : Set G} {T : G → Subgroup G}
  {S₁ S₂ : Set (↥L → ℂ)} {ν₁ : Submodule.span ℤ S₁ →+ virtualChars G}
  {τ₁ : charSpanZero S₁ →+ virtualChars G} {τ₂ : charSpanZero S₂ →+ virtualChars G}
  {τU : charSpanZero (S₁ ∪ S₂) →+ virtualChars G}

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
include h in
theorem primeTIrow_principal_sub_mem_dadeZDomain (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀) :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ ∈ dadeZDomain L A₀ :=
  mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
    (h.primeTIrow_sub_mem_span_Irr hB.isometry hB.mem_indFam), fun x hx =>
      h.primeTIrow_sub_apply_eq_zero hB.isometry hB.mem_indFam hB.apply_one fun hmemx =>
        hx (hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hmemx.1
          (by simpa using hmemx.2), rfl⟩)⟩

omit [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [K.Normal] in
theorem sum_prodCharEta_eq_prodCharEtaColSum [Finite G]
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) :
    ∑ i : Irr ↥W₁, hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
      = hW.prodCharEtaColSum ω (irrMapSubtype L W₂ j) := by
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum]
  exact Fintype.sum_bijective (irrMapSubtype L W₁) (irrMapSubtype_bijective L W₁) _ _ fun _ => rfl

theorem dadeZMap_primeTIrow_sub_smul_eq (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hprime₁ : (Nat.card ↥W₁).Prime) (hprime₂ : (Nat.card ↥W₂).Prime)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁)
    (hncard : (S₁.ncard : ℤ) = n) (hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥W₁ : ℂ))
    (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hpsi : tauPrincipalRowSub hB hA hD
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
          (principalIrr ↥(W₂.map L.subtype)) - (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ))
    (hpsi' : ((dadeZMap hD ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
        primeTIrow_principal_sub_mem_dadeZDomain (h := h) hB hA⟩ :
          charSpanZero (Irr G)) : G → ℂ)
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
          (principalIrr ↥(W₂.map L.subtype)) - (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ))
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (hmem : h.primeTIrow σ j - (d : ℂ) • ζ ∈ dadeZDomain L A₀) :
    ((dadeZMap hD ⟨h.primeTIrow σ j - (d : ℂ) • ζ, hmem⟩ : charSpanZero (Irr G)) : G → ℂ)
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j)
        - (d : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set e : G → ℂ := (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) with he
  have hmem0 := primeTIrow_principal_sub_mem_dadeZDomain (h := h) hB hA (A₀ := A₀)
  have key : (⟨h.primeTIrow σ j - (d : ℂ) • ζ, hmem⟩ : dadeZDomain L A₀)
      = (∑ i : Irr ↥W₁, (⟨h.primeTIbridge σ ζ 1 n i j,
            primeTIbridge_mem_dadeZDomain hB hA i hj⟩ : dadeZDomain L A₀))
        + ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ, hmem0⟩ := by
    refine Subtype.ext ?_
    push_cast
    rw [sum_primeTIbridge_eq hB j]
    simp only [Int.cast_one, one_smul]
    abel
  have hmap := congrArg (fun z : charSpanZero (Irr G) => (z : G → ℂ))
    (congrArg (dadeZMap hD) key)
  simp only [map_add, map_sum, Submodule.coe_add] at hmap
  have hsum : (((∑ i : Irr ↥W₁, dadeZMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
        primeTIbridge_mem_dadeZDomain hB hA i hj⟩ : charSpanZero (Irr G))) : G → ℂ)
      = ∑ i : Irr ↥W₁, ((dadeZMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
          primeTIbridge_mem_dadeZDomain hB hA i hj⟩ : charSpanZero (Irr G)) : G → ℂ) := by
    simp
  rw [hsum] at hmap
  have hb : ∀ i : Irr ↥W₁,
      ((dadeZMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
          primeTIbridge_mem_dadeZDomain hB hA i hj⟩ : charSpanZero (Irr G)) : G → ℂ)
        = hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
          - hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype))
          - (n : ℂ) • e := by
    intro i
    rw [← tauBridge_def hB hA hD i hj]
    exact tauBridge_eq_prodCharEta_sub hodd hB hA hD hstab hdisj hω hprime₁ hprime₂ hS₁ hS₁star
      hζS₁ hncard hdeg hν₁ hτ₁ hpsi i hj
  rw [hmap, Finset.sum_congr rfl fun i _ => hb i, hpsi']
  have hcard : (Fintype.card ↑(Irr ↥W₁) : ℂ) = (Nat.card ↥W₁ : ℂ) := by
    rw [← Nat.card_eq_fintype_card, h.isCyclicTIPair.card_Irr_left]
  have hcolj := sum_prodCharEta_eq_prodCharEtaColSum (ω := ω) hW j
  have hcol0 : ∑ i : Irr ↥W₁,
      hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype))
      = hW.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype)) := by
    have hx := sum_prodCharEta_eq_prodCharEtaColSum (ω := ω) hW (principalIrr ↥W₂)
    rwa [irrMapSubtype_principal] at hx
  have hd := hB.sub_eq_complex
  funext x
  have hcj := congrFun hcolj x
  have hc0 := congrFun hcol0 x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply,
    Finset.sum_apply, smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hcj hc0 ⊢
  rw [hcj, hc0, hcard]
  push_cast at hd ⊢
  linear_combination (e x) * hd

omit [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)] [K.Normal] in
theorem image_bridgeSupport_subset
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀) :
    (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀ := by
  refine Set.Subset.trans (Set.image_mono (bridgeSupport_subset ?_ ?_)) hA
  · exact fun x hx => mem_primeTIbridgeSupport_of_mem_of_ne_one hx.1 (by simpa using hx.2)
  · intro x hx
    obtain ⟨t, v, hv, rfl⟩ := mem_cyclicTIsetConj.1 hx
    exact mem_primeTIbridgeSupport_of_isConj hv (isConj_iff.2 ⟨t⁻¹, by group⟩)

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem coe_tau_eq_dadeMapFun {P : Set (↥L → ℂ)} {τ : charSpanZero P →+ virtualChars G}
    (hD : IsDadeData L A₀ T) (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hτ : ∀ (f : charSpanZero P) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (f : charSpanZero P) :
    ((τ f : virtualChars G) : G → ℂ) = dadeMapFun L A₀ T (f : ↥L → ℂ) := by
  have hdom : (f : ↥L → ℂ) ∈ dadeDomain L A₀ :=
    mem_dadeDomain_of_mem_dadeZDomain (TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain hPS
      (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA) f.2)
  rw [hτ f ⟨_, hdom⟩ rfl, coe_dadeMap]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] [K.Normal] in
theorem exists_isCoherentWith_of_set_eq {S S' : Set (↥L → ℂ)} (hSS' : S = S')
    {τ : charSpanZero S →+ virtualChars G} {τ' : charSpanZero S' →+ virtualChars G}
    (hτ : ∀ (f : charSpanZero S) (f' : charSpanZero S'), (f : ↥L → ℂ) = (f' : ↥L → ℂ) →
      ((τ f : virtualChars G) : G → ℂ) = ((τ' f' : virtualChars G) : G → ℂ))
    {ν : Submodule.span ℤ S →+ virtualChars G} (hν : IsCoherentWith S τ ν) :
    ∃ ν' : Submodule.span ℤ S' →+ virtualChars G, IsCoherentWith S' τ' ν' ∧
      ∀ (f : Submodule.span ℤ S) (f' : Submodule.span ℤ S'),
        (f : ↥L → ℂ) = (f' : ↥L → ℂ) → (ν f : G → ℂ) = (ν' f' : G → ℂ) := by
  subst hSS'
  refine ⟨ν, ⟨hν.inner_eq, fun f => Subtype.ext ?_⟩, fun f f' hff' => ?_⟩
  · rw [hν.eq_on_zero f]; exact hτ f f rfl
  · rw [show f = f' from Subtype.ext hff']

noncomputable def toFinsetOfSubset {P : Set (↥L → ℂ)} (hPS : P ⊆ indFam K (Irr ↥K \ {1})) :
    Finset (↥L → ℂ) :=
  (Set.Finite.subset (indFam_finite K (finite_Irr.subset Set.sdiff_subset)) hPS).toFinset

@[simp] theorem coe_toFinsetOfSubset {P : Set (↥L → ℂ)} (hPS : P ⊆ indFam K (Irr ↥K \ {1})) :
    ((toFinsetOfSubset hPS : Finset (↥L → ℂ)) : Set (↥L → ℂ)) = P := Set.Finite.coe_toFinset _

theorem mem_toFinsetOfSubset {P : Set (↥L → ℂ)} (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    {f : ↥L → ℂ} : f ∈ toFinsetOfSubset hPS ↔ f ∈ P := Set.Finite.mem_toFinset _

include h in
theorem exists_isSubcoherent_indFam (hodd : Odd (Nat.card G))
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {Sfin : Finset (↥L → ℂ)} (hSfin : (Sfin : Set (↥L → ℂ)) = indFam K (Irr ↥K \ {1})) :
    ∃ R : (↥L → ℂ) → Finset (G → ℂ), IsSubcoherent Sfin (dadeMapFun L A₀ T) R := by
  obtain ⟨R, hR, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect
    (ω := ω) (A₀ := A₀) (T := T) hodd h hσ (H := K) h.right_le le_rfl
    (A := (K : Set ↥L) \ {1})
    (fun t => PrimeFixedTIPGroupCoherence.conj_image_punctured_eq K t)
    (fun y _ _ => PrimeFixedTIPGroupCoherence.centralizer_sdiff_subset_punctured K y)
    (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA) hD hstab hdisj hω
    (by rw [hSfin, PrimeFixedTIPGroupCoherence.indFamDetect_self_eq_indFam_sdiff])
  exact ⟨R, hR⟩

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_nu_nu_eq_zero_of_disjoint
    {Sfin : Finset (↥L → ℂ)} {tau : (↥L → ℂ) → (G → ℂ)} {R : (↥L → ℂ) → Finset (G → ℂ)}
    (hc : IsSubcoherent Sfin tau R)
    (hSfin : (Sfin : Set (↥L → ℂ)) = indFam K (Irr ↥K \ {1}))
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1})) (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂)
    (hS₁S₂ : Disjoint S₁ S₂)
    {ν₁' : Submodule.span ℤ S₁ →+ virtualChars G} (hν₁ : IsCoherentWith S₁ τ₁ ν₁')
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₁ : ∀ f : charSpanZero S₁, ((τ₁ f : virtualChars G) : G → ℂ) = tau (f : ↥L → ℂ))
    (hτ₂ : ∀ f : charSpanZero S₂, ((τ₂ f : virtualChars G) : G → ℂ) = tau (f : ↥L → ℂ))
    (f₁ : Submodule.span ℤ S₁) (f₂ : Submodule.span ℤ S₂) :
    cfInner (ν₁' f₁ : G → ℂ) (ν₂ f₂ : G → ℂ) = 0 := by
  classical
  set T₁ := toFinsetOfSubset (K := K) hS₁ with hT₁def
  set T₂ := toFinsetOfSubset (K := K) hS₂ with hT₂def
  have hc₁ : (T₁ : Set (↥L → ℂ)) = S₁ := coe_toFinsetOfSubset (K := K) hS₁
  have hc₂ : (T₂ : Set (↥L → ℂ)) = S₂ := coe_toFinsetOfSubset (K := K) hS₂
  have hT₁sub : (T₁ : Set (↥L → ℂ)) ⊆ (Sfin : Set (↥L → ℂ)) := by rw [hc₁, hSfin]; exact hS₁
  have hT₂sub : (T₂ : Set (↥L → ℂ)) ⊆ (Sfin : Set (↥L → ℂ)) := by rw [hc₂, hSfin]; exact hS₂
  obtain ⟨ν₁'', hν₁'', hval₁⟩ := exists_isCoherentWith_of_set_eq
    (τ' := WeightedFeitExtension.subTauHom hc hT₁sub) hc₁.symm
    (fun f f' hff' => by rw [hτ₁ f, WeightedFeitExtension.subTauHom_apply, hff']) hν₁
  obtain ⟨ν₂'', hν₂'', hval₂⟩ := exists_isCoherentWith_of_set_eq
    (τ' := WeightedFeitExtension.subTauHom hc hT₂sub) hc₂.symm
    (fun f f' hff' => by rw [hτ₂ f, WeightedFeitExtension.subTauHom_apply, hff']) hν₂
  have hdisjT : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.1 hS₁S₂ ((mem_toFinsetOfSubset (K := K) hS₁).1 hx)
      ((mem_toFinsetOfSubset (K := K) hS₂).1 hx')
  have hm₁ : (f₁ : ↥L → ℂ) ∈ Submodule.span ℤ (T₁ : Set (↥L → ℂ)) := by rw [hc₁]; exact f₁.2
  have hm₂ : (f₂ : ↥L → ℂ) ∈ Submodule.span ℤ (T₂ : Set (↥L → ℂ)) := by rw [hc₂]; exact f₂.2
  have key := DisjointCoherentBlocks.cfInner_eq_zero_of_disjoint hc
    (Finset.coe_subset.1 hT₁sub) (fun ψ hψ => (mem_toFinsetOfSubset (K := K) hS₁).2
      (hS₁star ψ ((mem_toFinsetOfSubset (K := K) hS₁).1 hψ))) hν₁''
    (fun f => WeightedFeitExtension.subTauHom_apply hc hT₁sub f)
    (Finset.coe_subset.1 hT₂sub) (fun ψ hψ => (mem_toFinsetOfSubset (K := K) hS₂).2
      (hS₂star ψ ((mem_toFinsetOfSubset (K := K) hS₂).1 hψ))) hν₂''
    (fun f => WeightedFeitExtension.subTauHom_apply hc hT₂sub f) hdisjT
    ⟨(f₁ : ↥L → ℂ), hm₁⟩ ⟨(f₂ : ↥L → ℂ), hm₂⟩
  rw [← hval₁ f₁ _ rfl, ← hval₂ f₂ _ rfl] at key
  exact key

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_nu_dadeZMap (hD : IsDadeData L A₀ T)
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (w : Submodule.span ℤ S₂) (hwD : (w : ↥L → ℂ) ∈ dadeZDomain L A₀)
    (g : dadeZDomain L A₀) :
    cfInner (ν₂ w : G → ℂ) ((dadeZMap hD g : charSpanZero (Irr G)) : G → ℂ)
      = cfInner (w : ↥L → ℂ) (g : ↥L → ℂ) := by
  have hval := PrimeDadePivot.coe_nu_eq_coe_dadeMap hD hν₂ hτ₂ w
    ⟨(w : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain hwD⟩ rfl
  rw [hval, ← coe_dadeZMap hD ⟨(w : ↥L → ℂ), hwD⟩, cfInner_dadeZMap]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] [K.Normal] in
theorem coe_nu_zsmul_sub_zsmul {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G}
    {χ ψ : ↥L → ℂ} (hχ : χ ∈ S₂) (hψ : ψ ∈ S₂) (a b : ℤ)
    (w : Submodule.span ℤ S₂) (hw : (w : ↥L → ℂ) = (a : ℂ) • χ - (b : ℂ) • ψ) :
    (ν₂ w : G → ℂ) = (a : ℂ) • (ν₂ ⟨χ, Submodule.subset_span hχ⟩ : G → ℂ)
      - (b : ℂ) • (ν₂ ⟨ψ, Submodule.subset_span hψ⟩ : G → ℂ) := by
  have hsplit : w = a • (⟨χ, Submodule.subset_span hχ⟩ : Submodule.span ℤ S₂)
      - b • (⟨ψ, Submodule.subset_span hψ⟩ : Submodule.span ℤ S₂) := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sub, SetLike.val_smul, SetLike.val_smul,
      ← Int.cast_smul_eq_zsmul ℂ a χ, ← Int.cast_smul_eq_zsmul ℂ b ψ]
  rw [hsplit, map_sub, map_zsmul, map_zsmul, Submodule.coe_sub, SetLike.val_smul,
    SetLike.val_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

theorem exists_isCoherentWith_tauPrincipalRowSub_eq (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁)
    (hncard : (S₁.ncard : ℤ) = n) (hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥W₁ : ℂ))
    (hτ₁ : ∀ (f : charSpanZero S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₁ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hcoh₁ : IsCoherent S₁ τ₁)
    (hproj : ∀ (i : Irr ↥(W₁.map L.subtype)) (l : Irr ↥(W₂.map L.subtype)),
      IsOrthogonal (tauPrincipalRowSub hB hA hD
          - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
              (principalIrr ↥(W₂.map L.subtype)))
        ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω i l)) :
    ∃ ν₁' : Submodule.span ℤ S₁ →+ virtualChars G, IsCoherentWith S₁ τ₁ ν₁' ∧
      tauPrincipalRowSub hB hA hD
        = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
            (principalIrr ↥(W₂.map L.subtype))
          - (ν₁' ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh₁
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  have hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A₀ := fun x hx hx1 =>
    hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hx hx1, rfl⟩
  have hm : K.index = Nat.card ↥W₁ := h.index_eq
  have hmW : K.index = Nat.card ↥(W₁.map L.subtype) := by
    rw [hm, Subgroup.card_map_of_injective L.subtype_injective]
  have hdomP : indClassFun K (1 : ↥K → ℂ) - ζ ∈ dadeDomain L A₀ :=
    PrimeDadePivot.indClassFun_one_sub_mem_dadeDomain hA0 (hS₁ hζS₁).1 (by rw [hdeg ζ hζS₁, hm])
  have hψ : tauPrincipalRowSub hB hA hD
      = dadeMapFun L A₀ T (indClassFun K (1 : ↥K → ℂ) - ζ) := by
    rw [tauPrincipalRowSub_eq_dadeMap hB hA hD ⟨indClassFun K (1 : ↥K → ℂ) - ζ, hdomP⟩
      (by rw [h.primeTIrow_principal hB.isometry]), coe_dadeMap]
  have hcard : 2 ≤ S₁.ncard := by
    have h2 : (2 : ℤ) ≤ (S₁.ncard : ℤ) := by rw [hncard]; exact hB.two_le
    omega
  have hdeg' : ∀ χ ∈ S₁, χ 1 = (K.index : ℂ) := fun χ hχ => by rw [hdeg χ hχ, hm]
  obtain ⟨ν', hν', heq⟩ := PrimeDadePivot.exists_isCoherentWith_eq_prodCharEtaColSum_sub
    (ω := ω) (T := T) (ζ := ζ) hodd hW (Subgroup.map_mono h.right_le)
    (by rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]) hω hD (mixedSet_subset_param hA) hA0 hmW
    (fun _ hx => (hS₁ hx).1) (fun _ hx => (hS₁ hx).2) hS₁star hcard hdeg' hζS₁ hν hτ₁
    (by rw [← hψ]; exact hproj)
  exact ⟨ν', hν', by rw [hψ, heq, coherentVal_apply]⟩

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem rowEtaSum_one_eq_prodCharEtaColSum [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
    [Fintype ↑(Irr ↥W₁)]
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) :
    rowEtaSum hW ω 1 j = hW.prodCharEtaColSum ω (irrMapSubtype L W₂ j) := by
  rw [rowEtaSum_def, ← sum_prodCharEta_eq_prodCharEtaColSum (ω := ω) hW j]
  simp

theorem coe_nu_primeTIrow_sub (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hjS : h.primeTIrow σ j ∈ S₂) (hkS : h.primeTIrow σ k ∈ S₂) :
    (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span hjS⟩ : G → ℂ)
        - (ν₂ ⟨h.primeTIrow σ k, Submodule.subset_span hkS⟩ : G → ℂ)
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j)
        - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
            (irrMapSubtype L W₂ k) := by
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  have hA₀ := image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA
  have hmem : h.primeTIrow σ j - h.primeTIrow σ k ∈ Submodule.span ℤ S₂ :=
    sub_mem (Submodule.subset_span hjS) (Submodule.subset_span hkS)
  have hz : (h.primeTIrow σ j - h.primeTIrow σ k) 1 = 0 := by
    rw [Pi.sub_apply, primeTIrow_apply_one hB hj, primeTIrow_apply_one hB hk, sub_self]
  have hdom : h.primeTIrow σ j - h.primeTIrow σ k ∈ dadeDomain L A₀ :=
    mem_dadeDomain_of_mem_dadeZDomain (TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain hS₂ hA₀
      (mem_charSpanZero.2 ⟨hmem, hz⟩))
  have hsplit : (⟨h.primeTIrow σ j - h.primeTIrow σ k, hmem⟩ : Submodule.span ℤ S₂)
      = ⟨h.primeTIrow σ j, Submodule.subset_span hjS⟩
        - ⟨h.primeTIrow σ k, Submodule.subset_span hkS⟩ := Subtype.ext rfl
  have hval := PrimeDadePivot.coe_nu_eq_coe_dadeMap hD hν₂ hτ₂
    ⟨h.primeTIrow σ j - h.primeTIrow σ k, hmem⟩ ⟨_, hdom⟩ rfl
  rw [hsplit, map_sub, Submodule.coe_sub] at hval
  rw [hval, dadeMap_primeTIrow_sub_eq hB hA₀ hD hstab hdisj hω hj hk ⟨_, hdom⟩ rfl,
    rowEtaSum_one_eq_prodCharEtaColSum hW j, rowEtaSum_one_eq_prodCharEtaColSum hW k]

include h in
omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_prodCharEtaColSum_nu_eq_zero (hodd : Odd (Nat.card G))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1})) (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂)
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ξ : ↥L → ℂ} (hξS : ξ ∈ S₂) (hξIrr : ξ ∈ Irr ↥L) (j : Irr ↥(W₂.map L.subtype)) :
    cfInner (hW.prodCharEtaColSum ω j) (ν₂ ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) = 0 := by
  refine hW.cfInner_prodCharEtaColSum_eq_zero j fun i l => ?_
  exact CoherentCore.isOrthogonal_nu_prodCharEta hodd hW (Subgroup.map_mono h.right_le)
    (by rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]) hω hD (mixedSet_subset_param hA)
    (fun _ hx => PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K (hS₂ hx)) hS₂star
    hν₂.inner_eq
    (fun f x hx =>
      PrimeDadeCommonError.eq_zero_of_mem_charSpanZero_of_notMem (h := h) hS₂ hA f x hx)
    (PrimeDadePivot.coe_nu_eq_coe_dadeMap hD hν₂ hτ₂) hξS hξIrr i l

theorem coe_nu_primeTIrow_eq_or (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1})) (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂)
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hrows : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTIrow σ j ∈ S₂)
    {ξ : ↥L → ℂ} (hξS : ξ ∈ S₂) (hξIrr : ξ ∈ Irr ↥L)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (hcol : (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
        - (ν₂ ⟨h.primeTIrow σ (starIrr j),
            Submodule.subset_span (hrows _ (starIrr_ne_principalIrr hj))⟩ : G → ℂ)
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j)
        - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
            (irrMapSubtype L W₂ (starIrr j))) :
    (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
        = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j) ∨
      (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
        = (-1 : ℂ) • (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
            (irrMapSubtype L W₂ (starIrr j)) := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  obtain ⟨a, -, ha⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hξIrr
  have hjstar : starIrr j ≠ principalIrr ↥W₂ := starIrr_ne_principalIrr hj
  have hjne : irrMapSubtype L W₂ j ≠ irrMapSubtype L W₂ (starIrr j) := fun hc =>
    (starIrr_ne_self h.isCyclicTIPair.odd_natCard_right hj) (irrMapSubtype_injective L W₂ hc).symm
  have key := CoherentRowColumn.eq_signed_col_or_neg_signed_col (ω := ω) hodd hW
    (Subgroup.map_mono h.right_le)
    (by rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]) hω hD (mixedSet_subset_param hA)
    (H := ⊤) (fun _ hx => PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K (hS₂ hx)) hS₂star
    (fun f x hx =>
      PrimeDadeCommonError.eq_zero_of_mem_charSpanZero_of_notMem (h := h) hS₂ hA f x hx)
    hν₂ (PrimeDadePivot.coe_nu_eq_coe_dadeMap hD hν₂ hτ₂)
    (hrows j hj) (hrows _ hjstar) hξS hξIrr (a := (a : ℤ))
    (b := ((Nat.card ↥W₁ : ℤ) * d)) (by rw [ha]; push_cast; ring)
    (by rw [primeTIrow_apply_one hB hj]; push_cast; ring)
    (by
      have hc : Nat.card ↥(W₁.map L.subtype) = Nat.card ↥W₁ :=
        Subgroup.card_map_of_injective L.subtype_injective
      rw [TypeVTwoFamilyJoining.cfInner_self_primeTIrow hB j, hc])
    (h.cfInner_primeTIrow_primeTIrow_of_ne hB.isometry
      (fun hc => (starIrr_ne_self h.isCyclicTIPair.odd_natCard_right hj) hc.symm))
    (δ := 1) (Or.inl rfl) hjne (by simpa using hcol)
  simpa using key

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem cfInner_smul_primeTIrow_sub_smul (hB : h.IsUniformBridgeData σ ζ d n 1)
    {ξ : ↥L → ℂ} (hξS : ξ ∈ indFam K (Irr ↥K \ {1})) (hξIrr : ξ ∈ Irr ↥L) (hξζ : ξ ≠ ζ)
    (j : Irr ↥W₂) (a b : ℂ) :
    cfInner (a • h.primeTIrow σ j - b • ξ) (h.primeTIrow σ j - (d : ℂ) • ζ)
      = a * (Nat.card ↥W₁ : ℂ) := by
  have hrowζ : cfInner (h.primeTIrow σ j) ζ = 0 := by
    rw [← conj_cfInner, h.cfInner_primeTIrow_eq_zero_of_mem_indFam hB.isometry
      (indFam_mono K Set.sdiff_subset hB.mem_indFam) hB.mem_Irr j, map_zero]
  have hξrow : cfInner ξ (h.primeTIrow σ j) = 0 :=
    h.cfInner_primeTIrow_eq_zero_of_mem_indFam hB.isometry
      (indFam_mono K Set.sdiff_subset hξS) hξIrr j
  have hξζ' : cfInner ξ ζ = 0 := cfInner_eq_zero_of_mem_Irr hξIrr hB.mem_Irr hξζ
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left, cfInner_smul_left,
    cfInner_smul_right, cfInner_smul_right, cfInner_smul_left, cfInner_smul_left,
    hrowζ, hξrow, hξζ', TypeVTwoFamilyJoining.cfInner_self_primeTIrow hB j]
  ring

omit [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)]
  [K.Normal] in
theorem cfInner_eq_of_pivot {ρj ρξ Pj e : G → ℂ} {t m : ℂ} (htne : t ≠ 0)
    (hlocal : cfInner (t • ρj - (m * (d : ℂ)) • ρξ) (Pj - (d : ℂ) • e) = t * m)
    (hξP : cfInner ρξ Pj = 0) (hje : cfInner ρj e = 0) (hξe : cfInner ρξ e = 0) :
    cfInner ρj Pj = m := by
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left, cfInner_smul_left,
    cfInner_smul_left, cfInner_smul_left, cfInner_smul_right, cfInner_smul_right,
    hξP, hje, hξe] at hlocal
  exact mul_left_cancel₀ htne (by linear_combination hlocal)

theorem cfInner_nu_primeTIrow_prodCharEtaColSum_eq (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hζS₁ : ζ ∈ S₁) (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ξ : ↥L → ℂ} (hξS₂ : ξ ∈ S₂) (hξIrr : ξ ∈ Irr ↥L) (hξζ : ξ ≠ ζ)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hjS : h.primeTIrow σ j ∈ S₂)
    (hcross₁ : cfInner (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span hjS⟩ : G → ℂ)
      (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) = 0)
    (hcross₂ : cfInner (ν₂ ⟨ξ, Submodule.subset_span hξS₂⟩ : G → ℂ)
      (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) = 0)
    (hcol : cfInner (ν₂ ⟨ξ, Submodule.subset_span hξS₂⟩ : G → ℂ)
      ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
        (irrMapSubtype L W₂ j)) = 0)
    (hbridge : ((dadeZMap hD ⟨h.primeTIrow σ j - (d : ℂ) • ζ,
        TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain
          (P := indFam K (Irr ↥K \ {1})) (subset_refl _)
          (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA)
          (primeTIrow_sub_smul_zeta_mem_charSpanZero hB hj)⟩ :
          charSpanZero (Irr G)) : G → ℂ)
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j)
        - (d : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)) :
    cfInner (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span hjS⟩ : G → ℂ)
        ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j))
      = (Nat.card ↥W₁ : ℂ) := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set gD : dadeZDomain L A₀ := ⟨h.primeTIrow σ j - (d : ℂ) • ζ,
    TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain (P := indFam K (Irr ↥K \ {1}))
      (subset_refl _) (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA)
      (primeTIrow_sub_smul_zeta_mem_charSpanZero hB hj)⟩ with hgD
  obtain ⟨t, htpos, ht⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hξIrr
  set m : ℤ := (Nat.card ↥W₁ : ℤ) with hmdef
  have hwmem : ((t : ℤ) : ℂ) • h.primeTIrow σ j - ((m * d : ℤ) : ℂ) • ξ
      ∈ Submodule.span ℤ S₂ := by
    refine sub_mem ?_ ?_
    · rw [Int.cast_smul_eq_zsmul ℂ (t : ℤ) (h.primeTIrow σ j)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hjS)
    · rw [Int.cast_smul_eq_zsmul ℂ (m * d) ξ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hξS₂)
  set w : Submodule.span ℤ S₂ := ⟨_, hwmem⟩ with hwdef
  have hwcoe : (w : ↥L → ℂ)
      = ((t : ℤ) : ℂ) • h.primeTIrow σ j - ((m * d : ℤ) : ℂ) • ξ := rfl
  have hw1 : (w : ↥L → ℂ) 1 = 0 := by
    rw [hwcoe, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      primeTIrow_apply_one hB hj, ht, hmdef]
    push_cast
    ring
  have hwD : (w : ↥L → ℂ) ∈ dadeZDomain L A₀ :=
    TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain (P := S₂) hS₂
      (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA)
      (mem_charSpanZero.2 ⟨w.2, hw1⟩)
  have hiso := cfInner_nu_dadeZMap (τ₂ := τ₂) hD hν₂ hτ₂ w hwD gD
  have hlocal : cfInner (w : ↥L → ℂ) (gD : ↥L → ℂ) = (t : ℂ) * (Nat.card ↥W₁ : ℂ) := by
    rw [hwcoe, show (gD : ↥L → ℂ) = h.primeTIrow σ j - (d : ℂ) • ζ from rfl,
      cfInner_smul_primeTIrow_sub_smul hB (hS₂ hξS₂) hξIrr hξζ j _ _]
    push_cast
    ring
  have hν₂w := coe_nu_zsmul_sub_zsmul (ν₂ := ν₂) hjS hξS₂ (t : ℤ) (m * d) w hwcoe
  rw [hbridge, hν₂w, hlocal] at hiso
  refine cfInner_eq_of_pivot (d := d) (t := (t : ℂ)) (m := (Nat.card ↥W₁ : ℂ))
    (by exact_mod_cast htpos.ne') ?_ hcol hcross₁ hcross₂
  rw [← hiso]
  congr 1
  rw [hmdef]
  push_cast
  ring

theorem exists_isCoherentWith_forall_eq_prodCharEtaColSum_of_inter_Irr_eq_empty
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hrows : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTIrow σ j ∈ S₂)
    (hempty : S₂ ∩ Irr ↥L = ∅) :
    ∃ ν : Submodule.span ℤ S₂ →+ virtualChars G, IsCoherentWith S₂ τ₂ ν ∧
      ∀ (j : Irr ↥W₂) (hj : j ≠ principalIrr ↥W₂),
        (ν ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
          = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
              (irrMapSubtype L W₂ j) := by
  classical
  have hcardW₁ : Nat.card ↥(W₁.map L.subtype) = Nat.card ↥W₁ :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hSM : S₂ = Set.range
      (fun j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} => h.primeTIrow σ (j : Irr ↥W₂)) := by
    refine Set.Subset.antisymm (fun f hf => ?_) ?_
    · have hfd : f ∈ indFamDetect K (K.subgroupOf K) := by
        rw [PrimeFixedTIPGroupCoherence.indFamDetect_self_eq_indFam_sdiff]; exact hS₂ hf
      rcases PrimeDadeSubcoherence.mem_Irr_or_exists_primeTIrow_eq h hB.isometry hfd with
        hirr | ⟨j, hj, hfj⟩
      · exact absurd (Set.mem_inter hf hirr) (by rw [hempty]; exact Set.notMem_empty f)
      · exact ⟨⟨j, hj⟩, hfj⟩
    · rintro f ⟨⟨j, hj⟩, rfl⟩
      exact hrows j hj
  have hne := h.isCyclicTIPair.nontrivial_Irr_right
  obtain ⟨j0, hj0⟩ := exists_ne (principalIrr ↥W₂)
  have hnonempty : Nonempty {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} := ⟨⟨j0, hj0⟩⟩
  have hfinι : Finite {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} := Subtype.finite
  obtain ⟨ν, hν, hval⟩ := CoherentSimultaneousOrientation.exists_isCoherentWith_row_family
    (τ := τ₂) (ω := ω) (h.isCyclicTIPair_map_subtype hstab hdisj) hω (δ := 1) (Or.inl rfl)
    (c := fun j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} => irrMapSubtype L W₂ (j : Irr ↥W₂))
    (fun j k hjk => Subtype.ext (irrMapSubtype_injective L W₂ hjk)) hSM
    (fun j => by
      show cfInner (h.primeTIrow σ (j : Irr ↥W₂)) (h.primeTIrow σ (j : Irr ↥W₂)) = _
      rw [TypeVTwoFamilyJoining.cfInner_self_primeTIrow hB, hcardW₁])
    (fun j k hjk => h.cfInner_primeTIrow_primeTIrow_of_ne hB.isometry
      (fun hc => hjk (Subtype.ext hc)))
    (b := (Nat.card ↥W₁ : ℤ) * d)
    (by
      have h3 := h.three_le_natCard_left
      have hd := hB.one_lt
      have hpos : (0 : ℤ) < (Nat.card ↥W₁ : ℤ) := by exact_mod_cast Nat.card_pos
      positivity)
    (fun j => by
      show h.primeTIrow σ (j : Irr ↥W₂) 1 = _
      rw [primeTIrow_apply_one hB j.2]; push_cast; ring) hν₂
    (fun j k => by
      simpa using coe_nu_primeTIrow_sub hB hA hD hstab hdisj hω hS₂ hν₂ hτ₂ j.2 k.2
        (hrows _ j.2) (hrows _ k.2))
  exact ⟨ν, hν, fun j hj => by rw [hval ⟨j, hj⟩ _ rfl, one_smul]⟩

theorem exists_isCoherentWith_coe_nu_primeTIrow_eq (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hζS₁ : ζ ∈ S₁) (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂) (hS₁S₂ : Disjoint S₁ S₂)
    (hrows : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTIrow σ j ∈ S₂)
    {Sfin : Finset (↥L → ℂ)} {R : (↥L → ℂ) → Finset (G → ℂ)}
    (hR : IsSubcoherent Sfin (dadeMapFun L A₀ T) R)
    (hSfin : (Sfin : Set (↥L → ℂ)) = indFam K (Irr ↥K \ {1}))
    (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : charSpanZero S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₁ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hcoh₂ : IsCoherent S₂ τ₂)
    (hbridge : ∀ {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂),
      ((dadeZMap hD ⟨h.primeTIrow σ j - (d : ℂ) • ζ,
          TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain
            (P := indFam K (Irr ↥K \ {1})) (subset_refl _)
            (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA)
            (primeTIrow_sub_smul_zeta_mem_charSpanZero hB hj)⟩ :
            charSpanZero (Irr G)) : G → ℂ)
        = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω (irrMapSubtype L W₂ j)
          - (d : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ))
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∃ ν₂ : Submodule.span ℤ S₂ →+ virtualChars G, IsCoherentWith S₂ τ₂ ν₂ ∧
      (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
        = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
            (irrMapSubtype L W₂ j) := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  have hmpos : (Nat.card ↥W₁ : ℂ) ≠ 0 := by
    have h3 := h.three_le_natCard_left
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rcases Set.eq_empty_or_nonempty (S₂ ∩ Irr ↥L) with hempty | ⟨ξ, hξS₂, hξIrr⟩
  · obtain ⟨ν₂, hν₂⟩ := isCoherent_iff.1 hcoh₂
    obtain ⟨ν, hν, hval⟩ :=
      exists_isCoherentWith_forall_eq_prodCharEtaColSum_of_inter_Irr_eq_empty hB hA hD hstab hdisj
        hω hS₂ hν₂ hτ₂ hrows hempty
    exact ⟨ν, hν, hval j hj⟩
  · obtain ⟨ν₂, hν₂⟩ := isCoherent_iff.1 hcoh₂
    have hjS := hrows j hj
    have hξζ : ξ ≠ ζ := fun hc => Set.disjoint_left.1 hS₁S₂ (hc ▸ hζS₁) hξS₂
    have hcross := cfInner_nu_nu_eq_zero_of_disjoint (K := K) hR hSfin
      (fun _ hx => (hS₁ hx).1) hS₂ hS₁star hS₂star hS₁S₂ hν₁ hν₂
      (fun f => coe_tau_eq_dadeMapFun (W₁ := W₁) (W₂ := W₂) hD (fun _ hx => (hS₁ hx).1) hA hτ₁ f)
      (fun f => coe_tau_eq_dadeMapFun (W₁ := W₁) (W₂ := W₂) hD hS₂ hA hτ₂ f)
    have hcross₁ : cfInner (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span hjS⟩ : G → ℂ)
        (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) = 0 := by
      rw [← conj_cfInner, hcross _ _, map_zero]
    have hcross₂ : cfInner (ν₂ ⟨ξ, Submodule.subset_span hξS₂⟩ : G → ℂ)
        (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) = 0 := by
      rw [← conj_cfInner, hcross _ _, map_zero]
    have hcol : cfInner (ν₂ ⟨ξ, Submodule.subset_span hξS₂⟩ : G → ℂ)
        (hW.prodCharEtaColSum ω (irrMapSubtype L W₂ j)) = 0 := by
      rw [← conj_cfInner,
        cfInner_prodCharEtaColSum_nu_eq_zero (h := h) hodd hA hD hW hω hS₂ hS₂star hν₂ hτ₂
          hξS₂ hξIrr _, map_zero]
    have hpivot := cfInner_nu_primeTIrow_prodCharEtaColSum_eq (ν₁ := ν₁) hB hA hD hstab hdisj
      hζS₁ hS₂ hν₂ hτ₂ hξS₂ hξIrr hξζ hj hjS hcross₁ hcross₂ hcol (hbridge hj)
    have hor := coe_nu_primeTIrow_eq_or hodd hB hA hD hstab hdisj hω hS₂ hS₂star hν₂ hτ₂ hrows
      hξS₂ hξIrr hj
      (coe_nu_primeTIrow_sub hB hA hD hstab hdisj hω hS₂ hν₂ hτ₂ hj (starIrr_ne_principalIrr hj)
        hjS (hrows _ (starIrr_ne_principalIrr hj)))
    refine ⟨ν₂, hν₂, hor.resolve_right fun hc => ?_⟩
    rw [hc, cfInner_smul_left,
      CoherentSimultaneousOrientation.cfInner_prodCharEtaColSum hW hω] at hpivot
    have hjne : irrMapSubtype L W₂ (starIrr j) ≠ irrMapSubtype L W₂ j := fun he =>
      (starIrr_ne_self h.isCyclicTIPair.odd_natCard_right hj) (irrMapSubtype_injective L W₂ he)
    rw [if_neg hjne, mul_zero] at hpivot
    exact hmpos hpivot.symm

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem isCoherent_union_of_bridge
    {Sfin : Finset (↥L → ℂ)} {R : (↥L → ℂ) → Finset (G → ℂ)}
    (hc : IsSubcoherent Sfin (dadeMapFun L A₀ T) R)
    (hSfin : (Sfin : Set (↥L → ℂ)) = indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1})) (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    (hS₁star : ∀ γ ∈ S₁, star γ ∈ S₁) (hS₂star : ∀ γ ∈ S₂, star γ ∈ S₂)
    (hS₁S₂ : Disjoint S₁ S₂) (hS₁ne : S₁.Nonempty) (hS₂ne : S₂.Nonempty)
    (hτ₁ : ∀ (f : charSpanZero S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₁ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτU : ∀ (f : charSpanZero (S₁ ∪ S₂)) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τU f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    {χ φ : ↥L → ℂ} (hχ : χ ∈ S₂) (hφmem : φ ∈ Submodule.span ℤ S₁) (hdegeq : χ 1 = φ 1)
    (hbridge : dadeMapFun L A₀ T (χ - φ)
      = (ν₂ ⟨χ, Submodule.subset_span hχ⟩ : G → ℂ) - (ν₁ ⟨φ, hφmem⟩ : G → ℂ)) :
    IsCoherent (S₁ ∪ S₂) τU := by
  classical
  set T₁ := toFinsetOfSubset (K := K) hS₂ with hT₁def
  set T₂ := toFinsetOfSubset (K := K) hS₁ with hT₂def
  have hc₁ : (T₁ : Set (↥L → ℂ)) = S₂ := coe_toFinsetOfSubset hS₂
  have hc₂ : (T₂ : Set (↥L → ℂ)) = S₁ := coe_toFinsetOfSubset hS₁
  have hT₁sub : T₁ ⊆ Sfin := by rw [← Finset.coe_subset, hc₁, hSfin]; exact hS₂
  have hT₂sub : T₂ ⊆ Sfin := by rw [← Finset.coe_subset, hc₂, hSfin]; exact hS₁
  have hUcoe : ((T₁ ∪ T₂ : Finset (↥L → ℂ)) : Set (↥L → ℂ)) = S₁ ∪ S₂ := by
    rw [Finset.coe_union, hc₁, hc₂, Set.union_comm]
  obtain ⟨ν₂', hν₂', hval₂⟩ := exists_isCoherentWith_of_set_eq (τ' :=
    WeightedFeitExtension.subTauHom hc (Finset.coe_subset.2 hT₁sub)) hc₁.symm
    (fun f f' hff' => by
      rw [coe_tau_eq_dadeMapFun (W₁ := W₁) (W₂ := W₂) hD hS₂ hA hτ₂ f,
        WeightedFeitExtension.subTauHom_apply, hff']) hν₂
  obtain ⟨ν₁', hν₁', hval₁⟩ := exists_isCoherentWith_of_set_eq (τ' :=
    WeightedFeitExtension.subTauHom hc (Finset.coe_subset.2 hT₂sub)) hc₂.symm
    (fun f f' hff' => by
      rw [coe_tau_eq_dadeMapFun (W₁ := W₁) (W₂ := W₂) hD hS₁ hA hτ₁ f,
        WeightedFeitExtension.subTauHom_apply, hff']) hν₁
  set τU' : charSpanZero ((T₁ ∪ T₂ : Finset (↥L → ℂ)) : Set (↥L → ℂ)) →+ virtualChars G :=
    WeightedFeitExtension.subTauHom hc
      (by rw [hUcoe, hSfin]; exact Set.union_subset hS₁ hS₂) with hτU'def
  have hdisjT : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.1 hS₁S₂ ((mem_toFinsetOfSubset hS₁).1 hx')
      ((mem_toFinsetOfSubset hS₂).1 hx)
  have hφmem' : φ ∈ Submodule.span ℤ (T₂ : Set (↥L → ℂ)) := by rw [hc₂]; exact hφmem
  have hχ' : χ ∈ T₁ := (mem_toFinsetOfSubset hS₂).2 hχ
  have hχmem' : χ ∈ Submodule.span ℤ (T₁ : Set (↥L → ℂ)) := by
    rw [hc₁]; exact Submodule.subset_span hχ
  have hbr : dadeMapFun L A₀ T (χ - φ)
      = (ν₂' ⟨χ, hχmem'⟩ : G → ℂ) - (ν₁' ⟨φ, hφmem'⟩ : G → ℂ) := by
    rw [← hval₂ ⟨χ, Submodule.subset_span hχ⟩ ⟨χ, hχmem'⟩ rfl,
      ← hval₁ ⟨φ, hφmem⟩ ⟨φ, hφmem'⟩ rfl]
    exact hbridge
  have key := CoherentJoin.isCoherentWith_joinHom (τU := τU') hc hT₁sub
    (fun ψ hψ => (mem_toFinsetOfSubset hS₂).2 (hS₂star ψ ((mem_toFinsetOfSubset hS₂).1 hψ)))
    (by rw [← Finset.coe_nonempty, hc₁]; exact hS₂ne) hν₂'
    (fun f => WeightedFeitExtension.subTauHom_apply hc _ f) hT₂sub
    (fun ψ hψ => (mem_toFinsetOfSubset hS₁).2 (hS₁star ψ ((mem_toFinsetOfSubset hS₁).1 hψ)))
    (by rw [← Finset.coe_nonempty, hc₂]; exact hS₁ne) hν₁'
    (fun f => WeightedFeitExtension.subTauHom_apply hc _ f) hdisjT
    (fun f => WeightedFeitExtension.subTauHom_apply hc _ f) hχ' ⟨φ, hφmem'⟩ hdegeq
    (by convert hbr using 2)
  refine CentralSectionCoherence.isCoherent_of_eq hUcoe ?_ key.isCoherent
  intro f h1 h2
  rw [hτU'def, WeightedFeitExtension.subTauHom_apply,
    coe_tau_eq_dadeMapFun (W₁ := W₁) (W₂ := W₂) hD (Set.union_subset hS₁ hS₂) hA hτU ⟨f, h2⟩]

theorem isCoherent_union (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hprime₁ : (Nat.card ↥W₁).Prime) (hprime₂ : (Nat.card ↥W₂).Prime)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁)
    (hncard : (S₁.ncard : ℤ) = n) (hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥W₁ : ℂ))
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂) (hS₁S₂ : Disjoint S₁ S₂)
    (hrows : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTIrow σ j ∈ S₂)
    (hτ₁ : ∀ (f : charSpanZero S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₁ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτU : ∀ (f : charSpanZero (S₁ ∪ S₂)) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τU f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hcoh₁ : IsCoherent S₁ τ₁) (hcoh₂ : IsCoherent S₂ τ₂)
    (hproj : ∀ (i : Irr ↥(W₁.map L.subtype)) (l : Irr ↥(W₂.map L.subtype)),
      IsOrthogonal (tauPrincipalRowSub hB hA hD
          - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
              (principalIrr ↥(W₂.map L.subtype)))
        ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω i l)) :
    IsCoherent (S₁ ∪ S₂) τU := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  obtain ⟨R, hR⟩ := exists_isSubcoherent_indFam (σ := σ) (ω := ω) (h := h) hodd hB.isometry hA hD
    hstab hdisj hω (Sfin := toFinsetOfSubset (K := K) (subset_refl _)) (coe_toFinsetOfSubset _)
  set Sfin := toFinsetOfSubset (K := K) (P := indFam K (Irr ↥K \ {1})) (subset_refl _)
    with hSfindef
  have hSfin : (Sfin : Set (↥L → ℂ)) = indFam K (Irr ↥K \ {1}) := coe_toFinsetOfSubset _
  obtain ⟨ν₁', hν₁', hpsi⟩ := exists_isCoherentWith_tauPrincipalRowSub_eq hodd hB hA hD
    hstab hdisj hω hS₁ hS₁star hζS₁ hncard hdeg hτ₁ hcoh₁ hproj
  have hτ₁' : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁' f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) :=
    PrimeDadePivot.coe_nu_eq_coe_dadeMap hD hν₁' hτ₁
  have hpsi' : ((dadeZMap hD ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
        primeTIrow_principal_sub_mem_dadeZDomain (h := h) hB hA⟩ :
          charSpanZero (Irr G)) : G → ℂ)
      = hW.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype))
        - (ν₁' ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
    rw [← hpsi, tauPrincipalRowSub_def hB hA hD
      (primeTIrow_principal_sub_mem_dadeZDomain (h := h) hB hA)]
  have hbridge : ∀ {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂),
      ((dadeZMap hD ⟨h.primeTIrow σ j - (d : ℂ) • ζ,
          TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain
            (P := indFam K (Irr ↥K \ {1})) (subset_refl _)
            (image_bridgeSupport_subset (K := K) (W₁ := W₁) (W₂ := W₂) hA)
            (primeTIrow_sub_smul_zeta_mem_charSpanZero hB hj)⟩ :
            charSpanZero (Irr G)) : G → ℂ)
        = hW.prodCharEtaColSum ω (irrMapSubtype L W₂ j)
          - (d : ℂ) • (ν₁' ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) :=
    fun {j} hj => dadeZMap_primeTIrow_sub_smul_eq hodd hB hA hD hstab hdisj hω hprime₁ hprime₂ hS₁
      hS₁star hζS₁ hncard hdeg hν₁' hτ₁' hpsi hpsi' hj _
  have hne := h.isCyclicTIPair.nontrivial_Irr_right
  obtain ⟨j, hj⟩ := exists_ne (principalIrr ↥W₂)
  obtain ⟨ν₂, hν₂, hνj⟩ := exists_isCoherentWith_coe_nu_primeTIrow_eq (ν₁ := ν₁') hodd hB hA hD
    hstab hdisj hω hζS₁ hS₁ hS₁star hS₂ hS₂star hS₁S₂ hrows hR hSfin hν₁' hτ₁ hτ₂ hcoh₂
    (fun {j} hj => hbridge hj) hj
  have hφmem : ((d : ℂ) • ζ) ∈ Submodule.span ℤ S₁ := by
    rw [Int.cast_smul_eq_zsmul ℂ d ζ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hζS₁)
  have hφval : (ν₁' ⟨(d : ℂ) • ζ, hφmem⟩ : G → ℂ)
      = (d : ℂ) • (ν₁' ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
    have hsplit : (⟨(d : ℂ) • ζ, hφmem⟩ : Submodule.span ℤ S₁)
        = d • (⟨ζ, Submodule.subset_span hζS₁⟩ : Submodule.span ℤ S₁) :=
      Subtype.ext (Int.cast_smul_eq_zsmul ℂ d ζ)
    rw [hsplit, map_zsmul, SetLike.val_smul, Int.cast_smul_eq_zsmul]
  have hbr : dadeMapFun L A₀ T (h.primeTIrow σ j - (d : ℂ) • ζ)
      = (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
        - (ν₁' ⟨(d : ℂ) • ζ, hφmem⟩ : G → ℂ) := by
    rw [hνj, hφval, ← hbridge hj, coe_dadeZMap, coe_dadeMap]
  refine isCoherent_union_of_bridge (K := K) (W₁ := W₁) (W₂ := W₂) hR hSfin hA hD
    (fun _ hx => (hS₁ hx).1) hS₂ hS₁star hS₂star hS₁S₂ ⟨ζ, hζS₁⟩
    ⟨h.primeTIrow σ j, hrows j hj⟩ hτ₁ hτ₂ hτU hν₁' hν₂ (hrows j hj) hφmem ?_ hbr
  rw [primeTIrow_apply_one hB hj, Pi.smul_apply, smul_eq_mul, hB.apply_one]
  ring

end PrimeDadeColumnGluing

end CFSG.FeitThompson

end
