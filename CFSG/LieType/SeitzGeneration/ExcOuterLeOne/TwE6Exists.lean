module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Entry
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCellConj
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.PairLemma
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic
import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.QBorel

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Exists

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}

noncomputable def twPair (σ η : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) :
    Subgroup ↥(twistedE6RootGroup K σ) :=
  Subgroup.closure ((twR σ η : Set ↥(twistedE6RootGroup K σ)) ∪
    ((twR σ η).map (MulAut.conj g).toMonoidHom : Set ↥(twistedE6RootGroup K σ)))

theorem twR_le_twPair (σ η : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) : twR σ η ≤ twPair σ η g :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem conj_mem_twPair (σ η : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) {x : ↥(twistedE6RootGroup K σ)}
    (hx : x ∈ twR σ η) : g * x * g⁻¹ ∈ twPair σ η g :=
  Subgroup.subset_closure (Or.inr ⟨x, hx, by simp [MulAut.conj_apply]⟩)

theorem twPair_le {σ η : K ≃+* K} {M : Subgroup ↥(twistedE6RootGroup K σ)} (hRM : twR σ η ≤ M)
    {g : ↥(twistedE6RootGroup K σ)} (hg : g ∈ M) : twPair σ η g ≤ M := by
  refine (Subgroup.closure_le M).2 ?_
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact hRM hx
  · exact M.mul_mem (M.mul_mem hg (hRM hy)) (M.inv_mem hg)

private theorem twE6X1_P_apply_labelPerm (v : RootModule TwistTag.E6.tag K) (a : Label TwistTag.E6.tag) :
    (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) v
      (labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm a) = v a := by
  change Finsupp.equivMapDomain (labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm) v
      (labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm a) = v a
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

private theorem twE6X1_P_single (b : Label TwistTag.E6.tag) :
    (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) (Finsupp.single b 1) =
      Finsupp.single (labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm b) 1 :=
  Finsupp.domLCongr_single (labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm) b 1

private theorem twE6X1_labelPerm_rootLabel {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ) :
    labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm (rootLabel (τ := TwistTag.E6.tag) hθ.1) =
      rootLabel (τ := TwistTag.E6.tag) hθ.1 := by
  change Sum.inr _ = Sum.inr _
  congr 1
  apply Subtype.ext
  show permLattice TwistTag.E6.perm θ = θ
  exact isMaxHeightRoot_perm_fixed hθ

private theorem twE6X1_labelPerm_negLabel {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ) :
    labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm (negLabel (τ := TwistTag.E6.tag) hθ.1) =
      negLabel (τ := TwistTag.E6.tag) hθ.1 := by
  change Sum.inr _ = Sum.inr _
  congr 1
  apply Subtype.ext
  show permLattice TwistTag.E6.perm (-θ) = -θ
  exact (permLattice_neg TwistTag.E6.perm θ).trans (congrArg Neg.neg (isMaxHeightRoot_perm_fixed hθ))

private theorem twE6X1_core (σ : K ≃+* K) (A : Module.End K (RootModule TwistTag.E6.tag K))
    (hcomm : (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) *
        entrywise σ.toRingHom A =
      A * (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)))
    (b a : Label TwistTag.E6.tag)
    (hb : labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm b = b)
    (ha : labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm a = a) :
    σ (A (Finsupp.single b 1) a) = A (Finsupp.single b 1) a := by
  have key := congrArg
    (fun F : Module.End K (RootModule TwistTag.E6.tag K) => F (Finsupp.single b 1)) hcomm
  simp only [Module.End.mul_apply, twE6X1_P_single, hb] at key
  have h3 := twE6X1_P_apply_labelPerm (entrywise σ.toRingHom A (Finsupp.single b 1)) a
  rw [ha, key] at h3
  rw [entrywise_single, Finsupp.mapRange_apply] at h3
  exact h3.symm

theorem twE6_entry_mem_fixSubfield {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ)
    (g : ↥(twistedE6RootGroup K σ)) :
    entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ := by
  have hfix : twistHom TwistTag.E6 K σ.toRingHom (g : ModGL TwistTag.E6.tag K) = g :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom g.2)).2
  have h1 : ((twistHom TwistTag.E6 K σ.toRingHom (g : ModGL TwistTag.E6.tag K) :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) =
      ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) := by
    rw [hfix]
  rw [coe_twistHom] at h1
  have hQP : (((diagramMap TwistTag.E6 K)⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) *
      (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) *
      entrywise σ.toRingHom ((g : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) =
      ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) *
        (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) := by
    have h2 := congrArg
      (· * (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))) h1
    simpa only [mul_assoc, hQP, mul_one] using h2
  have hb := twE6X1_labelPerm_rootLabel hθ
  have ha := twE6X1_labelPerm_negLabel hθ
  rw [mem_fixSubfield]
  exact twE6X1_core σ _ hcomm (rootLabel (τ := TwistTag.E6.tag) hθ.1)
    (negLabel (τ := TwistTag.E6.tag) hθ.1) hb ha

private theorem twE6X2_ringChar_fixSubfield (σ : K ≃+* K) :
    ringChar ↥(fixSubfield σ) = ringChar K := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : CharP ↥(fixSubfield σ) (ringChar K) :=
    ((fixSubfield σ).subtype.charP_iff Subtype.val_injective _).2 inferInstance
  exact ringChar.eq _ _

private theorem twE6X2_map_u2 (c : ↥(fixSubfield σ)) :
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype (u2 c) = u2 (c : K) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, u2_coe, u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

private theorem twE6X2_map_l2 (c : ↥(fixSubfield σ)) :
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype (l2 c) = l2 (c : K) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, l2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

private theorem twE6X2_aux (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)))
    (g : ↥(twistedE6RootGroup K σ))
    (hbad : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield η) :
    ∃ t : K, σ t = t ∧ η t ≠ t ∧ xE6 θ t ∈ (twPair σ η g).map (twIncl σ) := by
  have hlamσ : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ :=
    twE6_entry_mem_fixSubfield hθ g
  have hlam0 : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 :=
    fun h => hbad (h ▸ (fixSubfield η).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμμ, hbig⟩ :=
    bigCell' (τ := Tag.E6) (Or.inl rfl) hθ (twIncl σ g) hlam0
  have hF : μ₁ * μ₂ ∈ fixSubfield σ := by
    rcases hμμ with hμ | hμ
    · rw [hμ]
      exact hlamσ
    · rw [hμ]
      exact neg_mem hlamσ
  have hlam'' : (1 : ↥(fixSubfield σ)) * (⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ)) ∉
      fixSubfield (fixSubfieldRestrict η σ) := by
    intro h
    rw [mem_fixSubfield, one_mul] at h
    have h' : η (μ₁ * μ₂) = μ₁ * μ₂ := congrArg Subtype.val h
    apply hbad
    rw [mem_fixSubfield]
    rcases hμμ with hμ | hμ
    · rw [hμ] at h'
      exact h'
    · rw [hμ, map_neg] at h'
      exact neg_injective h'
  obtain ⟨ψ', hψ'u, hψ'l⟩ : ∃ ψ' : Matrix.SpecialLinearGroup (Fin 2) ↥(fixSubfield σ) →*
      ↥(adjointGroup Tag.E6 K),
      (∀ c : ↥(fixSubfield σ), ψ' (u2 c) = xE6 θ (c : K)) ∧
      (∀ c : ↥(fixSubfield σ), ψ' (l2 ((⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ)) * c)) =
        twIncl σ g * xE6 θ (c : K) * (twIncl σ g)⁻¹) := by
    refine ⟨(ψ.comp (diagConj μ₁ hμ₁)).comp (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype),
      ?_, ?_⟩
    · intro c
      simp only [MonoidHom.comp_apply]
      rw [twE6X2_map_u2, diagConj_u2]
      exact (hbig (c : K)).1
    · intro c
      simp only [MonoidHom.comp_apply]
      rw [twE6X2_map_l2]
      show ψ (diagConj μ₁ hμ₁ (l2 (μ₁ * μ₂ * (c : K)))) = _
      rw [diagConj_l2]
      have e : μ₁⁻¹ * (μ₁ * μ₂ * (c : K)) = μ₂ * (c : K) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ₁, one_mul]
      rw [e]
      exact (hbig (c : K)).2
  have hX : ∀ c : K, σ c = c → η c = c →
      ∃ x ∈ twR σ η, twIncl σ x = xE6 θ c := fun c hc hηc =>
    xPar_fixed_mem_twR σ η hθ.1 (isMaxHeightRoot_perm_fixed hθ) hc hηc
  have hxR : ∀ c : K, σ c = c → η c = c → xE6 θ c ∈ (twPair σ η g).map (twIncl σ) := by
    intro c hc hηc
    obtain ⟨x, hx, hxe⟩ := hX c hc hηc
    rw [← hxe]
    exact Subgroup.mem_map_of_mem _ (twR_le_twPair σ η g hx)
  have hconj : ∀ c : K, σ c = c → η c = c →
      twIncl σ g * xE6 θ c * (twIncl σ g)⁻¹ ∈ (twPair σ η g).map (twIncl σ) := by
    intro c hc hηc
    obtain ⟨x, hx, hxe⟩ := hX c hc hηc
    have h := Subgroup.mem_map_of_mem (twIncl σ) (conj_mem_twPair σ η g hx)
    rw [map_mul, map_mul, map_inv, hxe] at h
    exact h
  have hD' : ringChar ↥(fixSubfield σ) ≠ 2 ∨
      4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)) := by
    rw [twE6X2_ringChar_fixSubfield]
    exact hD
  have hσ' : orderOf (fixSubfieldRestrict η σ) = p := hS.orderOf_restrict
  have hu : ∀ c ∈ fixSubfield (fixSubfieldRestrict η σ),
      ψ' (u2 (1 * c)) ∈ (twPair σ η g).map (twIncl σ) := by
    intro c hc
    have hc' : η (c : K) = (c : K) := congrArg Subtype.val ((mem_fixSubfield _).1 hc)
    rw [one_mul, hψ'u]
    exact hxR (c : K) ((mem_fixSubfield _).1 c.2) hc'
  have hl : ∀ c ∈ fixSubfield (fixSubfieldRestrict η σ),
      ψ' (l2 ((⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ)) * c)) ∈ (twPair σ η g).map (twIncl σ) := by
    intro c hc
    have hc' : η (c : K) = (c : K) := congrArg Subtype.val ((mem_fixSubfield _).1 hc)
    rw [hψ'l c]
    exact hconj (c : K) ((mem_fixSubfield _).1 c.2) hc'
  have hne1 : fixSubfieldRestrict η σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ'
    have := hS.two_lt
    omega
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥(fixSubfield σ), fixSubfieldRestrict η σ c₀ ≠ c₀ := by
    by_contra h
    push Not at h
    exact hne1 (RingEquiv.ext h)
  have key := sl2_hom_mem_of_pair (K := ↥(fixSubfield σ)) (fixSubfieldRestrict η σ) hS.prime
    hS.ne_two hσ' hD' (H := (twPair σ η g).map (twIncl σ)) ψ' 1 (⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ))
    one_ne_zero hlam'' hu hl c₀
  rw [one_mul, hψ'u] at key
  exact ⟨(c₀ : K), (mem_fixSubfield _).1 c₀.2, fun h => hc₀ (Subtype.ext h), key⟩

theorem exists_irrational_longRootElt_twE6_of_ge3 (hS : TwE6Setup K σ η p)
    {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)))
    (g : ↥(twistedE6RootGroup K σ)) (hg : g ∉ twR σ η) :
    ∃ r ∈ twR σ η, ∃ r' ∈ twR σ η, ∃ t : K, σ t = t ∧ η t ≠ t ∧
      xE6 θ t ∈ (twPair σ η (r * g * r')).map (twIncl σ) := by
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_twE6 hS hθ g hg
  exact ⟨r, hr, r', hr', twE6X2_aux hS hθ hD (r * g * r') hbad⟩

private noncomputable def twE6F (σ : K ≃+* K) :
    ↥(adjointGroup Tag.E6 K) →* ↥(adjointGroup Tag.E6 K) :=
  MonoidHom.codRestrict
    ((twistHom TwistTag.E6 K σ.toRingHom).comp (adjointGroup Tag.E6 K).subtype)
    (adjointGroup Tag.E6 K)
    (fun g => twistHom_mem_adjointGroup TwistTag.E6 K σ.toRingHom g.2)

private theorem coe_twE6F (σ : K ≃+* K) (g : ↥(adjointGroup Tag.E6 K)) :
    ((twE6F σ g : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      twistHom TwistTag.E6 K σ.toRingHom (g : ModGL Tag.E6 K) := rfl

private theorem twE6F_twIncl (σ : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) :
    twE6F σ (twIncl σ g) = twIncl σ g := by
  apply Subtype.ext
  rw [coe_twE6F, coe_twIncl]
  exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom g.2)).2


private theorem twE6BC_eq_hiRoot {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ) :
    θ = hiRoot Tag.E6 := by
  have hmax := hiRoot_isMax (τ := Tag.E6) (Or.inr (Or.inl rfl))
  have hh : height θ = height (hiRoot Tag.E6) :=
    le_antisymm (hmax.2 θ hθ.1) (hθ.2 (hiRoot Tag.E6) hmax.1)
  have key : ∀ γ ∈ rootFinset Tag.E6, height γ = height (hiRoot Tag.E6) → γ = hiRoot Tag.E6 := by
    decide +kernel
  exact key θ (mem_rootFinset.2 hθ.1) hh

private theorem twE6BC_coe_xE6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (c : K) :
    ((xE6 γ c : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      pinnedX Tag.E6 K γ (((rootOperatorFamily Tag.E6).pinnedFamilySign γ : K) * c) := by
  have hss := (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K γ
  rw [(rootOperatorFamily Tag.E6).pinnedX_eq_eltUnit K hγ, ← mul_assoc, hss, one_mul, xE6,
    xPar_of_isRoot hγ, (rootOperatorFamily Tag.E6).coe_eltElement]

private theorem twE6F_xE6 (σ : K ≃+* K) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      twE6F σ (xE6 γ c) = xE6 (permLattice TwistTag.E6.perm γ) (ε * σ c) := by
  have hργ : IsRoot Tag.E6 (permLattice TwistTag.E6.perm γ) :=
    hγ.permLattice TwistTag.E6.cartan_perm
  obtain ⟨ε₀, hε₀, hP⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.E6 hγ
  set s : K := (((rootOperatorFamily Tag.E6).pinnedFamilySign γ : ℤ) : K) with hsdef
  set s' : K := (((rootOperatorFamily Tag.E6).pinnedFamilySign
    (permLattice TwistTag.E6.perm γ) : ℤ) : K) with hs'def
  have hs' : s' * s' = 1 := (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K _
  have hσs : σ s = s := map_intCast σ _
  refine ⟨s' * ε₀ * s, ?_, fun c => ?_⟩
  · have hs : s * s = 1 := (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K γ
    calc (s' * ε₀ * s) * (s' * ε₀ * s) = (s' * s') * (ε₀ * ε₀) * (s * s) := by ring
      _ = 1 := by rw [hs, hs', hε₀]; ring
  · apply Subtype.ext
    have e0 : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.E6.tag K γ (s * c)) =
        pinnedX TwistTag.E6.tag K γ (σ (s * c)) :=
      Units.ext (entrywise_pinnedX σ.toRingHom γ (s * c))
    have key : twistHom TwistTag.E6 K σ.toRingHom (pinnedX TwistTag.E6.tag K γ (s * c)) =
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (ε₀ * σ (s * c)) := by
      rw [twistHom_apply, e0]
      exact hP _
    have lhs : ((twE6F σ (xE6 γ c) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (ε₀ * σ (s * c)) :=
      (coe_twE6F σ _).trans (by rw [twE6BC_coe_xE6 hγ c]; exact key)
    refine lhs.trans ?_
    rw [twE6BC_coe_xE6 hργ]
    congr 1
    rw [map_mul, hσs]
    linear_combination (-(ε₀ * s * σ c)) * hs'

private theorem twE6_exists_weyl_commute {q : ↥(adjointGroup Tag.E6 K)}
    (hq : ∀ a : K, q * xE6 (hiRoot Tag.E6) a = xE6 (hiRoot Tag.E6) a * q) {m : K} (hm : m ≠ 0)
    (h : q * xE6 (-hiRoot Tag.E6) m = xE6 (-hiRoot Tag.E6) m * q) :
    ∃ (n : ModGL Tag.E6 K) (hn : n ∈ monomialSubgroup Tag.E6 K),
      weylQuotientHom Tag.E6 K ⟨n, hn⟩ = rootReflection (hiRoot Tag.E6) ∧
        n * (q : ModGL Tag.E6 K) = (q : ModGL Tag.E6 K) * n := by
  have hθ : IsRoot Tag.E6 (hiRoot Tag.E6) :=
    (hiRoot_isMax (τ := Tag.E6) (Or.inr (Or.inl rfl))).1
  have hθn : IsRoot Tag.E6 (-hiRoot Tag.E6) := IsRoot.neg hθ
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) hθ
  set sθ : K := (((rootOperatorFamily Tag.E6).pinnedFamilySign (hiRoot Tag.E6) : ℤ) : K) with hsθ
  set sn : K := (((rootOperatorFamily Tag.E6).pinnedFamilySign (-hiRoot Tag.E6) : ℤ) : K) with hsn
  have hsθ2 : sθ * sθ = 1 := (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K _
  have hsn2 : sn * sn = 1 := (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K _
  have hsn0 : sn ≠ 0 := fun h0 => by rw [h0, zero_mul] at hsn2; exact zero_ne_one hsn2
  have hε0 : ε ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε; exact zero_ne_one hε
  have hqθ : ∀ z : K, (q : ModGL Tag.E6 K) * pinnedX Tag.E6 K (hiRoot Tag.E6) z =
      pinnedX Tag.E6 K (hiRoot Tag.E6) z * (q : ModGL Tag.E6 K) := by
    intro z
    have h1 := congrArg (fun g : ↥(adjointGroup Tag.E6 K) => (g : ModGL Tag.E6 K)) (hq (sθ * z))
    simp only [Subgroup.coe_mul, twE6BC_coe_xE6 hθ] at h1
    rwa [← mul_assoc, hsθ2, one_mul] at h1
  have hqn : (q : ModGL Tag.E6 K) * pinnedX Tag.E6 K (-hiRoot Tag.E6) (sn * m) =
      pinnedX Tag.E6 K (-hiRoot Tag.E6) (sn * m) * (q : ModGL Tag.E6 K) := by
    have h1 := congrArg (fun g : ↥(adjointGroup Tag.E6 K) => (g : ModGL Tag.E6 K)) h
    simpa only [Subgroup.coe_mul, twE6BC_coe_xE6 hθn] using h1
  have hc0 : -(ε * (sn * m))⁻¹ ≠ 0 :=
    neg_ne_zero.2 (inv_ne_zero (mul_ne_zero hε0 (mul_ne_zero hsn0 hm)))
  set c : Kˣ := Units.mk0 _ hc0 with hcdef
  have hcinv : ((c⁻¹ : Kˣ) : K) = -(ε * (sn * m)) := by
    rw [Units.val_inv_eq_inv_val]
    simp [hcdef, Units.val_mk0]
  have hvc : ε * (-((c⁻¹ : Kˣ) : K)) = sn * m := by
    rw [hcinv]
    linear_combination (sn * m) * hε
  refine ⟨rootWeylSL2 Tag.E6 K (hiRoot Tag.E6) c,
    ((exceptional_Lang_root_rank_one_torus_transport Tag.E6 K hθ).2.2.1 c).1,
    ((exceptional_Lang_root_rank_one_torus_transport Tag.E6 K hθ).2.2.1 c).2, ?_⟩
  have hnSL : nSL c = uSL (c : K) * vSL (-((c⁻¹ : Kˣ) : K)) * uSL (c : K) := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
  have hu : ∀ z : K, Commute (q : ModGL Tag.E6 K) (rootSL2 Tag.E6 K (hiRoot Tag.E6) (uSL z)) := by
    intro z
    rw [rootSL2_uSL_eq]
    exact hqθ _
  have hvv : Commute (q : ModGL Tag.E6 K)
      (rootSL2 Tag.E6 K (hiRoot Tag.E6) (vSL (-((c⁻¹ : Kˣ) : K)))) := by
    rw [hv, hvc]
    exact hqn
  have hcomm : Commute (q : ModGL Tag.E6 K) (rootWeylSL2 Tag.E6 K (hiRoot Tag.E6) c) := by
    rw [rootWeylSL2, hnSL, map_mul, map_mul]
    exact ((hu _).mul_right hvv).mul_right (hu _)
  exact hcomm.symm.eq

private theorem twE6_conj_Q_mem_negUnipotent {n : ModGL Tag.E6 K}
    (hn : n ∈ monomialSubgroup Tag.E6 K)
    (hπ : weylQuotientHom Tag.E6 K ⟨n, hn⟩ = rootReflection (hiRoot Tag.E6))
    {q : ↥(adjointGroup Tag.E6 K)} (hq : q ∈ Qgrp Tag.E6 K) :
    n * (q : ModGL Tag.E6 K) * n⁻¹ ∈ negUnipotent Tag.E6 K := by
  have hθ : IsRoot Tag.E6 (hiRoot Tag.E6) :=
    (hiRoot_isMax (τ := Tag.E6) (Or.inr (Or.inl rfl))).1
  have hneg : ∀ γ ∈ rootFinset Tag.E6, 0 < lvl Tag.E6 γ →
      height (γ - corootPair (hiRoot Tag.E6) γ • hiRoot Tag.E6) < 0 := by decide +kernel
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, c, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hγ
    have hroot : IsRoot Tag.E6 (γ - corootPair (hiRoot Tag.E6) γ • hiRoot Tag.E6) := by
      rw [← rootReflection_smul hθ]
      exact IsRoot.smul hγ _
    rw [twE6BC_coe_xE6 hγ c, hμ, hπ, rootReflection_smul hθ]
    exact rootSpan_le_negUnipotent (S := {α | IsRoot Tag.E6 α ∧ height α < 0}) (fun α hα => hα)
      (pinnedX_mem_rootSpan (S := {α | IsRoot Tag.E6 α ∧ height α < 0})
        ⟨hroot, hneg γ (mem_rootFinset.2 hγ) hl⟩ _)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : n * ((x * y : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) * n⁻¹ =
        (n * (x : ModGL Tag.E6 K) * n⁻¹) * (n * (y : ModGL Tag.E6 K) * n⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : n * ((x⁻¹ : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) * n⁻¹ =
        (n * (x : ModGL Tag.E6 K) * n⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]; group
    rw [e]
    exact inv_mem hx

private theorem twE6_Q_le_posUnipotent {q : ↥(adjointGroup Tag.E6 K)} (hq : q ∈ Qgrp Tag.E6 K) :
    (q : ModGL Tag.E6 K) ∈ posUnipotent Tag.E6 K := by
  have hlvl : ∀ γ ∈ rootFinset Tag.E6, 0 < lvl Tag.E6 γ → 0 < height γ := by decide +kernel
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, c, rfl⟩ := hx
    rw [twE6BC_coe_xE6 hγ c]
    exact rootSpan_le_posUnipotent (S := {α | IsRoot Tag.E6 α ∧ 0 < height α}) (fun α hα => hα)
      (pinnedX_mem_rootSpan (S := {α | IsRoot Tag.E6 α ∧ 0 < height α})
        ⟨hγ, hlvl γ (mem_rootFinset.2 hγ) hl⟩ _)
  | one => exact one_mem _
  | mul x y _ _ hx hy => exact mul_mem hx hy
  | inv x _ hx => exact inv_mem hx

private theorem twE6_Q_rigid {q : ↥(adjointGroup Tag.E6 K)} (hq : q ∈ Qgrp Tag.E6 K) {m : K}
    (hm : m ≠ 0) (h : q * xE6 (-hiRoot Tag.E6) m = xE6 (-hiRoot Tag.E6) m * q) : q = 1 := by
  obtain ⟨n, hn, hπ, hcomm⟩ := twE6_exists_weyl_commute
    (fun a => (commute_Q_hiRoot (Or.inr (Or.inl rfl)) hq a).eq) hm h
  have h1 : n * (q : ModGL Tag.E6 K) * n⁻¹ ∈ negUnipotent Tag.E6 K :=
    twE6_conj_Q_mem_negUnipotent hn hπ hq
  have h2 : n * (q : ModGL Tag.E6 K) * n⁻¹ = (q : ModGL Tag.E6 K) := by
    rw [hcomm, mul_inv_cancel_right]
  have h3 : (q : ModGL Tag.E6 K) ∈ posUnipotent Tag.E6 K ⊓ negUnipotent Tag.E6 K :=
    Subgroup.mem_inf.2 ⟨twE6_Q_le_posUnipotent hq, h2 ▸ h1⟩
  rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

private theorem twE6_Q_fixed_mem_range (σ : K ≃+* K) {q : ↥(adjointGroup Tag.E6 K)}
    (hq : q ∈ Qgrp Tag.E6 K) (hF : twE6F σ q = q) :
    ∃ x : ↥(twistedE6RootGroup K σ), twIncl σ x = q := by
  have hfix : twistHom TwistTag.E6 K σ.toRingHom (q : ModGL Tag.E6 K) = (q : ModGL Tag.E6 K) :=
    congrArg Subtype.val hF
  have hΓ : (q : ModGL Tag.E6 K) ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).2 ⟨q.2, hfix⟩
  have hU : (q : ModGL Tag.E6 K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨twE6_Q_le_posUnipotent hq, hΓ⟩
  exact ⟨⟨(q : ModGL Tag.E6 K),
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom hU⟩, Subtype.ext rfl⟩

private theorem twE6_lvl_permLattice (γ : Fin Tag.E6.rank → ℤ) :
    lvl Tag.E6 (permLattice TwistTag.E6.perm γ) = lvl Tag.E6 γ := by
  show γ (TwistTag.E6.perm.symm (gradNode Tag.E6)) = γ (gradNode Tag.E6)
  congr 1

private theorem twE6F_mem_Qgrp (σ : K ≃+* K) {q : ↥(adjointGroup Tag.E6 K)}
    (hq : q ∈ Qgrp Tag.E6 K) : twE6F σ q ∈ Qgrp Tag.E6 K := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, c, rfl⟩ := hx
    obtain ⟨ε, hε, h⟩ := twE6F_xE6 σ hγ
    rw [h c]
    exact xPar_mem_Qgrp (hγ.permLattice TwistTag.E6.cartan_perm)
      (lt_of_lt_of_eq hl (twE6_lvl_permLattice γ).symm) _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

private theorem twE6F_xE6_of_fixed (σ : K ≃+* K) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) {c : K} (hc : σ c = c) :
    twE6F σ (xE6 γ c) = xE6 γ c := by
  obtain ⟨x, hx⟩ := xPar_fixed_mem_twIncl_range σ hγ hρ hc
  rw [← hx, twE6F_twIncl]

private theorem twE6F_xE6_hiRoot (σ : K ≃+* K) (c : K) :
    twE6F σ (xE6 (hiRoot Tag.E6) c) = xE6 (hiRoot Tag.E6) (σ c) := by
  have hmax := hiRoot_isMax (τ := Tag.E6) (Or.inr (Or.inl rfl))
  have hρθ : permLattice TwistTag.E6.perm (hiRoot Tag.E6) = hiRoot Tag.E6 :=
    isMaxHeightRoot_perm_fixed hmax
  obtain ⟨ε, hε, h⟩ := twE6F_xE6 σ hmax.1
  have h' : ∀ c : K, twE6F σ (xE6 (hiRoot Tag.E6) c) = xE6 (hiRoot Tag.E6) (ε * σ c) :=
    fun c => (h c).trans (congrArg (fun v => xE6 v (ε * σ c)) hρθ)
  have h1 : xE6 (hiRoot Tag.E6) ε = xE6 (hiRoot Tag.E6) 1 := by
    have := h' 1
    rw [map_one, mul_one] at this
    rw [← this]
    exact twE6F_xE6_of_fixed σ hmax.1 hρθ (map_one σ)
  have hε1 : ε = 1 := xPar_injective hmax.1 h1
  rw [h' c, hε1, one_mul]

theorem twE6_bigCell_Q (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (g : ↥(twistedE6RootGroup K σ))
    (hlam : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ≠ 0) :
    ∃ (q : ↥(twistedE6RootGroup K σ)) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      (∀ c : K, σ c = c → twIncl σ q * xE6 θ c * (twIncl σ q)⁻¹ = xE6 θ c) ∧
      (∀ c : K, σ c = c → twIncl σ g * xE6 θ c * (twIncl σ g)⁻¹ =
        twIncl σ q * xE6 (-θ) ((ε : K) * entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) * c) *
          (twIncl σ q)⁻¹) ∧
      (∀ δ : Fin Tag.E6.rank → ℤ, (δ = Pi.single 1 1 ∨ δ = θ - Pi.single 1 1) →
        ∃ c : K, σ c = c ∧ (twIncl σ q)⁻¹ * xE6 δ 1 * twIncl σ q = xE6 δ 1 * xE6 θ c) := by
  obtain rfl : θ = hiRoot Tag.E6 := twE6BC_eq_hiRoot hθ
  have hτ : Tag.E6 = .F4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inr (Or.inl rfl)
  have hθr : IsRoot Tag.E6 (hiRoot Tag.E6) := hθ.1
  have hρθ : permLattice TwistTag.E6.perm (hiRoot Tag.E6) = hiRoot Tag.E6 :=
    isMaxHeightRoot_perm_fixed hθ
  have hρθ' : permLattice TwistTag.E6.perm (-hiRoot Tag.E6) = -hiRoot Tag.E6 :=
    (permLattice_neg TwistTag.E6.perm (hiRoot Tag.E6)).trans (congrArg Neg.neg hρθ)
  obtain ⟨qq, hqq, ε, hε, hconj⟩ := bigCell_conj_Q hτ (twIncl σ g) hlam
  set lam := entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) with hlamdef
  have hlamσ : σ lam = lam := (mem_fixSubfield σ).1 (twE6_entry_mem_fixSubfield hθ g)
  have hεK : σ (ε : K) = ε := map_intCast σ ε
  have hεne : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> simp
  set m : K := (ε : K) * lam with hm
  have hm0 : m ≠ 0 := mul_ne_zero hεne hlam
  have hσm : σ m = m := by rw [hm, map_mul, hεK, hlamσ]
  have hfixθ : twE6F σ (xE6 (hiRoot Tag.E6) 1) = xE6 (hiRoot Tag.E6) 1 :=
    twE6F_xE6_of_fixed σ hθr hρθ (map_one σ)
  have hfixm : twE6F σ (xE6 (-hiRoot Tag.E6) m) = xE6 (-hiRoot Tag.E6) m :=
    twE6F_xE6_of_fixed σ (IsRoot.neg hθr) hρθ' hσm
  have hgfix : twE6F σ (twIncl σ g) = twIncl σ g := twE6F_twIncl σ g
  have h1 : twIncl σ g * xE6 (hiRoot Tag.E6) 1 * (twIncl σ g)⁻¹ =
      qq * xE6 (-hiRoot Tag.E6) m * qq⁻¹ := by
    have := hconj 1
    rwa [mul_one] at this
  have h2 := congrArg (twE6F σ) h1
  simp only [map_mul, map_inv] at h2
  rw [hgfix, hfixθ, hfixm] at h2
  have h3 : qq * xE6 (-hiRoot Tag.E6) m * qq⁻¹ =
      twE6F σ qq * xE6 (-hiRoot Tag.E6) m * (twE6F σ qq)⁻¹ := h1.symm.trans h2
  have hq'' : qq⁻¹ * twE6F σ qq ∈ Qgrp Tag.E6 K := mul_mem (inv_mem hqq) (twE6F_mem_Qgrp σ hqq)
  have hcomm : (qq⁻¹ * twE6F σ qq) * xE6 (-hiRoot Tag.E6) m =
      xE6 (-hiRoot Tag.E6) m * (qq⁻¹ * twE6F σ qq) := by
    calc (qq⁻¹ * twE6F σ qq) * xE6 (-hiRoot Tag.E6) m
        = qq⁻¹ * (twE6F σ qq * xE6 (-hiRoot Tag.E6) m * (twE6F σ qq)⁻¹) * twE6F σ qq := by group
      _ = qq⁻¹ * (qq * xE6 (-hiRoot Tag.E6) m * qq⁻¹) * twE6F σ qq := by rw [h3]
      _ = xE6 (-hiRoot Tag.E6) m * (qq⁻¹ * twE6F σ qq) := by group
  have hFq : twE6F σ qq = qq :=
    (inv_mul_eq_one.1 (twE6_Q_rigid hq'' hm0 hcomm)).symm
  obtain ⟨x, hx⟩ := twE6_Q_fixed_mem_range σ hqq hFq
  refine ⟨x, ε, hε, ?_, ?_, ?_⟩
  · intro c _
    rw [hx]
    exact mul_inv_eq_iff_eq_mul.2 (commute_Q_hiRoot hτ hqq c).eq
  · intro c _
    rw [hx]
    exact hconj c
  · intro δ hδ
    have hδr : IsRoot Tag.E6 δ ∧ permLattice TwistTag.E6.perm δ = δ ∧ lvl Tag.E6 δ = 1 := by
      rcases hδ with rfl | rfl
      · exact ⟨isRoot_delta1 Tag.E6,
          (show permLattice (τ := Tag.E6) TwistTag.E6.perm (delta1 Tag.E6) = delta1 Tag.E6 by
            decide +kernel), lvl_delta1 Tag.E6⟩
      · obtain ⟨h1, h2⟩ := isRoot_sub_single_one hθ
        exact ⟨h1, h2, lvl_delta2 hτ⟩
    obtain ⟨hδroot, hδρ, hδl⟩ := hδr
    obtain ⟨c', hc'⟩ := Q_conj_delta hτ (inv_mem hqq) hδroot hδl
    have h5 := hc' 1
    rw [inv_inv, mul_one] at h5
    have h6 := congrArg (twE6F σ) h5
    simp only [map_mul, map_inv] at h6
    rw [hFq, twE6F_xE6_of_fixed σ hδroot hδρ (map_one σ), twE6F_xE6_hiRoot] at h6
    have h7 : xE6 (hiRoot Tag.E6) (σ c') = xE6 (hiRoot Tag.E6) c' :=
      mul_left_cancel (h6.symm.trans h5)
    refine ⟨c', xPar_injective hθr h7, ?_⟩
    rw [hx]
    exact h5

private theorem twE6X4a_eq_hiRoot {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ) :
    θ = hiRoot Tag.E6 := by
  have hmax := hiRoot_isMax (τ := Tag.E6) (Or.inr (Or.inl rfl))
  have hh : height θ = height (hiRoot Tag.E6) :=
    le_antisymm (hmax.2 θ hθ.1) (hθ.2 (hiRoot Tag.E6) hmax.1)
  have key : ∀ γ ∈ rootFinset Tag.E6, height γ = height (hiRoot Tag.E6) → γ = hiRoot Tag.E6 := by
    decide +kernel
  exact key θ (mem_rootFinset.2 hθ.1) hh

private theorem twE6X4a_perm_delta1 :
    permLattice (τ := Tag.E6) TwistTag.E6.perm (delta1 Tag.E6) = delta1 Tag.E6 := by
  decide +kernel

private theorem twE6X4a_perm_delta2 :
    permLattice (τ := Tag.E6) TwistTag.E6.perm (delta2 Tag.E6) = delta2 Tag.E6 := by
  decide +kernel

private theorem twE6X4a_charP_two (F : Type) [Field F] [Finite F] (h : Nat.card F = 2) :
    CharP F 2 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hc, n, hp, hn⟩ := FiniteField.card' F
  have hdvd : p ∣ 2 := by
    rw [← h, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  exact hc

private theorem twE6X4a_map_t12 {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (t12 c) = t12 (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t12_coe, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem twE6X4a_map_t13 {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (t13 c) = t13 (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t13_coe, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem twE6X4a_map_t23 {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (t23 c) = t23 (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t23_coe, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem twE6X4a_map_t31 {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (t31 c) = t31 (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t31_coe, Matrix.SpecialLinearGroup.map_apply_coe]

theorem twE6_irrational_of_bigCell_two (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (hk2 : Nat.card (fixSubfield (fixSubfieldRestrict η σ)) = 2)
    (H : Subgroup ↥(twistedE6RootGroup K σ)) (hRH : twR σ η ≤ H)
    (g q : ↥(twistedE6RootGroup K σ)) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq1 : ∀ c : K, σ c = c → twIncl σ q * xE6 θ c * (twIncl σ q)⁻¹ = xE6 θ c)
    (hq2 : ∀ c : K, σ c = c → twIncl σ g * xE6 θ c * (twIncl σ g)⁻¹ =
      twIncl σ q * xE6 (-θ) ((ε : K) * entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) * c) *
        (twIncl σ q)⁻¹)
    (hq3 : ∀ δ : Fin Tag.E6.rank → ℤ, (δ = Pi.single 1 1 ∨ δ = θ - Pi.single 1 1) →
      ∃ c : K, σ c = c ∧ (twIncl σ q)⁻¹ * xE6 δ 1 * twIncl σ q = xE6 δ 1 * xE6 θ c)
    (hgH : ∀ x ∈ twR σ η, g * x * g⁻¹ ∈ H)
    (hbad : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield η) :
    ∃ s : K, σ s = s ∧ η s ≠ s ∧ xE6 θ s ∈ H.map (twIncl σ) := by
  obtain rfl : θ = hiRoot Tag.E6 := twE6X4a_eq_hiRoot hθ
  have hkC : CharP ↥(fixSubfield (fixSubfieldRestrict η σ)) 2 := twE6X4a_charP_two _ hk2
  have hF2 : CharP ↥(fixSubfield σ) 2 :=
    ((fixSubfield (fixSubfieldRestrict η σ)).subtype.charP_iff Subtype.val_injective 2).1 hkC
  have hKC : CharP K 2 :=
    ((fixSubfield σ).subtype.charP_iff Subtype.val_injective 2).1 hF2
  have hε1 : (ε : K) = 1 := intCast_eq_one_of_pm_one hε
  have hK : Nat.card ↥(fixSubfield σ) = Nat.card ↥(fixSubfield (fixSubfieldRestrict η σ)) ^ p := by
    have h := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow (fixSubfieldRestrict η σ)
    rw [hS.orderOf_restrict] at h
    exact h
  have hd2 : p ≠ 2 := hS.ne_two
  obtain ⟨lam, hlam⟩ : ∃ lam : ↥(fixSubfield σ),
      (lam : K) = entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) :=
    ⟨⟨_, twE6_entry_mem_fixSubfield hθ g⟩, rfl⟩
  have hlam_notin : lam ∉ fixSubfield (fixSubfieldRestrict η σ) := by
    intro hmem
    apply hbad
    have h1 : fixSubfieldRestrict η σ lam = lam := hmem
    have h2 := congrArg Subtype.val h1
    rw [coe_fixSubfieldRestrict] at h2
    rw [← hlam]
    exact h2
  obtain ⟨φK, h12, h23, h13, h31⟩ :=
    exists_a2Hom (K := K) (τ := Tag.E6) (Or.inr (Or.inl rfl))
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix.SpecialLinearGroup (Fin 3) ↥(fixSubfield σ) →*
      ↥(adjointGroup Tag.E6 K), ∀ x, Ψ x = φK (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype x) :=
    ⟨φK.comp (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype), fun x => rfl⟩
  have hΨ12 : ∀ c : ↥(fixSubfield σ), Ψ (t12 c) = xE6 (delta1 Tag.E6) (c : K) := by
    intro c
    rw [hΨ, twE6X4a_map_t12]
    exact h12 _
  have hΨ23 : ∀ c : ↥(fixSubfield σ), Ψ (t23 c) = xE6 (delta2 Tag.E6) (c : K) := by
    intro c
    rw [hΨ, twE6X4a_map_t23]
    exact h23 _
  have hΨ13 : ∀ c : ↥(fixSubfield σ), Ψ (t13 c) = xE6 (hiRoot Tag.E6) (c : K) := by
    intro c
    rw [hΨ, twE6X4a_map_t13]
    exact h13 _
  have hΨ31 : ∀ c : ↥(fixSubfield σ), Ψ (t31 c) = xE6 (-hiRoot Tag.E6) (c : K) := by
    intro c
    rw [hΨ, twE6X4a_map_t31]
    exact h31 _
  have hρ1 : permLattice TwistTag.E6.perm (delta1 Tag.E6) = delta1 Tag.E6 :=
    twE6X4a_perm_delta1
  have hρ2 : permLattice TwistTag.E6.perm (delta2 Tag.E6) = delta2 Tag.E6 :=
    twE6X4a_perm_delta2
  have hρθ : permLattice TwistTag.E6.perm (hiRoot Tag.E6) = hiRoot Tag.E6 :=
    isMaxHeightRoot_perm_fixed hθ
  have hr1 : IsRoot Tag.E6 (delta1 Tag.E6) := isRoot_delta1 Tag.E6
  have hr2 : IsRoot Tag.E6 (delta2 Tag.E6) := isRoot_delta2 (τ := Tag.E6) (Or.inr (Or.inl rfl))
  have hxR : ∀ (γ : Fin Tag.E6.rank → ℤ) (c : K), IsRoot Tag.E6 γ →
      permLattice TwistTag.E6.perm γ = γ → σ c = c → η c = c →
      xE6 γ c ∈ H.map (twIncl σ) := by
    intro γ c hγ hρ hc hηc
    obtain ⟨x, hx, hxι⟩ := xPar_fixed_mem_twR σ η hγ hρ hc hηc
    rw [← hxι]
    exact Subgroup.mem_map_of_mem _ (hRH hx)
  have hconjE : ∀ (γ : Fin Tag.E6.rank → ℤ) (c : K), IsRoot Tag.E6 γ →
      permLattice TwistTag.E6.perm γ = γ → σ c = c → η c = c →
      twIncl σ g * xE6 γ c * (twIncl σ g)⁻¹ ∈ H.map (twIncl σ) := by
    intro γ c hγ hρ hc hηc
    obtain ⟨x, hx, hxι⟩ := xPar_fixed_mem_twR σ η hγ hρ hc hηc
    rw [← hxι]
    have e : twIncl σ g * twIncl σ x * (twIncl σ g)⁻¹ = twIncl σ (g * x * g⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem _ (hgH x hx)
  obtain ⟨Hq, hHq⟩ : ∃ Hq : Subgroup ↥(adjointGroup Tag.E6 K),
      ∀ y, y ∈ Hq ↔ twIncl σ q * y * (twIncl σ q)⁻¹ ∈ H.map (twIncl σ) :=
    ⟨(H.map (twIncl σ)).comap (MulAut.conj (twIncl σ q)).toMonoidHom, fun y => Iff.rfl⟩
  have hpat : ∀ (A B : ↥(adjointGroup Tag.E6 K)), (twIncl σ q)⁻¹ * A * twIncl σ q = A * B →
      A ∈ H.map (twIncl σ) → twIncl σ q * (A * B) * (twIncl σ q)⁻¹ ∈ H.map (twIncl σ) := by
    intro A B hAB hA
    rw [← hAB]
    have e : twIncl σ q * ((twIncl σ q)⁻¹ * A * twIncl σ q) * (twIncl σ q)⁻¹ = A := by
      group
    rw [e]
    exact hA
  have g1 : Ψ (t13 1) ∈ Hq := by
    rw [hHq, hΨ13]
    show twIncl σ q * xE6 (hiRoot Tag.E6) 1 * (twIncl σ q)⁻¹ ∈ H.map (twIncl σ)
    rw [hq1 1 (map_one σ)]
    exact hxR _ 1 hθ.1 hρθ (map_one σ) (map_one η)
  have g2 : Ψ (t31 lam) ∈ Hq := by
    rw [hHq, hΨ31]
    have e : twIncl σ g * xE6 (hiRoot Tag.E6) 1 * (twIncl σ g)⁻¹ =
        twIncl σ q * xE6 (-hiRoot Tag.E6) (lam : K) * (twIncl σ q)⁻¹ := by
      have h := hq2 1 (map_one σ)
      rw [← hlam, hε1, one_mul, mul_one] at h
      exact h
    rw [← e]
    exact hconjE _ 1 hθ.1 hρθ (map_one σ) (map_one η)
  obtain ⟨c₁', hc₁σ, hz₁⟩ :=
    hq3 (delta1 Tag.E6) (Or.inl (show delta1 Tag.E6 = Pi.single 1 1 from rfl))
  obtain ⟨c₂', hc₂σ, hz₂⟩ :=
    hq3 (delta2 Tag.E6) (Or.inr (show delta2 Tag.E6 = hiRoot Tag.E6 - Pi.single 1 1 from rfl))
  obtain ⟨c₁, hc₁⟩ : ∃ c : ↥(fixSubfield σ), (c : K) = c₁' :=
    ⟨⟨c₁', hc₁σ⟩, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ↥(fixSubfield σ), (c : K) = c₂' :=
    ⟨⟨c₂', hc₂σ⟩, rfl⟩
  have g3 : Ψ (t12 1 * t13 c₁) ∈ Hq := by
    rw [hHq, map_mul, hΨ12, hΨ13, hc₁]
    show twIncl σ q * (xE6 (delta1 Tag.E6) 1 * xE6 (hiRoot Tag.E6) c₁') * (twIncl σ q)⁻¹ ∈
      H.map (twIncl σ)
    exact hpat _ _ hz₁ (hxR _ 1 hr1 hρ1 (map_one σ) (map_one η))
  have g4 : Ψ (t23 1 * t13 c₂) ∈ Hq := by
    rw [hHq, map_mul, hΨ23, hΨ13, hc₂]
    show twIncl σ q * (xE6 (delta2 Tag.E6) 1 * xE6 (hiRoot Tag.E6) c₂') * (twIncl σ q)⁻¹ ∈
      H.map (twIncl σ)
    exact hpat _ _ hz₂ (hxR _ 1 hr2 hρ2 (map_one σ) (map_one η))
  have hA2 : A2Gen lam c₁ c₂ ≤ Hq.comap Ψ := by
    unfold A2Gen
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_comap.2 g1
    · exact Subgroup.mem_comap.2 g2
    · exact Subgroup.mem_comap.2 g3
    · exact Subgroup.mem_comap.2 g4
  obtain ⟨s, hsk, hs⟩ := a2_lemma hk2 hS.prime hd2 hK hlam_notin c₁ c₂
  have hΨs : Ψ (t13 s) ∈ Hq := Subgroup.mem_comap.1 (hA2 hs)
  rw [hHq, hΨ13] at hΨs
  have hσs : σ (s : K) = (s : K) := s.2
  rw [hq1 (s : K) hσs] at hΨs
  refine ⟨(s : K), hσs, ?_, hΨs⟩
  intro hηs
  apply hsk
  show fixSubfieldRestrict η σ s = s
  apply Subtype.ext
  rw [coe_fixSubfieldRestrict]
  exact hηs

theorem exists_irrational_longRootElt_twE6_of_two (hS : TwE6Setup K σ η p)
    {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ)
    (hk2 : Nat.card (fixSubfield (fixSubfieldRestrict η σ)) = 2)
    (g : ↥(twistedE6RootGroup K σ)) (hg : g ∉ twR σ η) :
    ∃ r ∈ twR σ η, ∃ r' ∈ twR σ η, ∃ t : K, σ t = t ∧ η t ≠ t ∧
      xE6 θ t ∈ (twPair σ η (r * g * r')).map (twIncl σ) := by
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_twE6 hS hθ g hg
  have hne : entry (twIncl σ (r * g * r')) (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 := fun h =>
    hbad (h ▸ (fixSubfield η).zero_mem)
  obtain ⟨q, ε, hε, hq1, hq2, hq3⟩ := twE6_bigCell_Q hS hθ (r * g * r') hne
  refine ⟨r, hr, r', hr', ?_⟩
  exact twE6_irrational_of_bigCell_two hS hθ hk2 (twPair σ η (r * g * r')) (twR_le_twPair σ η _)
    (r * g * r') q ε hε hq1 hq2 hq3 (fun x hx => conj_mem_twPair σ η (r * g * r') hx) hbad

theorem ringChar_fixSubfield (σ : K ≃+* K) : ringChar ↥(fixSubfield σ) = ringChar K := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : CharP ↥(fixSubfield σ) (ringChar K) :=
    ((fixSubfield σ).subtype.charP_iff Subtype.val_injective _).2 inferInstance
  exact ringChar.eq _ _

theorem exists_irrational_longRootElt_twE6 (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (g : ↥(twistedE6RootGroup K σ)) (hg : g ∉ twR σ η) :
    ∃ r ∈ twR σ η, ∃ r' ∈ twR σ η, ∃ t : K, σ t = t ∧ η t ≠ t ∧
      xE6 θ t ∈ (twPair σ η (r * g * r')).map (twIncl σ) := by
  by_cases hk2 : Nat.card (fixSubfield (fixSubfieldRestrict η σ)) = 2
  · exact exists_irrational_longRootElt_twE6_of_two hS hθ hk2 g hg
  · refine exists_irrational_longRootElt_twE6_of_ge3 hS hθ ?_ g hg
    by_cases h2 : ringChar K = 2
    · rw [← ringChar_fixSubfield σ] at h2
      exact Or.inr ((card_fixSubfield_eq_two_or_four_dvd (fixSubfieldRestrict η σ) h2).resolve_left hk2)
    · exact Or.inl h2

end Exists

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
