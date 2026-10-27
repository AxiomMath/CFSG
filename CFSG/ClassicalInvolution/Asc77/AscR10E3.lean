module

public import CFSG.ClassicalInvolution.Asc77.AscR10E2
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.LieType.RootSystem
  CFSG.LieType CFSG.Timmesfeld CFSG.LieType.BorelTits CFSG.ClassicalInvolution.WeakCT Matrix
open scoped MatrixGroups



section Main

variable {p e : ℕ} [Fact p.Prime]

@[expose] def A2UnitaryF4Odd (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .F4 0 p e → p ≠ 2 →
    ∀ (R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e)))
      (c₂ : ↥(adjointGroup .F4 (GaloisField p e))),
      R₂ ∈ longestFundamental (f4Datum (GaloisField p e)) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      (c₂ : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
        signDiagF4 (GaloisField p e) thetaF4 * (c₂ : ModGL .F4 (GaloisField p e)) →
      ¬ (∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c₂ * r = r * c₂) →
      (∃ v ∈ h1F4 (AlgClosGF p e),
        v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
            (c₂ : ModGL .F4 (GaloisField p e)) * v⁻¹ = signDiagF4 (AlgClosGF p e) deltaF4 ∧
        ∃ m ∈ parabolicLevi .F4 (AlgClosGF p e) JF4,
          entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹ =
            m * rootSL2 .F4 (AlgClosGF p e) thetaF4 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂

theorem a2UnitaryF4_odd : A2UnitaryF4Odd p e := by
  intro hadm hp2 R₂ c₂ hR₂ hc₂ ho _ _ ⟨v, hv, hd, m, hm, hcoc⟩
  have hne : NeZero e := ⟨by have := hadm.2.1; omega⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hk2 : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  obtain ⟨Em⟩ := nonempty_a2Embedding_F4 (GaloisField p (2 * e))
  have hcocycle := cocycle_conj_pinnedX p hk2 e
    (entrywiseFrobGL_baseChangeGL_algebraMap (c₂ : ModGL .F4 (GaloisField p e))) hd hm hcoc
  have hv' : ∀ t ∈ torusGroup .F4 (AlgClosGF p e), t * v ∈ h1F4 (AlgClosGF p e) :=
    fun t ht => mul_mem (levi_le_h1F4 (torusGroup_le_parabolicLevi JF4 ht)) hv
  obtain ⟨θ, hinj, hB12', hneg⟩ := exists_unitary_hom_odd hp2 isRoot_thetaF4
    isPartnerF4_deltaF4.1 a2Pairing_F4 Em hd hcocycle
    (fun t ht => rootDiagUnit_mul_comm_of_mem_torusGroup (corootDiagF4 deltaF4 (-1)) ht)
    (fun t ht => h1F4_le_adjointGroup (hv' t ht))
    (fun t ht A => conj_rootSL2_of_mem_h1F4 (hv' t ht) A)
    (fun j => by
      rw [rootTorusSL2_corootDiagF4 isPartnerF4_deltaF4.1 isPartnerF4_deltaF4.2.1,
        baseChangeGL_rootDiagUnit_corootDiagF4 j deltaF4]
      rfl)
  have hB12eq : (Phan.B12 (GaloisField p (2 * e)) p e).map θ =
      stdRankOne (f4Datum (GaloisField p e)) thetaF4 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
      obtain ⟨A₀, hA₀⟩ := hB12' A
      exact (mem_stdRankOne_f4_iff' isRoot_thetaF4 _).2 ⟨A₀, hA₀⟩
    · rw [natCard_rankOne hp2 (stdRankOne (f4Datum (GaloisField p e)) thetaF4)
        (fun g => mem_stdRankOne_f4_iff' isRoot_thetaF4 g),
        Subgroup.card_map_of_injective hinj, natCard_B12 hcardE]
  have hB23eq : (Phan.B23 (GaloisField p (2 * e)) p e).map θ = R₂ := by
    have h1 : (Phan.B23 (GaloisField p (2 * e)) p e).map θ =
        (stdRankOne (f4Datum (GaloisField p e)) thetaF4).map
          (MulAut.conj (θ (swapElt (GaloisField p (2 * e)) p e))).toMonoidHom := by
      rw [← map_conj_swapElt_B12 (GaloisField p (2 * e)) p e, Subgroup.map_map, ← hB12eq,
        Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    have hR' := map_conj_mem_longestFundamental (θ (swapElt (GaloisField p (2 * e)) p e))
      (stdRankOne_mem_longestFundamental (p := p) (e := e) isRoot_thetaF4 iform_thetaF4_self)
    have hc : c₂ ∈ (Phan.B23 (GaloisField p (2 * e)) p e).map θ :=
      ⟨_, ⟨suNegOne (GaloisField p (2 * e)) p e, rfl⟩, hneg⟩
    rw [h1] at hc ⊢
    exact eq_of_mem_longestFundamental_F4 hp2 hadm hR' hR₂ hc hc₂ ho
  exact ⟨θ.range, unitaryBlockStandardPair_of_normalized
    (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) rfl hB12eq hB23eq⟩

theorem a2_normalized_F4_odd (hadm : StatedLieAdmissible .F4 0 p e) (hU : A2UnitaryF4Odd p e)
    (hp2 : p ≠ 2) [NeZero e]
    {R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e))}
    (hR₂ : R₂ ∈ longestFundamental (f4Datum (GaloisField p e)))
    {c₂ : ↥(adjointGroup .F4 (GaloisField p e))} (hc₂ : c₂ ∈ R₂) (ho : orderOf c₂ = 2)
    (hcd : (c₂ : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
      signDiagF4 (GaloisField p e) thetaF4 * (c₂ : ModGL .F4 (GaloisField p e)))
    (hn : ¬ ∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂) ∨
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂ := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .F4 (f4Datum (GaloisField p e)) :=
    fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (f4Datum (GaloisField p e)) thetaF4 ∈
      Generic.fundamentalSubgroups .F4 (f4Datum (GaloisField p e)) :=
    ⟨1, thetaF4, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4
      iform_thetaF4_self), (Generic.conjSub_one _).symm⟩
  obtain ⟨y, hy⟩ := hsingle _ hθmem R₂ (longestFundamental_subset .F4 _ hR₂)
  have h1 : y⁻¹ * c₂ * y ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4 :=
    Generic.mem_conjSub_iff.1 (hy ▸ hc₂)
  have hord : orderOf (y⁻¹ * c₂ * y) = 2 := by
    rw [← ho]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective c₂
    simpa [MulAut.conj_apply] using this
  have z1 := eq_signDiagF4_of_orderOf_eq_two hK isRoot_thetaF4 iform_thetaF4_self h1 hord
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at z1
  have hgc : (y : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 *
      (y : ModGL .F4 (GaloisField p e))⁻¹ = (c₂ : ModGL .F4 (GaloisField p e)) := by
    rw [← z1]
    group
  have hc2 : (c₂ : ModGL .F4 (GaloisField p e)) * c₂ = 1 := by
    have := (orderOf_eq_prime_iff (p := 2)).1 ho
    have h := congrArg
      (fun x : ↥(adjointGroup .F4 (GaloisField p e)) => (x : ModGL .F4 (GaloisField p e))) this.1
    simpa [sq] using h
  have hnc : ¬ ∀ A : SL2 (GaloisField p e),
      (c₂ : ModGL .F4 (GaloisField p e)) * rootSL2 .F4 (GaloisField p e) thetaF4 A =
        rootSL2 .F4 (GaloisField p e) thetaF4 A * (c₂ : ModGL .F4 (GaloisField p e)) := by
    intro h
    apply hn
    intro r hr
    obtain ⟨A, hA⟩ := (mem_stdRankOne_f4_iff' isRoot_thetaF4 r).1 hr
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, hA]
    exact h A
  rcases exists_split_or_anti_F4 hp2 c₂.2 y.2 hc2 hcd hgc hnc with
    ⟨u, hu, hud, huθ⟩ | hanti
  · left
    exact linearBlockStandardPair_of_split_F4 hp2 hadm hR₂ hc₂ ho (u := ⟨u, hu⟩) huθ hud
  · right
    exact hU hadm hp2 R₂ c₂ hR₂ hc₂ ho hcd hn hanti

theorem a2BranchLeft_f4_aux_odd (hadm : StatedLieAdmissible .F4 0 p e) (hU : A2UnitaryF4Odd p e)
    (hp2 : p ≠ 2) 
    {R₁ R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e))}
    (h₁ : R₁ ∈ longestFundamental (f4Datum (GaloisField p e)))
    (h₂ : R₂ ∈ longestFundamental (f4Datum (GaloisField p e)))
    {c₁ c₂ : ↥(adjointGroup .F4 (GaloisField p e))} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ R₁, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .F4 (f4Datum (GaloisField p e)) :=
    fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (f4Datum (GaloisField p e)) thetaF4 ∈
      Generic.fundamentalSubgroups .F4 (f4Datum (GaloisField p e)) :=
    ⟨1, thetaF4, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4
      iform_thetaF4_self), (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R₁ (longestFundamental_subset .F4 _ h₁)
  have hR₁ : R₁ = (stdRankOne (f4Datum (GaloisField p e)) thetaF4).map
      (MulAut.conj g).toMonoidHom := hg
  obtain ⟨r₁, hr₁, rfl⟩ : ∃ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4,
      c₁ = g * r * g⁻¹ := by
    rw [hR₁] at hc₁
    obtain ⟨r, hr, hrc⟩ := hc₁
    exact ⟨r, hr, hrc.symm⟩
  have hor₁ : orderOf r₁ = 2 := by
    have := a2_orderOf_conj_eq_two ho₁ g⁻¹
    simpa [mul_assoc] using this
  have hd₁ := eq_signDiagF4_of_orderOf_eq_two hK isRoot_thetaF4 iform_thetaF4_self hr₁ hor₁
  set R₂' := R₂.map (MulAut.conj g⁻¹).toMonoidHom with hR₂'
  set c₂' : ↥(adjointGroup .F4 (GaloisField p e)) := g⁻¹ * c₂ * g with hc₂'
  have hR₂'l : R₂' ∈ longestFundamental (f4Datum (GaloisField p e)) :=
    map_conj_mem_longestFundamental g⁻¹ h₂
  have hc₂'R : c₂' ∈ R₂' := ⟨c₂, hc₂, by simp [hc₂']⟩
  have ho₂' : orderOf c₂' = 2 := by
    have := a2_orderOf_conj_eq_two ho₂ g⁻¹
    simpa [hc₂'] using this
  have hcomm' : r₁ * c₂' = c₂' * r₁ := by
    have h : g * r₁ * g⁻¹ * c₂ = c₂ * (g * r₁ * g⁻¹) := hcomm
    calc r₁ * c₂' = g⁻¹ * (g * r₁ * g⁻¹ * c₂) * g := by simp [hc₂']; group
      _ = g⁻¹ * (c₂ * (g * r₁ * g⁻¹)) * g := by rw [h]
      _ = c₂' * r₁ := by simp [hc₂']; group
  have hcd : (c₂' : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
      signDiagF4 (GaloisField p e) thetaF4 * (c₂' : ModGL .F4 (GaloisField p e)) := by
    rw [← hd₁]
    exact (congrArg Subtype.val hcomm').symm
  have hn' : ¬ ∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c₂' * r = r * c₂' := by
    intro h
    apply hn
    intro r hr
    rw [hR₁] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have h' := h r' hr'
    calc c₂ * (MulAut.conj g).toMonoidHom r' = g * (c₂' * r') * g⁻¹ := by
          simp [hc₂', MulAut.conj_apply]; group
      _ = g * (r' * c₂') * g⁻¹ := by rw [h']
      _ = (MulAut.conj g).toMonoidHom r' * c₂ := by
          simp [hc₂', MulAut.conj_apply]; group
  rcases a2_normalized_F4_odd hadm hU hp2 hR₂'l hc₂'R ho₂' hcd hn' with ⟨W, hW⟩ | ⟨W, hW⟩
  · left
    have h := linearBlockStandardPair_map_conj hW g
    have e2 : R₂'.map (MulAut.conj g).toMonoidHom = R₂ := by
      have := a2_map_conj_inv_map_conj g⁻¹ R₂
      rwa [inv_inv] at this
    rw [e2, ← hR₁] at h
    exact ⟨_, h⟩
  · right
    have h := CFSG.ClassicalInvolution.Models.unitaryBlockStandardPair_map hW
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have e2 : R₂'.map (MulAut.conj g).toMonoidHom = R₂ := by
      have := a2_map_conj_inv_map_conj g⁻¹ R₂
      rwa [inv_inv] at this
    rw [e2, ← hR₁] at h
    exact ⟨_, h⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
