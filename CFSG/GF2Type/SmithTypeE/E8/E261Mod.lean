module

public import CFSG.GF2Type.SmithTypeE.E8.E23aMod
public import CFSG.GF2Type.SmithTypeE.E8.E23Four
public import CFSG.GF2Type.SmithTypeE.E8.SfCent

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open scoped Pointwise

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.Steinberg.Adjoint


theorem toWeight_dot_highRoot : ∀ γ ∈ rootList .E7, γ (highNode .E7) = 0 →
    MinData.toWeight γ ⬝ᵥ highRoot .E7 = 0 := by
  decide +kernel

theorem exists_wt_dot_neg_one : ∀ γ ∈ rootList .E7, γ (highNode .E7) = 0 →
    ∃ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ γ = -1 ∧ e7Data.wt a ⬝ᵥ highRoot .E7 = 0 := by
  decide +kernel

theorem exists_inComm_mem_V0 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ perpRoots .E7) :
    ∃ w ∈ weightVec, InComm (pinnedElt .E7 γ (1 : ZMod 2)) w ∧ w ∈ V0 := by
  obtain ⟨a, ha1, ha0⟩ := exists_wt_dot_neg_one γ (mem_rootList.2 hγ.1) hγ.2
  obtain ⟨b, hb⟩ := exists_wt_eq_of_dotProduct hγ.1 ha1
  refine ⟨Finsupp.single b 1, single_mem_weightVec b, ⟨Finsupp.single a 1, ?_⟩, ?_⟩
  · rw [e7Rep56_pinnedElt_single hγ.1 a, if_pos ha1, wt_e7Shift hb]
    abel
  · refine Finsupp.single_mem_supported (ZMod 2) _ ?_
    rw [Finset.mem_coe, mem_zeroIdx, hb, add_dotProduct, ha0,
      toWeight_dot_highRoot γ (mem_rootList.2 hγ.1) hγ.2]
    rfl

theorem highRadical_eq_rootRadical :
    highRadical .E7 (ZMod 2) = rootRadical .E7 (ZMod 2) (highRoot .E7) := by
  rw [highRadical, rootRadical, parabolicRadical, ← radicalRoots_highRoot (Or.inr (Or.inl rfl))]

theorem radicalRoots_highRoot_pos' :
    ∀ β ∈ radicalRoots .E7 (highRoot .E7), IsRoot .E7 β ∧ 0 < height β := by
  rintro β ⟨hβ, hpos⟩
  refine ⟨hβ, (IsRoot.height_pos_iff hβ).2 ?_⟩
  rw [iform_comm, iform_highRoot (Or.inr (Or.inl rfl))] at hpos
  rcases hβ.nonneg_or_nonpos with h | h
  · exact h
  · exact absurd (h (highNode .E7)) (not_le.2 hpos)

theorem radicalRoots_highRoot_closed' : ∀ α ∈ radicalRoots .E7 (highRoot .E7),
    ∀ β ∈ radicalRoots .E7 (highRoot .E7), ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot .E7 (a • α + b • β) → a • α + b • β ∈ radicalRoots .E7 (highRoot .E7) := by
  rintro α ⟨-, hα⟩ β ⟨-, hβ⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_⟩
  rw [iform_add_left, ← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β,
    iform_smul_left, iform_smul_left]
  nlinarith

theorem radicalRoots_highRoot_ncard' : (radicalRoots .E7 (highRoot .E7)).ncard = 33 := by
  rw [radicalRoots, ncard_setOf_isRoot_and]
  decide +kernel

theorem natCard_highRadical : Nat.card ↥(highRadical .E7 (ZMod 2)) = 2 ^ 33 := by
  have h : Nat.card ↥(rootRadical .E7 (ZMod 2) (highRoot .E7)) = 2 ^ 33 := by
    rw [rootRadical, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup' _)).toEquiv,
      card_rootSpan radicalRoots_highRoot_pos' radicalRoots_highRoot_closed',
      radicalRoots_highRoot_ncard']
    simp [Nat.card_zmod]
  rw [highRadical_eq_rootRadical]
  exact h

theorem card_centralizer_xT_le :
    Nat.card ↥(Subgroup.centralizer ({xT} : Set ↥(adjointGroup .E7 (ZMod 2)))) ≤
      2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) := by
  obtain ⟨-, hsup, -, hnorm⟩ := CFSG.SeitzReduction.EPilot.isTwoRadicalDecomp_highRoot
    (τ := .E7) (K := ZMod 2) (Or.inr (Or.inl rfl)) (one_ne_zero : (1 : ZMod 2) ≠ 0)
  have hset : ((Subgroup.centralizer ({xT} : Set ↥(adjointGroup .E7 (ZMod 2))) :
      Subgroup ↥(adjointGroup .E7 (ZMod 2))) : Set ↥(adjointGroup .E7 (ZMod 2))) =
      (highRadical .E7 (ZMod 2) : Set ↥(adjointGroup .E7 (ZMod 2))) *
        (perpLevi .E7 (ZMod 2) : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact congrArg _ hsup.symm
  calc Nat.card ↥(Subgroup.centralizer ({xT} : Set ↥(adjointGroup .E7 (ZMod 2))))
      = Nat.card ↥((highRadical .E7 (ZMod 2) : Set ↥(adjointGroup .E7 (ZMod 2))) *
        (perpLevi .E7 (ZMod 2) : Set ↥(adjointGroup .E7 (ZMod 2)))) := by
        rw [← hset]; rfl
    _ ≤ Nat.card ↥(highRadical .E7 (ZMod 2)) * Nat.card ↥(perpLevi .E7 (ZMod 2)) :=
        Set.natCard_mul_le
    _ = 2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) := by rw [natCard_highRadical]

theorem card_centralizer_conj' {X : Type*} [Group X] (g x : X) :
    Nat.card ↥(Subgroup.centralizer ({g * x * g⁻¹} : Set X)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * c * g, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      invFun := fun c => ⟨g * c * g⁻¹, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      left_inv := fun c => Subtype.ext (by simp only; group)
      right_inv := fun c => Subtype.ext (by simp only; group) }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    calc g⁻¹ * (c : X) * g * x = g⁻¹ * ((c : X) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (c : X)) * g := by rw [h]
      _ = x * (g⁻¹ * (c : X) * g) := by group
  · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    calc g * (c : X) * g⁻¹ * (g * x * g⁻¹) = g * ((c : X) * x) * g⁻¹ := by group
      _ = g * (x * (c : X)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * (c : X) * g⁻¹) := by group

theorem card_centralizer_le_of_isRootInvol {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : IsRootInvol r) :
    Nat.card ↥(Subgroup.centralizer ({r} : Set ↥(adjointGroup .E7 (ZMod 2)))) ≤
      2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) := by
  obtain ⟨h, hh⟩ := isConj_iff.1 hr
  have hr' : r = h * xT * h⁻¹ := hh.symm
  rw [hr', card_centralizer_conj' h xT]
  exact card_centralizer_xT_le

theorem exists_wt_dot_highRoot_eq_neg_one : ∃ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = -1 := by
  decide +kernel

theorem xT_ne_one : xT ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := exists_wt_dot_highRoot_eq_neg_one
  have h1 : e7Rep56 (ZMod 2) (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2))
      (Finsupp.single a 1) = Finsupp.single a 1 := by
    have : pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) = 1 := h
    rw [this, map_one]
    rfl
  rw [rep_pinnedElt_eq_self_iff (isRoot_highRoot .E7)] at h1
  have := h1 a ha
  simp at this

theorem xT_mul_self : xT * xT = 1 := pinnedElt_mul_self

theorem eq_top_of_simple_of_centralizer_le {J : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    [IsSimpleGroup ↥J] (h2 : 2 < Nat.card ↥J) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : IsRootInvol r) (hJ : ∀ g : ↥(adjointGroup .E7 (ZMod 2)), g * r = r * g → g ∈ J) :
    J = ⊤ := by
  obtain ⟨h, hh⟩ := isConj_iff.1 hr
  have hh' : h * xT * h⁻¹ = r := hh
  let A : Subgroup (ModGL .E7 (ZMod 2)) :=
    (J.map (adjointGroup .E7 (ZMod 2)).subtype).comap
      (MulAut.conj (h : ModGL .E7 (ZMod 2))).toMonoidHom
  have hA : ∀ g : ↥(adjointGroup .E7 (ZMod 2)), (g : ModGL .E7 (ZMod 2)) ∈ A ↔ h * g * h⁻¹ ∈ J := by
    intro g
    have e : (h : ModGL .E7 (ZMod 2)) * (g : ModGL .E7 (ZMod 2)) * (h : ModGL .E7 (ZMod 2))⁻¹ =
        ((h * g * h⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    show (h : ModGL .E7 (ZMod 2)) * (g : ModGL .E7 (ZMod 2)) * (h : ModGL .E7 (ZMod 2))⁻¹ ∈
      J.map (adjointGroup .E7 (ZMod 2)).subtype ↔ _
    rw [e]
    constructor
    · rintro ⟨j, hj, hjeq⟩
      have : j = h * g * h⁻¹ := Subtype.ext hjeq
      rwa [← this]
    · intro hj
      exact ⟨_, hj, rfl⟩
  have hcent : centThetaGL ≤ A := by
    intro c hc
    obtain ⟨x, rfl, hx⟩ := mem_centThetaGL.1 hc
    rw [hA]
    refine hJ _ ?_
    rw [← hh']
    calc h * x * h⁻¹ * (h * xT * h⁻¹) = h * (x * xT) * h⁻¹ := by group
      _ = h * (xT * x) * h⁻¹ := by rw [show x * xT = xT * x from hx]
      _ = h * xT * h⁻¹ * (h * x * h⁻¹) := by group
  have hB : borelGroup .E7 (ZMod 2) ≤ A := borelGroup_le_centThetaGL.trans hcent
  have hAle : A ≤ adjointGroup .E7 (ZMod 2) := by
    intro a ha
    obtain ⟨j, hjJ, hja⟩ := ha
    have e : a = (h : ModGL .E7 (ZMod 2))⁻¹ * (j : ModGL .E7 (ZMod 2)) * (h : ModGL .E7 (ZMod 2)) := by
      have : (j : ModGL .E7 (ZMod 2)) = (h : ModGL .E7 (ZMod 2)) * a * (h : ModGL .E7 (ZMod 2))⁻¹ := hja
      rw [this]
      group
    rw [e]
    exact (adjointGroup .E7 (ZMod 2)).mul_mem ((adjointGroup .E7 (ZMod 2)).mul_mem
      ((adjointGroup .E7 (ZMod 2)).inv_mem h.2) j.2) h.2
  have hcl := (borel_overgroup_classification .E7 (ZMod 2)).1 A hB hAle
  have hJ1 : ∀ i : Fin (Tag.rank .E7), i ≠ e7n1 → weylElt .E7 (ZMod 2) i 1 ∈ A := fun i hi =>
    hcent ((weylElt_mem_centThetaGL_iff i).2 hi)
  by_cases he : weylElt .E7 (ZMod 2) e7n1 1 ∈ A
  · have hall : {i | weylElt .E7 (ZMod 2) i 1 ∈ A} = Set.univ := by
      refine Set.eq_univ_of_forall fun i => ?_
      by_cases hi : i = e7n1
      · subst hi
        exact he
      · exact hJ1 i hi
    have hA' : A = adjointGroup .E7 (ZMod 2) := by
      rw [hcl, hall]
      exact (standard_parabolic_cells .E7 (ZMod 2)).2.2.2.2.2.1
    refine eq_top_iff.2 fun j _ => ?_
    have hmem : ((h⁻¹ * j * h : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈ A := by
      rw [hA']
      exact (h⁻¹ * j * h).2
    have := (hA _).1 hmem
    simpa [mul_assoc] using this
  · exfalso
    have hset : {i | weylElt .E7 (ZMod 2) i 1 ∈ A} = {i | i ≠ e7n1} := by
      ext i
      constructor
      · intro hi hi'
        subst hi'
        exact he hi
      · exact hJ1 i
    have hA' : A = parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n1} := by
      rw [hcl, hset]
    have hrJ : r ∈ J := hJ r rfl
    have hcomm : ∀ j ∈ J, j * r * j⁻¹ = r := by
      intro j hj
      have hmem : ((h⁻¹ * j * h : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈ A := by
        rw [hA]
        simpa [mul_assoc] using hj
      rw [hA'] at hmem
      have hx := (centralizer_xtheta_iff (h⁻¹ * j * h)).2 hmem
      have e : j * r * j⁻¹ = h * ((h⁻¹ * j * h) * xT * (h⁻¹ * j * h)⁻¹) * h⁻¹ := by
        rw [← hh']
        group
      rw [e]
      have hx' : (h⁻¹ * j * h) * xT * (h⁻¹ * j * h)⁻¹ = xT := hx
      rw [hx', hh']
    have hr1 : r ≠ 1 := by
      intro h1
      apply xT_ne_one
      rw [← hh'] at h1
      have : h * xT * h⁻¹ = 1 := h1
      calc xT = h⁻¹ * (h * xT * h⁻¹) * h := by group
        _ = 1 := by rw [this]; group
    have hrr : r * r = 1 := by
      rw [← hh']
      calc h * xT * h⁻¹ * (h * xT * h⁻¹) = h * (xT * xT) * h⁻¹ := by group
        _ = 1 := by rw [xT_mul_self]; group
    set r' : ↥J := ⟨r, hrJ⟩ with hr'
    have hcentral : ∀ x : ↥J, Commute x r' := fun x => by
      show (x : ↥J) * r' = r' * x
      refine Subtype.ext ?_
      have := hcomm x x.2
      exact (mul_inv_eq_iff_eq_mul.1 this)
    haveI : (Subgroup.zpowers r').Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : Commute g (r' ^ k) := (hcentral g).zpow_right k
      rw [hc.eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers r') k⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers r') with hbot | htop
    · have : r' ∈ Subgroup.zpowers r' := Subgroup.mem_zpowers r'
      rw [hbot, Subgroup.mem_bot] at this
      exact hr1 (congrArg Subtype.val this)
    · have hord : orderOf r' = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · exact Subtype.ext hrr
        · intro h1
          exact hr1 (congrArg Subtype.val h1)
      have hcard : Nat.card ↥J = 2 := by
        have := Nat.card_zpowers r'
        rw [htop, Subgroup.card_top, hord] at this
        exact this
      omega

end CFSG.GF2Type.SmithTypeE.E8
