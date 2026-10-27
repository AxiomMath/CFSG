module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PieceTorus
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignFieldTwist

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance e7PilotQ2FamilyTorusNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩


section Theta

variable {k : Type} [Field k] {K : Type} [Field K]

theorem baseChangeGL_mem_highRootSL2_of_E7 (ι : k →+* K) {x : ModGL .E7 k}
    (hx : x ∈ EPilot.highRootSL2 .E7 k) : baseChangeGL ι x ∈ EPilot.highRootSL2 .E7 K := by
  have hU : ∀ α : Fin (Tag.rank .E7) → ℤ,
      (rootSubgroup .E7 k α).map (baseChangeGL ι) ≤ rootSubgroup .E7 K α := by
    intro α
    rw [rootSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [baseChangeGL_pinnedX]
    exact subset_closure ⟨ι c, rfl⟩
  have h : (EPilot.highRootSL2 .E7 k).map (baseChangeGL ι) ≤ EPilot.highRootSL2 .E7 K := by
    rw [EPilot.highRootSL2, Subgroup.map_sup]
    exact sup_le_sup (hU _) (hU _)
  exact h ⟨x, hx, rfl⟩

theorem exists_conj_baseChangeGL_eq_highDiag_of_card_two_E7 [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {x : ModGL .E7 k}
    (hxJ : x ∈ EPilot.highRootSL2 .E7 k) (hx : orderOf x = 3) :
    ∃ n ∈ EPilot.highRootSL2 .E7 K, ∃ l : Kˣ, 3 ≤ orderOf l ∧
      n⁻¹ * baseChangeGL ι x * n = rootDiagUnit .E7 (EPilot.highDiag .E7 l) := by
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hk]; rfl)
  rw [← E6Pilot.range_rootSL2_highRoot] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = 3 := by
    rw [← hx, orderOf_injective _ E6Pilot.rootSL2_highRoot_injective]
  obtain ⟨P, l, hl, hP⟩ := E8Pilot.exists_inv_mul_map_mul_eq_HSL_of_card_two hk hK ι hA
  refine ⟨rootSL2 .E7 K (highRoot .E7) P, E6Pilot.rootSL2_highRoot_mem_highRootSL2 P, l, hl, ?_⟩
  rw [E6Pilot.baseChangeGL_rootSL2_highRoot, ← map_inv, ← map_mul, ← map_mul, hP,
    E6Pilot.rootSL2_highRoot_HSL (Or.inr (Or.inl rfl))]

theorem le_rootSpan_perpRoots_of_perfect_of_le_centralizer_E7 [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {x : ModGL .E7 k}
    (hxJ : x ∈ EPilot.highRootSL2 .E7 k) (hx : orderOf x = 3) {Q : Subgroup (ModGL .E7 K)}
    (hQ : ⁅Q, Q⁆ = Q) (hQC : Q ≤ adjointGroup .E7 K)
    (hQx : Q ≤ centralizer ({baseChangeGL ι x} : Set (ModGL .E7 K))) :
    Q ≤ rootSpan .E7 K (EPilot.perpRoots .E7) := by
  obtain ⟨n, hnJ, l, hl, hn⟩ :=
    exists_conj_baseChangeGL_eq_highDiag_of_card_two_E7 hk hK ι hxJ hx
  obtain ⟨hl1, hl2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hl
  have hnC : n ∈ adjointGroup .E7 K := EPilot.highRootSL2_le_adjointGroup hnJ
  set Q' := Q.map (MulAut.conj n⁻¹).toMonoidHom with hQ'
  have hQ'le : Q' ≤ torusGroup .E7 K ⊔ rootSpan .E7 K (EPilot.perpRoots .E7) := by
    rw [← EPilot.toralCentralizer_highDiag (Or.inr (Or.inl rfl)) hl1 hl2]
    rintro _ ⟨q, hq, rfl⟩
    have hqx : q * baseChangeGL ι x = baseChangeGL ι x * q :=
      mem_centralizer_singleton_iff.1 (hQx hq)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem (inv_mem hnC) (hQC hq)) hnC, ?_⟩
    rw [← hn]
    calc n⁻¹ * baseChangeGL ι x * n * (n⁻¹ * q * n) * (n⁻¹ * baseChangeGL ι x * n)⁻¹ =
        n⁻¹ * (baseChangeGL ι x * q) * (baseChangeGL ι x)⁻¹ * n := by group
      _ = n⁻¹ * q * n := by rw [← hqx]; group
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← map_commutator, hQ]
  have hQ'D : Q' ≤ rootSpan .E7 K (EPilot.perpRoots .E7) := by
    rw [← hQ'perf]
    exact (Subgroup.commutator_mono hQ'le hQ'le).trans
      (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer
        (fun x hx y hy => (triangular_borel_structure.{0, 0} .E7 K).1 x hx y hy)
        (torusGroup_le_normalizer_rootSpan fun α hα => hα.1))
  intro q hq
  have h1 : n⁻¹ * q * n ∈ rootSpan .E7 K (EPilot.perpRoots .E7) :=
    hQ'D ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have h2 : n * (n⁻¹ * q * n) * n⁻¹ = n⁻¹ * q * n := by
    rw [E6Pilot.commute_of_mem_highRootSL2_of_mem_perpLevi (Or.inr (Or.inl rfl)) hnJ h1,
      mul_inv_cancel_right]
  have h3 : q = n⁻¹ * q * n := by
    rw [← h2]
    group
  rw [h3]
  exact h1

end Theta

section Weyl

variable {k : Type} [Field k] {K : Type} [Field K]

theorem conj_wordElt_mem_rootSL2_E7 {F : Type} [Field F] (ω : List (Fin (Tag.rank .E7)))
    {x : ModGL .E7 F} (hx : x ∈ EPilot.highRootSL2 .E7 F) :
    wordElt F ω * x * (wordElt F ω)⁻¹ ∈
      rootSubgroup .E7 F ((coxeterSystem .E7).wordProd ω • highRoot .E7) ⊔
        rootSubgroup .E7 F (-((coxeterSystem .E7).wordProd ω • highRoot .E7)) := by
  have h : (EPilot.highRootSL2 .E7 F).map (MulAut.conj (wordElt F ω)).toMonoidHom =
      rootSubgroup .E7 F ((coxeterSystem .E7).wordProd ω • highRoot .E7) ⊔
        rootSubgroup .E7 F (-((coxeterSystem .E7).wordProd ω • highRoot .E7)) := by
    rw [EPilot.highRootSL2, Subgroup.map_sup,
      map_conj_prod_weylElt_rootSubgroup F ω (isRoot_highRoot .E7),
      map_conj_prod_weylElt_rootSubgroup F ω (IsRoot.neg (isRoot_highRoot .E7)), smul_neg]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem mem_centralizer_corootTuple_of_perfect_of_le_centralizer_word_E7 [Finite k] [Finite K]
    [CharP K 2] (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K)
    {x : ModGL .E7 k} (hxJ : x ∈ EPilot.highRootSL2 .E7 k) (hx : orderOf x = 3)
    (ω : List (Fin (Tag.rank .E7))) {Q : Subgroup (ModGL .E7 K)} (hQ : ⁅Q, Q⁆ = Q)
    (hQC : Q ≤ adjointGroup .E7 K)
    (hQx : Q ≤ centralizer ({baseChangeGL ι (wordElt k ω * x * (wordElt k ω)⁻¹)} :
      Set (ModGL .E7 K)))
    {g : ModGL .E7 K} (hg : g ∈ Q) (c : Kˣ) :
    g ∈ centralizer ({(rootDiagUnit .E7
      (corootTuple ((coxeterSystem .E7).wordProd ω • highRoot .E7) c))} :
        Set (ModGL .E7 K)) := by
  set m := wordElt K ω with hm
  have hmC : m ∈ adjointGroup .E7 K := wordElt_mem_adjointGroup ω
  have hι : baseChangeGL ι (wordElt k ω * x * (wordElt k ω)⁻¹) = m * baseChangeGL ι x * m⁻¹ := by
    rw [map_mul, map_mul, map_inv, baseChangeGL_wordElt]
  set Q' := Q.map (MulAut.conj m⁻¹).toMonoidHom with hQ'
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← map_commutator, hQ]
  have hQ'C : Q' ≤ adjointGroup .E7 K := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hmC) (hQC hq)) hmC
  have hQ'x : Q' ≤ centralizer ({baseChangeGL ι x} : Set (ModGL .E7 K)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqx := mem_centralizer_singleton_iff.1 (hQx hq)
    rw [hι] at hqx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mem_centralizer_singleton_iff]
    calc m⁻¹ * q * m * baseChangeGL ι x = m⁻¹ * (q * (m * baseChangeGL ι x * m⁻¹)) * m := by
          group
      _ = m⁻¹ * ((m * baseChangeGL ι x * m⁻¹) * q) * m := by rw [hqx]
      _ = baseChangeGL ι x * (m⁻¹ * q * m) := by group
  have hD := le_rootSpan_perpRoots_of_perfect_of_le_centralizer_E7 hk hK ι hxJ hx hQ'perf hQ'C hQ'x
  have hgD : m⁻¹ * g * m ∈ rootSpan .E7 K (EPilot.perpRoots .E7) :=
    hD ⟨g, hg, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hcomm := (EPilot.commute_of_mem_highTorusLine_of_mem_rootSpan
    (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c) hgD).eq
  have hconj : rootDiagUnit .E7 (corootTuple ((coxeterSystem .E7).wordProd ω • highRoot .E7) c) =
      m * rootDiagUnit .E7 (EPilot.highDiag .E7 c) * m⁻¹ := by
    rw [← list_prod_weylElt_conj_corootTuple, corootTuple_highRoot]
  rw [hconj, mem_centralizer_singleton_iff]
  set d := rootDiagUnit .E7 (EPilot.highDiag (K := K) .E7 c)
  calc g * (m * d * m⁻¹) = m * ((m⁻¹ * g * m) * d) * m⁻¹ := by group
    _ = m * (d * (m⁻¹ * g * m)) * m⁻¹ := by rw [hcomm]
    _ = m * d * m⁻¹ * g := by group

end Weyl

end CFSG.SeitzReduction.E7Pilot
