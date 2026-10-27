module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentSplit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentPaired

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem eigenPlus_eq_ker {l : E} (hl0 : l ≠ 0) (A : Module.End E V) :
    eigenPlus l A = LinearMap.ker (A - l • 1) := by
  ext v
  simp only [eigenPlus, invSMulOp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  constructor
  · intro hv
    calc A v = l • (l⁻¹ • A v) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      _ = l • v := by rw [hv]
  · intro hv
    rw [hv, smul_smul, inv_mul_cancel₀ hl0, one_smul]

theorem eigenMinus_eq_ker {l : E} (hl0 : l ≠ 0) (A : Module.End E V) :
    eigenMinus l A = LinearMap.ker (A + l • 1) := by
  ext v
  simp only [eigenMinus, invSMulOp, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  constructor
  · intro hv
    calc A v + l • v = l • (l⁻¹ • A v + v) := by
          rw [smul_add, smul_smul, mul_inv_cancel₀ hl0, one_smul]
      _ = 0 := by rw [hv, smul_zero]
  · intro hv
    calc l⁻¹ • A v + v = l⁻¹ • (A v + l • v) := by
          rw [smul_add, smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = 0 := by rw [hv, smul_zero]

theorem eigenPlus_neg (l : E) (A : Module.End E V) : eigenPlus (-l) A = eigenMinus l A := by
  have h1 : invSMulOp (-l) A - 1 = -(invSMulOp l A + 1) := by
    rw [invSMulOp, invSMulOp, inv_neg, neg_smul, neg_add']
  rw [eigenPlus, eigenMinus, h1, LinearMap.ker_neg]

theorem eigenMinus_neg (l : E) (A : Module.End E V) : eigenMinus (-l) A = eigenPlus l A := by
  have h1 : invSMulOp (-l) A + 1 = -(invSMulOp l A - 1) := by
    rw [invSMulOp, invSMulOp, inv_neg, neg_smul, neg_sub, neg_add_eq_sub]
  rw [eigenPlus, eigenMinus, h1, LinearMap.ker_neg]

theorem norm_neg' (h : UnitaryFieldData p f E) (l : E) : h.norm (-l) = h.norm l := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, map_neg, neg_mul_neg]

section Summand

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem eq_one_of_mem_sesqNormOneScalars {g : sesqUnitaryGroup B}
    (hg : g ∈ sesqNormOneScalars h B) {W : Submodule E V} (hW0 : W ≠ ⊥)
    (hfix : ∀ w ∈ W, unitaryOp g w = w) : g = 1 := by
  obtain ⟨c, -, hcx⟩ := hg
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hc1 : c = 1 := by
    have h2 := hfix w hwW
    rw [unitaryOp, hcx, LinearMap.smul_apply, Module.End.one_apply] at h2
    have h3 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hw0)
  apply Subtype.ext
  apply Units.ext
  rw [hcx, hc1, one_smul]
  rfl

theorem exists_summand_of_isComponent (hp : p ≠ 2) [FiniteDimensional E V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {T : sesqUnitaryGroup B} {l : E} (hl0 : l ≠ 0)
    (hAA : unitaryOp T * unitaryOp T = (l ^ 2) • 1) (hN : h.norm l = 1)
    (hP : eigenPlus l (unitaryOp T) ≠ ⊥) (hM : eigenMinus l (unitaryOp T) ≠ ⊥)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L) :
    ∃ A W : Submodule E V,
      (A = eigenPlus l (unitaryOp T) ∧ W = eigenMinus l (unitaryOp T) ∨
        A = eigenMinus l (unitaryOp T) ∧ W = eigenPlus l (unitaryOp T)) ∧
      2 ≤ finrank E A ∧
      ((L.map (Subgroup.centralizer {T}).subtype : Subgroup (sesqUnitaryGroup B)) :
        Set (sesqUnitaryGroup B)) = summandUnitarySet B A W ∧
      ∀ R : Subgroup (sesqUnitaryGroup B),
        R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
          Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)) →
        ⁅R, R⁆ = R → ∀ g ∈ R, ∀ a ∈ A, unitaryOp g a = a := by
  have := h.finite
  obtain ⟨-, -, -, e, he⟩ := exists_split_centralizer_equiv hp hB hBl hl0 hAA hN
  rcases fst_eq_or_snd_eq_of_isComponent_prod (isComponent_map_of_isComponent e hL) with
    h2 | h1
  · have hfix : ∀ x ∈ L, ∀ w ∈ eigenMinus l (unitaryOp T),
        unitaryOp (x : sesqUnitaryGroup B) w = w := by
      intro x hx w hw
      have h3 := h2 (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      have h4 : ((((e x).2 : LinearMap.GeneralLinearGroup E (eigenMinus l (unitaryOp T))) :
          Module.End E (eigenMinus l (unitaryOp T))) ⟨w, hw⟩ : V) =
          unitaryOp (x : sesqUnitaryGroup B) w :=
        LinearMap.congr_fun (he x).2 ⟨w, hw⟩
      rw [← h4, h3]
      rfl
    exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, split_case hp hB hBl hl0 hAA hN hP hL hfix⟩
  · have hfix : ∀ x ∈ L, ∀ w ∈ eigenMinus (-l) (unitaryOp T),
        unitaryOp (x : sesqUnitaryGroup B) w = w := by
      intro x hx w hw
      rw [eigenMinus_neg] at hw
      have h3 := h1 (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      have h4 : ((((e x).1 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
          Module.End E (eigenPlus l (unitaryOp T))) ⟨w, hw⟩ : V) =
          unitaryOp (x : sesqUnitaryGroup B) w :=
        LinearMap.congr_fun (he x).1 ⟨w, hw⟩
      rw [← h4, h3]
      rfl
    have hAA' : unitaryOp T * unitaryOp T = ((-l) ^ 2) • 1 := by rw [neg_sq]; exact hAA
    have hP' : eigenPlus (-l) (unitaryOp T) ≠ ⊥ := by rw [eigenPlus_neg]; exact hM
    have hs := split_case hp hB hBl (neg_ne_zero.mpr hl0) hAA' (by rw [norm_neg']; exact hN)
      hP' hL hfix
    rw [eigenPlus_neg, eigenMinus_neg] at hs
    exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, hs⟩

end Summand

theorem odd_projective_unitary_local_component_supported_on_eigenspace
    (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V] (hn : 2 ≤ finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {u : sesqProjUnitary h B} (hu : orderOf u = 2) {T : sesqUnitaryGroup B}
    (hTu : QuotientGroup.mk' (sesqNormOneScalars h B) T = u)
    {Bc : Subgroup (Subgroup.centralizer {u})} (hBc : CFSG.IsComponent Bc)
    {Q : Subgroup (sesqProjUnitary h B)}
    (hQB : Q ≤ Subgroup.centralizer ((Bc.map (Subgroup.centralizer {u}).subtype :
      Subgroup (sesqProjUnitary h B)) : Set (sesqProjUnitary h B)))
    (hQ : Q ≠ ⊥) (hQp : ⁅Q, Q⁆ = Q) :
    ∃ l : E, l ≠ 0 ∧ unitaryOp T * unitaryOp T = (l ^ 2) • 1 ∧ h.norm l = 1 ∧
      LinearMap.ker (unitaryOp T - l • 1) ≠ ⊥ ∧ LinearMap.ker (unitaryOp T + l • 1) ≠ ⊥ ∧
      IsCompl (LinearMap.ker (unitaryOp T - l • 1)) (LinearMap.ker (unitaryOp T + l • 1)) ∧
      (∀ v ∈ LinearMap.ker (unitaryOp T - l • 1), ∀ w ∈ LinearMap.ker (unitaryOp T + l • 1),
        B v w = 0) ∧
      (B.domRestrict₁₂ (LinearMap.ker (unitaryOp T - l • 1))
        (LinearMap.ker (unitaryOp T - l • 1))).Nondegenerate ∧
      (B.domRestrict₁₂ (LinearMap.ker (unitaryOp T + l • 1))
        (LinearMap.ker (unitaryOp T + l • 1))).Nondegenerate ∧
      ∃ A W : Submodule E V,
        (A = LinearMap.ker (unitaryOp T - l • 1) ∧ W = LinearMap.ker (unitaryOp T + l • 1) ∨
          A = LinearMap.ker (unitaryOp T + l • 1) ∧ W = LinearMap.ker (unitaryOp T - l • 1)) ∧
        2 ≤ finrank E A ∧
        ((⁅(Bc.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (sesqNormOneScalars h B)),
          (Bc.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (sesqNormOneScalars h B))⁆ : Subgroup (sesqUnitaryGroup B)) :
          Set (sesqUnitaryGroup B)) = summandUnitarySet B A W ∧
        (∃ e : (⁅(Bc.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (sesqNormOneScalars h B)),
          (Bc.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (sesqNormOneScalars h B))⁆ : Subgroup (sesqUnitaryGroup B)) ≃* Bc,
          ∀ g, ((e g : Subgroup.centralizer {u}) : sesqProjUnitary h B) =
            QuotientGroup.mk' (sesqNormOneScalars h B) (g : sesqUnitaryGroup B)) ∧
        ∀ g ∈ ⁅Q.comap (QuotientGroup.mk' (sesqNormOneScalars h B)),
            Q.comap (QuotientGroup.mk' (sesqNormOneScalars h B))⁆,
          ∀ a ∈ A, unitaryOp g a = a := by
  subst hTu
  have := h.finite
  obtain ⟨l, hl0, hAA, hN, hP, hM, hc, hsplit, -, -, hnorm, hidx, hZc, -, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hu
  have hrange : ((Subgroup.centralizer {T}).map
      (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
        (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) T}) =
      (centralizerProj (sesqNormOneScalars h B) T).range := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, hg, hgx⟩
      exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  have hcomm : _root_.commutator
      (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) T}) ≤
        (centralizerProj (sesqNormOneScalars h B) T).range := by
    rw [← hrange]
    exact commutator_le_of_index_le_two hidx
  obtain ⟨hLc, hLB, hPL, hQperf, -, hQhat, hQcent⟩ := lift_component hZc hcomm hBc hQB hQ hQp
  generalize ⁅Bc.comap (centralizerProj (sesqNormOneScalars h B) T),
    Bc.comap (centralizerProj (sesqNormOneScalars h B) T)⁆ = L at hLc hLB hPL hQcent
  have hN1 : h.norm l = 1 := by
    rcases hN with hN | hN
    · exact hN
    · exact absurd (paired_case hp hB hBl hl0 hAA hN hLc hQcent hQperf) hQhat
  obtain ⟨horth, hsepP, hsepM, -, -⟩ := hsplit hN1
  obtain ⟨A, W, hAW, hm2, hset, hfixR⟩ :=
    exists_summand_of_isComponent hp hB hBl hl0 hAA hN1 hP hM hLc
  have hW0 : W ≠ ⊥ := by
    rcases hAW with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hM, hP]
  obtain ⟨e, he⟩ := exists_mulEquiv_of_inf_eq_one hLB fun x hx hxZ => Subtype.ext
    (eq_one_of_mem_sesqNormOneScalars hxZ hW0
      (((Set.ext_iff.mp hset _).mp (Subgroup.mem_map_of_mem _ hx)).1))
  refine ⟨l, ?_⟩
  rw [← eigenPlus_eq_ker hl0, ← eigenMinus_eq_ker hl0, hPL]
  exact ⟨hl0, hAA, hN1, hP, hM, hc, horth,
    CatalogueBUnitaryB.nondegenerate_of_isSymm ⟨fun x y => hB.eq x y⟩ hsepP,
    CatalogueBUnitaryB.nondegenerate_of_isSymm ⟨fun x y => hB.eq x y⟩ hsepM, A, W, hAW, hm2,
    hset, ⟨e, he⟩, fun g hg a ha => hfixR _ hQcent hQperf g hg a ha⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
