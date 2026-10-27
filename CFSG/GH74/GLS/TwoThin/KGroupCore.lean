module

public import CFSG.GH74.GLS.TwoThin.KGroup
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.GLS.TwoThin.Count

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open scoped commutatorElement

@[expose] def fixedSubgroup {L : Type} [Group L] (σ : L ≃* L) : Subgroup L where
  carrier := {l | σ l = l}
  one_mem' := map_one σ
  mul_mem' {a b} ha hb := by
    change σ (a * b) = a * b
    change σ a = a at ha
    change σ b = b at hb
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    change σ a⁻¹ = a⁻¹
    change σ a = a at ha
    rw [map_inv, ha]

theorem mem_fixedSubgroup {L : Type} [Group L] {σ : L ≃* L} {l : L} :
    l ∈ fixedSubgroup σ ↔ σ l = l := Iff.rfl

@[expose] def TwoThinKGroupVertical' : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (σ : L ≃* L) (I : Subgroup L) (K₀ : Type) [Group K₀],
    CFSG.IsQuasisimple L → (InC2 L ∨ InT2 L) → (∀ l, σ (σ l) = l) →
    IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 L

@[expose] def TwoThinCentralCover : Prop :=
  ∀ (L L₁ K₀ : Type) [Group L] [Finite L] [Group L₁] [Group K₀] (δ : L →* L₁) (φ : L₁ →* K₀),
    CFSG.IsQuasisimple L → (InC2 L ∨ InT2 L) → Function.Surjective δ → δ.ker ≤ center L →
    Function.Surjective φ → Odd (Nat.card φ.ker) → InB2 K₀ → InB2 L

@[expose] def TwoThinC2Vertical : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (σ : L ≃* L) (I : Subgroup L) (K₀ : Type) [Group K₀],
    CFSG.IsQuasisimple L → InC2 L → (∀ l, σ (σ l) = l) →
    IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → False

@[expose] def TwoThinT2Vertical : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (σ : L ≃* L) (I : Subgroup L) (K₀ : Type) [Group K₀],
    CFSG.IsQuasisimple L → InT2 L → center L = ⊥ → (∀ l, σ (σ l) = l) →
    IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → False

@[expose] def TwoThinC2Cover : Prop :=
  ∀ (L L₁ K₀ : Type) [Group L] [Finite L] [Group L₁] [Group K₀] (δ : L →* L₁) (φ : L₁ →* K₀),
    CFSG.IsQuasisimple L → InC2 L → Function.Surjective δ → δ.ker ≤ center L →
    Function.Surjective φ → Odd (Nat.card φ.ker) → InB2 K₀ → False

@[expose] def TwoThinKGroupCore : Prop :=
  TwoThinC2Vertical ∧ TwoThinT2Vertical ∧ TwoThinC2Cover

@[expose] def TwoThinKGroupVertical'P (P : GroupPred) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (σ : L ≃* L) (I : Subgroup L) (K₀ : Type) [Group K₀],
    P L → CFSG.IsQuasisimple L → (InC2 L ∨ InT2 L) → (∀ l, σ (σ l) = l) →
    IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 L

@[expose] def TwoThinCentralCoverP (P : GroupPred) : Prop :=
  ∀ (L L₁ K₀ : Type) [Group L] [Finite L] [Group L₁] [Group K₀] (δ : L →* L₁) (φ : L₁ →* K₀),
    P L → CFSG.IsQuasisimple L → (InC2 L ∨ InT2 L) → Function.Surjective δ → δ.ker ≤ center L →
    Function.Surjective φ → Odd (Nat.card φ.ker) → InB2 K₀ → InB2 L

@[expose] def TwoThinC2VerticalP (P : GroupPred) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (σ : L ≃* L) (I : Subgroup L) (K₀ : Type) [Group K₀],
    P L → CFSG.IsQuasisimple L → InC2 L → (∀ l, σ (σ l) = l) →
    IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → False

@[expose] def TwoThinT2VerticalP (P : GroupPred) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (σ : L ≃* L) (I : Subgroup L) (K₀ : Type) [Group K₀],
    P L → CFSG.IsQuasisimple L → InT2 L → center L = ⊥ → (∀ l, σ (σ l) = l) →
    IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → False

@[expose] def TwoThinC2CoverP (P : GroupPred) : Prop :=
  ∀ (L L₁ K₀ : Type) [Group L] [Finite L] [Group L₁] [Group K₀] (δ : L →* L₁) (φ : L₁ →* K₀),
    P L → CFSG.IsQuasisimple L → InC2 L → Function.Surjective δ → δ.ker ≤ center L →
    Function.Surjective φ → Odd (Nat.card φ.ker) → InB2 K₀ → False

@[expose] def TwoThinKGroupCoreP (P : GroupPred) : Prop :=
  TwoThinC2VerticalP P ∧ TwoThinT2VerticalP P ∧ TwoThinC2CoverP P

theorem TwoThinKGroupCore.toP (h : TwoThinKGroupCore) (P : GroupPred) : TwoThinKGroupCoreP P := by
  refine ⟨?_, ?_, ?_⟩
  · intro L _ _ σ I K₀ _ _ hq hC hσ hI hK₀ hφ
    exact h.1 L σ I K₀ hq hC hσ hI hK₀ hφ
  · intro L _ _ σ I K₀ _ _ hq hT hz hσ hI hK₀ hφ
    exact h.2.1 L σ I K₀ hq hT hz hσ hI hK₀ hφ
  · intro L L₁ K₀ _ _ _ _ δ φ _ hq hC hδs hδk hφs hφo hK₀
    exact h.2.2 L L₁ K₀ δ φ hq hC hδs hδk hφs hφo hK₀

theorem TwoThinKGroupCoreP.toCore (h : TwoThinKGroupCoreP GroupPred.trivial) :
    TwoThinKGroupCore := by
  refine ⟨?_, ?_, ?_⟩
  · intro L _ _ σ I K₀ _ hq hC hσ hI hK₀ hφ
    exact h.1 L σ I K₀ trivial hq hC hσ hI hK₀ hφ
  · intro L _ _ σ I K₀ _ hq hT hz hσ hI hK₀ hφ
    exact h.2.1 L σ I K₀ trivial hq hT hz hσ hI hK₀ hφ
  · intro L L₁ K₀ _ _ _ _ δ φ hq hC hδs hδk hφs hφo hK₀
    exact h.2.2 L L₁ K₀ δ φ trivial hq hC hδs hδk hφs hφo hK₀

theorem twoThinKGroupVertical'P_of {P : GroupPred} (hC : TwoThinC2VerticalP P)
    (hT : TwoThinT2VerticalP P) : TwoThinKGroupVertical'P P := by
  intro L _ _ σ I K₀ _ hP hq hLC hσ hI hK₀ hφ
  rcases hLC with h | h
  · exact (hC L σ I K₀ hP hq h hσ hI hK₀ hφ).elim
  · by_cases hz : center L = ⊥
    · exact (hT L σ I K₀ hP hq h hz hσ hI hK₀ hφ).elim
    · exact ⟨h, hz⟩

theorem twoThinKGroupVertical'_of (hC : TwoThinC2Vertical) (hT : TwoThinT2Vertical) :
    TwoThinKGroupVertical' := by
  intro L _ _ σ I K₀ _ hq hLC hσ hI hK₀ hφ
  exact twoThinKGroupVertical'P_of (P := GroupPred.trivial)
    (by
      intro L _ _ σ I K₀ _ _ hq hC' hσ hI hK₀ hφ
      exact hC L σ I K₀ hq hC' hσ hI hK₀ hφ)
    (by
      intro L _ _ σ I K₀ _ _ hq hT' hz hσ hI hK₀ hφ
      exact hT L σ I K₀ hq hT' hz hσ hI hK₀ hφ)
    L σ I K₀ trivial hq hLC hσ hI hK₀ hφ

theorem twoThinCentralCoverP_of {P : GroupPred} (h : TwoThinC2CoverP P) :
    TwoThinCentralCoverP P := by
  intro L L₁ K₀ _ _ _ _ δ φ hP hq hLC hδs hδk hφs hφo hK₀
  rcases hLC with hC | hT
  · exact (h L L₁ K₀ δ φ hP hq hC hδs hδk hφs hφo hK₀).elim
  · by_cases hz : center L = ⊥
    · exfalso
      let ψ : L →* K₀ := φ.comp δ
      have hψs : Function.Surjective ψ := hφs.comp hδs
      have hδinj : Function.Injective δ :=
        (MonoidHom.ker_eq_bot_iff δ).mp (eq_bot_iff.mpr (hδk.trans hz.le))
      have hψodd : Odd (Nat.card ψ.ker) := by
        have h1 : ψ.ker = φ.ker.comap δ := (MonoidHom.comap_ker φ δ).symm
        rw [h1]
        exact hφo.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _ _ hδinj)
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker ψ) with
        htop | hle
      · have hS : IsSimpleGroup (L ⧸ center L) := hq.2.1
        have h4 : 4 ∣ Nat.card (L ⧸ center L) := four_dvd_card_of_simple_nonabelian hq.2.2
        have hc1 : Nat.card ↥(center L) = 1 := by
          rw [hz]
          exact Subgroup.card_bot
        have hcard : Nat.card L = Nat.card (L ⧸ center L) * Nat.card ↥(center L) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
        rw [hc1, mul_one] at hcard
        rw [htop, Subgroup.card_top, hcard] at hψodd
        exact (Nat.not_even_iff_odd.mpr hψodd) (even_iff_two_dvd.mpr
          (dvd_trans (by norm_num : 2 ∣ 4) h4))
      · have hψinj : Function.Injective ψ :=
          (MonoidHom.ker_eq_bot_iff ψ).mp (eq_bot_iff.mpr (hle.trans hz.le))
        let e : L ≃* K₀ := MulEquiv.ofBijective ψ ⟨hψinj, hψs⟩
        have hK₀z : center K₀ = ⊥ := by
          rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
        exact hK₀.2 hK₀z
    · exact ⟨hT, hz⟩

theorem twoThinCentralCover_of (h : TwoThinC2Cover) : TwoThinCentralCover := by
  intro L L₁ K₀ _ _ _ _ δ φ hq hLC hδs hδk hφs hφo hK₀
  exact twoThinCentralCoverP_of (P := GroupPred.trivial)
    (by
      intro L L₁ K₀ _ _ _ _ δ φ _ hq hC hδs hδk hφs hφo hK₀
      exact h L L₁ K₀ δ φ hq hC hδs hδk hφs hφo hK₀)
    L L₁ K₀ δ φ trivial hq hLC hδs hδk hφs hφo hK₀

theorem eq_top_or_le_center_of_subnormal {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {U : Subgroup Q} (hU : U.IsSubnormal) : U = ⊤ ∨ U ≤ center Q := by
  exact CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQ hU

theorem twoThinKGroupVerticalQ_of {Q P : GroupPred}
    (hQP : ∀ (H : Type) [Group H] [Finite H], Q H → ∀ L : Subgroup H, P ↥L)
    (h : TwoThinKGroupVertical'P P) : TwoThinKGroupVerticalQ Q := by
  intro H _ _ hQH s L I K₀ _ hs hL hLC hLs hI hIL hK₀ hφ
  obtain ⟨φ, hφs, hφo⟩ := hφ
  have key : ∀ x : H, x ∈ L ↔ s * x * s⁻¹ ∈ L := fun x => by
    have h1 := mem_conjSub_iff' (g := s⁻¹) (x := x) (K := L)
    rw [hLs, inv_inv] at h1
    exact h1
  have hsN : s ∈ normalizer (L : Set H) := Subgroup.mem_normalizer_iff.mpr key
  let σ : ↥L ≃* ↥L := conjAut hsN
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs, pow_two] at this
    exact this
  have hσσ : ∀ l, σ (σ l) = l := by
    intro l
    apply Subtype.ext
    show s * (s * (l : H) * s⁻¹) * s⁻¹ = l
    calc s * (s * (l : H) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
      _ = l := by rw [hss]; group
  have hfix : fixedSubgroup σ = (centralizer ({s} : Set H)).subgroupOf L := by
    ext a
    rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h' h'' hh''
      rw [Set.mem_singleton_iff.mp hh'']
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h')
    · intro h'
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (h' s (Set.mem_singleton s)))
  have hI' : IsPCompIn 2 (fixedSubgroup σ) (I.subgroupOf L) := by
    obtain ⟨hIC, hI2⟩ := isPCompIn_two_iff.mp hI
    have hIB : I ≤ centralizer ({s} : Set H) ⊓ L := le_inf hIC hIL
    have hI3 := TwoComponentTransport.restrict_nested I (centralizer ({s} : Set H) ⊓ L)
      (centralizer ({s} : Set H)) hIB inf_le_left hI2
    have hI4 := isTwoComponent_subgroupOf_subgroupOf hIB inf_le_right hI3
    refine isPCompIn_two_iff.mpr ⟨?_, ?_⟩
    · rw [hfix]
      intro a ha
      exact Subgroup.mem_subgroupOf.mpr (hIC (Subgroup.mem_subgroupOf.mp ha))
    · refine isTwoComponent_subgroupOf_congr ?_ hI4
      rw [hfix]
      exact Subgroup.inf_subgroupOf_right _ _
  let e : ↥(I.subgroupOf L) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIL
  refine h ↥L σ (I.subgroupOf L) K₀ (hQP H hQH L) hL.1 hLC hσσ hI' hK₀ ⟨φ.comp e.toMonoidHom,
    hφs.comp e.surjective, ?_⟩
  have h1 : (φ.comp e.toMonoidHom).ker = φ.ker.comap e.toMonoidHom := (MonoidHom.comap_ker _ _).symm
  rw [h1]
  exact hφo.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _ _ e.injective)

theorem twoThinKGroupVertical_of (h : TwoThinKGroupVertical') : TwoThinKGroupVertical := by
  intro H _ _ s L I K₀ _ hs hL hLC hLs hI hIL hK₀ hφ
  exact twoThinKGroupVerticalQ_of (Q := GroupPred.trivial) (P := GroupPred.trivial)
    (fun _ _ _ _ L => trivial)
    (by
      intro L _ _ σ I K₀ _ _ hq hLC hσ hI hK₀ hφ
      exact h L σ I K₀ hq hLC hσ hI hK₀ hφ)
    H trivial s L I K₀ hs hL hLC hLs hI hIL hK₀ hφ

theorem twoThinKGroupDiagonalQ_of {Q P : GroupPred}
    (hQP : ∀ (H : Type) [Group H] [Finite H], Q H → ∀ L : Subgroup H, P ↥L)
    (h : TwoThinCentralCoverP P) : TwoThinKGroupDiagonalQ Q := by
  intro H _ _ hQH s L I K₀ _ hAB hs hL hLC hLs hI hID hK₀ hφ
  obtain ⟨φ, hφs, hφo⟩ := hφ
  have hsinv : s⁻¹ = s := inv_eq_self_of_orderOf_eq_two hs
  have hDC : (swapDiag hAB).range ≤ centralizer ({s} : Set H) := by
    rintro _ ⟨x, rfl⟩
    exact swapDiag_mem_centralizer hAB hsinv x
  obtain ⟨hIC, hI2⟩ := isPCompIn_two_iff.mp hI
  have hperf : ⁅I, I⁆ = I := commutator_self_of_isTwoComponent hIC hI2
  have hne : I ≠ ⊥ := ne_bot_of_isTwoComponent hI2
  have hDa := isQuasisimple_range_swapDiag hAB (assembly_isQuasisimple_of_isComponent hL)
  have hDq : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
    CatalogueBAlternating.quasisimple_iff_native.mpr ⟨hDa.1, hDa.2⟩
  have hIsub : (I.subgroupOf (swapDiag hAB).range).IsSubnormal :=
    isSubnormal_inf_subgroupOf
      (Components.mathlib_subnormal_of_chain hI2.1 Subgroup.IsSubnormal.top) hDC
  have hmap : (I.subgroupOf (swapDiag hAB).range).map (swapDiag hAB).range.subtype = I :=
    Subgroup.map_subgroupOf_eq_of_le hID
  have hperf' : ⁅I.subgroupOf (swapDiag hAB).range, I.subgroupOf (swapDiag hAB).range⁆ =
      I.subgroupOf (swapDiag hAB).range := by
    apply Subgroup.map_injective (swapDiag hAB).range.subtype_injective
    rw [Subgroup.map_commutator, hmap, hperf]
  have hne' : I.subgroupOf (swapDiag hAB).range ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.map_bot] at hmap
    exact hne hmap.symm
  have htop : I.subgroupOf (swapDiag hAB).range = ⊤ := by
    rcases eq_top_or_le_center_of_subnormal hDq hIsub with h1 | h1
    · exact h1
    · exfalso
      apply hne'
      rw [← hperf']
      refine eq_bot_iff.mpr ?_
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have := Subgroup.mem_center_iff.mp (h1 hb) a
      exact commutatorElement_eq_one_iff_mul_comm.mpr this
  have hDI : (swapDiag hAB).range ≤ I := by
    intro d hd
    have : (⟨d, hd⟩ : ↥(swapDiag hAB).range) ∈ I.subgroupOf (swapDiag hAB).range := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  let δ' : ↥L →* ↥I := (swapDiag hAB).codRestrict I fun l => hDI ⟨l, rfl⟩
  have hδs : Function.Surjective δ' := by
    intro i
    obtain ⟨l, hl⟩ := hID i.2
    exact ⟨l, Subtype.ext hl⟩
  have hδk : δ'.ker ≤ center ↥L := by
    rw [show δ'.ker = (swapDiag hAB).ker from MonoidHom.ker_codRestrict _ _ _]
    exact ker_swapDiag_le_center hAB
  exact h ↥L ↥I K₀ δ' φ (hQP H hQH L) hL.1 hLC hδs hδk hφs hφo hK₀

theorem twoThinKGroupDiagonal_of (h : TwoThinCentralCover) : TwoThinKGroupDiagonal := by
  intro H _ _ s L I K₀ _ hAB hs hL hLC hLs hI hID hK₀ hφ
  exact twoThinKGroupDiagonalQ_of (Q := GroupPred.trivial) (P := GroupPred.trivial)
    (fun _ _ _ _ L => trivial)
    (by
      intro L L₁ K₀ _ _ _ _ δ φ _ hq hLC hδs hδk hφs hφo hK₀
      exact h L L₁ K₀ δ φ hq hLC hδs hδk hφs hφo hK₀)
    H trivial s L I K₀ hAB hs hL hLC hLs hI hID hK₀ hφ

theorem twoThinKGroupFactQ_of_coreP {Q P : GroupPred}
    (hQP : ∀ (H : Type) [Group H] [Finite H], Q H → ∀ L : Subgroup H, P ↥L)
    (h : TwoThinKGroupCoreP P) : TwoThinKGroupFactQ Q :=
  ⟨twoThinKGroupVerticalQ_of hQP (twoThinKGroupVertical'P_of h.1 h.2.1),
    twoThinKGroupDiagonalQ_of hQP (twoThinCentralCoverP_of h.2.2)⟩

theorem twoThinKGroupFact_of_core (h : TwoThinKGroupCore) : TwoThinKGroupFact :=
  ⟨twoThinKGroupVertical_of (twoThinKGroupVertical'_of h.1 h.2.1),
    twoThinKGroupDiagonal_of (twoThinCentralCover_of h.2.2)⟩

end CFSG.GH74.GLS.TwoThin
