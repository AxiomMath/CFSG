module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4LeviT
public import CFSG.LieType.Steinberg.RankTwo.Statement
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open scoped commutatorElement Matrix

section SL3

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

theorem mem_rootsA2_d4 {γ : Fin 2 → ℤ} : γ ∈ RA2 ↔
    γ = ![1, 0] ∨ γ = ![0, 1] ∨ γ = ![1, 1] ∨ γ = ![-1, 0] ∨ γ = ![0, -1] ∨ γ = ![-1, -1] := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
  have inj := CFSG.LieType.Universal.SpecialLinear.toStd_injective 2
  constructor
  · rintro ⟨i, j, hij, h⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl (inj (h.trans (by decide)))
    · exact Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide))))))
    · exact absurd rfl hij
    · exact Or.inr (Or.inl (inj (h.trans (by decide))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inj (h.trans (by decide)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))))
    · exact absurd rfl hij
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide⟩
    · exact ⟨1, 0, by decide, by decide⟩
    · exact ⟨2, 1, by decide, by decide⟩
    · exact ⟨2, 0, by decide, by decide⟩

@[expose] def a2D4 (γ : Fin 2 → ℤ) : Fin TwistTag.D4.tag.rank → ℤ :=
  γ 0 • trialityRoot 1 + γ 1 • trialityRoot 4

theorem a2D4_add (α β : Fin 2 → ℤ) : a2D4 (α + β) = a2D4 α + a2D4 β := by
  funext i
  simp only [a2D4, Pi.add_apply, add_smul]
  ring

theorem isRoot_d4_iff {v : Fin TwistTag.D4.tag.rank → ℤ} :
    IsRoot TwistTag.D4.tag v ↔ ∃ k : Fin 24, TwistTag.D4.tag.rootCertificate.root k = v := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 h
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, hk⟩
    exact (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨k, k.2, hk⟩

@[expose] def a2Roots : List (Fin 2 → ℤ) :=
  [![1, 0], ![0, 1], ![1, 1], ![-1, 0], ![0, -1], ![-1, -1]]

theorem mem_a2Roots {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) : γ ∈ a2Roots := by
  rcases mem_rootsA2_d4.1 hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [a2Roots]

theorem a2D4_pair_check : ∀ α ∈ a2Roots, ∀ β ∈ a2Roots,
    (∃ k : Fin 24, TwistTag.D4.tag.rootCertificate.root k = a2D4 α) ∧
      (α + β ≠ 0 → a2D4 α ≠ -a2D4 β) ∧ (α ≠ β → a2D4 α ≠ a2D4 β) ∧
      ((∃ k : Fin 24, TwistTag.D4.tag.rootCertificate.root k = a2D4 α + a2D4 β) ↔
        α + β ∈ a2Roots) ∧ (α = β → α + β ∉ a2Roots) := by
  decide +kernel

theorem a2Roots_iff {γ : Fin 2 → ℤ} : γ ∈ a2Roots ↔ γ ∈ RA2 := by
  constructor
  · intro h
    simp only [a2Roots, List.mem_cons, List.not_mem_nil, or_false] at h
    exact mem_rootsA2_d4.2 h
  · exact mem_a2Roots

theorem isRoot_a2D4 {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) :
    IsRoot TwistTag.D4.tag (a2D4 γ) :=
  isRoot_d4_iff.2 (a2D4_pair_check γ (mem_a2Roots hγ) γ (mem_a2Roots hγ)).1

variable {K : Type} [Field K]

theorem commute_pinnedX_self_d4
    (γ : Fin TwistTag.D4.tag.rank → ℤ) (c d : K) :
    Commute (pinnedX TwistTag.D4.tag K γ c) (pinnedX TwistTag.D4.tag K γ d) := by
  show _ * _ = _ * _
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

variable [CharP K 2]

theorem commutator_a2D4
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (c d : K) :
    (α + β ∈ RA2 → ⁅pinnedX TwistTag.D4.tag K (a2D4 α) c, pinnedX TwistTag.D4.tag K (a2D4 β) d⁆ =
        pinnedX TwistTag.D4.tag K (a2D4 (α + β)) (c * d)) ∧
      (α + β ∉ RA2 →
        ⁅pinnedX TwistTag.D4.tag K (a2D4 α) c, pinnedX TwistTag.D4.tag K (a2D4 β) d⁆ = 1) := by
  obtain ⟨-, hne', hne, hsum, hnot⟩ := a2D4_pair_check α (mem_a2Roots hα) β (mem_a2Roots hβ)
  have hsum' : IsRoot TwistTag.D4.tag (a2D4 α + a2D4 β) ↔ α + β ∈ RA2 := by
    rw [isRoot_d4_iff, hsum, a2Roots_iff]
  by_cases hab : α = β
  · refine ⟨fun h => absurd (mem_a2Roots h) (hnot hab), fun _ => ?_⟩
    subst hab
    exact commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self_d4 _ c d)
  obtain ⟨h1, h2⟩ := simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl)
    (isRoot_a2D4 hα) (isRoot_a2D4 hβ) (hne hab) (hne' hαβ)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hε, hF⟩ := h1 (hsum'.2 h)
    rw [hF K c d, a2D4_add]
    congr 1
    rcases hε with e | e <;> rw [e] <;> simp [CharTwo.neg_eq]
  · exact commutatorElement_eq_one_iff_commute.2 (h2 (fun hr => h (hsum'.1 hr)) K _
      (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩))

end SL3

section SL3Hom

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

section Order

variable {F : Type} [Field F]

theorem mem_commOrder_list_iff_d4
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := F)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ O.list α β ↔ p = (1, 1) ∧ α + β ∈ RA2 := by
  have hα' : α ∈ (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := F)).roots := by
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    exact hα
  have hβ' : β ∈ (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := F)).roots := by
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    exact hβ
  rw [O.mem_iff α hα' β hβ' hαβ p]
  constructor
  · intro hp
    obtain ⟨rfl, -⟩ := (CFSG.LieType.Steinberg.SL.mem_expPairs_iff (F := F) hα hβ hαβ p).1 hp
    obtain ⟨-, -, h⟩ := hp
    rw [CFSG.LieType.Steinberg.SL.Φ_roots] at h
    exact ⟨rfl, by simpa using h⟩
  · rintro ⟨rfl, h⟩
    refine ⟨one_pos, one_pos, ?_⟩
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    simpa using h

theorem commOrder_list_eq_singleton_d4
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := F)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (h : α + β ∈ RA2) :
    O.list α β = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup (O.nodup α β)
    (List.nodup_singleton _)).2 fun p => by
      rw [mem_commOrder_list_iff_d4 O hα hβ hαβ, List.mem_singleton, and_iff_left h])

theorem commOrder_list_eq_nil_d4
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := F)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (h : α + β ∉ RA2) :
    O.list α β = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun p hp =>
    h ((mem_commOrder_list_iff_d4 O hα hβ hαβ p).1 hp).2

end Order

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem commutatorFormula_a2D4
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := d4k K σ))) :
    CFSG.LieType.Steinberg.CommutatorFormula
      (fun γ (c : d4k K σ) => pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K)) O
      (CFSG.LieType.Steinberg.SL.commC (m := 2)) := by
  intro α hα β hβ hαβ c d
  have hc1 : ((CFSG.LieType.Steinberg.SL.commC (m := 2) α β (1, 1) : d4k K σ) : K) = 1 := by
    have h := CFSG.LieType.Steinberg.SL.commC_natAbs (m := 2) α β (1, 1)
    rcases Int.natAbs_eq (CFSG.LieType.Steinberg.SL.commC (m := 2) α β (1, 1)) with e | e <;>
      rw [e, h] <;> simp [CharTwo.neg_eq]
  have hα' : α ∈ RA2 := by rw [← CFSG.LieType.Steinberg.SL.Φ_roots (F := d4k K σ)]; exact hα
  have hβ' : β ∈ RA2 := by rw [← CFSG.LieType.Steinberg.SL.Φ_roots (F := d4k K σ)]; exact hβ
  obtain ⟨h1, h2⟩ := commutator_a2D4 hα' hβ' hαβ (c : K) (d : K)
  by_cases h : α + β ∈ RA2
  · rw [commOrder_list_eq_singleton_d4 O hα' hβ' hαβ h]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
      pow_one]
    rw [h1 h, Subfield.coe_mul, Subfield.coe_mul, hc1, one_mul]
  · rw [commOrder_list_eq_nil_d4 O hα' hβ' hαβ h]
    simp only [List.map_nil, List.prod_nil]
    exact h2 h

variable [Finite K]

theorem exists_sl3_hom_d4 :
    ∃ φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) (d4k K σ) →* ModGL TwistTag.D4.tag K,
      ∀ γ ∈ RA2, ∀ c : d4k K σ, φ (CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) γ c) =
        pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K) := by
  have : Finite (d4k K σ) := Subtype.finite
  obtain ⟨⟨-, ⟨O⟩, -⟩, -, huniv, -⟩ :=
    CFSG.LieType.Steinberg.RankTwo.sl3_rankTwoPresentation (d4k K σ)
  obtain ⟨φ, hφ, -⟩ := huniv O (CFSG.LieType.Steinberg.SL.commC (m := 2))
    (CFSG.LieType.Steinberg.SL.commutatorFormula O) (ModGL TwistTag.D4.tag K)
    (fun γ (c : d4k K σ) => pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K))
    (fun γ _ c d => by rw [Subfield.coe_add]; exact pinnedX_add _ _ _ _ _)
    (commutatorFormula_a2D4 σ O)
  exact ⟨φ, hφ⟩

theorem a2D4_x₂ : a2D4 ![1, 0] = trialityRoot 1 := by funext i; fin_cases i <;> rfl
theorem a2D4_x₅ : a2D4 ![0, 1] = trialityRoot 4 := by funext i; fin_cases i <;> rfl
theorem a2D4_x₆ : a2D4 ![1, 1] = trialityRoot 5 := by funext i; fin_cases i <;> rfl
theorem a2D4_y₂ : a2D4 ![-1, 0] = -trialityRoot 1 := by funext i; fin_cases i <;> rfl
theorem a2D4_y₅ : a2D4 ![0, -1] = -trialityRoot 4 := by funext i; fin_cases i <;> rfl
theorem a2D4_y₆ : a2D4 ![-1, -1] = -trialityRoot 5 := by funext i; fin_cases i <;> rfl

omit [CharP K 2] [Finite K] in
theorem pinnedX_a2D4_mem
    {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) (c : d4k K σ) :
    pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K) ∈ d4Lz K σ := by
  rcases mem_rootsA2_d4.1 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a2D4_x₂]
    exact subset_closure (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c, rfl⟩)))))
  · rw [a2D4_x₅]
    exact subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩))))
  · rw [a2D4_x₆]
    exact subset_closure (Or.inl (Or.inr ⟨c, rfl⟩))
  · rw [a2D4_y₂]
    exact subset_closure (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩)))))
  · rw [a2D4_y₅]
    exact subset_closure (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩)))
  · rw [a2D4_y₆]
    exact subset_closure (Or.inr ⟨c, rfl⟩)

omit [CharP K 2] in
theorem range_sl3_hom_d4
    {φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) (d4k K σ) →* ModGL TwistTag.D4.tag K}
    (hφ : ∀ γ ∈ RA2, ∀ c : d4k K σ, φ (CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) γ c) =
      pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K)) : φ.range = d4Lz K σ := by
  have : Finite (d4k K σ) := Subtype.finite
  obtain ⟨⟨hpar, -⟩, hgen, -⟩ :=
    CFSG.LieType.Steinberg.RankTwo.sl3_rankTwoPresentation.{0} (d4k K σ)
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    refine (closure_le _).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_iUnion] at hg
    obtain ⟨γ, hγ, hgγ⟩ := hg
    obtain ⟨c, rfl⟩ := ((hpar γ hγ).1 g).1 hgγ
    rw [SetLike.mem_coe, hφ γ hγ c]
    exact pinnedX_a2D4_mem σ hγ c
  · have key : ∀ γ ∈ RA2, ∀ c : d4k K σ, pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K) ∈ φ.range :=
      fun γ hγ c => ⟨_, hφ γ hγ c⟩
    refine (closure_le _).2 ?_
    rintro _ (((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
    · change pinnedX TwistTag.D4.tag K (trialityRoot 1) (x : K) ∈ φ.range
      rw [← a2D4_x₂]
      exact key _ (mem_rootsA2_d4.2 (by decide)) x
    · change pinnedX TwistTag.D4.tag K (-trialityRoot 1) (x : K) ∈ φ.range
      rw [← a2D4_y₂]
      exact key _ (mem_rootsA2_d4.2 (by decide)) x
    · change pinnedX TwistTag.D4.tag K (trialityRoot 4) (x : K) ∈ φ.range
      rw [← a2D4_x₅]
      exact key _ (mem_rootsA2_d4.2 (by decide)) x
    · change pinnedX TwistTag.D4.tag K (-trialityRoot 4) (x : K) ∈ φ.range
      rw [← a2D4_y₅]
      exact key _ (mem_rootsA2_d4.2 (by decide)) x
    · change pinnedX TwistTag.D4.tag K (trialityRoot 5) (x : K) ∈ φ.range
      rw [← a2D4_x₆]
      exact key _ (mem_rootsA2_d4.2 (by decide)) x
    · change pinnedX TwistTag.D4.tag K (-trialityRoot 5) (x : K) ∈ φ.range
      rw [← a2D4_y₆]
      exact key _ (mem_rootsA2_d4.2 (by decide)) x

end SL3Hom

section SL3Quot

theorem sl3_quot_facts_d4 {F : Type} [Field F] [Finite F] {L : Type} [Group L]
    (ψ : Matrix.SpecialLinearGroup (Fin (2 + 1)) F →* L) (hψ : Function.Surjective ψ)
    (hψ1 : ∃ g, ψ g ≠ 1) (hodd : Odd (Nat.card Fˣ)) :
    commutator L = ⊤ ∧ CFSG.Open.IsQuasisimple L ∧ Odd (Nat.card (center L)) ∧
      Nonempty (L ⧸ center L ≃* StatedProj (StatedSL 3 F)) := by
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hψ1
  have hcomm : commutator L = ⊤ := by
    rw [commutator_def, ← MonoidHom.range_eq_top.2 hψ, MonoidHom.range_eq_map, ← map_commutator,
      ← commutator_def, hq.1.commutator_eq_top]
  let e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hψ hker
  have := hq.2.1
  have hcen : (center (Matrix.SpecialLinearGroup (Fin (2 + 1)) F)).map ψ = center L := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hq.1 ψ hψ hker,
      map_comap_eq_self_of_surjective hψ]
  refine ⟨hcomm, ⟨hcomm, e.symm.isSimpleGroup⟩, ?_, ⟨e.symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (2 + 1) F)⟩⟩
  refine Odd.of_dvd_nat hodd ?_
  rw [← hcen]
  refine (card_map_dvd _ ψ).trans ?_
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (⟨0, by decide⟩ : Fin (2 + 1))).toEquiv]
  exact card_subgroup_dvd_card _

end SL3Quot

section Words

open CFSG.ComponentClassification.UnbalancedCatalog

abbrev d4o0 : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

abbrev d4o1 : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩

@[expose] def d4RelWord (ω : List (Fin TwistTag.D4.foldedTag.rank)) : WeylGroup TwistTag.D4.tag :=
  (ω.map fun i => TwistTag.D4.orbitReflection i).prod

theorem d4RelWord_mem
    (ω : List (Fin TwistTag.D4.foldedTag.rank)) :
    d4RelWord ω ∈ relWeylTwist TwistTag.D4 := by
  induction ω with
  | nil => exact one_mem _
  | cons i ω ih =>
    rw [d4RelWord, List.map_cons, List.prod_cons]
    exact mul_mem (TwistTag.D4.orbitReflection_mem i) ih

theorem canonicalRep_d4RelWord {K : Type} [Field K] [CharP K 2]
    (ω : List (Fin TwistTag.D4.foldedTag.rank)) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (d4RelWord ω) =
      (ω.map fun i => canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection i)).prod := by
  induction ω with
  | nil => exact canonicalRep_one (coxeterSystem TwistTag.D4.tag) K
  | cons i ω ih =>
    rw [d4RelWord, List.map_cons, List.prod_cons, canonicalRep_mul_d4, ← d4RelWord, ih,
      List.map_cons, List.prod_cons]

@[expose] def d4Words : List (List (Fin TwistTag.D4.foldedTag.rank)) :=
  [[], [d4o0], [d4o1], [d4o0, d4o1], [d4o1, d4o0], [d4o0, d4o1, d4o0], [d4o1, d4o0, d4o1], [d4o1,
      d4o0, d4o1, d4o0], [d4o0, d4o1, d4o0, d4o1], [d4o0, d4o1, d4o0, d4o1, d4o0],
    [d4o1, d4o0, d4o1, d4o0, d4o1], [d4o0, d4o1, d4o0, d4o1, d4o0, d4o1]]

theorem exists_d4Words
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) :
    ∃ ω ∈ d4Words, w = d4RelWord ω := by
  set W : WeylGroup .G2 := foldedWeylEquiv TwistTag.D4 ⟨w, hw⟩ with hW
  have key : ∀ ω : List (Fin TwistTag.D4.foldedTag.rank),
      TwistTag.D4.foldMap (W • g2a) = d4RelWord ω • TwistTag.D4.foldMap g2a →
      TwistTag.D4.foldMap (W • g2r) = d4RelWord ω • TwistTag.D4.foldMap g2r →
        w = d4RelWord ω := by
    intro ω ha hr
    set W' : WeylGroup .G2 := foldedWeylEquiv TwistTag.D4 ⟨d4RelWord ω, d4RelWord_mem ω⟩
      with hW'
    have e : ∀ v : Fin Tag.G2.rank → ℤ,
        d4RelWord ω • TwistTag.D4.foldMap v = TwistTag.D4.foldMap (W' • v) := fun v =>
      smul_foldMap_foldedWeylEquiv (t := TwistTag.D4) ⟨d4RelWord ω, d4RelWord_mem ω⟩ v
    have ha' : W • g2a = W' • g2a := TwistTag.D4.foldMap_injective (ha.trans (e _))
    have hr' : W • g2r = W' • g2r := TwistTag.D4.foldMap_injective (hr.trans (e _))
    have h := eq_one_of_smul (w := W'⁻¹ * W) (by rw [mul_smul, ha', inv_smul_smul])
      (by rw [mul_smul, hr', inv_smul_smul])
    have h1 : foldedWeylEquiv TwistTag.D4 ⟨w, hw⟩ =
        foldedWeylEquiv TwistTag.D4 ⟨d4RelWord ω, d4RelWord_mem ω⟩ :=
      (inv_mul_eq_one.1 h).symm
    exact congrArg Subtype.val ((foldedWeylEquiv TwistTag.D4).injective h1)
  rcases g2_weyl_cases W with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩
  · exact ⟨[], by simp [d4Words], key [] (by rw [ha]; simp [d4RelWord])
      (by rw [hr]; simp [d4RelWord])⟩
  · refine ⟨[d4o0], by simp [d4Words], key [d4o0] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o1], by simp [d4Words], key [d4o1] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o0, d4o1], by simp [d4Words], key [d4o0, d4o1] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o1, d4o0], by simp [d4Words], key [d4o1, d4o0] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o0, d4o1, d4o0], by simp [d4Words], key [d4o0, d4o1, d4o0] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o1, d4o0, d4o1], by simp [d4Words], key [d4o1, d4o0, d4o1] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o1, d4o0, d4o1, d4o0], by simp [d4Words], key [d4o1, d4o0, d4o1, d4o0] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o0, d4o1, d4o0, d4o1], by simp [d4Words], key [d4o0, d4o1, d4o0, d4o1] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o0, d4o1, d4o0, d4o1, d4o0], by simp [d4Words], key [d4o0, d4o1, d4o0, d4o1,
      d4o0] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o1, d4o0, d4o1, d4o0, d4o1], by simp [d4Words], key [d4o1, d4o0, d4o1, d4o0,
      d4o1] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
  · refine ⟨[d4o0, d4o1, d4o0, d4o1, d4o0, d4o1], by simp [d4Words], key [d4o0, d4o1, d4o0, d4o1,
      d4o0, d4o1] ?_ ?_⟩
    · rw [ha]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel
    · rw [hr]
      simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_smul, TwistTag.orbitReflection_smul]
      decide +kernel

end Words

section CentW0

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))

omit [CharP K 2] in
theorem d4x₂_mem_d4Lz {c : K}
    (hc : σ c = c) : d4x₂ K c ∈ d4Lz K σ :=
  subset_closure (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨c, hc⟩, rfl⟩)))))

omit [CharP K 2] in
theorem d4y₂_mem_d4Lz {c : K}
    (hc : σ c = c) : d4y₂ K c ∈ d4Lz K σ :=
  subset_closure (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨c, hc⟩, rfl⟩)))))

omit [CharP K 2] in
theorem d4x₅_mem_d4Lz {c : K}
    (hc : σ c = c) : d4x₅ K c ∈ d4Lz K σ :=
  subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨c, hc⟩, rfl⟩))))

omit [CharP K 2] in
theorem d4y₅_mem_d4Lz {c : K}
    (hc : σ c = c) : d4y₅ K c ∈ d4Lz K σ :=
  subset_closure (Or.inl (Or.inl (Or.inr ⟨⟨c, hc⟩, rfl⟩)))

omit [CharP K 2] in
theorem d4x₆_mem_d4Lz {c : K}
    (hc : σ c = c) : d4x₆ K c ∈ d4Lz K σ :=
  subset_closure (Or.inl (Or.inr ⟨⟨c, hc⟩, rfl⟩))

omit [CharP K 2] in
theorem d4y₆_mem_d4Lz {c : K}
    (hc : σ c = c) : d4y₆ K c ∈ d4Lz K σ :=
  subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem trialityMiddleRep_eq_d4 :
    trialityMiddleRep K = d4x₂ K 1 * d4y₂ K 1 * d4x₂ K 1 := by
  obtain ⟨-, -, -, -, -, hN, -⟩ := exceptional_fixed_rank_one_central_image TwistTag.D4 K
    (RingEquiv.refl K).toRingHom ⟨1, by decide⟩
  rw [trialityMiddleRep, ← hN, orbitN, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_orbitX_one_d4 (RingEquiv.refl K), coe_orbitY_one_d4 (RingEquiv.refl K)]
  simp only [inv_one, Units.val_one, OneMemClass.coe_one, CharTwo.neg_eq]

theorem trialityMiddleRep_mem_d4Lz :
    trialityMiddleRep K ∈ d4Lz K σ := by
  rw [trialityMiddleRep_eq_d4]
  exact mul_mem (mul_mem (d4x₂_mem_d4Lz σ (map_one σ)) (d4y₂_mem_d4Lz σ (map_one σ)))
    (d4x₂_mem_d4Lz σ (map_one σ))

theorem trialityOuterRep_conj_mem_d4Lz :
    trialityOuterRep K * trialityMiddleRep K * trialityOuterRep K ∈ d4Lz K σ := by
  have hinv : trialityOuterRep K = (trialityOuterRep K)⁻¹ :=
    (canonicalRep_orbitReflection_inv_d4 (K := K) _).symm
  rw [show trialityOuterRep K * trialityMiddleRep K * trialityOuterRep K =
      trialityOuterRep K * trialityMiddleRep K * (trialityOuterRep K)⁻¹ by rw [← hinv],
    trialityMiddleRep_eq_d4,
    show trialityOuterRep K * (d4x₂ K 1 * d4y₂ K 1 * d4x₂ K 1) * (trialityOuterRep K)⁻¹ =
      (trialityOuterRep K * d4x₂ K 1 * (trialityOuterRep K)⁻¹) *
        (trialityOuterRep K * d4y₂ K 1 * (trialityOuterRep K)⁻¹) *
          (trialityOuterRep K * d4x₂ K 1 * (trialityOuterRep K)⁻¹) by group,
    trialityOuterRep_conj_d4x₂, trialityOuterRep_conj_d4y₂]
  exact mul_mem (mul_mem (d4x₅_mem_d4Lz σ (map_one σ)) (d4y₅_mem_d4Lz σ (map_one σ)))
    (d4x₅_mem_d4Lz σ (map_one σ))

theorem canonicalRep_mem_d4Lz_of_commute_ho
    {μ : Kˣ} (hμ : μ ≠ 1)
    (hN : (μ : K) * σ μ * σ (σ μ) = 1) {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4)
    (hc : trialityOuterTorus K σ μ * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * trialityOuterTorus K σ μ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈ d4Lz K σ := by
  have hN' : μ * σu μ * σu (σu μ) = 1 := Units.ext hN
  have hN'' : μ * (σu μ * σu (σu μ)) = 1 := by rw [← mul_assoc]; exact hN'
  have hinv : σu μ ^ 2 * σu (σu μ) ^ 2 = μ⁻¹ ^ 2 := by
    rw [← mul_pow, eq_inv_of_mul_eq_one_right hN'']
  obtain ⟨ω, hω, rfl⟩ := exists_d4Words hw
  rw [trialityOuterTorus_eq_rootDiagUnit] at hc
  have hstab := (conj_canonicalRep_eq_iff _ _).1 (by rw [hc, mul_inv_cancel_right])
  have h0 := hstab (Pi.single ⟨0, by decide⟩ 1)
  have he0 : rootChar (d4Tuple (μ ^ 2) (σu μ ^ 2) (μ * σu μ * σu (σu μ))⁻¹ (σu (σu μ) ^ 2))
      (Pi.single ⟨0, by decide⟩ 1) = μ ^ 2 := by
    rw [rootChar_d4Tuple _ _ _ _ 1 0 0 0 (by funext i; fin_cases i <;> rfl)]
    simp
  rw [he0] at h0
  have key : ∀ ω : List (Fin TwistTag.D4.foldedTag.rank),
      rootChar (d4Tuple (μ ^ 2) (σu μ ^ 2) (μ * σu μ * σu (σu μ))⁻¹ (σu (σu μ) ^ 2))
        (d4RelWord ω • Pi.single ⟨0, by decide⟩ 1) = (μ ^ 2)⁻¹ →
      rootChar (d4Tuple (μ ^ 2) (σu μ ^ 2) (μ * σu μ * σu (σu μ))⁻¹ (σu (σu μ) ^ 2))
        (d4RelWord ω • Pi.single ⟨0, by decide⟩ 1) = μ ^ 2 → False := by
    intro ω h1 h2
    have h4 : μ ^ (4 : ℤ) = 1 := by
      have h3 : (μ ^ 2)⁻¹ = μ ^ 2 := h1.symm.trans h2
      have h5 : μ ^ 2 * μ ^ 2 = 1 := by
        calc μ ^ 2 * μ ^ 2 = μ ^ 2 * (μ ^ 2)⁻¹ := by rw [h3]
          _ = 1 := mul_inv_cancel _
      rw [← h5, show (4 : ℤ) = ((2 + 2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_add]
    exact hμ (eq_one_of_zpow_d4 (n := 4) (by norm_num) h4)
  have hv₁ : rootChar (d4Tuple (μ ^ 2) (σu μ ^ 2) (μ * σu μ * σu (σu μ))⁻¹ (σu (σu μ) ^ 2))
      ![-1, 0, 0, 0] = (μ ^ 2)⁻¹ := by
    rw [rootChar_d4Tuple _ _ _ _ (-1) 0 0 0 rfl]
    simp
  have hv₂ : rootChar (d4Tuple (μ ^ 2) (σu μ ^ 2) (μ * σu μ * σu (σu μ))⁻¹ (σu (σu μ) ^ 2))
      ![0, 1, 1, 1] = (μ ^ 2)⁻¹ := by
    rw [rootChar_d4Tuple _ _ _ _ 0 1 1 1 rfl, hN']
    simp only [zpow_zero, zpow_one, one_mul, inv_one, mul_one]
    rw [hinv, inv_pow]
  have hv₃ : rootChar (d4Tuple (μ ^ 2) (σu μ ^ 2) (μ * σu μ * σu (σu μ))⁻¹ (σu (σu μ) ^ 2))
      ![-1, 0, -1, 0] = (μ ^ 2)⁻¹ := by
    rw [rootChar_d4Tuple _ _ _ _ (-1) 0 (-1) 0 rfl, hN']
    simp
  have hA : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection d4o0) *
      canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection d4o1) *
        canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection d4o0) ∈
          d4Lz K σ := trialityOuterRep_conj_mem_d4Lz σ
  have hB : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection d4o1) ∈
      d4Lz K σ := trialityMiddleRep_mem_d4Lz σ
  simp only [d4Words, List.mem_cons, List.not_mem_nil, or_false] at hω
  rcases hω with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [canonicalRep_d4RelWord]
    exact one_mem _
  · exfalso
    refine key [d4o0] ?_ h0
    rw [show d4RelWord [d4o0] • (Pi.single ⟨0, by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      ![-1, 0, 0, 0] by
        simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, TwistTag.orbitReflection_smul]
        exact List.ofFn_injective (by decide +kernel)]
    exact hv₁
  · rw [canonicalRep_d4RelWord]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact hB
  · exfalso
    refine key [d4o0, d4o1] ?_ h0
    rw [show d4RelWord [d4o0, d4o1] • (Pi.single ⟨0, by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      ![0, 1, 1, 1] by
        simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, mul_smul, TwistTag.orbitReflection_smul]
        exact List.ofFn_injective (by decide +kernel)]
    exact hv₂
  · exfalso
    refine key [d4o1, d4o0] ?_ h0
    rw [show d4RelWord [d4o1, d4o0] • (Pi.single ⟨0, by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      ![-1, 0, -1, 0] by
        simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, mul_smul, TwistTag.orbitReflection_smul]
        exact List.ofFn_injective (by decide +kernel)]
    exact hv₃
  · rw [canonicalRep_d4RelWord]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (by simpa only [mul_assoc] using hA)
  · exfalso
    refine key [d4o1, d4o0, d4o1] ?_ h0
    rw [show d4RelWord [d4o1, d4o0, d4o1] • (Pi.single ⟨0,
        by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      ![0, 1, 1, 1] by
        simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, mul_smul, TwistTag.orbitReflection_smul]
        exact List.ofFn_injective (by decide +kernel)]
    exact hv₂
  · rw [canonicalRep_d4RelWord]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (by simpa only [mul_assoc] using mul_mem hB hA)
  · rw [canonicalRep_d4RelWord]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (by simpa only [mul_assoc] using mul_mem hA hB)
  · exfalso
    refine key [d4o0, d4o1, d4o0, d4o1, d4o0] ?_ h0
    rw [show d4RelWord [d4o0, d4o1, d4o0, d4o1, d4o0] • (Pi.single ⟨0,
        by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      ![-1, 0, -1, 0] by
        simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, mul_smul, TwistTag.orbitReflection_smul]
        exact List.ofFn_injective (by decide +kernel)]
    exact hv₃
  · rw [canonicalRep_d4RelWord]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (by simpa only [mul_assoc] using mul_mem (mul_mem hB hA) hB)
  · exfalso
    refine key [d4o0, d4o1, d4o0, d4o1, d4o0, d4o1] ?_ h0
    rw [show d4RelWord [d4o0, d4o1, d4o0, d4o1, d4o0, d4o1] • (Pi.single ⟨0,
        by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      ![-1, 0, 0, 0] by
        simp only [d4RelWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, mul_smul, TwistTag.orbitReflection_smul]
        exact List.ofFn_injective (by decide +kernel)]
    exact hv₁

end CentW0

section CentZ

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem mem_d4Lz_of_commute_ho
    [Finite K] (hσ3 : σ.toRingHom ^ 3 = 1)
    (hσ : ∀ c, σ (σ (σ c)) = c) {μ : Kˣ} (hμ : μ ≠ 1) (hN : (μ : K) * σ μ * σ (σ μ) = 1)
    {u : ModGL TwistTag.D4.tag K} (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hc : trialityOuterTorus K σ μ * u = u * trialityOuterTorus K σ μ) : u ∈ d4Lz K σ := by
  obtain ⟨a, b, c, d, e, f, hb, he, hf, rfl⟩ := exists_d4coord σ hσ3 hu
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hμ1 : (μ : K) ≠ 1 := fun h => hμ (Units.ext h)
  have hsq : (μ : K) ^ 2 ≠ 1 := fun h => hμ1 (CharTwo.sq_injective
    (show (μ : K) ^ 2 = 1 ^ 2 by rw [h, one_pow]))
  have hsq' : (σ μ : K) ^ 2 * σ (σ (μ : K)) ^ 2 * ((μ : K) * σ μ * σ (σ μ))⁻¹ ≠ 1 := by
    rw [hN, inv_one, mul_one, ← mul_pow]
    have h1 : σ (μ : K) * σ (σ (μ : K)) = (μ : K)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm, ← mul_assoc]; exact hN)
    rw [h1, inv_pow]
    exact fun h => hsq (inv_eq_one.1 h)
  have hconj : trialityOuterTorus K σ μ * (d4x₁ K σ a * d4v K σ b c d e f) *
      (trialityOuterTorus K σ μ)⁻¹ =
        d4x₁ K σ ((μ : K) ^ 2 * a) * d4v K σ (((μ : K) * σ μ * σ (σ μ))⁻¹ * b)
          ((μ : K) ^ 2 * ((μ : K) * σ μ * σ (σ μ))⁻¹ * c)
          (σ μ ^ 2 * σ (σ μ) ^ 2 * ((μ : K) * σ μ * σ (σ μ))⁻¹ * d)
          (((μ : K) * σ μ * σ (σ μ)) * e) f := by
    rw [show trialityOuterTorus K σ μ * (d4x₁ K σ a * d4v K σ b c d e f) *
        (trialityOuterTorus K σ μ)⁻¹ =
          (trialityOuterTorus K σ μ * d4x₁ K σ a * (trialityOuterTorus K σ μ)⁻¹) *
            (trialityOuterTorus K σ μ * d4v K σ b c d e f * (trialityOuterTorus K σ μ)⁻¹) by
        group, ho_conj_d4x₁ σ, ho_conj_d4v σ hσ]
  have hfix : trialityOuterTorus K σ μ * (d4x₁ K σ a * d4v K σ b c d e f) *
      (trialityOuterTorus K σ μ)⁻¹ = d4x₁ K σ a * d4v K σ b c d e f := by
    rw [hc, mul_inv_cancel_right]
  obtain ⟨ha, -, hc', hd, -, -⟩ := d4coord_injective σ (hconj.symm.trans hfix)
  rw [hN, inv_one, mul_one] at hc'
  rw [eq_zero_of_mul_eq_self_d4 hsq ha, eq_zero_of_mul_eq_self_d4 hsq hc',
    eq_zero_of_mul_eq_self_d4 hsq' hd, d4x₁_zero, one_mul, d4v, d4x₃_zero, d4x₄_zero, mul_one,
    mul_one]
  exact mul_mem (mul_mem (d4x₂_mem_d4Lz σ hb) (d4x₅_mem_d4Lz σ he)) (d4x₆_mem_d4Lz σ hf)

theorem exists_inv_mul_mem_d4Lz
    [Finite K] (hσ3 : σ.toRingHom ^ 3 = 1)
    (hσ' : ∀ c, σ (σ (σ c)) = c) (hσ : σ ^ 3 = 1) {μ : Kˣ} (hμ : μ ≠ 1)
    (hN : (μ : K) * σ μ * σ (σ μ) = 1) {g : ModGL TwistTag.D4.tag K} (hg : g ∈ d4C K σ)
    (hc : trialityOuterTorus K σ μ * g = g * trialityOuterTorus K σ μ) :
    ∃ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, h⁻¹ * g ∈ d4Lz K σ := by
  have hs : trialityOuterTorus K σ μ ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    rw [ho_eq_d4]
    exact trialityTorusHom_mem_d4H σ hσ _
  obtain ⟨w, hw, h, hh, u₀, hu₀, u, hu, rfl, h1, h2, h3⟩ :=
    exists_bruhat_of_commute_torus_d4 σ hs hg hc
  refine ⟨h, hh, ?_⟩
  rw [show h⁻¹ * (h * u₀ * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u) =
    u₀ * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u by group]
  exact mul_mem (mul_mem (mem_d4Lz_of_commute_ho σ hσ3 hσ' hμ hN hu₀ h1)
    (canonicalRep_mem_d4Lz_of_commute_ho σ hμ hN hw h3))
    (mem_d4Lz_of_commute_ho σ hσ3 hσ' hμ hN hu h2)

end CentZ

section LeviDataZ

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit [Finite K] in
theorem d4Lz_le :
    d4Lz K σ ≤ d4C K σ :=
  (closure_le _).2 (by
    rintro _ (((((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩)
    · exact (d4x_long_mem σ c.2).1
    · exact (d4y_long_mem σ c.2).1
    · exact (d4x_long_mem σ c.2).2.1
    · exact (d4y_long_mem σ c.2).2.1
    · exact (d4x_long_mem σ c.2).2.2
    · exact (d4y_long_mem σ c.2).2.2)

omit [Finite K] [CharP K 2] in
theorem d4Mr_le
    (hσ : σ ^ 3 = 1) : d4Mr K σ ≤ d4C K σ := by
  rw [d4Mr, orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ((triality_all_characteristic_faithful_torus_coordinates K σ hσ).2.2.2.2.1
    ⟨0, by decide⟩).1

omit [CharP K 2] in
theorem d4Mr_commutator
    (h4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) :
    ⁅d4Mr K σ, d4Mr K σ⁆ = d4Mr K σ := by
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) := Subtype.finite
  rw [d4Mr, orbitRankOneGroup, ← orbitRankOneHom_range, MonoidHom.range_eq_map, ← map_commutator,
    ← commutator_def, sl2_commutator_d4 h4]

omit [Finite K] in
theorem d4Mr_commute_d4Zz :
    ∀ x ∈ d4Mr K σ, ∀ z ∈ d4Zz K σ, z * x = x * z := by
  have hgen : ∀ x ∈ (Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ =>
      (orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K)) ∪
      Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ =>
        (orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K))),
      ∀ c : K, d4x₆ K c * x = x * d4x₆ K c := by
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩) c <;> dsimp only
    · rw [coe_orbitX_zero_d4]
      exact (commute_d4x₁_d4x₆ σ (b : K) c).symm.eq
    · rw [coe_orbitY_zero_d4, ← trialityOuterRep_conj_d4x₁, ← trialityOuterRep_conj_d4x₆ (K := K) c]
      have h := (commute_d4x₁_d4x₆ σ (b : K) c).symm.eq
      calc trialityOuterRep K * d4x₆ K c * (trialityOuterRep K)⁻¹ *
            (trialityOuterRep K * d4x₁ K σ (b : K) * (trialityOuterRep K)⁻¹) =
          trialityOuterRep K * (d4x₆ K c * d4x₁ K σ (b : K)) * (trialityOuterRep K)⁻¹ := by
            group
        _ = trialityOuterRep K * (d4x₁ K σ (b : K) * d4x₆ K c) * (trialityOuterRep K)⁻¹ := by
            rw [h]
        _ = _ := by group
  intro x hx z hz
  obtain ⟨c, -, rfl⟩ := (mem_d4Zz σ).1 hz
  have hle : d4Mr K σ ≤ centralizer {d4x₆ K c} := (closure_le _).2 fun x hx => by
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (hgen x hx c).symm
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

omit [Finite K] [CharP K 2] in
theorem ho_mem_d4Mr
    (hσ : σ ^ 3 = 1) (a : Kˣ) : trialityOuterTorus K σ a ∈ d4Mr K σ := by
  rw [ho_eq_d4, trialityTorusHom_eq_orbitH hσ,
    show trialityMiddleParam (1 : (trialityFixedField K σ.toRingHom)ˣ) = 1 from Units.ext rfl,
    orbitH_one', mul_one, ← orbitRankOneHom_HSL, d4Mr, orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ⟨_, rfl⟩

omit [Finite K] [CharP K 2] in
theorem d4W0_le_d4Mr
    (hσ : σ ^ 3 = 1) : d4W0 K σ ≤ d4Mr K σ :=
  (closure_le _).2 (by rintro _ ⟨a, -, rfl⟩; exact ho_mem_d4Mr σ hσ a)

omit [Finite K] [CharP K 2] in
theorem d4W0_le_d4H
    (hσ : σ ^ 3 = 1) : d4W0 K σ ≤ d4H K σ :=
  (closure_le _).2 (by
    rintro _ ⟨a, -, rfl⟩
    rw [ho_eq_d4]
    exact trialityTorusHom_mem_d4H σ hσ _)

omit [Finite K] [CharP K 2] in
theorem d4H_le :
    d4H K σ ≤ d4C K σ := inf_le_right

omit [Finite K] [CharP K 2] in
theorem d4Lz_le_centralizer_d4W0 :
    d4Lz K σ ≤ centralizer (d4W0 K σ : Set (ModGL TwistTag.D4.tag K)) := by
  rw [d4W0, centralizer_closure]
  refine (closure_le _).2 fun x hx => ?_
  rw [SetLike.mem_coe, mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have ha' : ((a : K) * σ a * σ (σ a)) = 1 := ha
  have key : ∀ y : ModGL TwistTag.D4.tag K,
      trialityOuterTorus K σ a * y * (trialityOuterTorus K σ a)⁻¹ = y →
        trialityOuterTorus K σ a * y = y * trialityOuterTorus K σ a :=
    fun y hy => mul_inv_eq_iff_eq_mul.1 hy
  rcases hx with (((((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) <;>
    refine key _ ?_ <;> dsimp only
  · rw [ho_conj_d4x₂, ha', inv_one, one_mul]
  · rw [ho_conj_d4y₂, ha', inv_one, inv_one, one_mul]
  · rw [ho_conj_d4x₅, ha', one_mul]
  · rw [ho_conj_d4y₅, ha', inv_one, one_mul]
  · rw [ho_conj_d4x₆]
  · rw [ho_conj_d4y₆]

omit [Finite K] [CharP K 2] in
theorem conj_mem_d4Lz_of_torus
    (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ d4Lz K σ) : trialityTorusHom σ p * x * (trialityTorusHom σ p)⁻¹ ∈ d4Lz K σ := by
  have hN : σ ((p.1 : K) * σ p.1 * σ (σ p.1)) = (p.1 : K) * σ p.1 * σ (σ p.1) :=
    (mem_trialityFixedField).1 (norm_mem_trialityFixedField hσ (p.1 : K))
  have hb : σ ((trialityFixedUnit K σ p.2 : Kˣ) : K) = ((trialityFixedUnit K σ p.2 : Kˣ) : K) :=
    sigma_trialityFixedUnit p.2
  have fm : ∀ {x y : K}, σ x = x → σ y = y → σ (x * y) = x * y := fun hx hy => by
    rw [map_mul, hx, hy]
  have fi : ∀ {x : K}, σ x = x → σ x⁻¹ = x⁻¹ := fun hx => by rw [map_inv₀, hx]
  have fp : ∀ {x : K}, σ x = x → σ (x ^ 2) = x ^ 2 := fun hx => by rw [map_pow, hx]
  have hle : d4Lz K σ ≤ (d4Lz K σ).comap (MulAut.conj (trialityTorusHom σ p)).toMonoidHom := by
    refine (closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      trialityTorusHom_apply_d4, mul_inv_rev,
      show trialityOuterTorus K σ p.1 * trialityMiddleTorus K σ p.2 * y *
        ((trialityMiddleTorus K σ p.2)⁻¹ * (trialityOuterTorus K σ p.1)⁻¹) =
          trialityOuterTorus K σ p.1 * (trialityMiddleTorus K σ p.2 * y *
            (trialityMiddleTorus K σ p.2)⁻¹) * (trialityOuterTorus K σ p.1)⁻¹ by group]
    rcases hy with (((((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) <;>
      dsimp only
    · rw [hm_conj_d4x₂, ho_conj_d4x₂]
      exact d4x₂_mem_d4Lz σ (fm (fi hN) (fm (fp hb) c.2))
    · rw [hm_conj_d4y₂, ho_conj_d4y₂]
      exact d4y₂_mem_d4Lz σ (fm (fi (fi hN)) (fm (fi (fp hb)) c.2))
    · rw [hm_conj_d4x₅, ho_conj_d4x₅]
      exact d4x₅_mem_d4Lz σ (fm hN (fm (fi hb) c.2))
    · rw [hm_conj_d4y₅, ho_conj_d4y₅]
      exact d4y₅_mem_d4Lz σ (fm (fi hN) (fm (fi (fi hb)) c.2))
    · rw [hm_conj_d4x₆, ho_conj_d4x₆]
      exact d4x₆_mem_d4Lz σ (fm hb c.2)
    · rw [hm_conj_d4y₆, ho_conj_d4y₆]
      exact d4y₆_mem_d4Lz σ (fm (fi hb) c.2)
  exact hle hx

theorem d4_leviData_z
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    Exc.LeviData ((d4Zz K σ).subgroupOf (d4C K σ)) ((d4Mr K σ).subgroupOf (d4C K σ))
        ((d4W0 K σ).subgroupOf (d4C K σ)) ((d4H K σ).subgroupOf (d4C K σ))
        ((d4Lz K σ).subgroupOf (d4C K σ)) ∧
      StatedClassicalModel (rankTwoQuot ((d4Lz K σ).subgroupOf (d4C K σ))) .PSL 3 2 m := by
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ3 := toRingHom_pow_three_d4 σ hσ3'
  have hσ := ringEquiv_cube_d4 σ hσ3'
  have hm1 : 1 ≤ m := by omega
  have hk : Nat.card (d4k K σ) = 2 ^ m := card_d4k_of_card σ hm1 hK hσq
  have hq4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ m := hq4
      _ ≤ (2 ^ m) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, ⟨eH, -⟩, hL1, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  have hK0 : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) = Nat.card K := by
    rw [hL1]
    exact Nat.card_congr Subfield.topEquiv.toEquiv
  have hodd2 : ∀ j : ℕ, 1 ≤ j → Odd (2 ^ j - 1) := fun j hj => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨2 ^ i - 1, ?_⟩
    rw [pow_succ]
    have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    omega
  have hkodd : Odd (Nat.card (d4k K σ)ˣ) := by
    rw [Nat.card_units, hk]
    exact hodd2 m hm1
  have hHodd : Odd (Nat.card (d4H K σ)) := by
    rw [← Nat.card_congr eH.toEquiv, Nat.card_prod, Nat.card_units, hK, ← pow_mul]
    exact (hodd2 _ (by omega)).mul hkodd
  obtain ⟨x, hx⟩ := exists_not_fixed_d4 σ hm1 hK hσq
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have hσx0 : σ x ≠ 0 := (map_ne_zero σ).2 hx0
  set μ : Kˣ := Units.mk0 (σ x * x⁻¹) (mul_ne_zero hσx0 (inv_ne_zero hx0)) with hμdef
  have hμ1 : μ ≠ 1 := by
    intro h
    have h1 : σ x * x⁻¹ = 1 := congrArg Units.val h
    exact hx (by field_simp at h1; exact h1)
  have hμN : (μ : K) * σ μ * σ (σ μ) = 1 := by
    simp only [hμdef, Units.val_mk0, map_mul, map_inv₀, hσ3' x]
    have hσσx0 : σ (σ x) ≠ 0 := (map_ne_zero σ).2 hσx0
    field_simp
  have hμW : trialityOuterTorus K σ μ ∈ d4W0 K σ := subset_closure ⟨μ, hμN, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_sl3_hom_d4 σ
  have hrange := range_sl3_hom_d4 σ hφ
  have hmem : ∀ g, φ g ∈ d4Lz K σ := fun g => hrange ▸ ⟨g, rfl⟩
  let ψ : Matrix.SpecialLinearGroup (Fin (2 + 1)) (d4k K σ) →*
      ↥((d4Lz K σ).subgroupOf (d4C K σ)) :=
    (φ.codRestrict (d4C K σ) fun g => d4Lz_le σ (hmem g)).codRestrict _
      fun g => mem_subgroupOf.2 (hmem g)
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨y, hyC⟩, hy⟩
    have hy' : y ∈ φ.range := hrange ▸ mem_subgroupOf.1 hy
    obtain ⟨g, rfl⟩ := hy'
    exact ⟨g, rfl⟩
  have hψ1 : ∃ g, ψ g ≠ 1 := by
    refine ⟨CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) ![1, 0] 1, fun h => ?_⟩
    have h1 : φ (CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) ![1, 0] 1) = 1 :=
      congrArg (fun y : ↥((d4Lz K σ).subgroupOf (d4C K σ)) => ((y : ↥(d4C K σ)) :
        ModGL TwistTag.D4.tag K)) h
    rw [hφ _ (mem_rootsA2_d4.2 (by decide)), ← pinnedX_zero TwistTag.D4.tag K (a2D4 ![1, 0])]
      at h1
    exact one_ne_zero (pinnedX_injective _ _ _ h1)
  obtain ⟨-, hqs, hZodd, ⟨eP⟩⟩ := sl3_quot_facts_d4 ψ hψ hψ1 hkodd
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hqs, hZodd, ?_⟩, ?_⟩
  ·
    exact Exc.commutator_subgroupOf_of_perfect (d4Mr_le σ hσ)
      (d4Mr_commutator σ (by rw [hK0]; exact hK4))
  ·
    intro y hy
    rw [mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (d4Mr_commute_d4Zz σ y (mem_subgroupOf.1 hy) z (mem_subgroupOf.1 hz))
  ·
    intro y hy
    exact mem_subgroupOf.2 (d4W0_le_d4Mr σ hσ (mem_subgroupOf.1 hy))
  ·
    intro h
    have hmem' : (⟨trialityOuterTorus K σ μ, d4H_le σ (d4W0_le_d4H σ hσ hμW)⟩ : ↥(d4C K σ)) ∈
        (d4W0 K σ).subgroupOf (d4C K σ) := mem_subgroupOf.2 hμW
    rw [h, mem_bot] at hmem'
    have h1 : trialityTorusHom σ (μ, 1) = trialityTorusHom σ 1 := by
      rw [map_one, ← ho_eq_d4]; exact congrArg Subtype.val hmem'
    exact hμ1 (Prod.mk.inj (trialityTorusHom_injective_all hσ h1)).1
  ·
    rw [Nat.card_congr (subgroupOfEquivOfLe ((d4W0_le_d4H σ hσ).trans (d4H_le σ))).toEquiv]
    exact Odd.of_dvd_nat hHodd (card_dvd_of_le (d4W0_le_d4H σ hσ))
  ·
    intro y hy
    exact mem_subgroupOf.2 (d4W0_le_d4H σ hσ (mem_subgroupOf.1 hy))
  ·
    intro a ha b hb
    obtain ⟨p, hp⟩ := exists_trialityTorusHom_eq_d4 σ hσ (mem_subgroupOf.1 ha)
    obtain ⟨p', hp'⟩ := exists_trialityTorusHom_eq_d4 σ hσ (mem_subgroupOf.1 hb)
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, ← hp, ← hp', ← map_mul, mul_comm]
  ·
    intro h hh
    obtain ⟨p, hp⟩ := exists_trialityTorusHom_eq_d4 σ hσ (mem_subgroupOf.1 hh)
    rw [mem_normalizer_iff]
    intro l
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hp]
    constructor
    · exact conj_mem_d4Lz_of_torus σ hσ p
    · intro hl
      have h1 := conj_mem_d4Lz_of_torus σ hσ p⁻¹ hl
      rwa [map_inv, inv_inv, show (trialityTorusHom σ p)⁻¹ * (trialityTorusHom σ p * (l :
        ModGL TwistTag.D4.tag K) * (trialityTorusHom σ p)⁻¹) * trialityTorusHom σ p = l by
          group] at h1
  ·
    intro l hl
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.1 (d4Lz_le_centralizer_d4W0 σ (mem_subgroupOf.1 hl))
      _ (mem_subgroupOf.1 hy))
  ·
    intro c hc
    have hq : (⟨trialityOuterTorus K σ μ, d4H_le σ (d4W0_le_d4H σ hσ hμW)⟩ : ↥(d4C K σ)) ∈
        (d4W0 K σ).subgroupOf (d4C K σ) := mem_subgroupOf.2 hμW
    have h1 := congrArg Subtype.val (mem_centralizer_iff.1 hc _ hq)
    simp only [Subgroup.coe_mul] at h1
    obtain ⟨h, hh, hhL⟩ := exists_inv_mul_mem_d4Lz σ hσ3 hσ3' hσ hμ1 hμN c.2 h1
    refine ⟨⟨h, d4H_le σ hh⟩, mem_subgroupOf.2 hh, mem_subgroupOf.2 ?_⟩
    simpa using hhL
  ·
    intro z hz
    obtain ⟨c, hc, hzc⟩ := (mem_d4Zz σ).1 (mem_subgroupOf.1 hz)
    exact mem_subgroupOf.2 (hzc ▸ d4x₆_mem_d4Lz σ hc)
  ·
    refine ⟨⟨Nat.prime_two, hm1, by norm_num, ?_, ?_⟩, d4k K σ, inferInstance,
      Subtype.finite, hk, ⟨eP⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega

end LeviDataZ

end CFSG.ComponentClassification.RankTwoExceptional.D4
