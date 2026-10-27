module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Enum
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Unc25G2.M2x CFSG.EvenSporadicStandard.M23Std

@[expose] def InvClass (F : Subgroup (Carrier .M22)) (c f : ℕ) : Set ↥(autNorm F) :=
  {μ | μ * μ = 1 ∧ μ ≠ 1 ∧ Nat.card (centralizer ({μ} : Set ↥(autNorm F))) = c ∧
    Nat.card {y : Carrier .M22 // y ∈ F ∧ (μ : MulAut (Carrier .M22)) y = y} = f}

theorem nData_pinned {F1 : Subgroup (Carrier .M22)} (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    NData (⊤ : Subgroup (Carrier .M22)) F1 := by
  have hS := (Certificates.certificate24781).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M22.exists_at hP sylowS_index_odd
  obtain ⟨F1', F2, -, hN, hF'⟩ := m22_fusionData_pinned h2E
  have : F1 = F1' := by
    ext x
    rw [hF, hF']
  exact this ▸ hN

theorem isInv_autTab (μ : MulAut (Carrier .M22)) :
    isInv (autTab μ) = true ↔ μ * μ = 1 ∧ μ ≠ 1 := by
  simp only [isInv, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨autTab_injective (by rw [autTab_mul, autTab_one]; exact h2),
      fun h => h1 (by rw [h, autTab_one])⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h2 (autTab_injective (h.trans autTab_one.symm)), ?_⟩
    rw [← autTab_mul, h1, autTab_one]

variable {F1 : Subgroup (Carrier .M22)}
  (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)

include hF

theorem card_centralizer_eq (μ : ↥(autNorm F1)) :
    Nat.card (centralizer ({μ} : Set ↥(autNorm F1))) = centN tabL (autTab μ) := by
  obtain ⟨-, -, ⟨-, hnd⟩, -⟩ := censusCheck_spec Certificates.certificate24790
  refine (isTabsOf_N hF (nData_pinned hF)).card_subtype hnd
    (fun ν : ↥(autNorm F1) => ν ∈ centralizer ({μ} : Set ↥(autNorm F1)))
    (fun l => commF l (autTab μ)) fun ν => ?_
  show _ ↔ commF (autTab ν) (autTab μ) = true
  rw [Subgroup.mem_centralizer_singleton_iff, commF_iff]
  constructor
  · intro h
    have := congrArg (fun x : ↥(autNorm F1) => autTab (x : MulAut (Carrier .M22))) h
    simpa only [Subgroup.coe_mul, autTab_mul] using this
  · intro h
    refine Subtype.ext (autTab_injective ?_)
    simpa only [Subgroup.coe_mul, autTab_mul] using h

theorem card_fixed_eq (μ : MulAut (Carrier .M22)) :
    Nat.card {y : Carrier .M22 // y ∈ F1 ∧ μ y = y} = fixF (autTab μ) := by
  have h := (isTabsOf_F1 hF).card_subtype nodup_f1Tabs (fun y : F1 => μ y = y)
    (fun l => commF (autTab μ) l) fun y => by
      show _ ↔ commF (autTab μ) (tab y) = true
      rw [commF_iff, autTab_conj_iff]
  rw [← Nat.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ F1) (fun y => μ y = y)).symm] at h
  exact h

theorem invData_mem (μ : ↥(autNorm F1)) (h1 : μ * μ = 1) (h2 : μ ≠ 1) :
    (Nat.card (centralizer ({μ} : Set ↥(autNorm F1))),
      Nat.card {y : Carrier .M22 // y ∈ F1 ∧ (μ : MulAut (Carrier .M22)) y = y},
      decide (autTab (μ : MulAut (Carrier .M22)) ∈ tabLI),
      decide (autTab (μ : MulAut (Carrier .M22)) ∈ f1Tabs)) ∈ invClassData := by
  obtain ⟨-, -, -, -, -, hmem, -⟩ := censusCheck_spec Certificates.certificate24790
  have hN := isTabsOf_N hF (nData_pinned hF)
  have h1' : (μ : MulAut (Carrier .M22)) * μ = 1 := congrArg Subtype.val h1
  have hmu : autTab (μ : MulAut (Carrier .M22)) ∈ tabL.filter isInv :=
    List.mem_filter.2 ⟨hN.mem _ μ.2, (isInv_autTab _).2 ⟨h1', fun h => h2 (Subtype.ext h)⟩⟩
  have := hmem _ hmu
  rwa [invData, ← card_centralizer_eq hF, ← card_fixed_eq hF] at this

omit hF in
theorem mem_invClass_iff (μ : ↥(autNorm F1)) (c f : ℕ) :
    μ ∈ InvClass F1 c f ↔ μ * μ = 1 ∧ μ ≠ 1 ∧
      Nat.card (centralizer ({μ} : Set ↥(autNorm F1))) = c ∧
      Nat.card {y : Carrier .M22 // y ∈ F1 ∧ (μ : MulAut (Carrier .M22)) y = y} = f := Iff.rfl

theorem mem_innerImage_top_iff (μ : ↥(autNorm F1)) :
    (μ : MulAut (Carrier .M22)) ∈ innerImage (Carrier .M22) ⊤ ↔
      autTab (μ : MulAut (Carrier .M22)) ∈ tabLI := by
  have h := (isTabsOf_inner hF (nData_pinned hF)).mem_iff (μ : MulAut (Carrier .M22))
  rw [Subgroup.mem_inf] at h
  exact ⟨fun hi => h.1 ⟨hi, μ.2⟩, fun ht => (h.2 ht).1⟩

theorem mem_innerImage_iff (α : MulAut (Carrier .M22)) :
    α ∈ innerImage (Carrier .M22) F1 ↔ autTab α ∈ f1Tabs :=
  (isTabsOf_innerImage hF).mem_iff α

theorem flags_of_mem_invClass {c f : ℕ} {μ : ↥(autNorm F1)} (h : μ ∈ InvClass F1 c f) :
    (c = 768 ∧ f = 16 ∧ autTab (μ : MulAut (Carrier .M22)) ∈ tabLI ∧
        autTab (μ : MulAut (Carrier .M22)) ∈ f1Tabs) ∨
      (c = 384 ∧ f = 8 ∧ autTab (μ : MulAut (Carrier .M22)) ∉ tabLI ∧
        autTab (μ : MulAut (Carrier .M22)) ∉ f1Tabs) ∨
      (c = 128 ∧ f = 8 ∧ autTab (μ : MulAut (Carrier .M22)) ∉ tabLI ∧
        autTab (μ : MulAut (Carrier .M22)) ∉ f1Tabs) ∨
      (c = 192 ∧ f = 4 ∧ autTab (μ : MulAut (Carrier .M22)) ∉ tabLI ∧
        autTab (μ : MulAut (Carrier .M22)) ∉ f1Tabs) ∨
      (c = 64 ∧ f = 4 ∧ autTab (μ : MulAut (Carrier .M22)) ∈ tabLI ∧
        autTab (μ : MulAut (Carrier .M22)) ∉ f1Tabs) := by
  obtain ⟨h1, h2, hc, hf⟩ := h
  have := invData_mem hF μ h1 h2
  rw [hc, hf] at this
  simpa [invClassData] using this

theorem normalizer_involution_classes :
    (∀ μ : ↥(autNorm F1), μ * μ = 1 → μ ≠ 1 →
      μ ∈ InvClass F1 768 16 ∨ μ ∈ InvClass F1 384 8 ∨ μ ∈ InvClass F1 128 8 ∨
        μ ∈ InvClass F1 192 4 ∨ μ ∈ InvClass F1 64 4) ∧
    (∀ μ : ↥(autNorm F1), μ ∈ InvClass F1 768 16 ↔
      (μ : MulAut (Carrier .M22)) ∈ innerImage (Carrier .M22) F1 ∧ μ ≠ 1) ∧
    (∀ μ ∈ InvClass F1 64 4, (μ : MulAut (Carrier .M22)) ∈ innerImage (Carrier .M22) ⊤ ∧
      (μ : MulAut (Carrier .M22)) ∉ innerImage (Carrier .M22) F1) ∧
    (∀ μ : ↥(autNorm F1), μ ∈ InvClass F1 384 8 ∨ μ ∈ InvClass F1 128 8 ∨
      μ ∈ InvClass F1 192 4 → (μ : MulAut (Carrier .M22)) ∉ innerImage (Carrier .M22) ⊤) := by
  refine ⟨fun μ h1 h2 => ?_, fun μ => ⟨fun h => ?_, fun h => ?_⟩, fun μ h => ?_, fun μ h => ?_⟩
  · have h := invData_mem hF μ h1 h2
    simp only [invClassData, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨hc, hf, -⟩ | ⟨hc, hf, -⟩ | ⟨hc, hf, -⟩ | ⟨hc, hf, -⟩ | ⟨hc, hf, -⟩
    · exact Or.inl ⟨h1, h2, hc, hf⟩
    · exact Or.inr (Or.inl ⟨h1, h2, hc, hf⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hc, hf⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, hc, hf⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, hc, hf⟩)))
  · have hfl := flags_of_mem_invClass hF h
    rcases hfl with ⟨-, -, -, h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> try omega
    exact ⟨(mem_innerImage_iff hF _).2 h4, h.2.1⟩
  · obtain ⟨hF1, hne⟩ := h
    have hj := (mem_innerImage_iff hF _).1 hF1
    obtain ⟨y, hy, hyt⟩ := (isTabsOf_F1 hF).exists_mem _ hj
    have hμ : (μ : MulAut (Carrier .M22)) = MulAut.conj y :=
      autTab_injective (by rw [autTab_conj]; exact hyt.symm)
    have hsq : (μ : MulAut (Carrier .M22)) * μ = 1 := by
      rcases (hF y).1 hy with rfl | hy'
      · rw [hμ, map_one]
        simp
      · rw [hμ, ← map_mul, ((invs16_spec 1).2.2 y hy').2, map_one]
    have h1 : μ * μ = 1 := Subtype.ext hsq
    have hd := invData_mem hF μ h1 hne
    simp only [invClassData, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
      decide_eq_true_eq, decide_eq_false_iff_not] at hd
    rcases hd with ⟨hc, hf, -⟩ | ⟨-, -, -, hn⟩ | ⟨-, -, -, hn⟩ | ⟨-, -, -, hn⟩ | ⟨-, -, -, hn⟩
    · exact ⟨h1, hne, hc, hf⟩
    all_goals exact absurd hj hn
  · have hfl := flags_of_mem_invClass hF h
    rcases hfl with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨-, -, h3, h4⟩ <;> try omega
    exact ⟨(mem_innerImage_top_iff hF μ).2 h3, fun hmem => h4 ((mem_innerImage_iff hF _).1 hmem)⟩
  · rcases h with h | h | h <;>
    · have hfl := flags_of_mem_invClass hF h
      rcases hfl with ⟨hc, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨hc, -⟩ <;>
        first | omega | exact fun hi => h3 ((mem_innerImage_top_iff hF μ).1 hi)

omit hF in
theorem sq_eq_one_iff (μ : ↥(autNorm F1)) :
    (μ * μ = 1 ∧ μ ≠ 1) ↔
      (μ : MulAut (Carrier .M22)) * μ = 1 ∧ (μ : MulAut (Carrier .M22)) ≠ 1 := by
  simp only [ne_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one]

theorem card_invClass (c f : ℕ) :
    Nat.card (InvClass F1 c f) =
      (tabL.filter isInv).countP (fun t => centN tabL t == c && fixF t == f) := by
  obtain ⟨-, -, ⟨-, hnd⟩, -⟩ := censusCheck_spec Certificates.certificate24790
  have h := (isTabsOf_N hF (nData_pinned hF)).card_subtype hnd
    (fun μ : ↥(autNorm F1) => μ ∈ InvClass F1 c f)
    (fun t => (centN tabL t == c && fixF t == f) && isInv t) fun μ => ?_
  · rw [List.countP_filter]
    exact h
  · show _ ↔ ((centN tabL (autTab (μ : MulAut (Carrier .M22))) == c &&
      fixF (autTab (μ : MulAut (Carrier .M22))) == f) &&
        isInv (autTab (μ : MulAut (Carrier .M22)))) = true
    rw [mem_invClass_iff, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
      ← card_centralizer_eq hF, ← card_fixed_eq hF, isInv_autTab, ← sq_eq_one_iff]
    tauto

theorem normalizer_involution_census :
    Nat.card {μ : ↥(autNorm F1) // μ * μ = 1 ∧ μ ≠ 1} = 375 ∧
      Nat.card (InvClass F1 768 16) = 15 ∧ Nat.card (InvClass F1 384 8) = 30 ∧
      Nat.card (InvClass F1 128 8) = 90 ∧ Nat.card (InvClass F1 192 4) = 60 ∧
      Nat.card (InvClass F1 64 4) = 180 := by
  obtain ⟨-, -, ⟨-, hnd⟩, h375, -, -, hcls⟩ := censusCheck_spec Certificates.certificate24790
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (isTabsOf_N hF (nData_pinned hF)).card_subtype hnd
      (fun μ : ↥(autNorm F1) => μ * μ = 1 ∧ μ ≠ 1) isInv fun μ => by
        show _ ↔ isInv (autTab (μ : MulAut (Carrier .M22))) = true
        rw [isInv_autTab, sq_eq_one_iff]
    rw [List.countP_eq_length_filter] at h
    rw [h]
    exact h375
  · rw [card_invClass hF]
    exact hcls (768, 16, 15) (by simp [classTable])
  · rw [card_invClass hF]
    exact hcls (384, 8, 30) (by simp [classTable])
  · rw [card_invClass hF]
    exact hcls (128, 8, 90) (by simp [classTable])
  · rw [card_invClass hF]
    exact hcls (192, 4, 60) (by simp [classTable])
  · rw [card_invClass hF]
    exact hcls (64, 4, 180) (by simp [classTable])

end CFSG.EvenSporadicStandard.M22Std
