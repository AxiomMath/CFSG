module

public import CFSG.Goldschmidt.Setup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientStrongClosure

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem goldschmidtOddCore_eq_pPrimeCore (H : Type*) [Group H] :
    goldschmidtOddCore H = pPrimeCore 2 H := by
  unfold goldschmidtOddCore pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]


theorem goldschmidtOddCore_quotient_eq_bot (Y : Type*) [Group Y] [Finite Y] :
    goldschmidtOddCore (Y ⧸ goldschmidtOddCore Y) = ⊥ := by
  have key : ∀ (N : Subgroup Y) [N.Normal], N = pPrimeCore 2 Y →
      pPrimeCore 2 (Y ⧸ N) = ⊥ := by
    intro N _ e
    subst e
    exact pPrimeCore_quotient_pPrimeCore_eq_bot 2
  rw [goldschmidtOddCore_eq_pPrimeCore (Y ⧸ goldschmidtOddCore Y)]
  exact key _ (goldschmidtOddCore_eq_pPrimeCore Y)

@[expose] def CoreStatement : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (S : Sylow 2 Z) (A : Subgroup Z), A ≤ S →
    IsMulCommutative A → fusionStronglyClosed (A : Set Z) (S : Subgroup Z) →
    Subgroup.normalClosure (A : Set Z) = ⊤ → goldschmidtOddCore Z = ⊥ →
    CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z = ⊤ ∧
    A = CFSG.Open.pCore 2 Z ⊔
      Subgroup.closure {t | t ∈ (S : Subgroup Z) ⊓ goldschmidtLayer Z ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup Z, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K)

theorem isMulCommutative_map {Y Z : Type*} [Group Y] [Group Z] {A : Subgroup Y}
    (hA : IsMulCommutative A) (f : Y →* Z) : IsMulCommutative (A.map f) :=
  ⟨⟨by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have h := hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    have h' : a * b = b * a := congrArg Subtype.val h
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, h']⟩⟩

theorem normalClosure_map_eq_top {Y Z : Type*} [Group Y] [Group Z] {A : Subgroup Y}
    (htop : Subgroup.normalClosure (A : Set Y) = ⊤) (f : Y →* Z)
    (hf : Function.Surjective f) : Subgroup.normalClosure ((A.map f : Subgroup Z) : Set Z) = ⊤ := by
  rw [eq_top_iff]
  have hle : (⊤ : Subgroup Y).map f ≤ Subgroup.normalClosure ((A.map f : Subgroup Z) : Set Z) := by
    rw [← htop, Subgroup.map_le_iff_le_comap]
    apply Subgroup.normalClosure_le_normal
    intro a ha
    exact Subgroup.subset_normalClosure ⟨a, ha, rfl⟩
  intro z _
  obtain ⟨y, rfl⟩ := hf z
  exact hle ⟨y, trivial, rfl⟩

theorem topStatement_of_coreStatement (h : CoreStatement) : TopStatement := by
  intro Y _ _ S A hAS hAab hcl htop
  obtain ⟨Sbar, hSbar, hclbar⟩ :=
    CFSG.ShultStronglyClosedTI.quotient_stronglyClosed S A (goldschmidtOddCore Y) hAS hcl
  have hAbar : A.map (QuotientGroup.mk' (goldschmidtOddCore Y)) ≤ Sbar := by
    rw [hSbar]
    exact Subgroup.map_mono hAS
  obtain ⟨h1, h2, h3⟩ := h _ Sbar _ hAbar (isMulCommutative_map hAab _) hclbar
    (normalClosure_map_eq_top htop _ (QuotientGroup.mk'_surjective _))
    (goldschmidtOddCore_quotient_eq_bot Y)
  refine ⟨h1, ?_, h3⟩
  rw [hSbar] at h2
  exact h2
end CFSG.Goldschmidt
