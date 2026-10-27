module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryCommSpace
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeUC.JeTransport.JeTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinarySubgroup

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

private theorem Y_gen (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Y hc = Subgroup.closure {x : MulAut ↥P | x ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ∧
      x ∈ Subgroup.centralizer ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) : Subgroup (MulAut ↥P)) :
        Set (MulAut ↥P)) ∧ x ^ 2 = 1} :=
  JeTransport.mem_omegaOneZ_gen 2 _

theorem Y_le (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Y hc ≤ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) :=
  JeTransport.omegaOneZ_le 2 _

theorem Y_elemAbelian (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    CFSG.Open.IsElemAbelian 2 (Y hc) := by
  rw [Y_gen hc]
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ (fun x hx => hx.2.2)
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp hy.2.1 x hx.1

theorem Y_commute (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∀ ψ ∈ Y hc, ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal), Commute ψ φ := by
  intro ψ hψ
  rw [Y_gen hc] at hψ
  induction hψ using Subgroup.closure_induction with
  | mem x hx => exact fun φ hφ => (Subgroup.mem_centralizer_iff.mp hx.2.1 φ hφ).symm
  | one => exact fun φ _ => Commute.one_left _
  | mul x y _ _ ihx ihy => exact fun φ hφ => (ihx φ hφ).mul_left (ihy φ hφ)
  | inv x _ ih => exact fun φ hφ => (ih φ hφ).inv_left

private theorem normalizes_image (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    Bstar P B ≤ Subgroup.normalizer
      ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) : Subgroup (MulAut P)) : Set (MulAut P)) := by
  have hBT := hc.oddPrimeClassTwoAction.normalizes he
  have key : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := fun b hb t ht =>
    (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
  rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
  have hb' : b ∈ B := Subgroup.mem_subgroupOf.mp hb
  have hφ : Subgroup.normalizerMonoidHom P ⟨b, hbN⟩ = conjOnP P hc.faithfulBinaryIrreducibleAction.normal b := rfl
  rw [hφ, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨b * t * b⁻¹, key b hb' t ht, by simp⟩
  · rintro ⟨t, ht, hth⟩
    refine ⟨b⁻¹ * t * b, ?_, ?_⟩
    · have := key b⁻¹ (B.inv_mem hb') t ht
      simpa using this
    · have : h = (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b)⁻¹ * (conjOnP P hc.faithfulBinaryIrreducibleAction.normal t) *
          conjOnP P hc.faithfulBinaryIrreducibleAction.normal b := by
        rw [hth]; group
      rw [this]; simp [map_mul, map_inv]

private theorem conj_mem_Y (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {φ : MulAut ↥P}
    (hφ : φ ∈ Subgroup.normalizer
      ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) : Subgroup (MulAut P)) : Set (MulAut P)))
    {y : MulAut ↥P} (hy : y ∈ Y hc) : φ * y * φ⁻¹ ∈ Y hc := by
  rw [Y_gen hc] at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨(Subgroup.mem_normalizer_iff.mp hφ x).mp hx.1, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : φ⁻¹ * z * φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hφ) z).mp hz
        simpa using this
      have := Subgroup.mem_centralizer_iff.mp hx.2.1 _ hz'
      calc z * (φ * x * φ⁻¹) = φ * ((φ⁻¹ * z * φ) * x) * φ⁻¹ := by group
        _ = φ * (x * (φ⁻¹ * z * φ)) * φ⁻¹ := by rw [this]
        _ = φ * x * φ⁻¹ * z := by group
    · have : (φ * x * φ⁻¹) ^ 2 = φ * x ^ 2 * φ⁻¹ := by
        rw [conj_pow]
      rw [this, hx.2.2]; group
  | one => simp [Subgroup.one_mem]
  | mul x y _ _ ihx ihy =>
    have : φ * (x * y) * φ⁻¹ = (φ * x * φ⁻¹) * (φ * y * φ⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have : φ * x⁻¹ * φ⁻¹ = (φ * x * φ⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ih

theorem Bstar_normalizes_Y (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    Bstar P B ≤ Subgroup.normalizer (Y hc : Set (MulAut ↥P)) := by
  intro b hb
  have hb' := normalizes_image hc he hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_Y hc hb' hy, fun hy => ?_⟩
  have := conj_mem_Y hc ((Subgroup.normalizer _).inv_mem hb') hy
  simpa [mul_assoc] using this

theorem X_le_Y (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) : X hc ≤ Y hc :=
  ElementaryCommSpace.commutator_le_left (Bstar_normalizes_Y hc he)

theorem Bstar_normalizes_X (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    Bstar P B ≤ Subgroup.normalizer (X hc : Set (MulAut ↥P)) := fun b hb =>
  ElementaryCommSpace.normalizer_commutator (Bstar_normalizes_Y hc he hb)
    (Subgroup.le_normalizer hb)

theorem Y_isPGroup (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    IsPGroup 2 (Y hc) := by
  have h2 : IsPGroup 2 (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) :=
    hc.oddPrimeClassTwoAction.setting.twoGroup.map _
  exact h2.to_le (Y_le hc)

theorem commutator_X_eq (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    ⁅X hc, Bstar P B⁆ = X hc := by
  have hY2 := Y_isPGroup hc
  obtain ⟨n, hn⟩ := hY2.exists_card_eq
  have hodd := (CoprimeStarSubgroupStructure.structure hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).2.2.1
  have hcop : Nat.Coprime (Nat.card (Bstar P B)) (Nat.card (Y hc)) := by
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h := CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime (Y hc) (Bstar P B) hcop
    (Bstar_normalizes_Y hc he)
  exact h

theorem central_binary (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    CFSG.Open.IsElemAbelian 2 (Y hc) ∧ X hc ≤ Y hc ∧ CFSG.Open.IsElemAbelian 2 (X hc) ∧
      X hc ≤ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ∧
      (∀ ψ ∈ X hc, ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal), Commute ψ φ) ∧
      Bstar P B ≤ Subgroup.normalizer (X hc : Set (MulAut ↥P)) ∧
      ⁅X hc, Bstar P B⁆ = X hc := by
  have hXY := X_le_Y hc he
  have hYe := Y_elemAbelian hc
  haveI := hYe.1
  refine ⟨hYe, hXY, ?_, hXY.trans (Y_le hc), fun ψ hψ => Y_commute hc ψ (hXY hψ),
    Bstar_normalizes_X hc he, commutator_X_eq hc he⟩
  refine ⟨?_, fun x hx => hYe.2 x (hXY hx)⟩
  exact ⟨⟨fun a b => Subtype.ext ((Y_commute hc _ (hXY a.2) _ (hXY.trans (Y_le hc) b.2)).eq)⟩⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinarySubgroup
