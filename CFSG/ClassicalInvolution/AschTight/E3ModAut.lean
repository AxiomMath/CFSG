module

public import CFSG.ClassicalInvolution.AschTight.E3OddAut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

@[expose] def oddCoreQuotientAut (L : Type) [Group L] :
    MulAut L →* MulAut (L ⧸ classicalInvolutionOddCore L) where
  toFun α := QuotientGroup.congr (classicalInvolutionOddCore L) (classicalInvolutionOddCore L) α
    (CFSG.ComponentClassification.OddCore.char_invariant α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem oddCoreQuotientAut_mk (L : Type) [Group L] (α : MulAut L) (x : L) :
    oddCoreQuotientAut L α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

theorem eq_one_of_centerQuotientAut_eq_one {L : Type} [Group L] [Group.IsPerfect L]
    {β : MulAut L} (h : centerQuotientAut L β = 1) : β = 1 := by
  have hc : ∀ x : L, β x * x⁻¹ ∈ Subgroup.center L := by
    intro x
    have h1 := congrArg (fun γ : MulAut (L ⧸ Subgroup.center L) => γ (QuotientGroup.mk x)) h
    simp only [centerQuotientAut_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 := Subgroup.inv_mem _ h2
    rw [mul_inv_rev, inv_inv] at h3
    have h4 := (inferInstance : (Subgroup.center L).Normal).conj_mem _ h3 x
    rwa [show x * (x⁻¹ * β x) * x⁻¹ = β x * x⁻¹ by group] at h4
  let _ : CommGroup (Subgroup.center L) :=
    { (inferInstance : Group (Subgroup.center L)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : L →* Subgroup.center L :=
    { toFun := fun x => ⟨β x * x⁻¹, hc x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change β (x * y) * (x * y)⁻¹ = (β x * x⁻¹) * (β y * y⁻¹)
        have hy := Subgroup.mem_center_iff.mp (hc y) (β x)
        have hy' := Subgroup.mem_center_iff.mp (hc y) x⁻¹
        calc β (x * y) * (x * y)⁻¹ = β x * (β y * y⁻¹) * x⁻¹ := by rw [map_mul]; group
          _ = (β y * y⁻¹) * β x * x⁻¹ := by rw [← hy]
          _ = (β y * y⁻¹) * (β x * x⁻¹) := by group
          _ = (β x * x⁻¹) * (β y * y⁻¹) :=
            Subgroup.mem_center_iff.mp (hc y) _ |>.symm }
  ext x
  have h1 : β x * x⁻¹ = 1 := congrArg Subtype.val (eq_one_of_perfect φ x)
  rw [MulAut.one_apply]
  calc β x = β x * x⁻¹ * x := by group
    _ = x := by rw [h1, one_mul]

section Action

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F] [Finite F]

@[expose] noncomputable def normalizerToPGammaL2Mod
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h3 : 3 < Nat.card F) :
    Subgroup.normalizer (K : Set G) →* CFSG.GorensteinWalter.PGammaL2 F :=
  (MulEquiv.ofBijective (CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2 F hF h3)
      ⟨CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_injective F hF h3,
        CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hFcard hF h3⟩).symm.toMonoidHom.comp
    ((centerQuotientAut SL(2, F)).comp ((MulAut.congr e).toMonoidHom.comp
      ((oddCoreQuotientAut K).comp (normalizerConj K))))

theorem oddCoreQuotientAut_eq_one_of_normalizerToPGammaL2Mod_eq_one
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h3 : 3 < Nat.card F) {n : Subgroup.normalizer (K : Set G)}
    (hn : normalizerToPGammaL2Mod e hFcard hF h3 n = 1) :
    oddCoreQuotientAut K (normalizerConj K n) = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, F) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
  have h1 : centerQuotientAut SL(2, F) ((MulAut.congr e)
      ((oddCoreQuotientAut K) (normalizerConj K n))) = 1 := by
    have h2 := congrArg (MulEquiv.ofBijective (CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2 F hF h3)
      ⟨CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_injective F hF h3,
        CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hFcard hF h3⟩) hn
    simp only [normalizerToPGammaL2Mod, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at h2
    exact h2
  have h5 := eq_one_of_centerQuotientAut_eq_one h1
  exact (MulAut.congr e).injective (by rw [h5, map_one])

end Action

end CFSG.ClassicalInvolution.Disconnected.AschTight
