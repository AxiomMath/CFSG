module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Nat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Stab
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.AltTwo
public import CFSG.Quasithin.Background.B69Asm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem fixV_ffJ_invariant {X H : Subgroup (MulAut V)} (hHX : H ≤ X) :
    ∀ h : ↥H, ∀ c ∈ fixV (ffJ X), (h : MulAut V) c ∈ fixV (ffJ X) := by
  intro h c hc y hy
  have hn : (h : MulAut V)⁻¹ * y * (h : MulAut V) ∈ ffJ X := by
    have := (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X (X.inv_mem (hHX h.2))) y).mp hy
    simpa using this
  have h1 := hc _ hn
  have e : y ((h : MulAut V) c) = (h : MulAut V) (((h : MulAut V)⁻¹ * y * (h : MulAut V)) c) := by
    simp [MulAut.mul_apply]
  rw [e, h1]

@[expose] def CanonBlock (X T M H : Subgroup (MulAut V)) : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧
      Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
      M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) ∧
      BinaryNaturalSL H (fixV (ffJ X) ⊔ commV H) (fixV (ffJ X)) 2 e) ∨
    (∃ k : ℕ, Nonempty (↥H ≃* Equiv.Perm (Fin (2 ^ k + 1))) ∧
      Nonempty (↥(M ⊓ H) ≃* Equiv.Perm (Fin (2 ^ k))) ∧ G6.IsSymCore H (commV H) (2 ^ k + 1))

theorem canonBlock_of_nat {X T M H : Subgroup (MulAut V)} (hHX : H ≤ X) {e : ℕ} (he : 1 ≤ e)
    (hnat : BinaryNaturalSL H (commV H) (commV H ⊓ fixV (ffJ X)) 2 e)
    (hM : M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V))) :
    CanonBlock X T M H :=
  Or.inl ⟨e, he, nonempty_mulEquiv_sl2_of_binaryNatural he hnat, hM,
    binaryNaturalSL_sup_of_inf (fixV_ffJ_invariant hHX) hnat⟩

theorem nonempty_mulEquiv_inf_perm_of_stabilizer {H M : Subgroup (MulAut V)} {k : ℕ}
    {π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H} (hπ : Function.Injective π)
    (hM : (M ⊓ H).subgroupOf H =
      (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1))) (⟨0, by omega⟩ : Fin (2 * k + 1))).map π) :
    Nonempty (↥(M ⊓ H) ≃* Equiv.Perm (Fin (2 * k))) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_stabilizer_perm (2 * k) ⟨0, by omega⟩
  exact ⟨((Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ H ≤ H)).symm.trans
    ((MulEquiv.subgroupCongr hM).trans (Subgroup.equivMapOfInjective _ π hπ).symm)).trans e⟩

theorem canonBlock_of_sym {X T M H : Subgroup (MulAut V)} {k j : ℕ} (hkj : 2 * k + 1 = 2 ^ j + 1)
    {π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H}
    (hreal : (FFModel.symDn (2 * k + 1)).RealizesVia H (commV H) ⊥ π)
    (hM : (M ⊓ H).subgroupOf H =
      (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1))) (⟨0, by omega⟩ : Fin (2 * k + 1))).map π) :
    CanonBlock X T M H := by
  obtain ⟨θ, β, hθ, -⟩ := CFSG.Quasithin.Ch3z.isSymCore_of_realizes' hreal
  have hπ : Function.Injective π := fun a b hab =>
    θ.symm.injective ((hθ a).trans (hab.trans (hθ b).symm))
  refine Or.inr ⟨j, ?_, ?_, ?_⟩
  · have key : ∀ n : ℕ, n = 2 ^ j + 1 → Nonempty (↥H ≃* Equiv.Perm (Fin n)) →
        Nonempty (↥H ≃* Equiv.Perm (Fin (2 ^ j + 1))) := by
      rintro n rfl h
      exact h
    exact key _ hkj ⟨θ⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_inf_perm_of_stabilizer hπ hM
    have key : ∀ n : ℕ, n = 2 ^ j → Nonempty (↥(M ⊓ H) ≃* Equiv.Perm (Fin n)) →
        Nonempty (↥(M ⊓ H) ≃* Equiv.Perm (Fin (2 ^ j))) := by
      rintro n rfl h
      exact h
    exact key _ (by omega) ⟨e⟩
  · have key : ∀ n : ℕ, n = 2 ^ j + 1 → G6.IsSymCore H (commV H) n →
        G6.IsSymCore H (commV H) (2 ^ j + 1) := by
      rintro n rfl h
      exact h
    exact key _ hkj (CFSG.Quasithin.Ch3z.isSymCore_of_realizes hreal)

theorem canonBlock_blk {X T M : Subgroup (MulAut V)} (hB : BlkCtx X T M)
    (hK : CFSG.SectionRank.IsKGroupCat ↥X) (h : MinParabolic X T M) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) {L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    CanonBlock X T M (blk X L) := by
  obtain ⟨A₀, hA₀, hLA₀⟩ := hB.hact L hL
  have hW₀ : commV L ∈ IrrPlus L (⊤ : Subgroup V) := commV_mem_irrPlus hB.hV hB.hctx hA₀ hL hLA₀
  have hshape : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
      CompShape T M A L (commV L) := fun A hA hLA => hB.hctx A L hA hL hLA (commV L) hW₀
  by_cases hAlt : ∃ A : Subgroup (MulAut V), IsFFStarMin X A ∧ ⁅L, A⁆ = L ∧ AltShape M A L (commV L)
  · obtain ⟨A, hA, hLA, hAlt⟩ := hAlt
    have hblk : blk X L = L ⊔ A := le_antisymm
      (blk_le_iff.2 ⟨le_sup_left, fun A' hA' hLA' => hB.hG1 A L hA hL hLA hAlt A' hA' hLA'⟩)
      (sup_le le_blk_self (le_blk_of hA hLA))
    have hcomm : commV (L ⊔ A) = commV L := by
      rw [← hblk]
      exact commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL ⟨A₀, hA₀, hLA₀⟩)
    obtain ⟨k, hk, π, -, hreal, hLeq, -, hM⟩ := hAlt
    have hH : CompHypK X T M A L := ⟨hK, h, hB.hO2, hFF, hns, hA, hL, hLA⟩
    obtain ⟨j, hj⟩ := B69K.exists_two_pow_of_altShape hH hk hreal hLeq
    rw [← hcomm] at hreal
    rw [hblk]
    exact canonBlock_of_sym hj hreal hM
  · push Not at hAlt
    have hnat : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
        NatShape T M A L (commV L) := fun A hA hLA =>
      (compShape_iff.1 (hshape A hA hLA)).resolve_right (hAlt A hA hLA)
    have hblk : blk X L = L := le_antisymm
      (blk_le_iff.2 ⟨le_rfl, fun A hA hLA => (hnat A hA hLA).2.1.1⟩) le_blk_self
    obtain ⟨⟨e, he, hbin⟩, -, hMN⟩ := hnat A₀ hA₀ hLA₀
    have h1 := commV_inf_fixV_ffJ hB hL
    rw [hblk] at h1
    rw [hblk]
    exact canonBlock_of_nat hL.1 he (by rw [h1]; exact hbin) hMN

end B69

end CFSG.Quasithin
