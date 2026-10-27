module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Inner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped MatrixGroups

namespace F3D4

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_sup_centralizer_of_commutator {L M : Subgroup Q} (hMN : M ≤ normalizer (L : Set Q))
    (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    (hc : ∀ a ∈ M, ∀ g ∈ M, a * g * a⁻¹ * g⁻¹ ∈ L ⊔ centralizer (L : Set Q))
    {s : Q} (hs : s ∈ M) {n : ℕ} (hsn : s ^ 2 ^ n = 1) :
    s ∈ L ⊔ centralizer (L : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := centralizer (L : Set Q) with hZ
  set N := M ⊓ (L ⊔ Z) with hN
  have hNn : ∀ k ∈ M, ∀ y ∈ N, k * y * k⁻¹ ∈ N := by
    intro k hk y hy
    obtain ⟨hyM, hyLZ⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hk hyM) (inv_mem hk), ?_⟩
    have hle : L ⊔ Z ≤ (L ⊔ Z).comap (MulAut.conj k).toMonoidHom :=
      sup_le (fun l hl => mem_sup_left ((mem_normalizer_iff.mp (hMN hk) l).mp hl))
        (fun c hc => mem_sup_right (F3A75.conj_mem_centralizer (hMN hk) hc))
    exact hle hyLZ
  obtain ⟨a₀, g₀, -, hqa⟩ := F3L221.sl23_commutator (F3A75.e_mk_pow_four e hs hsn)
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm a₀)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm g₀)
  have hea : e (QuotientGroup.mk a) = a₀ := by rw [ha, MulEquiv.apply_symm_apply]
  have heg : e (QuotientGroup.mk g) = g₀ := by rw [hg, MulEquiv.apply_symm_apply]
  have h1 : (a * g * a⁻¹ * g⁻¹)⁻¹ * ⟨s, hs⟩ ∈ pPrimeCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hea, heg]
    rw [← hqa, inv_mul_cancel]
  have hmem : s ∈ N ⊔ (pPrimeCore 2 ↥M).map M.subtype := by
    have h2 : s = ((a * g * a⁻¹ * g⁻¹ : ↥M) : Q) *
        (((a * g * a⁻¹ * g⁻¹)⁻¹ * ⟨s, hs⟩ : ↥M) : Q) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    refine mul_mem (mem_sup_left (mem_inf.mpr ⟨(a * g * a⁻¹ * g⁻¹).2, ?_⟩))
      (mem_sup_right ⟨_, h1, rfl⟩)
    exact hc a a.2 g g.2
  have hOodd : Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact odd_card_pPrimeCore_two ↥M
  exact (mem_inf.mp (F3L221.mem_of_mem_sup_of_odd (F3A75.map_pPrimeCore_le_normalizer hNn) hOodd
    hmem hsn)).2

end F3D4

end CFSG.ComponentClassification.HarrisLit.T1
