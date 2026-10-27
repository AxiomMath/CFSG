module

public import CFSG.HardMathSupport.Timmesfeld.Balance.DeltaLocal
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem i192_le_centralizer {G : Type*} [Group G] {p : ℕ} {B : Subgroup G}
    (hB : IsElemAbelian p B) {x : G} (hx : x ∈ B) :
    B ≤ Subgroup.centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hB.1
  have h := mul_comm' (⟨y, hy⟩ : B) ⟨x, hx⟩
  simpa using congrArg Subtype.val h

theorem input19_2_2Pos_holds :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ B : Subgroup G, IsElemAbelian p B →
        ∀ k : ℕ, 1 ≤ k →
        (∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
          GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J → IsCompLocallyBalanced p k B J) →
        IsBalancedWrt p k B := by
  intro G _ _ _ _ _ p hp hp2 B hB k hk hloc D hD x hx hx1
  have hBx := i192_le_centralizer hB hx
  have hΔ := CFSG.HardMathSupport.Timmesfeld.Balance.deltaOfLocalBalance_proved G p hp hp2 k hk
    (Subgroup.centralizer ({x} : Set G)) B D hBx hB hD (hloc x hx hx1)
  refine le_trans ?_ hΔ
  intro y hy
  obtain ⟨hyΔ, hyx⟩ := Subgroup.mem_inf.1 hy
  simp only [Subgroup.mem_iInf]
  intro e he he1
  have hye : y ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set G)) := by
    simp only [GLADelta, Subgroup.mem_iInf] at hyΔ
    exact hyΔ e he he1
  have hyCe : y ∈ Subgroup.centralizer ({e} : Set G) := Subgroup.map_subtype_le _ hye
  exact inf_glaPPrimeCoreOf_le (H := Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) (A := Subgroup.centralizer ({e} : Set G)) hp inf_le_right
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hyx, hyCe⟩, hye⟩)

end CFSG.HardMathSupport.Solomon.Coordinator
