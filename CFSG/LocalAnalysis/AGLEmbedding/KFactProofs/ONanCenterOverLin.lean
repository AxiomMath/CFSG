module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCenterOverUnital
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneDickson

public section

namespace CFSG.AGLEmbedding.CenterOver

theorem sylow_commutative_of_equiv_psl2GF {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) {L : Type*}
    [Group L] [Finite L] (e : L ≃* PSL2GF p n) (T₁ : Sylow p L) :
    ∀ x ∈ (T₁ : Subgroup L), ∀ y ∈ (T₁ : Subgroup L), x * y = y * x := by
  have h := (psl2GF_sylow p n hn (T₁.mapSurjective (f := (e : L →* PSL2GF p n))
    e.surjective)).1.1
  rw [Sylow.coe_mapSurjective] at h
  intro x hx y hy
  have := h.is_comm.comm ⟨e x, Subgroup.mem_map_of_mem _ hx⟩ ⟨e y, Subgroup.mem_map_of_mem _ hy⟩
  have h2 : e (x * y) = e (y * x) := by simpa using congrArg Subtype.val this
  exact e.injective h2

theorem eq_top_of_equiv_psl2GF {K L : Type} [Group K] [Finite K]
    [IsSimpleGroup K] [Group L] [Finite L] {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hKnc : ∃ a b : K, a * b ≠ b * a) (e : L ≃* PSL2GF p n) (T₁ : Sylow p L) (Y : Subgroup L)
    (φ : Y →* K) (hφ : Function.Surjective φ)
    (hZY : (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤ Y) :
    Y = ⊤ := by
  have hYns : ¬ Group.IsSolvable Y := not_isSolvable_of_surjective hKnc φ hφ
  have hcomm := sylow_commutative_of_equiv_psl2GF (Nat.one_le_iff_ne_zero.mpr hn) e T₁
  have hTY : (T₁ : Subgroup L) ≤ Y := fun x hx =>
    hZY ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx⟩
  exact eq_top_of_sylow_le_of_equiv_psl2GF hp2 hn e Y T₁ hTY hYns

end CFSG.AGLEmbedding.CenterOver
