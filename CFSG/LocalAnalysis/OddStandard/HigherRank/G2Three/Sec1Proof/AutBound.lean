module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Basic

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem card_le_mulAut_mul_centIn [Finite G] {N F : Subgroup G} (hN : N ≤ normalizer (F : Set G))
    (hA : Nat.card (MulAut F) ≠ 0) :
    Nat.card N ≤ Nat.card (MulAut F) * Nat.card (centIn N F) := by
  have : Finite (MulAut F) := Nat.finite_of_card_ne_zero hA
  let ψ : N →* MulAut F := F.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have h1 : Nat.card N = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have h2 : Nat.card ψ.range ≤ Nat.card (MulAut F) := Subgroup.card_le_card_group _
  have h3 : Nat.card ψ.ker ≤ Nat.card (centIn N F) := by
    have hmem : ∀ k : ψ.ker, ((k : N) : G) ∈ centIn N F := by
      intro k
      change ((k : N) : G) ∈ N ⊓ centralizer (F : Set G)
      refine Subgroup.mem_inf.mpr ⟨(k : N).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro f hf
      have hk : ψ (k : N) = 1 := k.2
      have e : (((ψ (k : N)) ⟨f, hf⟩ : F) : G) = ((k : N) : G) * f * ((k : N) : G)⁻¹ := rfl
      rw [hk] at e
      have e' : f = ((k : N) : G) * f * ((k : N) : G)⁻¹ := e
      rw [eq_mul_inv_iff_mul_eq] at e'
      exact e'
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : N) : G), hmem k⟩) ?_
    intro a b hab
    have hab' : ((a : N) : G) = ((b : N) : G) :=
      congrArg (fun x : centIn N F => (x : G)) hab
    exact Subtype.ext (Subtype.ext hab')
  calc Nat.card N = Nat.card ψ.ker * Nat.card ψ.range := h1
    _ ≤ Nat.card (centIn N F) * Nat.card (MulAut F) := Nat.mul_le_mul h3 h2
    _ = Nat.card (MulAut F) * Nat.card (centIn N F) := mul_comm _ _

variable {Y : Type} [Group Y] [Finite Y]

theorem card_mulAut_of_isE {n : ℕ} (h : IsE n Y) :
    Nat.card (MulAut Y) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨⟨hc, hsq⟩, hcard⟩ := h
  refine CFSG.EvenSporadicStandard.TwoCo1.card_mulAut_eq (fun a b => ?_)
    (fun a => hsq a (Subgroup.mem_top a)) hcard
  have := hc.is_comm.comm ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩
  exact congrArg Subtype.val this

theorem card_mulAut_of_isE3 (h : IsE 3 Y) : Nat.card (MulAut Y) = 168 := by
  rw [card_mulAut_of_isE h, Matrix.card_GL_field]
  simp [Fin.prod_univ_three]

theorem card_mulAut_of_isE2 (h : IsE 2 Y) : Nat.card (MulAut Y) = 6 := by
  rw [card_mulAut_of_isE h, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
