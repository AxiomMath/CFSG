module

import CFSG.Walter.W67.Section5.P56R1512
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open scoped MatrixGroups

theorem card_psl2_eight : Nat.card PSL(2, GaloisField 2 3) = 504 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hSL : Nat.card SL(2, GaloisField 2 3) = 504 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula, hK]
    norm_num
  have h2 : (2 : GaloisField 2 3) = 0 := by
    have : CharP (GaloisField 2 3) 2 := inferInstance
    exact CharP.cast_eq_zero (GaloisField 2 3) 2
  have hc : Nat.card (Subgroup.center SL(2, GaloisField 2 3)) = 1 := by
    let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (i := (0 : Fin 2)) (R := GaloisField 2 3)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    have key : ∀ y : rootsOfUnity 2 (GaloisField 2 3), y = 1 := by
      intro y
      have hy : ((y : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ 2 = 1 := by
        have := (mem_rootsOfUnity 2 (y : (GaloisField 2 3)ˣ)).mp y.property
        simpa using congrArg Units.val this
      have hsq : (((y : (GaloisField 2 3)ˣ) : GaloisField 2 3) - 1) ^ 2 = 0 := by
        linear_combination hy - (((y : (GaloisField 2 3)ˣ) : GaloisField 2 3) - 1) * h2
      have h1 : ((y : (GaloisField 2 3)ˣ) : GaloisField 2 3) - 1 = 0 := pow_eq_zero_iff
        (by norm_num) |>.mp hsq
      exact Subtype.ext (Units.ext (sub_eq_zero.mp h1))
    rw [key a, key b]
  change Nat.card (SL(2, GaloisField 2 3) ⧸ Subgroup.center SL(2, GaloisField 2 3)) = _
  rw [← Subgroup.index_eq_card]
  have hi := Subgroup.index_mul_card (Subgroup.center SL(2, GaloisField 2 3))
  rw [hc, hSL] at hi
  omega

theorem not_isElemAbelian_of_psl28 {X : Type} [Group X] [Finite X] (R : Sylow 3 X)
    {K : Subgroup X} (e : K ≃* PSL2GF 2 3) : ¬ IsElemAbelian 3 (R : Subgroup X) := by
  intro hel
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hcyc : IsCyclic (P₀ : Subgroup K) := by
    have h1 := CFSG.Walter.W67.Sec56.psl28_sylow_three_cyclic
      (P₀.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hcoe : ((P₀.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 3 (PSL2GF 2 3)) :
        Subgroup (PSL2GF 2 3)) = (P₀ : Subgroup K).map e.toMonoidHom :=
      Sylow.coe_mapSurjective e.surjective P₀
    have h2 : IsCyclic ↥((P₀ : Subgroup K).map e.toMonoidHom) := by
      rw [← hcoe]
      exact h1
    exact (Subgroup.equivMapOfInjective (P₀ : Subgroup K) e.toMonoidHom e.injective).isCyclic.mpr h2
  have hexp : ∀ x ∈ (P₀ : Subgroup K), x ^ 3 = 1 := by
    obtain ⟨Q, hQ⟩ := (P₀.isPGroup'.map K.subtype).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R Q
    intro x hx
    have hxQ : (x : X) ∈ (Q : Subgroup X) := hQ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨r, hr, hrx⟩ := hxQ
    have hrx' : g * r * g⁻¹ = (x : X) := by simpa [MulAut.smul_def, MulAut.conj_apply] using hrx
    have hx3 : (x : X) ^ 3 = 1 := by
      rw [← hrx', conj_pow, hel.2 r hr]
      group
    exact Subtype.ext (by simpa using hx3)
  obtain ⟨⟨g, hgP⟩, hgen⟩ := IsCyclic.exists_generator (α := (P₀ : Subgroup K))
  have hcard : Nat.card (P₀ : Subgroup K) ∣ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hexp g hgP))
  have hK504 : Nat.card K = 504 := (Nat.card_congr e.toEquiv).trans card_psl2_eight
  have hidx := P₀.not_dvd_index
  have hmul := (P₀ : Subgroup K).card_mul_index
  rw [hK504] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h1 | h3
  · rw [h1] at hmul
    exact hidx ⟨168, by omega⟩
  · rw [h3] at hmul
    exact hidx ⟨56, by omega⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
