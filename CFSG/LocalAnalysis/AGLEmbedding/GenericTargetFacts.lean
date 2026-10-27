module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

abbrev CatGroup (d : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie d).Group

theorem isElemAbelian_range_galoisField {Y : Type} [Group Y] {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (ψ : Multiplicative (GaloisField p n) →* Y) (hψ : Function.Injective ψ) :
    IsElemAbelian p ψ.range ∧ Nat.card ψ.range = p ^ n := by
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rw [← map_pow, hap, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p n hn]

theorem JStarElimDataOf.congr_target {L T T' : Type} [Group L] [Finite L] [Group T] [Group T']
    {p b : ℕ} (e : T ≃* T') (h : JStarElimDataOf L p b T) : JStarElimDataOf L p b T' := by
  obtain ⟨A, J, hA, hJ, hcard, φ, hs, hc⟩ := h
  refine ⟨A, J, hA, hJ, hcard, e.toMonoidHom.comp φ, e.surjective.comp hs, ?_⟩
  have hk : (e.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hk]
  exact hc

end CFSG.AGLEmbedding
