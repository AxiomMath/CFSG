module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsOdd

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin CFSG.Assembly.LowTwoRank TauCeti

theorem exists_mulEquiv_psl2_of_lie_A1 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) (hp : q.p ≠ 2)
    (he : 3 ≤ q.exponent) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), CharP K q.p ∧ Nat.card K = q.p ^ q.exponent ∧
      Nonempty (↥L ≃* CFSG.GorensteinWalter.PSL2 K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hmod := CFSG.HardMathSupport.Cooperstein.Coordinator.statedClassicalModel_PSL_of_lieA hv e
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = q.p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hchar : CharP K q.p := charP_of_card_eq_prime_pow hKcard
  have : Group.IsPerfect ↥L := hq.1
  let π : ↥L →* StatedProj (StatedSL 2 K) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπs : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := CFSG.SectionRank.OddCover.ker_comp_mk'_center e'
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible hW hirr.2
  have h9 : q.p ^ q.exponent ≠ 9 := by
    intro h9
    have h3 := (CFSG.SectionRank.OddCover.eq_three_of_pow_eq_nine q.prime_p h9).2
    omega
  have hbot : π.ker = ⊥ :=
    (CFSG.SectionRank.OddCover.odd_psl_two_perfect_odd_cover_kernel (p := q.p) (f := q.exponent)
      hp hK π hπs hker.le (hker ▸ hodd)).1 h9
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
  exact ⟨K, inferInstance, inferInstance, hchar, hK,
    ⟨(MulEquiv.ofBijective π ⟨hπinj, hπs⟩).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩⟩

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
