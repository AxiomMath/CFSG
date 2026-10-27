module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.RankThree.PGroups.ZJCenterIntersection
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem three_le_pRank_of_central_of_exponent {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) {T Z : Subgroup K} (hZT : Z ≤ T)
    (hZc : Z ≤ Subgroup.centralizer (T : Set K)) (hZcard : Nat.card Z = p ^ 2)
    (hexp : ∀ u ∈ T, u ^ p = 1) (hTZ : ¬ T ≤ Z) : 3 ≤ Open.pRank p T := by
  obtain ⟨v, hvT, hvZ⟩ := IsConcreteLE.not_le_iff_exists.mp hTZ
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Z.one_mem)
  have : Fact p.Prime := ⟨hp⟩
  have hvo : orderOf v = p := orderOf_eq_prime (hexp v hvT) hv1
  have hvc : v ∈ Subgroup.centralizer (Z : Set K) :=
    Subgroup.mem_centralizer_iff.2 fun z hz =>
      ((Subgroup.mem_centralizer_iff.1 (hZc hz)) v hvT).symm
  have hZab : IsMulCommutative Z :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hZc b.2)) a (hZT a.2))⟩⟩
  have hle : Subgroup.zpowers v ≤ Subgroup.normalizer (Z : Set K) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hvc)
  have hdisj : Z ⊓ Subgroup.zpowers v = ⊥ := by
    have hd : Nat.card (Z ⊓ Subgroup.zpowers v : Subgroup K) ∣ p := by
      rw [← hvo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hd with h1 | hpq
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Z ⊓ Subgroup.zpowers v = Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hpq, Nat.card_zpowers, hvo])
      exact hvZ ((heq ▸ inf_le_left : Subgroup.zpowers v ≤ Z) (Subgroup.mem_zpowers v))
  have hcard : Nat.card (Z ⊔ Subgroup.zpowers v : Subgroup K) = p ^ 3 := by
    rw [CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj, hZcard,
      Nat.card_zpowers, hvo]
    ring
  have hET : (Z ⊔ Subgroup.zpowers v : Subgroup K) ≤ T :=
    sup_le hZT (Subgroup.zpowers_le.2 hvT)
  refine CFSG.SectionRank.le_pRank hp.one_lt hET ⟨?_, fun x hx => hexp x (hET hx)⟩ hcard
  exact CFSG.RankThree.PGroups.isMulCommutative_sup_zpowers hZab hvc

theorem kFactSmallAutRank_of_torus (hTor : KFactOneLieTorus) : KFactSmallAutRank := by
  intro K _ _ hs hnab hcat p hp hp2 T hnc hΓ hrank
  by_contra hbig
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, e, hF⟩ := hTor K hs hnab hcat p hp2 T hnc hΓ hbig
  obtain ⟨ψ, hψ, hrange, -⟩ := hF.torus
  have hn2 := hF.two_le
  have hn0 : n ≠ 0 := by omega
  have hcardF : Nat.card (Multiplicative (GaloisField p n)) = p ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact GaloisField.card p n hn0
  have hpowF : ∀ a : Multiplicative (GaloisField p n), a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hZT : ψ.range ≤ (T : Subgroup K) := hrange ▸ inf_le_left
  have h3 : 3 ≤ Open.pRank p (T : Subgroup K) := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3n
    · obtain ⟨hTcard, -, hexp, -⟩ := hF.pair rfl
      have hZcard : Nat.card ψ.range = p ^ 2 := by
        rw [← hcardF]
        exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
      refine three_le_pRank_of_central_of_exponent hp hZT (hrange ▸ inf_le_right) hZcard hexp ?_
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [hTcard, hZcard] at this
      have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 6 by norm_num)
      omega
    · exact h3n.trans (CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b)
        hpowF hcardF ψ hψ hZT)
  omega

theorem kFactOneLieBorelSolvable_of_torus (hTor : KFactOneLieTorus) :
    KFactOneLieBorelSolvable := by
  intro K _ _ hs hnab hcat p hp hp2 T hnc hΓ hbig
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, e, hF⟩ := hTor K hs hnab hcat p hp2 T hnc hΓ hbig
  have hT : (T : Subgroup K) ≠ ⊥ := by
    intro h
    apply hnc
    rw [h]
    infer_instance
  have hdvd : p ∣ Nat.card (T : Subgroup K) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hT (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    rw [hk]
    exact dvd_pow_self p hk0
  have hle : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ GLBCore p 1 (T : Subgroup K) :=
    le_sSup ⟨T, le_rfl, KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd hp hdvd, rfl⟩
  have heq : GLBCore p 1 (T : Subgroup K) = Subgroup.normalizer ((T : Subgroup K) : Set K) :=
    ((hF.borel_coatom.le_iff).1 hle).resolve_left hΓ
  rw [heq]
  set N := Subgroup.normalizer ((T : Subgroup K) : Set K) with hN
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot (center_bot_of_simple_nonab hnab)
  have hA : Group.IsSolvable (N.map (MulAut.conj : K →* MulAut K)) := by
    refine hF.borel_solvable _ ?_
    rintro α ⟨x, hx, rfl⟩
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hx t).1 ht
    · intro hy
      refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.1 (N.inv_mem hx) y).1 hy
      simpa [mul_assoc] using this
  exact Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective _ hinj).toMonoidHom) (N.equivMapOfInjective _ hinj).injective

end CFSG.AGLEmbedding
