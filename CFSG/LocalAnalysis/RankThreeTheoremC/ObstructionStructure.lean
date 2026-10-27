module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G]

@[expose] def omegaOneOf (p : ℕ) (D : Subgroup G) : Subgroup G :=
  closure {x | x ∈ D ∧ x ^ p = 1}

theorem omegaOneOf_le (p : ℕ) (D : Subgroup G) : omegaOneOf p D ≤ D :=
  closure_le _ |>.2 fun _ hx => hx.1

theorem le_omegaOneOf_of_isElemAbelian {p : ℕ} {D E : Subgroup G} (hED : E ≤ D)
    (hE : IsElemAbelian p E) : E ≤ omegaOneOf p D :=
  fun x hx => subset_closure ⟨hED hx, hE.2 x hx⟩

theorem isElemAbelian_omegaOneOf {p : ℕ} {D : Subgroup G} (hD : IsMulCommutative D) :
    IsElemAbelian p (omegaOneOf p D) := by
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : ∀ x ∈ omegaOneOf p D, ∀ y ∈ omegaOneOf p D, x * y = y * x :=
    fun x hx y hy => hcommD x (omegaOneOf_le p D hx) y (omegaOneOf_le p D hy)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (hcomm x hx y hy) p), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem normalizer_le_normalizer_omegaOneOf [Finite G] (p : ℕ) (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (omegaOneOf p D : Set G) := by
  intro g hg
  have hconj : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
  have hle : (omegaOneOf p D).map (MulAut.conj g).toMonoidHom ≤ omegaOneOf p D := by
    rw [omegaOneOf, MonoidHom.map_closure]
    refine closure_le _ |>.2 ?_
    rintro _ ⟨x, ⟨hxD, hxp⟩, rfl⟩
    refine subset_closure ⟨?_, ?_⟩
    · rw [← hconj]
      exact ⟨x, hxD, rfl⟩
    · change (g * x * g⁻¹) ^ p = 1
      rw [conj_pow, hxp, mul_one, mul_inv_cancel]
  have heq : (omegaOneOf p D).map (MulAut.conj g).toMonoidHom = omegaOneOf p D :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  exact mem_normalizer_iff_map_conj_eq.mpr heq

variable [Finite G]

theorem ExtremalObstruction.isElemAbelian_of_isMulCommutative {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime)
    (hD : IsMulCommutative D) : IsElemAbelian p D ∧ Nat.card D = p ^ 2 := by
  obtain ⟨E, hED, hE, hEc⟩ := pRank_attained p D (by rw [hext.rank_eq]; norm_num)
  rw [hext.rank_eq] at hEc
  have hX2 : 2 ≤ CFSG.Open.pRank p (omegaOneOf p D) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hp.one_lt _)
      ⟨E, le_omegaOneOf_of_isElemAbelian hED hE, hE, hEc⟩
  have hXD := hext.minimal (omegaOneOf p D) (omegaOneOf_le p D) hX2
    (normalizer_le_normalizer_omegaOneOf p D)
  have hDe : IsElemAbelian p D := hXD ▸ isElemAbelian_omegaOneOf hD
  refine ⟨hDe, ?_⟩
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (elementary_isPGroup p D hDe).exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank p D := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨D, le_rfl, hDe, hk⟩
  rw [hext.rank_eq] at hkle
  have hlow : p ^ 2 ≤ Nat.card D := hEc ▸ Subgroup.card_le_of_le hED
  rw [hk] at hlow ⊢
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hlow
  congr 1
  omega

theorem ExtremalObstruction.isIsolatedPlane_of_isMulCommutative {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime)
    (hD : IsMulCommutative D) : IsIsolatedPlane p P D := by
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hp hD
  exact isIsolatedPlane_of_pRank_le_two hp hext.obstruction.2.1 hDe hDc
    hext.product_rank_eq.le

end CFSG.LocalAnalysis.RankThreeTheoremC
