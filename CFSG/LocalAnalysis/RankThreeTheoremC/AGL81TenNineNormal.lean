module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenNineRankCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → p ≠ 3 → Open.pRank 3 (H ⊓ M) ≤ 3

variable {G}

theorem four_le_pRank_of_commute {X : Type} [Group X] [Finite X] {A E E' : Subgroup X}
    (hE : E ≤ A) (hE' : E' ≤ A) (he : IsElemAbelian 3 E) (he' : IsElemAbelian 3 E')
    (hc : Nat.card E = 9) (hc' : Nat.card E' = 9)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E', Commute x y) (hdisj : ∀ x ∈ E, x ∈ E' → x = 1) :
    4 ≤ Open.pRank 3 A := by
  have hcm : ∀ (a : E) (b : E'), Commute (E.subtype a) (E'.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set f := MonoidHom.noncommCoprod E.subtype E'.subtype hcm with hf
  have hfapp : ∀ x : E × E', f x = (x.1 : X) * x.2 := fun x => rfl
  have hEc : ∀ a b : E, a * b = b * a := fun a b => he.1.is_comm.comm a b
  have hEc' : ∀ a b : E', a * b = b * a := fun a b => he'.1.is_comm.comm a b
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [hfapp] at hab
    have h1 : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have ha1 : (a : X) = 1 := hdisj _ a.2 (h1 ▸ E'.inv_mem b.2)
    have hb1 : (b : X) = 1 := by rw [ha1, one_mul] at hab; exact hab
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  set T := f.range with hT
  have hTA : T ≤ A := by
    rintro _ ⟨x, rfl⟩
    rw [hfapp]
    exact A.mul_mem (hE x.1.2) (hE' x.2.2)
  have hTel : IsElemAbelian 3 T := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, rfl⟩⟩ := b
      apply Subtype.ext
      change f x * f y = f y * f x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (hEc _ _) (hEc' _ _)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Prod.ext (Subtype.ext (he.2 _ x.1.2)) (Subtype.ext (he'.2 _ x.2.2))
      rw [this, map_one]
  have hTc : Nat.card T = 3 ^ 4 := by
    rw [hT, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hc, hc']; norm_num
  exact le_csSup (PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three A)
    ⟨T, hTA, hTel, hTc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
