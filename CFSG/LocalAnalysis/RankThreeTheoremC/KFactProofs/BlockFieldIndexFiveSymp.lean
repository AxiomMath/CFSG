module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveBlockOK
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexSymp
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem symp_blockOK_monoP (p : ℕ) {H H' S : Subgroup G} (hH : H' ≤ H) (h : BlockOKP p H S) :
    BlockOKP p H' S :=
  fun g hg => h g (hH hg)

theorem symp_blockOK_mapP (p : ℕ) (e : G' →* G) (he : Function.Injective e) {H S : Subgroup G'}
    (h : BlockOKP p H S) : BlockOKP p (H.map e) (S.map e) := by
  rintro _ ⟨x, hx, rfl⟩ hn k hk
  have hn' : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro s hs
    obtain ⟨y, hy, hyx⟩ := hn (e s) ⟨s, hs, rfl⟩
    have : e (x * s * x⁻¹) = e y := by
      rw [map_mul, map_mul, map_inv]
      exact hyx.symm
    rw [he this]
    exact hy
  have hk' : ∀ s ∈ S, x ^ (p ^ k) * s * (x ^ (p ^ k))⁻¹ = s := by
    intro s hs
    apply he
    have := hk (e s) ⟨s, hs, rfl⟩
    simpa only [map_mul, map_pow, map_inv] using this
  rcases h x hx hn' k hk' with ⟨u, hu, hue⟩ | ⟨E, hES, hE, hcard⟩
  · left
    refine ⟨e u, ⟨u, hu, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := congrArg e (hue s hs)
    simpa only [map_mul, map_inv] using this
  · right
    refine ⟨E.map e, Subgroup.map_mono hES, CFSG.SectionRank.isElemAbelian_map hE e, ?_⟩
    rw [Subgroup.card_map_of_injective he]
    exact hcard

end Transport

section Residual

variable {K : Type} [Field K]

theorem symp_blockOK_statedSp_twoP (p : ℕ) [OddPrime p] [Finite K] (hK : Nat.card K = 2) :
    BlockOKP p (⊤ : Subgroup (StatedSp 2 K)) (commutator (StatedSp 2 K)) := by
  intro g _ _ k hk
  left
  obtain ⟨c, hc⟩ := OddPrime.odd_pow p k
  have hq : g ^ 2 ∈ commutator (StatedSp 2 K) := symp_sq_mem_commutator_two hK g
  have hqc : (g ^ 2) ^ c ∈ commutator (StatedSp 2 K) := Subgroup.pow_mem _ hq c
  have hg : g = ((g ^ 2) ^ c)⁻¹ * g ^ (p ^ k) := by
    rw [hc, pow_succ g (2 * c), pow_mul]
    group
  refine ⟨((g ^ 2) ^ c)⁻¹, Subgroup.inv_mem _ hqc, fun s hs => ?_⟩
  have h1 := hk s hs
  conv_lhs => rw [hg]
  calc ((g ^ 2) ^ c)⁻¹ * g ^ (p ^ k) * s * (((g ^ 2) ^ c)⁻¹ * g ^ (p ^ k))⁻¹
      = ((g ^ 2) ^ c)⁻¹ * (g ^ (p ^ k) * s * (g ^ (p ^ k))⁻¹) * ((g ^ 2) ^ c)⁻¹⁻¹ := by
        group
    _ = ((g ^ 2) ^ c)⁻¹ * s * ((g ^ 2) ^ c)⁻¹⁻¹ := by rw [h1]

theorem symp_blockOK_statedSpP (p : ℕ) [OddPrime p] [Finite K] [CharP K 2] (m : ℕ)
    (hq : CFSG.Open.IsQuasisimple (commutator (StatedSp m K))) :
    BlockOKP p (⊤ : Subgroup (StatedSp m K)) (commutator (StatedSp m K)) := by
  have hK := spFlag_card_eq_two_or_four_le (K := K)
  rcases spFlag_res_cases m K with hs | ⟨rfl, hK2⟩ | hperf | hbad
  · exfalso
    have : Group.IsSolvable (StatedSp m K) := spFlag_isSolvable_Sp hs
    have : Group.IsSolvable (commutator (StatedSp m K)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    exact spFlag_not_isSolvable hq this
  · exact symp_blockOK_statedSp_twoP p hK2
  · have hperf' : commutator (StatedSp m K) = ⊤ :=
      (spFlag_isQuasisimple_Sp hperf.1 hperf.2).1
    intro g _ _ k _
    left
    exact ⟨g, hperf' ▸ Subgroup.mem_top g, fun s _ => rfl⟩
  · omega

end Residual

section Blocks

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {I : Set ℕ}

theorem blockOK_spFlagLeviBlockP (p : ℕ) [OddPrime p] (hI : ∀ i ∈ I, i ≤ r) {t : ℕ}
    (htI : t ∈ I) (j : Fin (r + 1))
    (hq : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j)) :
    BlockOKP p (spFlagLeviCoord hI htI j).range (spFlagLeviBlock (K := K) hI t j) := by
  by_cases hj0 : (j : ℕ) = 0
  · have hq' : CFSG.Open.IsQuasisimple (commutator (StatedSp (r - t) K)) :=
      isQuasisimple_of_mulEquiv (spFlagLeviBlockZeroEquiv hI t hj0) hq
    rw [spFlagLeviBlock_of_eq_zero hI hj0, spFlagLeviCoord_of_eq_zero hI htI hj0]
    refine symp_blockOK_monoP p ?_ (symp_blockOK_mapP p (spFlagResEmb t)
      (spFlagResEmb_injective t) (symp_blockOK_statedSpP p (r - t) hq'))
    rw [MonoidHom.range_comp]
    exact Subgroup.map_mono le_top
  by_cases hj : (j : ℕ) ∈ I
  · have hm := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (spFlagLeviBlockMemEquiv hI t hj0 hj) hq)
    rw [spFlagLeviBlock_of_mem hI hj0 hj, spFlagLeviCoord_of_mem hI htI hj0 hj,
      MonoidHom.range_comp, MonoidHom.range_comp]
    exact symp_blockOK_monoP p (Subgroup.map_mono le_top)
      (symp_blockOK_mapP p (spFlagCutEmb (spFlagPrev I j) j (hI j hj))
        (spFlagCutEmb_injective _ _ _) (blockOK_gl_slP (p := p) _ hm))
  · exfalso
    rw [spFlagLeviBlock_of_not_mem hI hj0 hj] at hq
    exact spFlag_not_isSolvable hq (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)

end Blocks

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
