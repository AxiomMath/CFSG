module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexBlockOK
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem symp_blockOK_mono {H H' S : Subgroup G} (hH : H' ≤ H) (h : BlockOK H S) : BlockOK H' S :=
  fun g hg => h g (hH hg)

theorem symp_blockOK_map (e : G' →* G) (he : Function.Injective e) {H S : Subgroup G'}
    (h : BlockOK H S) : BlockOK (H.map e) (S.map e) := by
  rintro _ ⟨x, hx, rfl⟩ hn k hk
  have hn' : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro s hs
    obtain ⟨y, hy, hyx⟩ := hn (e s) ⟨s, hs, rfl⟩
    have : e (x * s * x⁻¹) = e y := by
      rw [map_mul, map_mul, map_inv]
      exact hyx.symm
    rw [he this]
    exact hy
  have hk' : ∀ s ∈ S, x ^ (3 ^ k) * s * (x ^ (3 ^ k))⁻¹ = s := by
    intro s hs
    apply he
    have := hk (e s) ⟨s, hs, rfl⟩
    simpa only [map_mul, map_pow, map_inv] using this
  rcases h x hx hn' k hk' with ⟨p, hp, hpe⟩ | ⟨E, hES, hE, hcard⟩
  · left
    refine ⟨e p, ⟨p, hp, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := congrArg e (hpe s hs)
    simpa only [map_mul, map_inv] using this
  · right
    refine ⟨E.map e, Subgroup.map_mono hES, CFSG.SectionRank.isElemAbelian_map hE e, ?_⟩
    rw [Subgroup.card_map_of_injective he]
    exact hcard

end Transport

section Residual

variable {K : Type} [Field K]

theorem symp_sq_mem_commutator_two [Finite K] (hK : Nat.card K = 2) (x : StatedSp 2 K) :
    x ^ 2 ∈ commutator (StatedSp 2 K) := by
  classical
  set A : Subgroup (StatedSp 2 K) := commutator (StatedSp 2 K)
  haveI : A.Normal := Subgroup.commutator_normal ⊤ ⊤
  have h720 : Nat.card (StatedSp 2 K) = 720 := by
    rw [SymplecticFlag.card_statedSp_two, hK]
    norm_num
  obtain ⟨-, h360⟩ := spFlag_spFour_comm hK
  have hAc : 360 ≤ Nat.card A := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥A)
    rw [h360] at h
    have : 0 < Nat.card (Subgroup.center ↥A) := Nat.card_pos
    nlinarith
  have hidx : A.index = 1 ∨ A.index = 2 := by
    have h := A.card_mul_index
    rw [h720] at h
    have h1 : A.index ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h
      omega
    by_contra hne
    have h3 : 3 ≤ A.index := by omega
    nlinarith
  rcases hidx with h1 | h2
  · have := A.pow_index_mem x
    rw [h1, pow_one] at this
    exact A.pow_mem this 2
  · have := A.pow_index_mem x
    rwa [h2] at this

theorem symp_blockOK_statedSp_two [Finite K] (hK : Nat.card K = 2) :
    BlockOK (⊤ : Subgroup (StatedSp 2 K)) (commutator (StatedSp 2 K)) := by
  intro g _ _ k hk
  left
  obtain ⟨c, hc⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hq : g ^ 2 ∈ commutator (StatedSp 2 K) := symp_sq_mem_commutator_two hK g
  have hqc : (g ^ 2) ^ c ∈ commutator (StatedSp 2 K) := Subgroup.pow_mem _ hq c
  have hg : g = ((g ^ 2) ^ c)⁻¹ * g ^ (3 ^ k) := by
    rw [hc, pow_succ g (2 * c), pow_mul]
    group
  refine ⟨((g ^ 2) ^ c)⁻¹, Subgroup.inv_mem _ hqc, fun s hs => ?_⟩
  have h1 := hk s hs
  conv_lhs => rw [hg]
  calc ((g ^ 2) ^ c)⁻¹ * g ^ 3 ^ k * s * (((g ^ 2) ^ c)⁻¹ * g ^ 3 ^ k)⁻¹
      = ((g ^ 2) ^ c)⁻¹ * (g ^ 3 ^ k * s * (g ^ 3 ^ k)⁻¹) * ((g ^ 2) ^ c)⁻¹⁻¹ := by group
    _ = ((g ^ 2) ^ c)⁻¹ * s * ((g ^ 2) ^ c)⁻¹⁻¹ := by rw [h1]

theorem symp_blockOK_statedSp [Finite K] [CharP K 2] (m : ℕ)
    (hq : CFSG.Open.IsQuasisimple (commutator (StatedSp m K))) :
    BlockOK (⊤ : Subgroup (StatedSp m K)) (commutator (StatedSp m K)) := by
  have hK := spFlag_card_eq_two_or_four_le (K := K)
  rcases spFlag_res_cases m K with hs | ⟨rfl, hK2⟩ | hperf | hbad
  · exfalso
    have : Group.IsSolvable (StatedSp m K) := spFlag_isSolvable_Sp hs
    have : Group.IsSolvable (commutator (StatedSp m K)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    exact spFlag_not_isSolvable hq this
  · exact symp_blockOK_statedSp_two hK2
  · have hperf' : commutator (StatedSp m K) = ⊤ :=
      (spFlag_isQuasisimple_Sp hperf.1 hperf.2).1
    intro g _ _ k _
    left
    exact ⟨g, hperf' ▸ Subgroup.mem_top g, fun s _ => rfl⟩
  · omega

end Residual

section Blocks

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {I : Set ℕ}

theorem blockOK_spFlagLeviBlock (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) (j : Fin (r + 1))
    (hq : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j)) :
    BlockOK (spFlagLeviCoord hI htI j).range (spFlagLeviBlock (K := K) hI t j) := by
  by_cases hj0 : (j : ℕ) = 0
  · have hq' : CFSG.Open.IsQuasisimple (commutator (StatedSp (r - t) K)) :=
      isQuasisimple_of_mulEquiv (spFlagLeviBlockZeroEquiv hI t hj0) hq
    rw [spFlagLeviBlock_of_eq_zero hI hj0, spFlagLeviCoord_of_eq_zero hI htI hj0]
    refine symp_blockOK_mono ?_ (symp_blockOK_map (spFlagResEmb t) (spFlagResEmb_injective t)
      (symp_blockOK_statedSp (r - t) hq'))
    rw [MonoidHom.range_comp]
    exact Subgroup.map_mono le_top
  by_cases hj : (j : ℕ) ∈ I
  · have hm := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (spFlagLeviBlockMemEquiv hI t hj0 hj) hq)
    rw [spFlagLeviBlock_of_mem hI hj0 hj, spFlagLeviCoord_of_mem hI htI hj0 hj,
      MonoidHom.range_comp, MonoidHom.range_comp]
    exact symp_blockOK_mono (Subgroup.map_mono le_top)
      (symp_blockOK_map (spFlagCutEmb (spFlagPrev I j) j (hI j hj))
        (spFlagCutEmb_injective _ _ _) (blockOK_gl_sl _ hm))
  · exfalso
    rw [spFlagLeviBlock_of_not_mem hI hj0 hj] at hq
    exact spFlag_not_isSolvable hq (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)

end Blocks

theorem leviInnOn_symp (hGA : GriessAllModelsStatement) :
    LeviInnOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB hLn _ _ hrk
  haveI := hLn
  obtain ⟨r, K, _, _, _, -, ⟨φ⟩⟩ :=
    exists_mulEquiv_statedSp_of_idxB (oddCenterRest_of_griess hGA) hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hker : ρ.toMonoidHom.ker ≤ Subgroup.center (StatedSp r K) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective]
    exact bot_le
  refine leviInnAt_of_levi_data (K := StatedSp r K)
    (G := fun _ : Fin (r + 1) => StatedSp r K) hCP.parab.1 ρ.toMonoidHom ρ.surjective hker
    (flagStabilizer r K I) hρ.symm (spFlagLeviBlock hI' t)
    (fun j => (spFlagLeviCoord hI' htI j).range) (spFlagLeviHom hI' htI)
    (isPGroup_ker_spFlagLeviHom hI' htI fun i hi => (hI i hi).1)
    (pi_le_range_spFlagLeviHom hI' htI hmax) (commutator_range_spFlagLeviHom_le hI' htI)
    (spFlagLeviBlock_cases hI' t) (fun x j => ⟨x, rfl⟩)
    (fun j hq => blockOK_spFlagLeviBlock hI' htI j hq)
    (fun j E _ _ _ x hρx _ => ?_) hrk
  exact Subtype.ext (ρ.injective (hρx.trans (map_one ρ.toMonoidHom).symm))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
