module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem24
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20Stmts

public section

namespace CFSG.Quasithin.H13
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

open Lem24

theorem lem12224Block_of_F4
    (h1222 : Stmt12_2_2_F4) : Lem12224Block_F4 := by
  intro G _ _ T L V H P U I h n p hyp hNE hchain
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨hHs, -, hn, hV, -, htop, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, ⟨hcomm, htr⟩,
    hUO, -, -, -, -, -, -, -, hQU⟩ := hchain
  have hn3 : 3 ≤ n := by omega

  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hV2' : ∀ w : ↥V, w ^ 2 = 1 := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    simpa using congrArg Subtype.val (hV2' ⟨v, hv⟩)
  obtain ⟨e⟩ := nonempty_coords hVc hV2 hV

  have hUT : U ≤ T := hUO.trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hHs.1.1))
  have hQU' : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ u ∈ U, ⁅q, u⁆ ∈ V := fun q hq u hu =>
    (hQU (Subgroup.commutator_mem_commutator hq hu)).2
  have hA : ((U ⊓ V).subgroupOf V).index = 2 := hidx
  have hA1 : (U ⊓ V).subgroupOf V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.index_bot, hV] at hA
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have hUV : autOn U V ≠ ⊥ := by
    rw [htr]
    exact transvAxis_ne_bot hV2' hA a.2 (fun h => ha1 (Subtype.ext h))

  have hUL := blockU_eq hyp hVT hTV hred hn3 e htop hUT hQU' hUV
  have hZ := inf_centralizer_eq_bot (le_normalizer_of_hyp1223 hyp) (by omega) e htop
  have hCL := centralizer_le_pCoreOf hyp hred hn3 e htop
  have hV1 : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hV
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  exact ⟨isShort2 hyp hVT hred hUL hZ hV1, isMatrixBlockType hyp hred e htop hCL hUL hZ⟩
end CFSG.Quasithin.H13
