module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParam
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesBlocks
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore ordSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono mem_modelToG symm_mem_modelToG)
open scoped MatrixGroups

section Small

variable {F : Type} [Field F] {n : ℕ}

theorem eq_one_of_mem_center_siegelLevi_of_mem_siegelBlock {B : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ B) {z : siegelLevi F n} (hz : z ∈ center (siegelLevi F n))
    (hzB : (z : StatedSp n F) ∈ siegelBlock F B) : z = 1 := by
  obtain ⟨A, hA, hzA⟩ := hzB
  have hAc : A ∈ center (SL(n, F)) := by
    rw [mem_center_iff]
    intro C
    have h := mem_center_iff.1 hz ⟨leviEmbedSL F n C, C, rfl⟩
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    rw [← hzA, ← map_mul, ← map_mul] at h'
    exact leviEmbedSL_injective h'
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
  have hjj : (A : Matrix (Fin n) (Fin n) F) j j = 1 := by
    rw [hA j j (Or.inl hj), Matrix.one_apply_eq]
  have hr1 : r = 1 := by
    rw [← hr, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hjj
    exact hjj
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  apply Subtype.ext
  rw [← hzA, hA1, map_one]
  rfl

theorem natCard_siegelBlock [Finite F] {B : Finset (Fin n)} (hB : 1 ≤ B.card) :
    Nat.card (siegelBlock F B) = ordSL B.card (Nat.card F) := by
  rw [← Nat.card_congr (siegelBlockEquiv (F := F) B).toEquiv]
  have h := F4Pilot.natCard_blockSpecialLinear (F := F) (n := B.card)
    (I := Finset.univ) (by simpa using hB)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  exact Nat.card_congr ((Subgroup.topEquiv).symm.toEquiv.trans
    (MulEquiv.subgroupCongr (by
      ext x
      simp only [mem_top, true_iff]
      intro i j hij
      simp at hij)).toEquiv)

theorem card_pair_succ {j : Fin n} (h : j.val + 1 < n) :
    ({j, ⟨j.val + 1, h⟩} : Finset (Fin n)).card = 2 := by
  rw [Finset.card_pair]
  intro e
  have := congrArg Fin.val e
  simp at this

end Small

section Field

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

theorem SiegelFieldParam.stringCore_eq_map (P : SiegelFieldParam e t ι σ) (hK : 4 ≤ Nat.card K)
    {B : Finset (Fin n)} (hB : 2 ≤ B.card) :
    stringCore e B = ((siegelBlock F B).subgroupOf (siegelLevi F n)).map P.Φ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  rw [stringCore, torusCore_eq_map_of_conjDiagSub e ι diagSp_mem_normalizer_siegelLevi
    (modelToG_mono e (siegelTorus_le_stringTorusSp B)) P.Φ P.ker_le P.range_eq
    (fun s _ x => P.N2 s (mem_top s) x),
    perfectCore_siegelLevi_inf_centralizer_stringTorus ι hκ
      (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hB (le_card_of_ringHom ι hK))]

theorem SiegelFieldParam.pieceCore_singleton_eq_map (P : SiegelFieldParam e t ι σ)
    (hK : 4 ≤ Nat.card K) {j : Fin n} (h : j.val + 1 < n) :
    pieceCore e {j} =
      ((siegelBlock F {j, ⟨j.val + 1, h⟩}).subgroupOf (siegelLevi F n)).map P.Φ := by
  rw [pieceCore_singleton_eq_stringCore e h]
  exact P.stringCore_eq_map hK (card_pair_succ h).ge

theorem SiegelFieldParam.stringCore_le_centralizer_stringCore (P : SiegelFieldParam e t ι σ)
    (hK : 4 ≤ Nat.card K) {B B' : Finset (Fin n)} (hBB' : Disjoint B B') (hB : 2 ≤ B.card)
    (hB' : 2 ≤ B'.card) : stringCore e B ≤ centralizer (stringCore e B' : Set G) := by
  rw [P.stringCore_eq_map hK hB, P.stringCore_eq_map hK hB']
  exact map_subgroupOf_le_centralizer_of_commute
    (fun x hx y hy => commute_of_mem_siegelBlock_of_disjoint hBB' hx hy) P.Φ

omit [Finite G] [Finite F] in
theorem SiegelFieldParam.injective_siegelBlock (P : SiegelFieldParam e t ι σ)
    {B : Finset (Fin n)} {j : Fin n} (hj : j ∉ B) :
    Function.Injective (P.Φ.comp ((siegelBlock F B).subgroupOf (siegelLevi F n)).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact Subtype.ext (eq_one_of_mem_center_siegelLevi_of_mem_siegelBlock hj
    (P.ker_le ((MonoidHom.mem_ker).2 hx)) (mem_subgroupOf.mp x.2))

theorem SiegelFieldParam.natCard_pieceCore_singleton (P : SiegelFieldParam e t ι σ)
    (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n) {j : Fin n} (h : j.val + 1 < n) :
    Nat.card (pieceCore e {j}) = ordSL 2 (Nat.card F) := by
  set B : Finset (Fin n) := {j, ⟨j.val + 1, h⟩} with hBdef
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ B := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ B := fun x _ => hall x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, hBdef, card_pair_succ h] at this
    omega
  rw [P.pieceCore_singleton_eq_map hK h, ← hBdef]
  have hinj := P.injective_siegelBlock hk
  have hrange : (P.Φ.comp ((siegelBlock F B).subgroupOf (siegelLevi F n)).subtype).range =
      ((siegelBlock F B).subgroupOf (siegelLevi F n)).map P.Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (siegelBlock_le_siegelLevi B)).toEquiv,
    natCard_siegelBlock (by rw [hBdef, card_pair_succ h]; omega), hBdef, card_pair_succ h]

theorem SiegelFieldParam.pieceCore_zero_le_centralizer_pieceCore_two
    (P : SiegelFieldParam e t ι σ) (hK : 4 ≤ Nat.card K) (hn : 4 ≤ n) :
    pieceCore e {(⟨0, by omega⟩ : Fin n)} ≤
      centralizer (pieceCore e {(⟨2, by omega⟩ : Fin n)} : Set G) := by
  rw [pieceCore_singleton_eq_stringCore e (j := ⟨0, by omega⟩) (by simp; omega),
    pieceCore_singleton_eq_stringCore e (j := ⟨2, by omega⟩) (by simp; omega)]
  refine P.stringCore_le_centralizer_stringCore hK ?_ (card_pair_succ _).ge (card_pair_succ _).ge
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at ha hb
  omega

end Field

section Swap

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  {n : ℕ} {e : L ≃* StatedSp n K} {t : G}

theorem SiegelSwapParam.stringCore_eq_map (P : SiegelSwapParam e t) (hK : 4 ≤ Nat.card K)
    {B : Finset (Fin n)} (hB : 2 ≤ B.card) :
    stringCore e B = (((siegelBlock K B).subgroupOf (siegelLevi K n)).prod
      ((siegelBlock K B).subgroupOf (siegelLevi K n))).map P.Ψ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  rw [stringCore, torusCore_eq_map_of_conjDiagSub_prod e (RingHom.id K)
    diagSp_mem_normalizer_siegelLevi (modelToG_mono e (siegelTorus_le_stringTorusSp B)) P.Ψ
    P.ker_le P.range_eq (fun s _ x => P.N2 s x),
    perfectCore_siegelLevi_inf_centralizer_stringTorus (RingHom.id K) hκ
      (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hB hK)]

theorem SiegelSwapParam.pieceCore_singleton_eq_map (P : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) {j : Fin n} (h : j.val + 1 < n) :
    pieceCore e {j} = (((siegelBlock K {j, ⟨j.val + 1, h⟩}).subgroupOf (siegelLevi K n)).prod
      ((siegelBlock K {j, ⟨j.val + 1, h⟩}).subgroupOf (siegelLevi K n))).map P.Ψ := by
  rw [pieceCore_singleton_eq_stringCore e h]
  exact P.stringCore_eq_map hK (card_pair_succ h).ge

theorem SiegelSwapParam.stringCore_le_centralizer_stringCore (P : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) {B B' : Finset (Fin n)} (hBB' : Disjoint B B') (hB : 2 ≤ B.card)
    (hB' : 2 ≤ B'.card) : stringCore e B ≤ centralizer (stringCore e B' : Set G) := by
  rw [P.stringCore_eq_map hK hB, P.stringCore_eq_map hK hB']
  exact map_prod_subgroupOf_le_centralizer_of_commute
    (fun x hx y hy => commute_of_mem_siegelBlock_of_disjoint hBB' hx hy) P.Ψ

theorem SiegelSwapParam.pieceCore_zero_le_centralizer_pieceCore_two (P : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) (hn : 4 ≤ n) :
    pieceCore e {(⟨0, by omega⟩ : Fin n)} ≤
      centralizer (pieceCore e {(⟨2, by omega⟩ : Fin n)} : Set G) := by
  rw [pieceCore_singleton_eq_stringCore e (j := ⟨0, by omega⟩) (by simp; omega),
    pieceCore_singleton_eq_stringCore e (j := ⟨2, by omega⟩) (by simp; omega)]
  refine P.stringCore_le_centralizer_stringCore hK ?_ (card_pair_succ _).ge (card_pair_succ _).ge
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at ha hb
  omega

omit [Finite G] [Finite K] in
theorem SiegelSwapParam.injective_siegelBlock (P : SiegelSwapParam e t) {B : Finset (Fin n)}
    {j : Fin n} (hj : j ∉ B) :
    Function.Injective (P.Ψ.comp (((siegelBlock K B).subgroupOf (siegelLevi K n)).prod
      ((siegelBlock K B).subgroupOf (siegelLevi K n))).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hz := P.ker_le ((MonoidHom.mem_ker).2 hx)
  have h1 : (x : siegelLevi K n × siegelLevi K n).1 ∈ center (siegelLevi K n) :=
    mem_center_iff.2 fun g => by
      have := congrArg Prod.fst (mem_center_iff.1 hz (g, 1))
      simpa using this
  have h2 : (x : siegelLevi K n × siegelLevi K n).2 ∈ center (siegelLevi K n) :=
    mem_center_iff.2 fun g => by
      have := congrArg Prod.snd (mem_center_iff.1 hz (1, g))
      simpa using this
  have hx1 := eq_one_of_mem_center_siegelLevi_of_mem_siegelBlock hj h1
    (mem_subgroupOf.mp (mem_prod.1 x.2).1)
  have hx2 := eq_one_of_mem_center_siegelLevi_of_mem_siegelBlock hj h2
    (mem_subgroupOf.mp (mem_prod.1 x.2).2)
  exact Subtype.ext (Prod.ext hx1 hx2)

theorem SiegelSwapParam.natCard_pieceCore_singleton (P : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n) {j : Fin n} (h : j.val + 1 < n) :
    Nat.card (pieceCore e {j}) = ordSL 2 (Nat.card K) ^ 2 := by
  set B : Finset (Fin n) := {j, ⟨j.val + 1, h⟩} with hBdef
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ B := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ B := fun x _ => hall x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, hBdef, card_pair_succ h] at this
    omega
  rw [P.pieceCore_singleton_eq_map hK h, ← hBdef]
  have hinj := P.injective_siegelBlock hk
  have hrange : (P.Ψ.comp (((siegelBlock K B).subgroupOf (siegelLevi K n)).prod
      ((siegelBlock K B).subgroupOf (siegelLevi K n))).subtype).range =
      (((siegelBlock K B).subgroupOf (siegelLevi K n)).prod
        ((siegelBlock K B).subgroupOf (siegelLevi K n))).map P.Ψ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (subgroupOfEquivOfLe (siegelBlock_le_siegelLevi B)).toEquiv,
    natCard_siegelBlock (by rw [hBdef, card_pair_succ h]; omega), hBdef, card_pair_succ h, sq]

end Swap

end CFSG.SeitzReduction.SymplecticPilot
