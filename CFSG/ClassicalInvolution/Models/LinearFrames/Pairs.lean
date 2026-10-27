module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Generic.LineModelLinear

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat)
open scoped MatrixGroups

section Commuting

variable {K : Type} [Field K] {n : ℕ}

theorem commutes_Lc_of_disjoint (h2 : (2 : K) ≠ 0) {T T' : Pair n} (hd : Disjoint T.1 T'.1) :
    Commutes (Lc K T) (Lc K T') := by
  intro x hx y hy
  refine mul_comm_of_inf_eq_bot h2 (zMat_mul_self T.1) (zMat_mul_self T'.1)
    (zMat_mul_comm _ _) ?_ hx hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_eigSpace_zMat_neg_one h2, mem_eigSpace_zMat_neg_one h2] at hv
  rw [Submodule.mem_bot]
  funext a
  by_cases ha : a ∈ T.1
  · exact hv.2 a (Finset.disjoint_left.mp hd ha)
  · exact hv.1 a ha

theorem not_commutes_Lc_overlap (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Commutes (Lc K (⟨{i, j}, Finset.card_pair hij⟩ : Pair n))
      (Lc K (⟨{j, k}, Finset.card_pair hjk⟩ : Pair n)) := by
  intro hc
  let T : Pair n := ⟨{i, j}, Finset.card_pair hij⟩
  let T' : Pair n := ⟨{j, k}, Finset.card_pair hjk⟩
  have hne : zElt K T ≠ zElt K T' := by
    intro h
    have := congrArg Subtype.val (zElt_injective h2 h)
    have hi : i ∈ T.1 := by simp [T]
    rw [this] at hi
    simp only [T', Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · exact hij h
    · exact hik h
  have hcomm : Commute (zElt K T) (zElt K T') :=
    signGroup_comm (zElt_mem_signGroup T) (zElt_mem_signGroup T')
  have hL := isLongRootSL2_Lc h2 (by omega : 2 ≤ n) T
  have hL' := isLongRootSL2_Lc h2 (by omega : 2 ≤ n) T'
  rcases lemma_6_5 h2 hn hL hL' hcomm hne with ⟨-, -, -, hV⟩ | ⟨hnot, -⟩
  · have hv : (Pi.single j 1 : Fin n → K) ∈ minusSpace (zElt K T) ⊓ minusSpace (zElt K T') :=
      ⟨single_mem_eigSpace_zMat h2 (by simp [T]) 1, single_mem_eigSpace_zMat h2 (by simp [T']) 1⟩
    rw [hV, Submodule.mem_bot] at hv
    have := congr_fun hv j
    simp at this
  · exact hnot (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx _ hL'.mem)

theorem isPairFamily_Lc (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) : IsPairFamily (Lc K (n := n)) where
  inj := Lc_injective h2 (by omega)
  commutes_iff := by
    intro T T' hne
    constructor
    · intro hc
      by_contra hnd
      rcases pair_disjoint_or_share_one T.2 T'.2 (fun h => hne (Subtype.ext h)) with
        hd | ⟨i, j, k, hij, hjk, hik, h1, h1'⟩
      · exact hnd hd
      · have e1 : T = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext h1
        have e2 : T' = ⟨{j, k}, Finset.card_pair hjk⟩ := Subtype.ext h1'
        rw [e1, e2] at hc
        exact not_commutes_Lc_overlap h2 hn hij hjk hik hc
    · exact commutes_Lc_of_disjoint h2

end Commuting

section A2

variable {K : Type} [Field K] {n : ℕ}

@[expose] def chart3 (hn : 3 ≤ n) (g : SL(n, K)) : SL(3, K) →* SL(n, K) :=
  (MulAut.conj g).toMonoidHom.comp (blockSL K n 3 0 (by omega))

theorem chart3_apply (hn : 3 ≤ n) (g : SL(n, K)) (x : SL(3, K)) :
    chart3 hn g x = g * blockSL K n 3 0 (by omega) x * g⁻¹ := rfl

theorem chart3_injective (hn : 3 ≤ n) (g : SL(n, K)) : Function.Injective (chart3 hn g) :=
  (MulAut.conj g).injective.comp (blockSL_injective _)

theorem map_B12_chart3 (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {g : SL(n, K)} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ) {T : Pair n}
    (hT : T.1 = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩}) :
    (B12 K).map (chart3 hn g) = Lc K T := by
  rw [Lc_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT, chart3, ← Subgroup.map_map,
    B12_map_blockSL hn]

theorem map_B23_chart3 (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {g : SL(n, K)} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ) {T : Pair n}
    (hT : T.1 = {τ ⟨1, by omega⟩, τ ⟨1 + 1, by omega⟩}) :
    (B23 K).map (chart3 hn g) = Lc K T := by
  rw [Lc_eq_map_conj h2 hg (by omega : 1 + 2 ≤ n) hT, chart3, ← Subgroup.map_map,
    B23_map_blockSL hn]

theorem conj_blockSL3_eq (hn : 3 ≤ n) {e : SL(n, K)} (he : e ∈ signGroup K n) :
    ∃ a b : Kˣ, ∀ x : SL(3, K), e * blockSL K n 3 0 (by omega) x * e⁻¹ =
      blockSL K n 3 0 (by omega) (diagConj3 a b x) := by
  have h22 : ent e ⟨2, by omega⟩ * ent e ⟨2, by omega⟩ = 1 := ent_mul_self he _
  have hsq : ∀ c : Fin n, ent e c * ent e ⟨2, by omega⟩ * (ent e c * ent e ⟨2, by omega⟩) = 1 :=
    fun c => by
      calc ent e c * ent e ⟨2, by omega⟩ * (ent e c * ent e ⟨2, by omega⟩)
          = (ent e c * ent e c) * (ent e ⟨2, by omega⟩ * ent e ⟨2, by omega⟩) := by ring
        _ = 1 := by rw [ent_mul_self he, h22, one_mul]
  refine ⟨signUnit _ (hsq ⟨0, by omega⟩), signUnit _ (hsq ⟨1, by omega⟩), fun x => ?_⟩
  apply Subtype.ext
  rw [inv_eq_self_of_mem he, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL, coe_eq_diagonal he, diagonal_conj_blockMat_three hn (ent_mul_self he), coe_blockSL,
    coe_diagConj3]
  simp only [coe_signUnit, coe_signUnit_inv]
  rw [diagonal_three_conj_eq h22]

theorem diagAction_chart3 (hn : 3 ≤ n) {g : SL(n, K)} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ) :
    DiagAction (chart3 hn g) (signGroup K n) := by
  intro e he
  obtain ⟨he', -⟩ := conj_mem_signGroup hg he
  obtain ⟨a, b, hab⟩ := conj_blockSL3_eq hn he'
  refine ⟨a, b, fun x => ?_⟩
  have := hab x
  rw [chart3_apply, chart3_apply, ← this]
  group

theorem linearA2Pair_Lc_overlap (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    LinearA2Pair K (signGroup K n) (Lc K (⟨{i, j}, Finset.card_pair hij⟩ : Pair n))
      (Lc K (⟨{j, k}, Finset.card_pair hjk⟩ : Pair n)) := by
  obtain ⟨τ, h0, h1, h2'⟩ := exists_perm_triple hn hij hjk hik
  let g : SL(n, K) := ⟨monoMat K τ, det_monoMat (by omega) τ⟩
  have hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ := isMonomialFor_monoMat τ
  refine linearA2Pair_of_diagAction (θ := chart3 hn g) ?_ ?_ ?_ (diagAction_chart3 hn hg)
    (inSigma_Lc h2 hn _) (inSigma_Lc h2 hn _)
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr (chart3_injective hn g)]
    exact bot_le
  · refine map_B12_chart3 h2 hn hg ?_
    show ({i, j} : Finset (Fin n)) = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩}
    rw [h0, show τ ⟨0 + 1, by omega⟩ = j from h1]
  · refine map_B23_chart3 h2 hn hg ?_
    show ({j, k} : Finset (Fin n)) = {τ ⟨1, by omega⟩, τ ⟨1 + 1, by omega⟩}
    rw [h1, show τ ⟨1 + 1, by omega⟩ = k from h2']

end A2

section FrameProperties

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem a2Dichotomy_coordSet (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn : 4 ≤ n) :
    A2Dichotomy (signGroup K n) (coordSet K n) := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  refine a2Dichotomy_of_linear (toralFrame hodd h5 hn) ?_
  rintro _ ⟨T, rfl⟩ _ ⟨T', rfl⟩ hne
  have hTT' : T ≠ T' := fun h => hne (by rw [h])
  rcases pair_disjoint_or_share_one T.2 T'.2 (fun h => hTT' (Subtype.ext h)) with
    hd | ⟨i, j, k, hij, hjk, hik, h1, h1'⟩
  · exact Or.inl (commutes_Lc_of_disjoint h2 hd)
  · have e1 : T = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext h1
    have e2 : T' = ⟨{j, k}, Finset.card_pair hjk⟩ := Subtype.ext h1'
    rw [e1, e2]
    exact Or.inr (Or.inl (linearA2Pair_Lc_overlap h2 (by omega) hij hjk hik))

theorem nonCommConnected_coordSet (hodd : Odd (Nat.card K)) (hn : 3 ≤ n) :
    NonCommConnected (coordSet K n) :=
  (isPairFamily_Lc (two_ne_zero_of_odd_natCard hodd) hn).nonCommConnected (by omega)

theorem fibreLE2_coordSet (hodd : Odd (Nat.card K)) (hn : 2 ≤ n) :
    FibreLE2 (coordSet K n) := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  rintro z _ ⟨T, rfl⟩ _ ⟨T', rfl⟩ M _ hz hz' -
  left
  have e : zElt K T = zElt K T' :=
    (isUniqueInvolution_Lc h2 hn T).eq hz |>.trans ((isUniqueInvolution_Lc h2 hn T').eq hz').symm
  rw [zElt_injective h2 e]

theorem ncard_coordSet (hodd : Odd (Nat.card K)) (hn : 3 ≤ n) :
    (coordSet K n).ncard = n.choose 2 :=
  (isPairFamily_Lc (two_ne_zero_of_odd_natCard hodd) hn).ncard_range

end FrameProperties

end CFSG.ClassicalInvolution.Models
