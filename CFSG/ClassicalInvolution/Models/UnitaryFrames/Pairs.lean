module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
public import CFSG.ClassicalInvolution.Generic.LineModelUnitary
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

section CommutingU

theorem commutes_LcU_of_disjoint (h2 : (2 : K) ≠ 0) {T T' : Pair n} (hd : Disjoint T.1 T'.1) :
    Commutes (LcU K p f T) (LcU K p f T') := by
  intro x hx y hy
  refine mul_comm_of_inf_eq_bot_su h2 (i₁ := zEltU K p f T) (i₂ := zEltU K p f T')
    (zMat_mul_self T.1) (zMat_mul_self T'.1) (zMat_mul_comm _ _) ?_ hx hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have h1 := (mem_eigSpace_zMat_neg_one h2).mp hv.1
  have h3 := (mem_eigSpace_zMat_neg_one h2).mp hv.2
  rw [Submodule.mem_bot]
  funext a
  by_cases ha : a ∈ T.1
  · exact h3 a (Finset.disjoint_left.mp hd ha)
  · exact h1 a ha

theorem not_commutes_LcU_overlap (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Commutes (LcU K p f (⟨{i, j}, Finset.card_pair hij⟩ : Pair n))
      (LcU K p f (⟨{j, k}, Finset.card_pair hjk⟩ : Pair n)) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  intro hc
  let T : Pair n := ⟨{i, j}, Finset.card_pair hij⟩
  let T' : Pair n := ⟨{j, k}, Finset.card_pair hjk⟩
  have hne : zEltU K p f T ≠ zEltU K p f T' := by
    intro h
    have := zMat_inj h2 (congrArg suMat h)
    have hi : i ∈ T.1 := by simp [T]
    rw [this] at hi
    simp only [T', Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · exact hij h
    · exact hik h
  have hcomm : Commute (zEltU K p f T) (zEltU K p f T') :=
    signGroupU_comm (zEltU_mem_signGroupU T) (zEltU_mem_signGroupU T')
  have hL := isLongRootSU2_LcU (p := p) (f := f) h2 (by omega : 2 ≤ n) T
  have hL' := isLongRootSU2_LcU (p := p) (f := f) h2 (by omega : 2 ≤ n) T'
  rcases lemma_6_5_su hK hp hn hL hL' hcomm hne with ⟨-, -, -, hV⟩ | ⟨hnot, -⟩
  · have hv : (Pi.single j 1 : Fin n → K) ∈
        minusSpaceSU (zEltU K p f T) ⊓ minusSpaceSU (zEltU K p f T') :=
      ⟨single_mem_eigSpace_zMat h2 (by simp [T]) 1, single_mem_eigSpace_zMat h2 (by simp [T']) 1⟩
    rw [hV, Submodule.mem_bot] at hv
    have := congr_fun hv j
    simp at this
  · exact hnot (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx _ hL'.mem)

theorem isPairFamily_LcU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n) :
    IsPairFamily (LcU K p f (n := n)) where
  inj := LcU_injective hK hp (by omega)
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
        exact not_commutes_LcU_overlap hK hp hn hij hjk hik hc
    · exact commutes_LcU_of_disjoint (two_ne_zero_of_charP_ne_two hp)

end CommutingU

section A2U

@[expose] noncomputable def chart3U (hn : 3 ≤ n) (g : Su K p f n) : Su K p f 3 →* Su K p f n :=
  (MulAut.conj g).toMonoidHom.comp (blockEmb K p f n 3 0 (by omega))

theorem chart3U_apply (hn : 3 ≤ n) (g : Su K p f n) (x : Su K p f 3) :
    chart3U hn g x = g * blockEmb K p f n 3 0 (by omega) x * g⁻¹ := rfl

theorem chart3U_injective (hn : 3 ≤ n) (g : Su K p f n) : Function.Injective (chart3U hn g) :=
  (MulAut.conj g).injective.comp (blockEmb_injective _)

theorem map_B12_chart3U (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {g : Su K p f n}
    {τ : Equiv.Perm (Fin n)} (hg : IsMonomialFor (suMat g) τ) {T : Pair n}
    (hT : T.1 = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩}) :
    (B12 K p f).map (chart3U hn g) = LcU K p f T := by
  rw [LcU_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT, chart3U, ← Subgroup.map_map,
    B12_map_blockEmb hn]

theorem map_B23_chart3U (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {g : Su K p f n}
    {τ : Equiv.Perm (Fin n)} (hg : IsMonomialFor (suMat g) τ) {T : Pair n}
    (hT : T.1 = {τ ⟨1, by omega⟩, τ ⟨1 + 1, by omega⟩}) :
    (B23 K p f).map (chart3U hn g) = LcU K p f T := by
  rw [LcU_eq_map_conj h2 hg (by omega : 1 + 2 ≤ n) hT, chart3U, ← Subgroup.map_map,
    B23_map_blockEmb hn]

@[expose] noncomputable def signNorm (x : K) (hx : x * x = 1) (hσ : unitaryInvolution K p f x = x) :
    normOne (unitaryInvolution K p f) :=
  ⟨signUnit x hx, by rw [mem_normOne, coe_signUnit, hσ, hx]⟩

theorem coe_signNorm (x : K) (hx : x * x = 1) (hσ : unitaryInvolution K p f x = x) :
    (((signNorm x hx hσ : normOne (unitaryInvolution K p f)) : Kˣ) : K) = x := rfl

theorem coe_signNorm_inv (x : K) (hx : x * x = 1) (hσ : unitaryInvolution K p f x = x) :
    ((((signNorm x hx hσ : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ) : K) = x := rfl

theorem unitaryInvolution_eq_self_of_sign {x : K} (hx : x = 1 ∨ x = -1) :
    unitaryInvolution K p f x = x := by
  rcases hx with rfl | rfl <;> simp

theorem conj_blockEmb3_eq (hK : Nat.card K = (p ^ f) ^ 2) (hn : 3 ≤ n) {e : Su K p f n}
    (he : e ∈ signGroupU K p f n) :
    ∃ a b : normOne (unitaryInvolution K p f), ∀ x : Su K p f 3,
      e * blockEmb K p f n 3 0 (by omega) x * e⁻¹ =
        blockEmb K p f n 3 0 (by omega) (diagConj3U hK a b x) := by
  have h22 : entU e ⟨2, by omega⟩ * entU e ⟨2, by omega⟩ = 1 := entU_mul_self he _
  have hsq : ∀ c : Fin n, entU e c * entU e ⟨2, by omega⟩ * (entU e c * entU e ⟨2, by omega⟩) =
      1 := fun c => by
    calc entU e c * entU e ⟨2, by omega⟩ * (entU e c * entU e ⟨2, by omega⟩)
        = (entU e c * entU e c) * (entU e ⟨2, by omega⟩ * entU e ⟨2, by omega⟩) := by ring
      _ = 1 := by rw [entU_mul_self he, h22, one_mul]
  have hσ : ∀ c : Fin n, unitaryInvolution K p f (entU e c * entU e ⟨2, by omega⟩) =
      entU e c * entU e ⟨2, by omega⟩ := fun c => by
    rw [map_mul, unitaryInvolution_eq_self_of_sign (entU_cases he c),
      unitaryInvolution_eq_self_of_sign (entU_cases he ⟨2, by omega⟩)]
  refine ⟨signNorm _ (hsq ⟨0, by omega⟩) (hσ _), signNorm _ (hsq ⟨1, by omega⟩) (hσ _),
    fun x => ?_⟩
  apply suMat_injective
  rw [inv_eq_self_of_mem_signGroupU he, suMat_mul, suMat_mul, suMat_blockEmb,
    suMat_eq_diagonal he, diagonal_conj_blockMat_three hn (entU_mul_self he), suMat_blockEmb]
  congr 1
  have : suMat (diagConj3U hK (signNorm _ (hsq ⟨0, by omega⟩) (hσ _))
      (signNorm _ (hsq ⟨1, by omega⟩) (hσ _)) x) =
      Matrix.diagonal ![entU e ⟨0, by omega⟩ * entU e ⟨2, by omega⟩,
        entU e ⟨1, by omega⟩ * entU e ⟨2, by omega⟩, 1] * suMat x *
        Matrix.diagonal ![entU e ⟨0, by omega⟩ * entU e ⟨2, by omega⟩,
          entU e ⟨1, by omega⟩ * entU e ⟨2, by omega⟩, 1] := by
    show ((diagU3 _ _ _ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * suMat x *
      (((diagU3 _ _ _ : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    simp only [diagU3, coe_diagGL, coe_diagGL_inv]
    congr 2
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp <;> exact inv_eq_of_mul_eq_one_right (hsq _)
  rw [this]
  exact diagonal_three_conj_eq h22 _

theorem diagActionU_chart3U (hK : Nat.card K = (p ^ f) ^ 2) (hn : 3 ≤ n) {g : Su K p f n}
    {τ : Equiv.Perm (Fin n)} (hg : IsMonomialFor (suMat g) τ) :
    DiagActionU hK (chart3U hn g) (signGroupU K p f n) := by
  intro e he
  obtain ⟨he', -⟩ := conj_mem_signGroupU hg he
  obtain ⟨a, b, hab⟩ := conj_blockEmb3_eq hK hn he'
  refine ⟨a, b, fun x => ?_⟩
  have := hab x
  rw [chart3U_apply, chart3U_apply, ← this]
  group

theorem unitaryA2Pair_LcU_overlap (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    UnitaryA2Pair K p f (signGroupU K p f n) (LcU K p f (⟨{i, j}, Finset.card_pair hij⟩ : Pair n))
      (LcU K p f (⟨{j, k}, Finset.card_pair hjk⟩ : Pair n)) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨τ, h0, h1, h2'⟩ := exists_perm_triple hn hij hjk hik
  let g : Su K p f n := monoSU K p f (by omega) τ
  have hg : IsMonomialFor (suMat g) τ := isMonomialFor_monoMat τ
  refine unitaryA2Pair_of_diagAction (θ := chart3U hn g) hK ?_ ?_ ?_
    (diagActionU_chart3U hK hn hg) (inSigma_LcU hK hp hn _) (inSigma_LcU hK hp hn _)
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr (chart3U_injective hn g)]
    exact bot_le
  · refine map_B12_chart3U h2 hn hg ?_
    show ({i, j} : Finset (Fin n)) = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩}
    rw [h0, show τ ⟨0 + 1, by omega⟩ = j from h1]
  · refine map_B23_chart3U h2 hn hg ?_
    show ({j, k} : Finset (Fin n)) = {τ ⟨1, by omega⟩, τ ⟨1 + 1, by omega⟩}
    rw [h1, show τ ⟨1 + 1, by omega⟩ = k from h2']

end A2U

section FramePropertiesU

theorem a2Dichotomy_coordSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hn : 4 ≤ n) : A2Dichotomy (signGroupU K p f n) (coordSetU K p f n) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  refine a2Dichotomy_of_unitary (toralFrameU hK hp h5 hn) hK ?_
  rintro _ ⟨T, rfl⟩ _ ⟨T', rfl⟩ hne
  have hTT' : T ≠ T' := fun h => hne (by rw [h])
  rcases pair_disjoint_or_share_one T.2 T'.2 (fun h => hTT' (Subtype.ext h)) with
    hd | ⟨i, j, k, hij, hjk, hik, h1, h1'⟩
  · exact Or.inl (commutes_LcU_of_disjoint h2 hd)
  · have e1 : T = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext h1
    have e2 : T' = ⟨{j, k}, Finset.card_pair hjk⟩ := Subtype.ext h1'
    rw [e1, e2]
    exact Or.inr (Or.inl (unitaryA2Pair_LcU_overlap hK hp (by omega) hij hjk hik))

theorem nonCommConnected_coordSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n) :
    NonCommConnected (coordSetU K p f n) :=
  (isPairFamily_LcU hK hp hn).nonCommConnected (by omega)

theorem fibreLE2_coordSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n) :
    FibreLE2 (coordSetU K p f n) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  rintro z _ ⟨T, rfl⟩ _ ⟨T', rfl⟩ M _ hz hz' -
  left
  have e : zEltU K p f T = zEltU K p f T' :=
    (isUniqueInvolution_LcU hK hp hn T).eq hz |>.trans
      ((isUniqueInvolution_LcU hK hp hn T').eq hz').symm
  have := Subtype.ext (zMat_inj h2 (congrArg suMat e))
  rw [this]

theorem ncard_coordSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n) :
    (coordSetU K p f n).ncard = n.choose 2 :=
  (isPairFamily_LcU hK hp hn).ncard_range

end FramePropertiesU

end CFSG.ClassicalInvolution.Models
