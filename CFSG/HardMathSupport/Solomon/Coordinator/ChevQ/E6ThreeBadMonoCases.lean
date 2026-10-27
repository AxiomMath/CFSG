module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoNormal
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.RankThree.E6 (e6RootVec isRoot_iff_exists_e6RootVec)

set_option linter.unusedSectionVars false

@[expose] def bmInvS : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![-1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

theorem bm_foldr_invS : ∀ j : Fin Tag.E6.rank,
    ([0] : List (Fin Tag.E6.rank)).reverse.foldr (reflect .E6) (Pi.single j 1) = bmInvS j := by
  decide +kernel

theorem bm_inv_s (j : Fin Tag.E6.rank) :
    ((coxeterSystem .E6).wordProd [0])⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = bmInvS j :=
  bm_inv_smul bm_foldr_invS j

theorem bm_s_char : ∀ j : Fin Tag.E6.rank,
    (∑ k, bmKhExp k * bmInvS j k - bmKhExp j) % 3 = 0 ∧
    (∑ k, bmD0Exp k * bmInvS j k - bmD0Exp j) % 3 = 0 := by
  decide +kernel

theorem bm_foldr_sq : ∀ i : Fin Tag.E6.rank,
    ((e6BadWord ++ e6BadWord) ++ (e6BadWord ++ e6BadWord)).foldr (reflect .E6) (Pi.single i 1) =
      (e6BadWord ++ []).foldr (reflect .E6) (Pi.single i 1) ∧
    (([0] ++ e6BadWord ++ e6BadWord ++ [0]) ++ ([0] ++ e6BadWord ++ e6BadWord ++ [0])).foldr
        (reflect .E6) (Pi.single i 1) =
      (([0] ++ e6BadWord ++ [0]) ++ []).foldr (reflect .E6) (Pi.single i 1) := by
  decide +kernel

theorem bm_w2_sq :
    (coxeterSystem .E6).wordProd (e6BadWord ++ e6BadWord) *
        (coxeterSystem .E6).wordProd (e6BadWord ++ e6BadWord) =
      (coxeterSystem .E6).wordProd e6BadWord := by
  rw [bm_wordProd_comm fun i => (bm_foldr_sq i).1, CoxeterSystem.wordProd_nil, mul_one]

theorem bm_sw2s_sq :
    (coxeterSystem .E6).wordProd ([0] ++ e6BadWord ++ e6BadWord ++ [0]) *
        (coxeterSystem .E6).wordProd ([0] ++ e6BadWord ++ e6BadWord ++ [0]) =
      (coxeterSystem .E6).wordProd ([0] ++ e6BadWord ++ [0]) := by
  rw [bm_wordProd_comm fun i => (bm_foldr_sq i).2, CoxeterSystem.wordProd_nil, mul_one]

theorem bm_isRoot_fixA : IsRoot Tag.E6 bmFixA :=
  isRoot_iff_exists_e6RootVec.2 (by decide +kernel)

theorem bm_isRoot_fixB : IsRoot Tag.E6 bmFixB :=
  isRoot_iff_exists_e6RootVec.2 (by decide +kernel)

theorem bm_cand {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    (β 3 % 3 = 0 → (β 1 + β 4 + β 5) % 3 = 0 → β ∈ bmCandA) ∧
    (β 3 % 3 = 0 → (β 1 + β 4 + β 5) % 3 = 1 → β ∈ bmCandB) ∧
    (β 3 % 3 = 1 → (β 1 + β 4 + β 5) % 3 = 0 → β ∈ bmCandC) := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hβ
  exact ⟨bmCand_completeA m, bmCand_completeB m, bmCand_completeC m⟩

theorem bm_gram_smul
    (v : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) : bmGram (v • x) (v • y) = bmGram x y := by
  rw [← iform_eq_bmGram, ← iform_eq_bmGram, iform_smul]

theorem bm_weyl_cases_int
    {v : WeylGroup Tag.E6} (hv3 : v ^ 3 = 1)
    (hc : ∀ i : Fin Tag.E6.rank,
      ((v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 3 - bmKhExp i) % 3 = 0 ∧
      ((v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 1 +
        (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 4 +
        (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 5 - bmD0Exp i) % 3 = 0) :
    v • bmFixA = bmFixA ∨ v • bmFixB = bmFixB ∨
      v = (coxeterSystem .E6).wordProd e6BadWord ∨
      v = (coxeterSystem .E6).wordProd (e6BadWord ++ e6BadWord) ∨
      v = (coxeterSystem .E6).wordProd ([0] ++ e6BadWord ++ [0]) ∨
      v = (coxeterSystem .E6).wordProd ([0] ++ e6BadWord ++ e6BadWord ++ [0]) := by
  have hk : bmKhExp 0 = 0 ∧ bmKhExp 1 = 0 ∧ bmKhExp 2 = 0 ∧ bmKhExp 3 = 1 ∧ bmKhExp 4 = 0 ∧
      bmKhExp 5 = 0 ∧ bmD0Exp 0 = 0 ∧ bmD0Exp 1 = 1 ∧ bmD0Exp 2 = 0 ∧ bmD0Exp 3 = 0 ∧
      bmD0Exp 4 = 1 ∧ bmD0Exp 5 = 1 := by
    decide +kernel
  obtain ⟨k0, k1, k2, k3, k4, k5, f0, f1, f2, f3, f4, f5⟩ := hk
  have hr : ∀ i, IsRoot Tag.E6 (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := fun i =>
    IsRoot.smul (isRoot_single Tag.E6 i) v
  obtain ⟨c0, d0⟩ := hc 0
  obtain ⟨c1, d1⟩ := hc 1
  obtain ⟨c2, d2⟩ := hc 2
  obtain ⟨c3, d3⟩ := hc 3
  obtain ⟨c4, d4⟩ := hc 4
  obtain ⟨c5, d5⟩ := hc 5
  have m0 := (bm_cand (hr 0)).1 (by omega) (by omega)
  have m1 := (bm_cand (hr 1)).2.1 (by omega) (by omega)
  have m2 := (bm_cand (hr 2)).1 (by omega) (by omega)
  have m3 := (bm_cand (hr 3)).2.2 (by omega) (by omega)
  have m4 := (bm_cand (hr 4)).2.1 (by omega) (by omega)
  have m5 := (bm_cand (hr 5)).2.1 (by omega) (by omega)
  have hM : bmMat (v • Pi.single 0 1) (v • Pi.single 1 1) (v • Pi.single 2 1)
      (v • Pi.single 3 1) (v • Pi.single 4 1) (v • Pi.single 5 1) =
        fun i => v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    funext i
    fin_cases i <;> rfl
  have key := bm_enum _ m3 _ m2 (by rw [bm_gram_smul]; decide +kernel) _ m4
    (by rw [bm_gram_smul]; decide +kernel) (by rw [bm_gram_smul]; decide +kernel) _ m1
    (by rw [bm_gram_smul]; decide +kernel) (by rw [bm_gram_smul]; decide +kernel)
    (by rw [bm_gram_smul]; decide +kernel) _ m0 (by rw [bm_gram_smul]; decide +kernel)
    (by rw [bm_gram_smul]; decide +kernel) (by rw [bm_gram_smul]; decide +kernel)
    (by rw [bm_gram_smul]; decide +kernel) _ m5 (by rw [bm_gram_smul]; decide +kernel)
    (by rw [bm_gram_smul]; decide +kernel) (by rw [bm_gram_smul]; decide +kernel)
    (by rw [bm_gram_smul]; decide +kernel) (by rw [bm_gram_smul]; decide +kernel) (by
      rw [hM]
      intro i
      rw [← bm_smul_eq_bmV, ← bm_smul_eq_bmV, ← bm_smul_eq_bmV, smul_smul, smul_smul,
        ← pow_three', hv3, one_smul])
  rw [hM, ← bm_smul_eq_bmV, ← bm_smul_eq_bmV] at key
  rcases key with hA | hB | hw | hw2 | hs | hs2
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr (Or.inl (bm_wordProd_eq_of_smul bm_foldr_Tw fun i => congrFun hw i)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (bm_wordProd_eq_of_smul bm_foldr_Tw2 fun i => congrFun hw2 i))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (bm_wordProd_eq_of_smul bm_foldr_Ts fun i => congrFun hs i)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (bm_wordProd_eq_of_smul bm_foldr_Ts2 fun i => congrFun hs2 i)))))

section Mono

variable
  {K : Type} [Field K]

theorem bm_mul_comm_of_mem {G : Type*} [Group G] {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem bm_emod_of_zpow_eq {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {a b : ℤ}
    (h : ω ^ a = ω ^ b) : (a - b) % 3 = 0 := by
  have ho : orderOf ω = 3 := orderOf_eq_prime h3 h1
  have h' : ω ^ (a - b) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
  have hd := orderOf_dvd_iff_zpow_eq_one.2 h'
  rw [ho, Nat.cast_ofNat] at hd
  omega

theorem bm_sum_kh (β : Fin Tag.E6.rank → ℤ) : ∑ j, bmKhExp j * β j = β 3 := by
  simp [bm_sum_six, bmKhExp]

theorem bm_sum_kd (β : Fin Tag.E6.rank → ℤ) : ∑ j, bmD0Exp j * β j = β 1 + β 4 + β 5 := by
  simp [bm_sum_six, bmD0Exp]

theorem bm_char_cond {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {v : WeylGroup Tag.E6}
    (hkh : weylTuple v (e6LineChar ω) = e6LineChar ω)
    (hkd : weylTuple v (e6D0Char ω) = e6D0Char ω) (i : Fin Tag.E6.rank) :
    ((v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 3 - bmKhExp i) % 3 = 0 ∧
      ((v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 1 +
        (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 4 +
        (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 5 - bmD0Exp i) % 3 = 0 := by
  have hinv : ∀ t : Fin Tag.E6.rank → Kˣ, weylTuple v t = t → weylTuple v⁻¹ t = t :=
    fun t ht => by
      conv_lhs => rw [← ht]
      rw [weylTuple_weylTuple, inv_mul_cancel, weylTuple_one]
  have e1 := congrFun (hinv _ hkh) i
  have e2 := congrFun (hinv _ hkd) i
  simp only [weylTuple, inv_inv] at e1 e2
  rw [bm_e6LineChar_eq, rootChar_zpow] at e1
  rw [bm_e6D0Char_zpow, rootChar_zpow] at e2
  have c1 := bm_emod_of_zpow_eq h3 h1 e1
  have c2 := bm_emod_of_zpow_eq h3 h1 e2
  rw [bm_sum_kh] at c1
  rw [bm_sum_kd] at c2
  exact ⟨c1, c2⟩

theorem bm_s_kh {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd [0]) (e6LineChar ω) = e6LineChar ω := by
  rw [bm_e6LineChar_eq]
  exact bm_weylTuple_char bm_inv_s h3 fun j => (bm_s_char j).1

theorem bm_s_kd {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd [0]) (e6D0Char ω) = e6D0Char ω := by
  rw [bm_e6D0Char_zpow]
  exact bm_weylTuple_char bm_inv_s h3 fun j => (bm_s_char j).2

@[expose] def BmFixedRoot (K : Type) [Field K] : Prop :=
  ∀ (ν : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → Kˣ) (β : Fin Tag.E6.rank → ℤ),
    IsRoot Tag.E6 β → (coxeterSystem Tag.E6).wordProd ν • β = β →
    ∃ R : Subgroup (adjointGroup Tag.E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      (∀ e : Fin Tag.E6.rank → Kˣ, R.map (rootDiagAutHom Tag.E6 K e).toMonoidHom = R) ∧
      R.map (MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom Tag.E6 K a).toMonoidHom = R

variable [Finite K]

theorem bm_false_of_fixed (hfix : BmFixedRoot K) {ω : Kˣ} (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {ν : List (Fin Tag.E6.rank)}
    {a : Fin Tag.E6.rank → Kˣ}
    (h : BmGood ω E (MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom Tag.E6 K a))
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (hν : (coxeterSystem Tag.E6).wordProd ν • β = β) : False := by
  obtain ⟨R, hR1, hRp, hRd, hRX⟩ := hfix ν a β hβ hν
  refine h.2.2.1 (bm_e6NormalizesR_of_closure (h.closure_eq h1) hR1 hRp ?_)
  rintro ε (rfl | rfl | rfl)
  · rw [bm_conj_e6LineElt]
    exact hRd _
  · exact hRd _
  · exact hRX

theorem BmGood.sq {ω : Kˣ} {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {X : MulAut (adjointGroup Tag.E6 K)} (h : BmGood ω E X) : BmGood ω E (X * X) := by
  obtain ⟨hE, hEc, hER, hh, hd, hX, hXi⟩ := h
  refine ⟨hE, hEc, hER, hh, hd, mul_mem hX hX, fun hi => hXi ?_⟩
  have h4 : X = X * X * (X * X) := by
    calc X = X ^ 3 * X := by rw [hE.2 X hX, one_mul]
      _ = X * X * (X * X) := by rw [pow_three', mul_assoc]
  rw [h4]
  exact mul_mem hi hi

theorem bmGoal_of_mono {ω : Kˣ} (hpar : BmParabolic K ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {X : MulAut (adjointGroup Tag.E6 K)}
    (h : BmGood ω E X) (hm : BmMono X ((coxeterSystem Tag.E6).wordProd e6BadWord)) :
    BmGoal ω E := by
  obtain ⟨b, rfl⟩ := hm.exists_eq_word
  exact bmGoal_of_bmX_any hpar h3 h1 h

theorem bm_main {ω : Kˣ} (hpar : BmParabolic K ω) (hfix : BmFixedRoot K) (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {ν : List (Fin Tag.E6.rank)}
    {a : Fin Tag.E6.rank → Kˣ}
    (h : BmGood ω E (MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom Tag.E6 K a)) :
    BmGoal ω E := by
  have hn := bm_weylWordElt_mem_monomial (K := K) ν
  have hv := bm_mapsRootLines_weylWordElt (K := K) ν
  have hE := h.1
  have hX := h.2.2.2.2.2.1
  have hkh : weylTuple ((coxeterSystem Tag.E6).wordProd ν) (e6LineChar ω) = e6LineChar ω := by
    refine bm_weylTuple_eq_of_commute hn hv a _ ?_
    have hc := bm_mul_comm_of_mem hE hX h.2.2.2.1
    rwa [bm_conj_e6LineElt] at hc
  have hkd : weylTuple ((coxeterSystem Tag.E6).wordProd ν) (e6D0Char ω) = e6D0Char ω :=
    bm_weylTuple_eq_of_commute hn hv a _ (bm_mul_comm_of_mem hE hX h.2.2.2.2.1)
  have hv3 : (coxeterSystem Tag.E6).wordProd ν ^ 3 = 1 := by
    have hX3 := hE.2 _ hX
    rw [pow_three', bm_word_mul, bm_word_mul] at hX3
    have e := bm_wordProd_eq_one hX3
    rwa [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, ← pow_three'] at e
  have hm := bmMono_word (K := K) ν a
  rcases bm_weyl_cases_int hv3 (bm_char_cond h3 h1 hkh hkd) with hA | hB | hw | hw2 | hs | hs2
  · exact (bm_false_of_fixed hfix h1 h bm_isRoot_fixA hA).elim
  · exact (bm_false_of_fixed hfix h1 h bm_isRoot_fixB hB).elim
  · rw [hw] at hm
    exact bmGoal_of_mono hpar h3 h1 h hm
  · have hm2 := hm.mul hm
    rw [hw2, bm_w2_sq] at hm2
    exact bmGoal_of_mono hpar h3 h1 h.sq hm2
  · have hm' := ((bmMono_conj (K := K) [0]).mul hm).mul (bmMono_conj_inv [0])
    rw [hs, bm_comm_s, mul_inv_cancel_right] at hm'
    exact bmGoal_of_map _ (bmGoal_of_mono hpar h3 h1
      (h.conj_word (Or.inl (bm_s_kh h3)) (bm_s_kd h3)) hm')
  · have hm2 := hm.mul hm
    rw [hs2, bm_sw2s_sq] at hm2
    have hm' := ((bmMono_conj (K := K) [0]).mul hm2).mul (bmMono_conj_inv [0])
    rw [bm_comm_s, mul_inv_cancel_right] at hm'
    exact bmGoal_of_map _ (bmGoal_of_mono hpar h3 h1
      (h.sq.conj_word (Or.inl (bm_s_kh h3)) (bm_s_kd h3)) hm')

end Mono

section Assembly


theorem e6BadCube_of_monomial_of
    (hpar : ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → ∀ ω : Kˣ, ω ^ 3 = 1 →
      ω ≠ 1 → BmParabolic K ω)
    (hfix : ∀ (K : Type) [Field K] [Finite K], BmFixedRoot K) : E6ThreeNotAll24NFB2 := by
  intro K _ _ hK3 _ _ ω h3 h1 E hE hEc _ hER hh hd ν a hX hXi
  exact bm_main (hpar K hK3 ω h3 h1) (hfix K) h3 h1 ⟨hE, hEc, hER, hh, hd, hX, hXi⟩

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
