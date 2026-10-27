module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwMove

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.Lattice
open scoped commutatorElement Matrix

@[expose] def twCommWord {α : Type*} (x y : List α) : List α := x ++ y ++ x.reverse ++ y.reverse

section Words

variable {τ : Tag}

theorem wordProd_twCommWord (x y : List (Fin τ.rank)) :
    (coxeterSystem τ).wordProd (twCommWord x y) =
      ⁅(coxeterSystem τ).wordProd x, (coxeterSystem τ).wordProd y⁆ := by
  simp only [twCommWord, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_reverse,
    commutatorElement_def]

theorem tw_commWord_smul (x y : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    ⁅(coxeterSystem τ).wordProd x, (coxeterSystem τ).wordProd y⁆⁻¹ • v =
      wordMat τ (twCommWord y x) *ᵥ v := by
  rw [commutatorElement_inv, ← wordProd_twCommWord]
  exact wordProd_smul_eq_wordMat_mulVec τ _ v

theorem tw_wordMat_comm_of_check (l : List (Fin τ.rank)) (Ml : List (List ℤ))
    (h : lmul τ.rank Ml (lword τ.rank (cartanList τ) (l.map Fin.val)) =
      lmul τ.rank (lword τ.rank (cartanList τ) (l.map Fin.val)) Ml) :
    toMat τ.rank Ml * wordMat τ l = wordMat τ l * toMat τ.rank Ml := by
  rw [← toMat_lword τ (toMat_cartanList τ) l, ← toMat_lmul, ← toMat_lmul, h]

theorem tw_wordMat_eq_smul_pow_of_check (l : List (Fin τ.rank)) (Ml : List (List ℤ)) (s : ℤ)
    (k : ℕ) (h : lword τ.rank (cartanList τ) (l.map Fin.val) = lsmul τ.rank s (lpow τ.rank Ml k)) :
    wordMat τ l = s • toMat τ.rank Ml ^ k := by
  rw [← toMat_lword τ (toMat_cartanList τ) l, h, toMat_lsmul, toMat_lpow]

theorem tw_cert_of_check (l : List (Fin τ.rank)) (Ml Y1 Y2 : List (List ℤ)) (e' c : ℤ)
    (h : ladd τ.rank (lmul τ.rank (ladd τ.rank Ml (lsmul τ.rank (-e') (lid τ.rank))) Y1)
        (lmul τ.rank (ladd τ.rank (lword τ.rank (cartanList τ) (l.map Fin.val))
          (lsmul τ.rank (-1) (lid τ.rank))) Y2) = lsmul τ.rank c (lid τ.rank)) :
    (toMat τ.rank Ml - e' • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) * toMat τ.rank Y1 +
      (wordMat τ l - 1) * toMat τ.rank Y2 = c • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := by
  have h' := congrArg (toMat τ.rank) h
  rw [toMat_ladd, toMat_lmul, toMat_lmul, toMat_ladd, toMat_ladd, toMat_lsmul, toMat_lid,
    toMat_lsmul, toMat_lid, toMat_lword τ (toMat_cartanList τ) l, toMat_lsmul, toMat_lid] at h'
  rw [← h']
  simp [sub_eq_add_neg]

end Words

section Moves

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]

theorem tw_comm_of_matrix {w a : WeylGroup t.tag} {M Wa : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) (ha : ∀ x, a • x = Wa *ᵥ x)
    (hcomm : M * Wa = Wa * M) : w * weylTwist t a = a * w := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin t.tag.rank → ℤ) fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, x = permLattice t.perm y :=
    ⟨permLattice t.perm.symm x, (CFSG.LieType.Chevalley.permLattice_permLattice_symm _ _).symm⟩
  rw [mul_smul, mul_smul, weylTwist_smul_permLattice, hv, ha, hv, ha, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hcomm]

theorem tw_comm_of_word_matrix {lw la : List (Fin t.tag.rank)}
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, (coxeterSystem t.tag).wordProd lw • permLattice t.perm x = M *ᵥ x)
    (hcomm : M * wordMat t.tag la = wordMat t.tag la * M) :
    (coxeterSystem t.tag).wordProd lw * weylTwist t ((coxeterSystem t.tag).wordProd la) =
      (coxeterSystem t.tag).wordProd la * (coxeterSystem t.tag).wordProd lw :=
  tw_comm_of_matrix hv (wordProd_smul_eq_wordMat_mulVec t.tag la) hcomm

variable (D : LangDatum t.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
  (hΦ : D.Φ = twistHom t L Fr) {lw : List (Fin t.tag.rank)}
  (hn : D.n = canonicalRep (coxeterSystem t.tag) L ((coxeterSystem t.tag).wordProd lw))
  {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
  (hv : ∀ x, (coxeterSystem t.tag).wordProd lw • permLattice t.perm x = M *ᵥ x)
  {N : ℕ} (hN0 : N ≠ 0) (hpow : M ^ N = 1)

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_moves_of_sc_scalar {p : ℕ} [Fact p.Prime] (hMΓ : D.model ≤ D.Γ) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {la lb : List (Fin t.tag.rank)}
    (hca : M * wordMat t.tag la = wordMat t.tag la * M)
    (hcb : M * wordMat t.tag lb = wordMat t.tag lb * M) {s : ℤ} {k : ℕ}
    (hmat : wordMat t.tag (twCommWord lb la) = s • M ^ k)
    (hnd : ¬ (p : ℤ) ∣ s * (q : ℤ) ^ k - 1) : NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  refine normalizerMovesLines_of_tw_sc D hq hFr hΦ hn hv hN0 hpow hMΓ S₀ hS₀
    (tw_comm_of_word_matrix hv hca) (tw_comm_of_word_matrix hv hcb) ?_
  intro β hβ hβp hfix
  refine twFixedPointFree_of_scalar hFr (fun x => ?_) hnd hβ hβp hfix
  rw [tw_commWord_smul, hmat, Matrix.smul_mulVec]

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_moves_of_sc_cert {p : ℕ} [Fact p.Prime] (hMΓ : D.model ≤ D.Γ) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {la lb : List (Fin t.tag.rank)}
    (hca : M * wordMat t.tag la = wordMat t.tag la * M)
    (hcb : M * wordMat t.tag lb = wordMat t.tag lb * M) {e' : ℤ} (hq' : (p : ℤ) ∣ (q : ℤ) - e')
    {Y₁ Y₂ : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ} {c : ℤ}
    (hcert : (M - e' • (1 : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ)) * Y₁ +
      (wordMat t.tag (twCommWord lb la) - 1) * Y₂ =
        c • (1 : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ)) (hc : ¬ (p : ℤ) ∣ c) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  refine normalizerMovesLines_of_tw_sc D hq hFr hΦ hn hv hN0 hpow hMΓ S₀ hS₀
    (tw_comm_of_word_matrix hv hca) (tw_comm_of_word_matrix hv hcb) ?_
  intro β hβ hβp hfix
  exact twFixedPointFree_of_cert hFr (fun x => tw_commWord_smul la lb x) hq' hcert hc hβ hβp hfix

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_moves_of_dc_scalar {p : ℕ} [Fact p.Prime] (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ)
    {la lb lc ld : List (Fin t.tag.rank)}
    (hca : M * wordMat t.tag la = wordMat t.tag la * M)
    (hcb : M * wordMat t.tag lb = wordMat t.tag lb * M)
    (hcc : M * wordMat t.tag lc = wordMat t.tag lc * M)
    (hcd : M * wordMat t.tag ld = wordMat t.tag ld * M) {s : ℤ} {k : ℕ}
    (hmat : wordMat t.tag (twCommWord (twCommWord lc ld) (twCommWord la lb)) = s • M ^ k)
    (hnd : ¬ (p : ℤ) ∣ s * (q : ℤ) ^ k - 1) : NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  refine normalizerMovesLines_of_tw_dc D hq hFr hΦ hn hv hN0 hpow S₀ hS₀
    (tw_comm_of_word_matrix hv hca) (tw_comm_of_word_matrix hv hcb)
    (tw_comm_of_word_matrix hv hcc) (tw_comm_of_word_matrix hv hcd) ?_
  intro β hβ hβp hfix
  refine twFixedPointFree_of_scalar hFr (fun x => ?_) hnd hβ hβp hfix
  have := tw_commWord_smul (twCommWord la lb) (twCommWord lc ld) x
  rw [wordProd_twCommWord, wordProd_twCommWord] at this
  rw [this, hmat, Matrix.smul_mulVec]

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_moves_of_dc_cert {p : ℕ} [Fact p.Prime] (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ)
    {la lb lc ld : List (Fin t.tag.rank)}
    (hca : M * wordMat t.tag la = wordMat t.tag la * M)
    (hcb : M * wordMat t.tag lb = wordMat t.tag lb * M)
    (hcc : M * wordMat t.tag lc = wordMat t.tag lc * M)
    (hcd : M * wordMat t.tag ld = wordMat t.tag ld * M) {e' : ℤ} (hq' : (p : ℤ) ∣ (q : ℤ) - e')
    {Y₁ Y₂ : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ} {c : ℤ}
    (hcert : (M - e' • (1 : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ)) * Y₁ +
      (wordMat t.tag (twCommWord (twCommWord lc ld) (twCommWord la lb)) - 1) * Y₂ =
        c • (1 : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ)) (hc : ¬ (p : ℤ) ∣ c) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  refine normalizerMovesLines_of_tw_dc D hq hFr hΦ hn hv hN0 hpow S₀ hS₀
    (tw_comm_of_word_matrix hv hca) (tw_comm_of_word_matrix hv hcb)
    (tw_comm_of_word_matrix hv hcc) (tw_comm_of_word_matrix hv hcd) ?_
  intro β hβ hβp hfix
  refine twFixedPointFree_of_cert hFr (fun x => ?_) hq' hcert hc hβ hβp hfix
  have := tw_commWord_smul (twCommWord la lb) (twCommWord lc ld) x
  rw [wordProd_twCommWord, wordProd_twCommWord] at this
  exact this

end Moves

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
