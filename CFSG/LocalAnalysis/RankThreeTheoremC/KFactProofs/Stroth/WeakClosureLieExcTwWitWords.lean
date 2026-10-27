module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWords

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.Lattice
open scoped commutatorElement Matrix

theorem tw_wcOn_of_noncomm {G : Type} [Group G] {Γ : Subgroup G} [Finite Γ] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQ : IsPGroup p Q) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (hxΓ : x ∈ Γ)
    (hyΓ : y ∈ Γ) (hxy : x * y ≠ y * x) : WCOn p Γ := by
  refine WCOn.of_noncomm_pSubgroup (Q := Q.comap Γ.subtype) hQ.comap_subtype (x := ⟨x, hxΓ⟩)
    (y := ⟨y, hyΓ⟩) hx hy fun h => hxy (congrArg Subtype.val h)

section Words

variable {τ : Tag}

theorem tw_wordProd_pow_eq_one_of_check (l : List (Fin τ.rank)) (n : ℕ)
    (h : lpow τ.rank (lword τ.rank (cartanList τ) (l.map Fin.val)) n = lid τ.rank) :
    (coxeterSystem τ).wordProd l ^ n = 1 := by
  have key : ∀ k : ℕ, ∀ x : Fin τ.rank → ℤ,
      ((coxeterSystem τ).wordProd l ^ k) • x = (wordMat τ l ^ k) *ᵥ x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, mul_smul, wordProd_smul_eq_wordMat_mulVec, ih, Matrix.mulVec_mulVec, pow_succ]
  have hW : wordMat τ l ^ n = 1 := by
    rw [← toMat_lword τ (toMat_cartanList τ) l, ← toMat_lpow, h, toMat_lid]
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin τ.rank → ℤ) fun x => ?_
  rw [key, hW, Matrix.one_mulVec, one_smul]

end Words

section Witness

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]
  (D : LangDatum t.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
  (hΦ : D.Φ = twistHom t L Fr) {lw : List (Fin t.tag.rank)}
  (hn : D.n = canonicalRep (coxeterSystem t.tag) L ((coxeterSystem t.tag).wordProd lw))
  {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
  (hv : ∀ x, (coxeterSystem t.tag).wordProd lw • permLattice t.perm x = M *ᵥ x)
  {N : ℕ} (hN0 : N ≠ 0) (hpow : M ^ N = 1)

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_witness_of_sc_check [Finite D.model] {p : ℕ} [Fact p.Prime]
    {la lb : List (Fin t.tag.rank)} (Ml : List (List ℤ)) (hM : M = toMat t.tag.rank Ml)
    (hcomm : lmul t.tag.rank Ml (lword t.tag.rank (cartanList t.tag)
        ((twCommWord la lb).map Fin.val)) =
      lmul t.tag.rank (lword t.tag.rank (cartanList t.tag) ((twCommWord la lb).map Fin.val)) Ml)
    (hup : lpow t.tag.rank (lword t.tag.rank (cartanList t.tag) ((twCommWord la lb).map Fin.val))
      p = lid t.tag.rank) {ζ : Lˣ} (hζp : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (b : Fin t.tag.rank → ℤ) {e' : ℤ} (hq' : (p : ℤ) ∣ (q : ℤ) - e')
    (hfix : ∀ j, (p : ℤ) ∣ ((toMat t.tag.rank Ml).transpose *ᵥ b) j - e' * b j)
    (i₀ : Fin t.tag.rank)
    (hmove : ¬ (p : ℤ) ∣ ((toMat t.tag.rank (lword t.tag.rank (cartanList t.tag)
      ((twCommWord lb la).map Fin.val))).transpose *ᵥ b) i₀ - b i₀) :
    ∃ (Q : Subgroup (ModGL t.tag L)) (x y : ModGL t.tag L), IsPGroup p Q ∧ x ∈ Q ∧ y ∈ Q ∧
      x ∈ D.model ∧ y ∈ D.model ∧ x * y ≠ y * x := by
  have hMmat : toMat t.tag.rank Ml * wordMat t.tag (twCommWord la lb) =
      wordMat t.tag (twCommWord la lb) * toMat t.tag.rank Ml :=
    tw_wordMat_comm_of_check _ _ hcomm
  have hu : (coxeterSystem t.tag).wordProd lw *
      weylTwist t ((coxeterSystem t.tag).wordProd (twCommWord la lb)) =
      (coxeterSystem t.tag).wordProd (twCommWord la lb) * (coxeterSystem t.tag).wordProd lw :=
    tw_comm_of_word_matrix hv (by rw [hM]; exact hMmat)
  have hup' := tw_wordProd_pow_eq_one_of_check (τ := t.tag) (twCommWord la lb) p hup
  have hβ : (fun i => ζ ^ b i) ∈ fixedCharTuples M Fr := by
    refine tw_mem_fixedCharTuples_of_vec hζp hFr fun j => ?_
    have h1 := hfix j
    have h2 : (p : ℤ) ∣ ((q : ℤ) - e') * b j := Dvd.dvd.mul_right hq' _
    rw [hM]
    have e : ((toMat t.tag.rank Ml).transpose *ᵥ b) j - (q : ℤ) * b j =
        (((toMat t.tag.rank Ml).transpose *ᵥ b) j - e' * b j) - ((q : ℤ) - e') * b j := by ring
    rw [e]
    exact dvd_sub h1 h2
  have hβp : ∀ i, (fun i => ζ ^ b i) i ^ p = 1 := fun i => by
    show (ζ ^ b i) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have hβu : weylTuple ((coxeterSystem t.tag).wordProd (twCommWord la lb)) (fun i => ζ ^ b i) ≠
      fun i => ζ ^ b i := by
    refine tw_weylTuple_ne_of_vec hζo (N := wordMat t.tag (twCommWord lb la))
      (fun x => ?_) (i₀ := i₀) ?_
    · rw [wordProd_twCommWord]
      exact tw_commWord_smul la lb x
    · rw [← toMat_lword t.tag (toMat_cartanList t.tag)]
      exact hmove
  exact tw_exists_noncomm_pSubgroup D hq hFr hΦ hn hv hN0 hpow hu hup' hβ hβp hβu

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_witness_Γ_of_check [Finite D.model] {p : ℕ} [Fact p.Prime]
    {la lb ls : List (Fin t.tag.rank)} (Ml : List (List ℤ)) (hM : M = toMat t.tag.rank Ml)
    (hca : lmul t.tag.rank Ml (lword t.tag.rank (cartanList t.tag) (la.map Fin.val)) =
      lmul t.tag.rank (lword t.tag.rank (cartanList t.tag) (la.map Fin.val)) Ml)
    (hcb : lmul t.tag.rank Ml (lword t.tag.rank (cartanList t.tag) (lb.map Fin.val)) =
      lmul t.tag.rank (lword t.tag.rank (cartanList t.tag) (lb.map Fin.val)) Ml)
    (hcs : lmul t.tag.rank Ml (lword t.tag.rank (cartanList t.tag) (ls.map Fin.val)) =
      lmul t.tag.rank (lword t.tag.rank (cartanList t.tag) (ls.map Fin.val)) Ml)
    (hup : lpow t.tag.rank (lword t.tag.rank (cartanList t.tag) ((twCommWord la lb).map Fin.val))
      p = lid t.tag.rank) {ζ : Lˣ} (hζp : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (b' : Fin t.tag.rank → ℤ) {e' : ℤ} (hq' : (p : ℤ) ∣ (q : ℤ) - e')
    (hfix : ∀ j, (p : ℤ) ∣ ((toMat t.tag.rank Ml).transpose *ᵥ b') j - e' * b' j)
    (i₀ : Fin t.tag.rank)
    (hmove : ¬ (p : ℤ) ∣ ((toMat t.tag.rank (lword t.tag.rank (cartanList t.tag)
        ((twCommWord lb la).map Fin.val))).transpose *ᵥ
          ((toMat t.tag.rank (lword t.tag.rank (cartanList t.tag)
            (ls.reverse.map Fin.val))).transpose *ᵥ b' - b')) i₀ -
        ((toMat t.tag.rank (lword t.tag.rank (cartanList t.tag)
          (ls.reverse.map Fin.val))).transpose *ᵥ b' - b') i₀) :
    ∃ (Q : Subgroup (ModGL t.tag L)) (x y : ModGL t.tag L), IsPGroup p Q ∧ x ∈ Q ∧ y ∈ Q ∧
      x ∈ D.Γ ∧ y ∈ D.Γ ∧ x * y ≠ y * x := by
  have hMa : toMat t.tag.rank Ml * wordMat t.tag la = wordMat t.tag la * toMat t.tag.rank Ml :=
    tw_wordMat_comm_of_check _ _ hca
  have hMb : toMat t.tag.rank Ml * wordMat t.tag lb = wordMat t.tag lb * toMat t.tag.rank Ml :=
    tw_wordMat_comm_of_check _ _ hcb
  have hMs : toMat t.tag.rank Ml * wordMat t.tag ls = wordMat t.tag ls * toMat t.tag.rank Ml :=
    tw_wordMat_comm_of_check _ _ hcs
  have hup' := tw_wordProd_pow_eq_one_of_check (τ := t.tag) (twCommWord la lb) p hup
  rw [wordProd_twCommWord] at hup'
  have hβ : (fun i => ζ ^ b' i) ∈ fixedCharTuples M Fr := by
    refine tw_mem_fixedCharTuples_of_vec hζp hFr fun j => ?_
    have h1 := hfix j
    have h2 : (p : ℤ) ∣ ((q : ℤ) - e') * b' j := Dvd.dvd.mul_right hq' _
    rw [hM]
    have e : ((toMat t.tag.rank Ml).transpose *ᵥ b') j - (q : ℤ) * b' j =
        (((toMat t.tag.rank Ml).transpose *ᵥ b') j - e' * b' j) - ((q : ℤ) - e') * b' j := by ring
    rw [e]
    exact dvd_sub h1 h2
  have hβp : ∀ i, (fun i => ζ ^ b' i) i ^ p = 1 := fun i => by
    show (ζ ^ b' i) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  set Sinv := toMat t.tag.rank (lword t.tag.rank (cartanList t.tag) (ls.reverse.map Fin.val))
    with hSinv
  have hSi : ∀ x, ((coxeterSystem t.tag).wordProd ls)⁻¹ • x = Sinv *ᵥ x := fun x => by
    rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_eq_wordMat_mulVec,
      ← toMat_lword t.tag (toMat_cartanList t.tag)]
  have hγ : weylTuple ((coxeterSystem t.tag).wordProd ls) (fun i => ζ ^ b' i) *
      (fun i => ζ ^ b' i)⁻¹ = fun i => ζ ^ ((Sinv.transpose *ᵥ b' - b') i) := by
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [weylTuple_zpow_vec hSi i, Pi.sub_apply, zpow_sub]
  have hγne : weylTuple ((coxeterSystem t.tag).wordProd (twCommWord la lb))
      (fun i => ζ ^ ((Sinv.transpose *ᵥ b' - b') i)) ≠
      fun i => ζ ^ ((Sinv.transpose *ᵥ b' - b') i) := by
    refine tw_weylTuple_ne_of_vec hζo (N := wordMat t.tag (twCommWord lb la))
      (fun x => ?_) (i₀ := i₀) ?_
    · rw [wordProd_twCommWord]
      exact tw_commWord_smul la lb x
    · rw [← toMat_lword t.tag (toMat_cartanList t.tag)]
      exact hmove
  refine tw_exists_noncomm_pSubgroup_Γ D hq hFr hΦ hn hv hN0 hpow
    (a := (coxeterSystem t.tag).wordProd la) (b := (coxeterSystem t.tag).wordProd lb)
    (s := (coxeterSystem t.tag).wordProd ls)
    (tw_comm_of_word_matrix hv (by rw [hM]; exact hMa))
    (tw_comm_of_word_matrix hv (by rw [hM]; exact hMb))
    (tw_comm_of_word_matrix hv (by rw [hM]; exact hMs)) hup' hβ hβp ?_
  rw [hγ, ← wordProd_twCommWord]
  exact hγne

end Witness

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
