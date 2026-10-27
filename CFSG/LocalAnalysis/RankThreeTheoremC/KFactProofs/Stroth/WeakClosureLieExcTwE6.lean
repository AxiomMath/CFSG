module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwE6Wit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwE6Arith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwE6Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false

theorem tw_pRank_top_le_one_of_rankLE1 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : RankLE1 p G) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1 := by
  unfold CFSG.Open.pRank
  apply csSup_le
  · refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun x hx => ?_⟩,
      by simp⟩
    rw [Subgroup.mem_bot.1 hx, one_pow]
  · rintro i ⟨E, -, hE, hcard⟩
    have h1 : p ^ i ≤ p ^ 1 := by
      have := h E hE
      rw [hcard] at this
      simpa using this
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1


theorem e6One_class_aux (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type)
    [Field F] (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup F σ ≃* D.Γ) := by
  have hp2 : p ≠ 2 := by omega
  have he' := orderOf_neg_natCast_zmod hp.out hp2 hpq he
  rw [show ennola 1 = 2 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs = ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
    show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
  exact exists_lang_twE6_data_of_blocks hF hℓ hf F hF2 σ hσ hp.out (by omega) hpq _ e6One_hv
    [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow (Or.inr (by decide)) he he' hΦ (by decide)
    (tw_not_dvd_div_of_144 hp.out hp5 (by decide)) (by decide)

theorem e6Two_class_aux (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type)
    [Field F] (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h7 : 7 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 2) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup F σ ≃* D.Γ) := by
  have hp2 : p ≠ 2 := by omega
  have he' := orderOf_neg_natCast_zmod hp.out hp2 hpq he
  rw [show ennola 2 = 1 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 1 ℤ).eval (-x)).natAbs = ((cyclotomic 2 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
    show -x - 1 = -(x + 1) by ring, Int.natAbs_neg]
  exact exists_lang_twE6_data_of_blocks hF hℓ hf F hF2 σ hσ hp.out (by omega) hpq _ e6Two_hv
    [2, 2, 2, 2, 2, 2] twE6Two_charpoly (by norm_num) twE6Two_pow (Or.inr (by decide)) he he' hΦ (by decide)
    (not_dvd_div_of_720 hp.out h7 (by decide)) (by decide)

theorem e6Three_class_aux (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type)
    [Field F] (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 3) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6ThreeWord) ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup F σ ≃* D.Γ) := by
  have hp2 : p ≠ 2 := by omega
  have he' := orderOf_neg_natCast_zmod hp.out hp2 hpq he
  rw [show ennola 3 = 6 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 6 ℤ).eval (-x)).natAbs = ((cyclotomic 3 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_six_eq, cyclotomic_three_eq]
    simp
  exact exists_lang_twE6_data_of_blocks hF hℓ hf F hF2 σ hσ hp.out (by omega) hpq _ e6Three_hv
    [3, 3, 6] twE6Three_charpoly (by norm_num) twE6Three_pow (Or.inr (by decide)) he he' hΦ (by decide)
    (tw_not_dvd_div_of_144 hp.out hp5 (by decide)) (by decide)

theorem e6Four_class_aux (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type)
    [Field F] (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 4) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6FourWord) ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup F σ ≃* D.Γ) := by
  have hp2 : p ≠ 2 := by omega
  have he' := orderOf_neg_natCast_zmod hp.out hp2 hpq he
  rw [show ennola 4 = 4 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 4 ℤ).eval (-x)).natAbs = ((cyclotomic 4 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_four_eq]
    simp
  exact exists_lang_twE6_data_of_blocks hF hℓ hf F hF2 σ hσ hp.out (by omega) hpq _ e6Four_hv
    [2, 2, 4, 4] twE6Four_charpoly (by norm_num) twE6Four_pow (Or.inr (by decide)) he he' hΦ (by decide)
    (tw_not_dvd_div_of_144 hp.out hp5 (by decide)) (by decide)

theorem e6Six_class_aux (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type)
    [Field F] (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 6) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup F σ ≃* D.Γ) := by
  have hp2 : p ≠ 2 := by omega
  have he' := orderOf_neg_natCast_zmod hp.out hp2 hpq he
  rw [show ennola 6 = 3 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 3 ℤ).eval (-x)).natAbs = ((cyclotomic 6 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_six_eq, cyclotomic_three_eq]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
    congr 1
    ring
  exact exists_lang_twE6_data_of_blocks hF hℓ hf F hF2 σ hσ hp.out (by omega) hpq _ e6Six_hv
    [6, 6, 6] twE6Six_charpoly (by norm_num) twE6Six_pow (Or.inr (by decide)) he he' hΦ (by decide)
    (tw_not_dvd_div_of_144 hp.out hp5 (by decide)) (by decide)

theorem wcOn_twistedE6_class {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {K : Type} [Group K] [Finite K] (eK : K ≃* twistedE6RootGroup F σ) {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f) {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (hE : e = 1 ∨ e = 3 ∨ e = 4 ∨ e = 6 ∨ (e = 2 ∧ 7 ≤ p)) : WCOn p K := by
  have hF := frobeniusOnRoots_proved
  have hp2 : p ≠ 2 := by omega
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  rcases hE with rfl | rfl | rfl | rfl | ⟨rfl, h7⟩
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      e6One_class_aux hF hℓ hf F hF2 σ hσ hp5 hpq he
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      e6One_moves D hq2 hFr hΦ hn hp2 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      e6Three_class_aux hF hℓ hf F hF2 σ hσ hp5 hpq he
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      e6Three_moves D hq2 hFr hΦ hn hp2 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      e6Four_class_aux hF hℓ hf F hF2 σ hσ hp5 hpq he
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      e6Four_moves D hq2 hFr hΦ hn hp2 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      e6Six_class_aux hF hℓ hf F hF2 σ hσ hp5 hpq he
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      e6Six_moves D hq2 hFr hΦ hn hp2 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      e6Two_class_aux hF hℓ hf F hF2 σ hσ hp5 h7 hpq he
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      e6Two_moves D hq2 hFr hΦ hn hp2 hp5 he S₀ hS₀)

theorem wcOn_twistedE6_cyclic {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {K : Type} [Group K] [Finite K] (eK : K ≃* twistedE6RootGroup F σ) {p : ℕ} [hp : Fact p.Prime]
    {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (hE : e = 8 ∨ e = 10 ∨ e = 12 ∨ e = 18) :
    WCOn p K := by
  have hst : SylowTorus (twistedE6RootGroup F σ) p 1 := by
    rcases hE with rfl | rfl | rfl | rfl
    · exact sylowTorus_twistedE6_eight hℓ hf F hF2 σ hσ hp.out he
    · exact sylowTorus_twistedE6_ten hℓ hf F hF2 σ hσ hp.out he
    · exact sylowTorus_twistedE6_twelve hℓ hf F hF2 σ hσ hp.out he
    · exact sylowTorus_twistedE6_eighteen hℓ hf F hF2 σ hσ hp.out he
  haveI : Finite (twistedE6RootGroup F σ) := Finite.of_equiv K eK.toEquiv
  exact WCOn.of_mulEquiv eK (WCOn.of_pRank_top_le_one
    (tw_pRank_top_le_one_of_rankLE1 hp.out (hst.rankLE1 hp.out)))

theorem wcOn_twistedE6_witness {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF2 : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {K : Type} [Group K] [Finite K] (eK : K ≃* twistedE6RootGroup F σ) {p : ℕ} [hp : Fact p.Prime]
    (hpℓ : p ≠ ℓ) {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (hcase : (p = 3 ∧ e = 1) ∨ (p = 3 ∧ e = 2) ∨ (p = 5 ∧ e = 2)) : WCOn p K := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨L, _, _, hLchar, Fr, hFr, D, hΦ, hn, hfin, ⟨eΓ⟩⟩ :=
      exists_lang_twE6_model hℓ hf F hF2 σ hσ
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord)
    haveI := hfin
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    haveI : NeZero ((3 : ℕ) : L) := ⟨by
      intro h
      have := (CharP.cast_eq_zero_iff L ℓ 3).1 h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this).symm⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
    have hζu := hζ0.isUnit_unit (by norm_num)
    obtain ⟨Q, x, y, hQ, hxQ, hyQ, hxΓ, hyΓ, hxy⟩ :=
      e6OneThree_witness D hq2 hFr hΦ hn (ζ := (hζ0.isUnit (by norm_num)).unit) hζu.pow_eq_one
        hζu.eq_orderOf.symm (tw_dvd_sub_of_orderOf_one Nat.prime_three he)
    exact WCOn.of_mulEquiv (eK.trans eΓ) (tw_wcOn_of_noncomm hQ hxQ hyQ hxΓ hyΓ hxy)
  · obtain ⟨L, _, _, hLchar, Fr, hFr, D, hΦ, hn, hfin, ⟨eΓ⟩⟩ :=
      exists_lang_twE6_model hℓ hf F hF2 σ hσ
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord)
    haveI := hfin
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    haveI : NeZero ((3 : ℕ) : L) := ⟨by
      intro h
      have := (CharP.cast_eq_zero_iff L ℓ 3).1 h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this).symm⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
    have hζu := hζ0.isUnit_unit (by norm_num)
    obtain ⟨Q, x, y, hQ, hxQ, hyQ, hxΓ, hyΓ, hxy⟩ :=
      e6TwoThree_witness D hq2 hFr hΦ hn (ζ := (hζ0.isUnit (by norm_num)).unit) hζu.pow_eq_one
        hζu.eq_orderOf.symm (tw_dvd_add_of_orderOf_two Nat.prime_three (by norm_num) he)
    exact WCOn.of_mulEquiv (eK.trans eΓ) (tw_wcOn_of_noncomm hQ hxQ hyQ hxΓ hyΓ hxy)
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨L, _, _, hLchar, Fr, hFr, D, hΦ, hn, hfin, ⟨eΓ⟩⟩ :=
      exists_lang_twE6_model hℓ hf F hF2 σ hσ
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord)
    haveI := hfin
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    haveI : NeZero ((5 : ℕ) : L) := ⟨by
      intro h
      have := (CharP.cast_eq_zero_iff L ℓ 5).1 h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 this).symm⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
    have hζu := hζ0.isUnit_unit (by norm_num)
    obtain ⟨Q, x, y, hQ, hxQ, hyQ, hxΓ, hyΓ, hxy⟩ :=
      e6TwoFive_witness D hq2 hFr hΦ hn (ζ := (hζ0.isUnit (by norm_num)).unit) hζu.pow_eq_one
        hζu.eq_orderOf.symm (tw_dvd_add_of_orderOf_two (by norm_num) (by norm_num) he)
    exact WCOn.of_mulEquiv (eK.trans eΓ) (tw_wcOn_of_noncomm hQ hxQ hyQ hxΓ hyΓ hxy)

theorem crossChevalley_twistedE6 : CrossChevalley .twistedE6 := by
  intro K _ _ ℓ f p hp hadm hp2 hpℓ hmodel
  obtain ⟨hℓ, hf, -⟩ := hadm
  have hpq : ¬ p ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp.out hℓ).1 (hp.out.dvd_of_dvd_pow h))
  have hcardK : Nat.card K = ordTwistedE6 (ℓ ^ f) := by
    by_cases h2 : ℓ = 2
    · subst h2
      exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmodel
    · exact CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two h2 hmodel
  obtain ⟨F, _, hFfin, hFcard, σ0, hσ0, ⟨e1⟩⟩ := hmodel.2
  have hF2 : Nat.card F = (ℓ ^ f) ^ 2 := hFcard
  obtain ⟨e2⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.E6 hℓ hf F
    hFcard σ0 hσ0
  obtain ⟨σ, hσE⟩ : ∃ σ : F ≃+* F, σ.toRingHom = σ0 :=
    ⟨RingEquiv.ofBijective σ0 ⟨σ0.injective, Finite.surjective_of_injective σ0.injective⟩, rfl⟩
  subst hσE
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := hσ0
  have eK : K ≃* twistedE6RootGroup F σ := e1.trans e2
  have hq0 : (((ℓ ^ f : ℕ)) : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff _ p).1 h)
  have hdv : orderOf (((ℓ ^ f : ℕ)) : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  have hp4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp.out (by norm_num)
  have hp6 : p ≠ 6 := fun h => by rw [h] at hp; exact absurd hp.out (by norm_num)
  have hp2' := hp.out.two_le
  by_cases hdvd : p ∣ ordTwistedE6 (ℓ ^ f)
  · rcases tw_e6_eclass hp.out hp2 hpq hdvd with he | he | he | he | he | he | he | he | he
    ·
      by_cases hp3 : p = 3
      · exact wcOn_twistedE6_witness hℓ hf F hF2 σ hσ eK hpℓ he (Or.inl ⟨hp3, rfl⟩)
      · exact wcOn_twistedE6_class hℓ hf F hF2 σ hσ eK (by omega) hpq he (Or.inl rfl)
    ·
      by_cases hp3 : p = 3
      · exact wcOn_twistedE6_witness hℓ hf F hF2 σ hσ eK hpℓ he (Or.inr (Or.inl ⟨hp3, rfl⟩))
      · by_cases hp5 : p = 5
        · exact wcOn_twistedE6_witness hℓ hf F hF2 σ hσ eK hpℓ he (Or.inr (Or.inr ⟨hp5, rfl⟩))
        · have : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 2 := he
          have h7 : 7 ≤ p := by omega
          exact wcOn_twistedE6_class hℓ hf F hF2 σ hσ eK (by omega) hpq he
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h7⟩))))
    ·
      rw [he] at hdv
      exact wcOn_twistedE6_class hℓ hf F hF2 σ hσ eK (by omega) hpq he
        (Or.inr (Or.inl rfl))
    ·
      rw [he] at hdv
      exact wcOn_twistedE6_class hℓ hf F hF2 σ hσ eK (by omega) hpq he
        (Or.inr (Or.inr (Or.inl rfl)))
    ·
      rw [he] at hdv
      exact wcOn_twistedE6_class hℓ hf F hF2 σ hσ eK (by omega) hpq he
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact wcOn_twistedE6_cyclic hℓ hf F hF2 σ hσ eK he (Or.inl rfl)
    · exact wcOn_twistedE6_cyclic hℓ hf F hF2 σ hσ eK he (Or.inr (Or.inl rfl))
    · exact wcOn_twistedE6_cyclic hℓ hf F hF2 σ hσ eK he (Or.inr (Or.inr (Or.inl rfl)))
    · exact wcOn_twistedE6_cyclic hℓ hf F hF2 σ hσ eK he (Or.inr (Or.inr (Or.inr rfl)))
  · refine WCOn.of_factorization_le_one ?_
    rw [hcardK, Nat.factorization_eq_zero_of_not_dvd hdvd]
    exact Nat.zero_le _

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
