module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.Models.Blueprint
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Polynomial CFSG.Open CFSG.HardMathSupport.Timmesfeld.LinearRank

theorem exists_extension_prime_root (p : ℕ) [hp : Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hF : (p : F) ≠ 0) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : Algebra F F') (r : F'),
      r ^ p = 1 ∧ r ≠ 1 := by
  have hΦ0 : cyclotomic p F ≠ 0 := cyclotomic_ne_zero p F
  have hnu : ¬ IsUnit (cyclotomic p F) := by
    intro hu
    have hdeg := (Polynomial.isUnit_iff_degree_eq_zero.1 hu)
    have hnat : (cyclotomic p F).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_cyclotomic, Nat.totient_prime hp.out] at hnat
    have := hp.out.two_le
    omega
  obtain ⟨g, hg, hgΦ⟩ := WfDvdMonoid.exists_irreducible_factor hnu hΦ0
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hfin : Finite (AdjoinRoot g) := by
    haveI : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
    exact Module.finite_of_finite F
  refine ⟨AdjoinRoot g, inferInstance, hfin, inferInstance, AdjoinRoot.root g, ?_, ?_⟩
  · have hdvd : g ∣ (X : F[X]) ^ p - 1 := by
      rw [← cyclotomic_prime_mul_X_sub_one F p]
      exact Dvd.dvd.mul_right hgΦ _
    have h0 : AdjoinRoot.mk g ((X : F[X]) ^ p - 1) = 0 := (AdjoinRoot.mk_eq_zero).2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
    exact h0
  · intro h1
    have h2 : AdjoinRoot.mk g (cyclotomic p F) = 0 := (AdjoinRoot.mk_eq_zero).2 hgΦ
    rw [← AdjoinRoot.aeval_eq, h1] at h2
    have h3 := Polynomial.aeval_algebraMap_apply (AdjoinRoot g) (1 : F) (cyclotomic p F)
    rw [map_one] at h3
    rw [h3] at h2
    have h4 : aeval (1 : F) (cyclotomic p F) = 0 :=
      (algebraMap F (AdjoinRoot g)).injective (by rw [h2, map_zero])
    rw [Polynomial.coe_aeval_eq_eval, eval_one_cyclotomic_prime] at h4
    exact hF h4


theorem mem_center_map_iff {n : ℕ} {F F' : Type} [Field F] [Field F'] [Algebra F F']
    (hinj : Function.Injective (algebraMap F F')) (B : GL (Fin n) F) :
    (Matrix.GeneralLinearGroup.map (algebraMap F F') B : GL (Fin n) F') ∈
        Subgroup.center (GL (Fin n) F') ↔ B ∈ Subgroup.center (GL (Fin n) F) := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    apply Units.ext
    apply Matrix.map_injective hinj
    have := congrArg Units.val (h (Matrix.GeneralLinearGroup.map (algebraMap F F') g))
    simpa [Matrix.GeneralLinearGroup.map, Matrix.map_mul] using this
  · intro h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    obtain ⟨c, rfl⟩ := h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨Units.map (algebraMap F F') c, by rw [← Matrix.GeneralLinearGroup.map_scalar]⟩

theorem card_le_pow_statedProj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hF : (p : F) ≠ 0) {n : ℕ} (hn : 0 < n) (H : Subgroup (GL (Fin n) F))
    (E : Subgroup (StatedProj H)) (hE : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F', _, hfin, _, r, hr, hr1⟩ := exists_extension_prime_root p hF
  have hpK : p ∣ Nat.card F'ˣ := by
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.pos.ne'] at hr
      exact zero_ne_one hr
    let u : F'ˣ := Units.mk0 r hr0
    have hu : u ^ p = 1 := Units.ext (by simpa [u] using hr)
    have hu1 : u ≠ 1 := fun h => hr1 (by simpa [u] using congrArg Units.val h)
    rw [← orderOf_eq_prime hu hu1]
    exact orderOf_dvd_natCard u
  let ι : GL (Fin n) F →* GL (Fin n) F' := Matrix.GeneralLinearGroup.map (algebraMap F F')
  have hinj : Function.Injective ι := by
    intro A B h
    apply Units.ext
    have := congrArg (fun C : GL (Fin n) F' => (C : Matrix (Fin n) (Fin n) F')) h
    exact Matrix.map_injective (algebraMap F F').injective this
  let U : Subgroup (GL (Fin n) F') := H.map ι
  let φ : ↥H ≃* ↥U := Subgroup.equivMapOfInjective H ι hinj
  let ρ : U →* StatedProj H :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf H)).comp φ.symm.toMonoidHom
  have hker : ∀ A : U, ρ A = 1 ↔ (A : GL (Fin n) F') ∈ Subgroup.center (GL (Fin n) F') := by
    intro A
    have hB : (A : GL (Fin n) F') = ι (φ.symm A : GL (Fin n) F) := by
      calc (A : GL (Fin n) F') = ((φ (φ.symm A) : U) : GL (Fin n) F') := by
            rw [φ.apply_symm_apply]
        _ = ι (φ.symm A : GL (Fin n) F) :=
            Subgroup.coe_equivMapOfInjective_apply H ι hinj _
    have hs : ρ A = 1 ↔ (φ.symm A : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
      change QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf H) (φ.symm A) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Matrix.GeneralLinearGroup.center_eq_range_scalar]
      rfl
    rw [hs, hB]
    exact (mem_center_map_iff (algebraMap F F').injective _).symm
  have hrange : ρ.range = ⊤ := by
    refine MonoidHom.range_eq_top.2 ?_
    exact (QuotientGroup.mk'_surjective _).comp φ.symm.surjective
  have hEρ : E ≤ ρ.range := by
    rw [hrange]
    exact le_top
  exact card_le_of_scalar_kernel hp hp2 hpK hn U ρ hker E hEρ hE

theorem inf_center_eq_bot_of_card_dvd_two {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : Nat.card (Subgroup.center Q) ∣ 2) {E : Subgroup Q}
    (hE : CFSG.Open.IsElemAbelian p E) : E ⊓ Subgroup.center Q = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p ↥(E ⊓ Subgroup.center Q) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g.1 (Subgroup.mem_inf.1 g.2).1)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card ↥(E ⊓ Subgroup.center Q) ∣ Nat.card (Subgroup.center Q) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : p ∣ 2 := (dvd_pow_self p hk0).trans (hdvd.trans hZ)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  rw [hk0, pow_zero] at hk
  exact (Subgroup.eq_bot_iff_card _).2 hk

theorem pRank_le_three_of_bound {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup Q) (hq : ∀ E : Subgroup Q, CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p ^ 3) :
    CFSG.Open.pRank p H ≤ 3 := by
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, hE, hcard⟩
  have h := hq E hE
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h

theorem evenRank_le_three_of_bound {Q : Type} [Group Q] [Finite Q]
    (hq : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ E : Subgroup Q, CFSG.Open.IsElemAbelian p E →
      Nat.card E ≤ p ^ 3) : CFSG.Open.evenRank Q ≤ 3 := by
  unfold CFSG.Open.evenRank
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, -, rfl⟩
  exact pRank_le_three_of_bound hp hp2 H (hq p hp hp2)

theorem card_le_three_of_quot {Q : Type} [Group Q] [Finite Q] (hZ : Nat.card (Subgroup.center Q) ∣ 2)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4) (H0 : Subgroup (GL (Fin n) F))
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj H0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : (p : F) ≠ 0) (E : Subgroup Q) (hE : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ 3 := by
  let g : Q →* StatedProj H0 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hbot := inf_center_eq_bot_of_card_dvd_two hp hp2 hZ hE
  have hinj : Function.Injective (g.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x.1 ∈ Subgroup.center Q := by
      have h1 : g x.1 = 1 := hx
      simp only [g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply] at h1
      have h2 : (QuotientGroup.mk x.1 : Q ⧸ Subgroup.center Q) = 1 := e.injective (by rw [map_one]; exact h1)
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hmem : x.1 ∈ E ⊓ Subgroup.center Q := Subgroup.mem_inf.2 ⟨x.2, hx'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  let E' : Subgroup (StatedProj H0) := E.map g
  have hE' : CFSG.Open.IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hE g
  have hrange : E' = (g.comp E.subtype).range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
  have hcard : Nat.card E' = Nat.card E := by
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h := card_le_pow_statedProj hp hp2 hF hn H0 E' hE'
  rw [hcard] at h
  exact h.trans (Nat.pow_le_pow_right hp.pos (by omega))

theorem natCast_ne_zero_of_card_two_pow {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro h
  haveI := Fintype.ofFinite F
  obtain ⟨m, hq, hcard⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card] at hcard
  have hdvd : ringChar F ∣ p := (CharP.cast_eq_zero_iff F (ringChar F) p).1 h
  have hpe : ringChar F = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd
  rw [hpe, hF] at hcard
  have h2 : p ∣ 2 ^ f := by
    rw [hcard]
    exact dvd_pow_self p (by exact_mod_cast m.pos.ne')
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))

abbrev multProd (t : CFSG.Open.StatedLieTag) (n p f : ℕ) : ℕ :=
  (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
    (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
    ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2)

theorem card_center_dvd_two {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q)
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) t n p f) (hd : multProd t n p f ∣ 2) :
    Nat.card (Subgroup.center Q) ∣ 2 := by
  have hne : multProd t n p f ≠ 0 := fun h => two_ne_zero (zero_dvd_iff.1 (h ▸ hd))
  exact (LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hQ hm rfl rfl hne).trans hd

theorem gcd_two_pow_sub_one_eq_one {m f : ℕ} (hm : m = 2 ∨ m = 4) (hf : 1 ≤ f) :
    Nat.gcd m (2 ^ f - 1) = 1 := by
  obtain ⟨c, hc⟩ := dvd_pow_self 2 (show f ≠ 0 by omega)
  have h1 := Nat.one_le_two_pow (n := f)
  have hodd : (2 ^ f - 1) % 2 = 1 := by omega
  have hcop : Nat.Coprime 2 (2 ^ f - 1) := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  rcases hm with rfl | rfl
  · exact hcop
  · exact Nat.Coprime.pow_left 2 hcop

theorem gcd_two_pow_add_one_eq_one {m f : ℕ} (hm : m = 2 ∨ m = 4) (hf : 1 ≤ f) :
    Nat.gcd m (2 ^ f + 1) = 1 := by
  obtain ⟨c, hc⟩ := dvd_pow_self 2 (show f ≠ 0 by omega)
  have hodd : (2 ^ f + 1) % 2 = 1 := by omega
  have hcop : Nat.Coprime 2 (2 ^ f + 1) := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  rcases hm with rfl | rfl
  · exact hcop
  · exact Nat.Coprime.pow_left 2 hcop

theorem genericOrders_PSL (n p f : ℕ) :
    CFSG.Blueprint.Multiplier.genericOrders .PSL n p f = (Nat.gcd n (p ^ f - 1), 1) := rfl

theorem genericOrders_PSU (n p f : ℕ) :
    CFSG.Blueprint.Multiplier.genericOrders .PSU n p f = (Nat.gcd n (p ^ f + 1), 1) := rfl

theorem exceptionalOrders_PSL_four_two (f : ℕ) (hf : f ≠ 1) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem multProd_PSL_four {f : ℕ} (hf : 1 ≤ f) : multProd .PSL 4 2 f ∣ 2 := by
  have hg : Nat.gcd 4 (2 ^ f - 1) = 1 := gcd_two_pow_sub_one_eq_one (Or.inr rfl) hf
  unfold multProd
  rw [genericOrders_PSL, hg]
  by_cases h1 : f = 1
  · subst h1
    exact (by decide : (1 * 1 * ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1).2) ∣ 2))
  · rw [exceptionalOrders_PSL_four_two f h1]
    simp

theorem multProd_PSU_four {f : ℕ} (hf : 1 ≤ f) : multProd .PSU 4 2 f ∣ 2 := by
  have hg : Nat.gcd 4 (2 ^ f + 1) = 1 := gcd_two_pow_add_one_eq_one (Or.inr rfl) hf
  unfold multProd
  rw [genericOrders_PSU, hg]
  by_cases h1 : f = 1
  · subst h1
    exact (by decide : (1 * 1 * ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1).2) ∣ 2))
  · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [he]
    simp

theorem multProd_PSL_two {f : ℕ} (hf : 1 ≤ f) : multProd .PSL 2 2 f ∣ 2 := by
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := gcd_two_pow_sub_one_eq_one (Or.inl rfl) hf
  unfold multProd
  rw [genericOrders_PSL, hg]
  by_cases h1 : f = 2
  · subst h1
    exact (by decide : (1 * 1 * ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 2).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 2).2) ∣ 2))
  · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [he]
    simp

theorem evenRank_le_three_PSL_four {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q) {f : ℕ} (hf : 1 ≤ f)
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 4 2 f) : CFSG.Open.evenRank Q ≤ 3 := by
  have hZ := card_center_dvd_two hGA hQ (CFSG.Models.LieModel.of_blueprint (by decide) hm)
    (multProd_PSL_four hf)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  exact evenRank_le_three_of_bound fun p hp hp2 E hE =>
    card_le_three_of_quot hZ (by norm_num) (by norm_num) _ e hp hp2
      (natCast_ne_zero_of_card_two_pow hF hp hp2) E hE

theorem evenRank_le_three_PSU_four {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q) {f : ℕ} (hf : 1 ≤ f)
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSU 4 2 f) : CFSG.Open.evenRank Q ≤ 3 := by
  have hZ := card_center_dvd_two hGA hQ (CFSG.Models.LieModel.of_blueprint (by decide) hm)
    (multProd_PSU_four hf)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  exact evenRank_le_three_of_bound fun p hp hp2 E hE =>
    card_le_three_of_quot hZ (by norm_num) (by norm_num) _ e hp hp2
      (natCast_ne_zero_of_card_two_pow (f := f * 2) (by rw [hF, ← pow_mul]) hp hp2) E hE

theorem evenRank_le_three_PSL_two {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q) {f : ℕ} (hf : 1 ≤ f)
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 2 2 f) : CFSG.Open.evenRank Q ≤ 3 := by
  have hZ := card_center_dvd_two hGA hQ (CFSG.Models.LieModel.of_blueprint (by decide) hm)
    (multProd_PSL_two hf)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  exact evenRank_le_three_of_bound fun p hp hp2 E hE =>
    card_le_three_of_quot hZ (by norm_num) (by norm_num) _ e hp hp2
      (natCast_ne_zero_of_card_two_pow hF hp hp2) E hE

theorem not_pow_four_dvd_2160 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 4 ∣ 2160 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hp7 : p < 7 := by
    by_contra h7
    have h7' : 7 ≤ p := not_lt.1 h7
    have : 7 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h7' 4
    omega
  interval_cases p
  all_goals revert h hp hp2; norm_num

theorem not_pow_four_dvd_12096 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 4 ∣ 12096 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hp11 : p < 11 := by
    by_contra h11
    have h11' : 11 ≤ p := not_lt.1 h11
    have : 11 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h11' 4
    omega
  interval_cases p
  all_goals revert h hp hp2; norm_num

theorem evenRank_le_three_of_card_dvd {Q : Type} [Group Q] [Finite Q] {N : ℕ}
    (hQ : Nat.card Q ∣ N) (hN : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 4 ∣ N) :
    CFSG.Open.evenRank Q ≤ 3 := by
  refine evenRank_le_three_of_bound fun p hp hp2 E hE => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hdvd : p ^ k ∣ N := by
    rw [← hk]
    exact (Subgroup.card_subgroup_dvd_card E).trans hQ
  have hk3 : k ≤ 3 := by
    by_contra h4
    have h4' : 4 ≤ k := not_le.1 h4
    have h4N : p ^ 4 ∣ N := (pow_dvd_pow p h4').trans hdvd
    exact hN p hp hp2 h4N
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk3

end CFSG.LocalAnalysis.GLTheoremA
