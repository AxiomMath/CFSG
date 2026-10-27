module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Root
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartOne.KE

section Norm

variable {G : Type*} [Group G]

@[expose] def langNorm (F : G →* G) (n : G) : ℕ → G
  | 0 => 1
  | k + 1 => n * F (langNorm F n k)

theorem langNorm_zero (F : G →* G) (n : G) : langNorm F n 0 = 1 :=
  rfl

theorem langNorm_succ (F : G →* G) (n : G) (k : ℕ) :
    langNorm F n (k + 1) = n * F (langNorm F n k) :=
  rfl

theorem iterate_map_eq_mul_langNorm (F : G →* G) {n g₀ : G} (hg : F g₀ = g₀ * n) (k : ℕ) :
    F^[k] g₀ = g₀ * langNorm F n k := by
  induction k with
  | zero => simp [langNorm_zero]
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, hg, langNorm_succ, mul_assoc]

theorem iterate_conj_comp_apply (F : G →* G) (n : G) (k : ℕ) (x : G) :
    ((MulAut.conj n).toMonoidHom.comp F)^[k] x =
      langNorm F n k * F^[k] x * (langNorm F n k)⁻¹ := by
  induction k with
  | zero => simp [langNorm_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', langNorm_succ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    group

end Norm

section Root


theorem exists_frobRoot_of_step_pow_twist {t : TwistTag} {L : Type} [Field L] [CharP L 2]
    {p e : ℕ} (D₀ D : LangDatum t.tag L) (hΦ₀ : D₀.Φ = twistHom t L (iterateFrobenius L 2 e))
    (hq : D.q = 2 ^ (e * p)) (hpow : ∀ g, D₀.step^[p] g = D.step g) :
    ∃ R : FrobRoot D p, R.q0 = 2 ^ e ∧ R.Fr0 = iterateFrobenius L 2 e ∧
      R.z0 = D₀.n * diagramMap t L ∧ ∀ g, D₀.step g = R.step0 g := by
  have hstepP : ∀ g, D₀.step g = D₀.n * diagramMap t L *
      Units.map (entrywiseHom (iterateFrobenius L 2 e)) g * (D₀.n * diagramMap t L)⁻¹ :=
    fun g => by
      show D₀.n * D₀.Φ g * D₀.n⁻¹ = _
      rw [hΦ₀, twistHom_apply, mul_inv_rev]
      group
  have hfun : (fun h => D₀.n * diagramMap t L *
      Units.map (entrywiseHom (iterateFrobenius L 2 e)) h * (D₀.n * diagramMap t L)⁻¹) =
        ⇑D₀.step := funext fun h => (hstepP h).symm
  refine ⟨⟨2 ^ e, iterateFrobenius L 2 e, iterateFrobenius_def 2 e, D₀.n * diagramMap t L,
    by rw [hq, pow_mul], fun g => ?_⟩, rfl, rfl, rfl, fun g => ?_⟩
  · rw [hfun]
    exact hpow g
  · exact hstepP g

end Root

section Canonical


theorem langNorm_twistHom_canonicalRep {t : TwistTag} {L : Type} [Field L] [CharP L 2]
    (σ : L →+* L) (w₀ : WeylGroup t.tag) (k : ℕ) :
    ∃ w : WeylGroup t.tag,
      langNorm (twistHom t L σ) (canonicalRep (coxeterSystem t.tag) L w₀) k =
        canonicalRep (coxeterSystem t.tag) L w := by
  induction k with
  | zero => exact ⟨1, by rw [langNorm_zero, canonicalRep_one]⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨w₀ * weylTwist t w, by
      rw [langNorm_succ, hw, twistHom_canonicalRep,
        CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo]⟩

theorem iterate_twistHom_iterateFrobenius {t : TwistTag} {L : Type} [Field L] [CharP L 2] {p : ℕ}
    (hpt : p % t.order = 1) (e : ℕ) (y : ModGL t.tag L) :
    (twistHom t L (iterateFrobenius L 2 e))^[p] y =
      twistHom t L (iterateFrobenius L 2 (e * p)) y := by
  have hQ : Units.map (entrywiseHom (iterateFrobenius L 2 e)) (diagramMap t L) =
      diagramMap t L := units_map_entrywiseHom_diagramMap _
  have hQp : diagramMap t L ^ p = diagramMap t L := by
    have h1 : p = t.order * (p / t.order) + 1 := by
      have := Nat.div_add_mod p t.order
      rw [hpt] at this
      exact this.symm
    conv_lhs => rw [h1]
    rw [pow_add, pow_mul, diagramMap_pow_order, one_pow, one_mul, pow_one]
  have hfun : ⇑(twistHom t L (iterateFrobenius L 2 e)) = fun h => diagramMap t L *
      Units.map (entrywiseHom (iterateFrobenius L 2 e)) h * (diagramMap t L)⁻¹ :=
    funext fun h => twistHom_apply _ h
  rw [hfun, iterate_conj_map_eq _ hQ p y, hQp,
    iterate_units_map_entrywiseHom_iterateFrobenius 2 e p, twistHom_apply]

theorem exists_langDatum_step_pow_twist {t : TwistTag} {L : Type} [Field L] [CharP L 2]
    {p e : ℕ} (hpt : p % t.order = 1) (D₀ : LangDatum t.tag L)
    (hΦ₀ : D₀.Φ = twistHom t L (iterateFrobenius L 2 e)) :
    ∃ D : LangDatum t.tag L, D.Φ = twistHom t L (iterateFrobenius L 2 (e * p)) ∧
      D.q = 2 ^ (e * p) ∧ D.g0 = D₀.g0 ∧ ∀ g, D₀.step^[p] g = D.step g := by
  obtain ⟨w₀, hw₀⟩ := D₀.n_weyl
  obtain ⟨wp, hwp⟩ := langNorm_twistHom_canonicalRep (iterateFrobenius L 2 e) w₀ p
  rw [← hw₀] at hwp
  have hlang : twistHom t L (iterateFrobenius L 2 e) D₀.g0 = D₀.g0 * D₀.n := by
    rw [← hΦ₀]
    exact D₀.lang
  have hg : twistHom t L (iterateFrobenius L 2 (e * p)) D₀.g0 =
      D₀.g0 * canonicalRep (coxeterSystem t.tag) L wp := by
    rw [← hwp, ← iterate_twistHom_iterateFrobenius hpt e, iterate_map_eq_mul_langNorm _ hlang p]
  obtain ⟨D, hDΦ, hDq, hDn, hDg⟩ : ∃ D : LangDatum t.tag L,
      D.Φ = twistHom t L (iterateFrobenius L 2 (e * p)) ∧ D.q = 2 ^ (e * p) ∧
        D.n = langNorm (twistHom t L (iterateFrobenius L 2 e)) D₀.n p ∧ D.g0 = D₀.g0 :=
    ⟨LangDatum.ofTwist t (iterateFrobenius L 2 (e * p)) (2 ^ (e * p))
      (iterateFrobenius_def 2 (e * p)) wp D₀.g0_mem hg, rfl, rfl, hwp.symm, rfl⟩
  have hstep : ⇑D₀.step = ⇑((MulAut.conj D₀.n).toMonoidHom.comp
      (twistHom t L (iterateFrobenius L 2 e))) :=
    funext fun x => by
      show D₀.n * D₀.Φ x * D₀.n⁻¹ = _
      rw [hΦ₀]
      rfl
  refine ⟨D, hDΦ, hDq, hDg, fun g => ?_⟩
  rw [hstep, iterate_conj_comp_apply]
  show _ = D.n * D.Φ g * D.n⁻¹
  rw [hDn, hDΦ, ← iterate_twistHom_iterateFrobenius hpt e]

end Canonical

section Datum


theorem exists_langDatum_frobRoot_twist_D0 {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p e : ℕ} (he : 1 ≤ e) (hpt : p % t.order = 1) {u : ModGL t.tag L}
    (hfix : twistHom t L (iterateFrobenius L 2 e) u = u)
    (hconj : ∃ g ∈ adjointGroup t.tag L, g⁻¹ * u * g ∈ torusGroup t.tag L) :
    ∃ (D₀ D : LangDatum t.tag L) (R : FrobRoot D p),
      D₀.Φ = twistHom t L (iterateFrobenius L 2 e) ∧ D₀.q = 2 ^ e ∧
      D.Φ = twistHom t L (iterateFrobenius L 2 (e * p)) ∧ D.q = 2 ^ (e * p) ∧
      D.g0 = D₀.g0 ∧ R.q0 = 2 ^ e ∧ R.Fr0 = iterateFrobenius L 2 e ∧
      R.z0 = D₀.n * diagramMap t L ∧ (∀ g, D₀.step g = R.step0 g) ∧
      u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom ∧
      R.step0 (D.g0⁻¹ * u * D.g0) = D.g0⁻¹ * u * D.g0 ∧
      ∀ y, R.step0 (D.g0⁻¹ * y * D.g0) =
        D.g0⁻¹ * twistHom t L (iterateFrobenius L 2 e) y * D.g0 := by
  obtain ⟨D₀, hΦ₀, hq₀, y, hy, hyu⟩ := exists_langDatum_of_toral_twisted t e he hfix hconj
  obtain ⟨D, hDΦ, hDq, hDg, hpow⟩ := exists_langDatum_step_pow_twist hpt D₀ hΦ₀
  obtain ⟨R, hRq, hRFr, hRz, hRstep⟩ := exists_frobRoot_of_step_pow_twist D₀ D hΦ₀ hDq hpow
  have hy1 : D₀.step y = y := (mem_twistedTorusOf.1 hy).2
  have hyD : y ∈ D.torus := mem_twistedTorusOf.2 ⟨(mem_twistedTorusOf.1 hy).1,
    (hpow y).symm.trans (Function.iterate_fixed hy1 p)⟩
  have hyu' : y = D₀.g0⁻¹ * u * D₀.g0 := by
    have h : D₀.g0 * y * D₀.g0⁻¹ = u := hyu
    rw [← h]
    group
  refine ⟨D₀, D, R, hΦ₀, hq₀, hDΦ, hDq, hDg, hRq, hRFr, hRz, hRstep,
    ⟨y, hyD, by rw [hDg]; exact hyu⟩, ?_, fun y' => ?_⟩
  · rw [hDg, ← hyu', ← hRstep]
    exact hy1
  · rw [hDg, ← hRstep]
    show D₀.n * D₀.Φ (D₀.g0⁻¹ * y' * D₀.g0) * D₀.n⁻¹ = _
    rw [map_mul, map_mul, map_inv, D₀.lang, hΦ₀]
    group

theorem exists_langSetup_frobRoot_twist_D0 {t : TwistTag} {K : Type} [Field K] [Finite K]
    [CharP K 2] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hpt : p % t.order = 1)
    (hmon : MonomialToralAt t.tag p) {C : Type} [Group C] (κ : C →* ModGL t.tag K)
    (hκ : Function.Injective κ) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e)) (β φ : MulAut C)
    (h : ModGL t.tag K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup t.tag (AlgebraicClosure K))
    (hβ : ∀ c, κ (β c) = h * κ c * h⁻¹)
    (hφ : ∀ c, κ (φ c) = diagramMap t K * Units.map (entrywiseHom T) (κ c) *
      (diagramMap t K)⁻¹)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1)
    (hfix : diagramMap t K * Units.map (entrywiseHom T) h * (diagramMap t K)⁻¹ = h)
    (hdesc : ∀ D : LangDatum t.tag (AlgebraicClosure K),
      D.Φ = twistHom t (AlgebraicClosure K)
        (iterateFrobenius (AlgebraicClosure K) 2 (e * p)) →
      Finite D.model ∧ D.Γ = ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp κ).range.map
        (MulAut.conj D.g0⁻¹).toMonoidHom) :
    ∃ (S : LangSetup t.tag (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin t.tag.rank → (AlgebraicClosure K)ˣ)
      (ι : C →* ModGL t.tag (AlgebraicClosure K)),
      S.D.q = 2 ^ (e * p) ∧ R.q0 = 2 ^ e ∧
      rootDiagUnit t.tag a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit t.tag a ≠ 1 ∧
      R.step0 (rootDiagUnit t.tag a) = rootDiagUnit t.tag a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit t.tag a * ι c * (rootDiagUnit t.tag a)⁻¹) ∧
      (∀ c, ι (φ c) = R.step0 (ι c)) ∧
      ∃ D₀ : LangDatum t.tag (AlgebraicClosure K), D₀.q = R.q0 ∧ ∀ g, D₀.step g = R.step0 g := by
  classical
  set L := AlgebraicClosure K with hLdef
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hcomp : (iterateFrobenius L 2 e).comp ι₁ = ι₁.comp T := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, iterateFrobenius_def, hT, map_pow]
  have hbc : ∀ x : ModGL t.tag K, twistHom t L (iterateFrobenius L 2 e) (baseChangeGL ι₁ x) =
      baseChangeGL ι₁ (twistHom t K T x) := twistHom_baseChangeGL ι₁ hcomp.symm
  set u : ModGL t.tag L := baseChangeGL ι₁ h with hu
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hfixL : twistHom t L (iterateFrobenius L 2 e) u = u := by
    rw [hu, hbc]
    exact congrArg (baseChangeGL ι₁) hfix
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon (Ne.symm hp2)
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hhL hup
  obtain ⟨D₀, D, R, -, hD₀q, hΦ, hq, -, hRq0, -, -, hstep, hmem, hfixd, hconjstep⟩ :=
    exists_langDatum_frobRoot_twist_D0 he hpt hfixL hconj
  obtain ⟨hfin, hΓ⟩ := hdesc D hΦ
  set ι₀ : C →* ModGL t.tag L := (baseChangeGL ι₁).comp κ with hι₀
  have hι₀inj : Function.Injective ι₀ := (baseChangeGL_injective _).comp hκ
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (κ (β c)) =
      baseChangeGL ι₁ h * baseChangeGL ι₁ (κ c) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hep : 2 ≤ e * p := by nlinarith [hp.two_le]
  have hq' : 5 ≤ p ∨ 4 ≤ D.q := Or.inr (by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * p) := Nat.pow_le_pow_right (by norm_num) hep)
  obtain ⟨S, a, ι, rfl, hTa, hap, h1, hda, hι, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime_descent Nat.prime_two (le_trans (by norm_num) hep) D
      hq hp hp2 hq' hfin ι₀ hι₀inj hΓ β hβ' hmem hup hu1
  refine ⟨S, R, a, ι, hq, hRq0, hTa, hap, h1, ?_, hinj, hrange, hconjι, fun c => ?_, D₀,
    hD₀q.trans hRq0.symm, hstep⟩
  · rw [hda]
    exact hfixd
  · have h' : ι₀ (φ c) = twistHom t L (iterateFrobenius L 2 e) (ι₀ c) :=
      (congrArg (baseChangeGL ι₁) (hφ c)).trans (hbc (κ c)).symm
    rw [hι (φ c), hι c, hconjstep, h']

end Datum

section Twisted


theorem exists_langSetup_frobRoot_twE6_D0 {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    {K : Type} [Field K] (hK : Nat.card K = (2 ^ (e * p)) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ (e * p))) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e))
    (β φ : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹)
    (hφ : ∀ c, (φ c : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
      Units.map (entrywiseHom T) c * (diagramMap TwistTag.E6 K)⁻¹)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1)
    (hfix : diagramMap TwistTag.E6 K * Units.map (entrywiseHom T) h *
      (diagramMap TwistTag.E6 K)⁻¹ = h) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = 2 ^ (e * p) ∧ R.q0 = 2 ^ e ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      R.step0 (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      (∀ c, ι (φ c) = R.step0 (ι c)) ∧
      ∃ D₀ : LangDatum Tag.E6 (AlgebraicClosure K), D₀.q = R.q0 ∧ ∀ g, D₀.step g = R.step0 g := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := e * p * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  set L := AlgebraicClosure K with hLdef
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ (2 ^ (e * p)) := fun c =>
    iterateFrobenius_def 2 (e * p) c
  have hhL : baseChangeGL ι₁ h ∈ adjointGroup TwistTag.E6.tag L :=
    (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ
      (iterateFrobenius L 2 (e * p)) hFr ⟨h, hh, rfl⟩).1
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  refine exists_langSetup_frobRoot_twist_D0 (t := TwistTag.E6) hp hp2 he ?_ hmon
    (twistedE6RootGroup K σ).subtype (Subgroup.subtype_injective _) T hT β φ h hhL hβ hφ hp1 hh1
    hfix ?_
  · show p % 2 = 1
    exact hp.eq_two_or_odd.resolve_left hp2
  · intro D hΦ
    refine ⟨finite_model_twistedE6 Nat.prime_two hf hK hσ hFr D hΦ, ?_⟩
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Γ_eq_map_twistedE6RootGroup Nat.prime_two hf hK hσ hFr D hΦ

end Twisted

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

end
