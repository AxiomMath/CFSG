module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Root
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TriD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

section Transport

variable {G : Type*} [Group G]

theorem iterate_transport_eq (F : G →* G) {Q : G} (hQ : F Q = Q) (g₀ : G) (k : ℕ) (x : G) :
    (fun h => (g₀⁻¹ * Q * F g₀) * F h * (g₀⁻¹ * Q * F g₀)⁻¹)^[k] x =
      g₀⁻¹ * (Q ^ k * F^[k] (g₀ * x * g₀⁻¹) * (Q ^ k)⁻¹) * g₀ := by
  have hstep : ∀ y, (g₀⁻¹ * Q * F g₀) * F y * (g₀⁻¹ * Q * F g₀)⁻¹ =
      g₀⁻¹ * (Q * F (g₀ * y * g₀⁻¹) * Q⁻¹) * g₀ := fun y => by
    rw [map_mul, map_mul, map_inv]
    group
  have key : ∀ (k : ℕ) (y : G),
      (fun h => (g₀⁻¹ * Q * F g₀) * F h * (g₀⁻¹ * Q * F g₀)⁻¹)^[k] y =
        g₀⁻¹ * ((fun h => Q * F h * Q⁻¹)^[k] (g₀ * y * g₀⁻¹)) * g₀ := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
      group
    | succ k ih =>
      intro y
      have e : g₀ * (g₀⁻¹ * (fun h => Q * F h * Q⁻¹)^[k] (g₀ * y * g₀⁻¹) * g₀) * g₀⁻¹ =
          (fun h => Q * F h * Q⁻¹)^[k] (g₀ * y * g₀⁻¹) := by group
      rw [Function.iterate_succ_apply', ih]
      show (g₀⁻¹ * Q * F g₀) * F (g₀⁻¹ * (fun h => Q * F h * Q⁻¹)^[k] (g₀ * y * g₀⁻¹) * g₀) *
        (g₀⁻¹ * Q * F g₀)⁻¹ = _
      rw [hstep, e, Function.iterate_succ_apply' (fun h => Q * F h * Q⁻¹) k]
  rw [key, iterate_conj_map_eq F hQ]

end Transport

section Root


theorem exists_frobRoot_of_transport {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) (p : ℕ)
    {q0 : ℕ} (Fr0 : L →+* L) (hFr0 : ∀ c, Fr0 c = c ^ q0) (hq : D.q = q0 ^ p)
    {Q : ModGL τ L} (hQ : Units.map (entrywiseHom Fr0) Q = Q)
    (hΦ : ∀ y, D.Φ y = Q ^ p * (⇑(Units.map (entrywiseHom Fr0)))^[p] y * (Q ^ p)⁻¹) :
    ∃ R : FrobRoot D p, R.q0 = q0 ∧ R.Fr0 = Fr0 ∧
      R.z0 = D.g0⁻¹ * Q * Units.map (entrywiseHom Fr0) D.g0 := by
  refine ⟨⟨q0, Fr0, hFr0, D.g0⁻¹ * Q * Units.map (entrywiseHom Fr0) D.g0, hq, fun g => ?_⟩,
    rfl, rfl, rfl⟩
  rw [iterate_transport_eq _ hQ, ← hΦ]
  show _ = D.n * D.Φ g * D.n⁻¹
  rw [map_mul, map_mul, map_inv, D.lang]
  group

end Root

section Core


theorem exists_langDatum_frobRoot_twist {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p e j : ℕ} (hp : 0 < p) (he : 1 ≤ e) (hjp : j * p % t.order = 1)
    {u : ModGL t.tag L}
    (hfix : diagramMap t L ^ j * Units.map (entrywiseHom (iterateFrobenius L 2 e)) u *
      (diagramMap t L ^ j)⁻¹ = u)
    (hconj : ∃ g ∈ adjointGroup t.tag L, g⁻¹ * u * g ∈ torusGroup t.tag L) :
    ∃ (D : LangDatum t.tag L) (R : FrobRoot D p),
      D.Φ = twistHom t L (iterateFrobenius L 2 (e * p)) ∧ D.q = 2 ^ (e * p) ∧ R.q0 = 2 ^ e ∧
      u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom ∧
      R.step0 (D.g0⁻¹ * u * D.g0) = D.g0⁻¹ * u * D.g0 ∧
      ∀ y, R.step0 (D.g0⁻¹ * y * D.g0) = D.g0⁻¹ * (diagramMap t L ^ j *
        Units.map (entrywiseHom (iterateFrobenius L 2 e)) y * (diagramMap t L ^ j)⁻¹) * D.g0 := by
  have hf : 1 ≤ e * p := Nat.mul_pos he hp
  have hQ : Units.map (entrywiseHom (iterateFrobenius L 2 e)) (diagramMap t L ^ j) =
      diagramMap t L ^ j := by
    rw [map_pow, units_map_entrywiseHom_diagramMap]
  have hQp : (diagramMap t L ^ j) ^ p = diagramMap t L := by
    have h1 : j * p = t.order * (j * p / t.order) + 1 := by
      have := Nat.div_add_mod (j * p) t.order
      rw [hjp] at this
      exact this.symm
    rw [← pow_mul, h1, pow_add, pow_mul, diagramMap_pow_order, one_pow, one_mul, pow_one]
  have hbig : ∀ y, (diagramMap t L ^ j) ^ p *
      (⇑(Units.map (entrywiseHom (iterateFrobenius L 2 e))))^[p] y *
        ((diagramMap t L ^ j) ^ p)⁻¹ = twistHom t L (iterateFrobenius L 2 (e * p)) y :=
    fun y => by
      rw [hQp, iterate_units_map_entrywiseHom_iterateFrobenius 2 e p, twistHom_apply]
  have hufix : twistHom t L (iterateFrobenius L 2 (e * p)) u = u := by
    rw [← hbig u, ← iterate_conj_map_eq _ hQ p u]
    exact Function.iterate_fixed (f := fun h => diagramMap t L ^ j *
      Units.map (entrywiseHom (iterateFrobenius L 2 e)) h * (diagramMap t L ^ j)⁻¹) hfix p
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted t (e * p) hf hufix hconj
  obtain ⟨R, hRq0, hRFr0, hRz0⟩ := exists_frobRoot_of_transport D p (iterateFrobenius L 2 e)
    (iterateFrobenius_def 2 e) (by rw [hDq, pow_mul]) hQ (fun y => by rw [hΦ, hbig])
  have hstep1 : ∀ x, R.step0 x = D.g0⁻¹ * (diagramMap t L ^ j *
      Units.map (entrywiseHom (iterateFrobenius L 2 e)) (D.g0 * x * D.g0⁻¹) *
        (diagramMap t L ^ j)⁻¹) * D.g0 := fun x => by
    have h := iterate_transport_eq (Units.map (entrywiseHom (iterateFrobenius L 2 e))) hQ D.g0 1 x
    simp only [Function.iterate_one, pow_one] at h
    rw [R.step0_apply, hRz0, hRFr0]
    exact h
  refine ⟨D, R, hΦ, hDq, hRq0, hmem, ?_, fun y => ?_⟩
  · rw [hstep1]
    have e1 : D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ = u := by group
    rw [e1, hfix]
  · rw [hstep1]
    have e1 : D.g0 * (D.g0⁻¹ * y * D.g0) * D.g0⁻¹ = y := by group
    rw [e1]

theorem exists_langSetup_frobRoot_twist {t : TwistTag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p e j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hjp : j * p % t.order = 1)
    (hmon : MonomialToralAt t.tag p) {C : Type} [Group C] (κ : C →* ModGL t.tag K)
    (hκ : Function.Injective κ) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e)) (β φ : MulAut C)
    (h : ModGL t.tag K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup t.tag (AlgebraicClosure K))
    (hβ : ∀ c, κ (β c) = h * κ c * h⁻¹)
    (hφ : ∀ c, κ (φ c) = diagramMap t K ^ j * Units.map (entrywiseHom T) (κ c) *
      (diagramMap t K ^ j)⁻¹)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1)
    (hfix : diagramMap t K ^ j * Units.map (entrywiseHom T) h * (diagramMap t K ^ j)⁻¹ = h)
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
      ∀ c, ι (φ c) = R.step0 (ι c) := by
  classical
  set L := AlgebraicClosure K with hLdef
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hcomp : (iterateFrobenius L 2 e).comp ι₁ = ι₁.comp T := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, iterateFrobenius_def, hT, map_pow]
  have hcomm := units_map_entrywiseHom_baseChangeGL_comm (τ := t.tag) ι₁ (iterateFrobenius L 2 e) T
    hcomp
  have hQK : baseChangeGL ι₁ (diagramMap t K ^ j) = diagramMap t L ^ j := by
    rw [map_pow, baseChangeGL_diagramMap]
  set u : ModGL t.tag L := baseChangeGL ι₁ h with hu
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hfixL : diagramMap t L ^ j * Units.map (entrywiseHom (iterateFrobenius L 2 e)) u *
      (diagramMap t L ^ j)⁻¹ = u := by
    have h1 := congrArg (baseChangeGL ι₁) hfix
    rw [map_mul, map_mul, map_inv, hQK, ← hcomm h] at h1
    exact h1
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon (Ne.symm hp2)
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hhL hup
  obtain ⟨D, R, hΦ, hq, hRq0, hmem, hfixd, hconjstep⟩ :=
    exists_langDatum_frobRoot_twist hp.pos he hjp hfixL hconj
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
  refine ⟨S, R, a, ι, hq, hRq0, hTa, hap, h1, ?_, hinj, hrange, hconjι, fun c => ?_⟩
  · rw [hda]
    exact hfixd
  · have h' : ι₀ (φ c) = diagramMap t L ^ j *
        Units.map (entrywiseHom (iterateFrobenius L 2 e)) (ι₀ c) * (diagramMap t L ^ j)⁻¹ := by
      change baseChangeGL ι₁ (κ (φ c)) = _
      rw [hφ c, map_mul, map_mul, map_inv, hQK, ← hcomm]
      rfl
    rw [hι (φ c), hι c, hconjstep, h']

end Core

section Twisted


theorem exists_langSetup_frobRoot_twE6 {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
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
      ∀ c, ι (φ c) = R.step0 (ι c) := by
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
  refine exists_langSetup_frobRoot_twist (t := TwistTag.E6) (j := 1) hp hp2 he ?_ hmon
    (twistedE6RootGroup K σ).subtype (Subgroup.subtype_injective _) T hT β φ h hhL hβ
    (fun c => by rw [pow_one]; exact hφ c) hp1 hh1 (by rw [pow_one]; exact hfix) ?_
  · show 1 * p % 2 = 1
    rw [one_mul]
    exact hp.eq_two_or_odd.resolve_left hp2
  · intro D hΦ
    refine ⟨finite_model_twistedE6 Nat.prime_two hf hK hσ hFr D hΦ, ?_⟩
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Γ_eq_map_twistedE6RootGroup Nat.prime_two hf hK hσ hFr D hΦ

theorem exists_langSetup_frobRoot_triD4 {p e j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hjp : j * p % 3 = 1) {K : Type} [Field K] (hK : Nat.card K = (2 ^ (e * p)) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ (e * p))) (T : K →+* K)
    (hT : ∀ c, T c = c ^ (2 ^ e))
    (β φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (h : ModGL TwistTag.D4.tag K)
    (hh : h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hβ : ∀ c, (β c : ModGL TwistTag.D4.tag K) = h * c * h⁻¹)
    (hφ : ∀ c, (φ c : ModGL TwistTag.D4.tag K) = diagramMap TwistTag.D4 K ^ j *
      Units.map (entrywiseHom T) c * (diagramMap TwistTag.D4 K ^ j)⁻¹)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1)
    (hfix : diagramMap TwistTag.D4 K ^ j * Units.map (entrywiseHom T) h *
      (diagramMap TwistTag.D4 K ^ j)⁻¹ = h) :
    ∃ (S : LangSetup Tag.D4 (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin Tag.D4.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        ModGL Tag.D4 (AlgebraicClosure K)),
      S.D.q = 2 ^ (e * p) ∧ R.q0 = 2 ^ e ∧
      rootDiagUnit Tag.D4 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.D4 a ≠ 1 ∧
      R.step0 (rootDiagUnit Tag.D4 a) = rootDiagUnit Tag.D4 a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.D4 a * ι c * (rootDiagUnit Tag.D4 a)⁻¹) ∧
      ∀ c, ι (φ c) = R.step0 (ι c) := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := e * p * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  set L := AlgebraicClosure K with hLdef
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ (2 ^ (e * p)) := fun c =>
    iterateFrobenius_def 2 (e * p) c
  have hhL : baseChangeGL (algebraMap K L) h ∈ adjointGroup TwistTag.D4.tag L :=
    triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L) ⟨h, hh⟩
  have hmon : MonomialToralAt Tag.D4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  refine exists_langSetup_frobRoot_twist (t := TwistTag.D4) hp hp2 he hjp hmon
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype (Subgroup.subtype_injective _) T hT
    β φ h hhL hβ hφ hp1 hh1 hfix ?_
  intro D hΦ
  have hd := langDescent_triD4_inner (K := K) (L := L) Nat.prime_two hf hK σ hσ hFr D hΦ (p := p)
  exact ⟨hd.finite_model, hd.Γ_eq⟩

end Twisted

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

end
