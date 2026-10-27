module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobRoot
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtExact
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE

section Iterate

variable {G : Type*} [Group G]

theorem iterate_conj_map_eq (F : G →* G) {z : G} (hz : F z = z) (k : ℕ) (g : G) :
    (fun h => z * F h * z⁻¹)^[k] g = z ^ k * F^[k] g * (z ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hzk : F (z ^ k) = z ^ k := by rw [map_pow, hz]
    have e1 := Function.iterate_succ_apply' (fun h => z * F h * z⁻¹) k g
    have e2 := Function.iterate_succ_apply' (⇑F) k g
    rw [e1, ih, e2]
    simp only [map_mul, map_inv, hzk]
    group

theorem iterate_map_eq_mul_pow (F : G →* G) {n g₀ : G} (hn : F n = n) (hg : F g₀ = g₀ * n)
    (k : ℕ) : F^[k] g₀ = g₀ * n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hn, hg, pow_succ', mul_assoc]

end Iterate

section Frobenius

variable {τ : Tag} {L : Type} [Field L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

theorem iterate_units_map_entrywiseHom_iterateFrobenius (e k : ℕ) (g : ModGL τ L) :
    (⇑(Units.map (entrywiseHom (iterateFrobenius L ℓ e))))^[k] g =
      Units.map (entrywiseHom (iterateFrobenius L ℓ (e * k))) g := by
  induction k with
  | zero => exact (entrywiseFrobGL_zero ℓ g).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Nat.mul_succ]
    exact entrywiseFrobGL_frobGL ℓ e (e * k) g

end Frobenius

section BaseChange


theorem units_map_entrywiseHom_baseChangeGL_comm {τ : Tag} {K L : Type} [Field K] [Field L]
    (ι₁ : K →+* L) (σ : L →+* L) (T : K →+* K) (hσT : σ.comp ι₁ = ι₁.comp T) (x : ModGL τ K) :
    Units.map (entrywiseHom σ) (baseChangeGL ι₁ x) =
      baseChangeGL ι₁ (Units.map (entrywiseHom T) x) := by
  rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hσT]

end BaseChange

section CharTwo


theorem canonicalRep_pow_charTwo {τ : Tag} {R : Type} [CommRing R] [CharP R 2] (w : WeylGroup τ)
    (k : ℕ) :
    canonicalRep (coxeterSystem τ) R (w ^ k) = canonicalRep (coxeterSystem τ) R w ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact canonicalRep_one _ _
  | succ k ih =>
    rw [pow_succ, pow_succ, CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, ih]

end CharTwo

section Lang


theorem exists_langDatum_frobRoot_pow {τ : Tag} {L : Type} [Field L] [CharP L 2] {e : ℕ} (p : ℕ)
    (D₀ : LangDatum τ L) (hΦ₀ : D₀.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 e))) :
    ∃ (D : LangDatum τ L) (R : FrobRoot D p),
      D.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 (e * p))) ∧ D.q = 2 ^ (e * p) ∧
      D.g0 = D₀.g0 ∧ R.q0 = 2 ^ e ∧ R.Fr0 = iterateFrobenius L 2 e ∧ R.z0 = D₀.n := by
  obtain ⟨w₀, hw₀⟩ := D₀.n_weyl
  have hFn : Units.map (entrywiseHom (iterateFrobenius L 2 e)) D₀.n = D₀.n := by
    rw [hw₀]
    exact frobenius_canonicalRep _ _
  have hlang : Units.map (entrywiseHom (iterateFrobenius L 2 e)) D₀.g0 = D₀.g0 * D₀.n := by
    have := D₀.lang
    rwa [hΦ₀] at this
  have hg := iterate_map_eq_mul_pow _ hFn hlang p
  rw [iterate_units_map_entrywiseHom_iterateFrobenius 2 e p, hw₀,
    ← canonicalRep_pow_charTwo] at hg
  let D : LangDatum τ L := LangDatum.ofFrobenius (iterateFrobenius L 2 (e * p)) (2 ^ (e * p))
    (iterateFrobenius_def 2 (e * p)) (w₀ ^ p) D₀.g0_mem hg
  have hDn : D.n = D₀.n ^ p := by
    rw [hw₀]
    exact canonicalRep_pow_charTwo w₀ p
  refine ⟨D, ⟨2 ^ e, iterateFrobenius L 2 e, iterateFrobenius_def 2 e, D₀.n, ?_, fun g => ?_⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show 2 ^ (e * p) = (2 ^ e) ^ p
    rw [pow_mul]
  · refine (iterate_conj_map_eq _ hFn p g).trans ?_
    rw [iterate_units_map_entrywiseHom_iterateFrobenius 2 e p]
    show _ = D.n * D.Φ g * D.n⁻¹
    rw [hDn]
    rfl

theorem langDescent_of_entrywiseFrobenius {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K L : Type} [Field K] [Finite K]
    [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (D : LangDatum τ L)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) (hperf : commutator ↥(adjointGroup τ K) = ⊤) :
    LangDescent D 7 ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) := by
  rcases hτ with h' | h' | h' | h' | h'
  · exact langDescent_exact (Or.inl h') hFr D hΦ hperf
  · exact langDescent_exact (Or.inr h') hFr D hΦ hperf
  · exact langDescent_untw 3 (Or.inl ⟨h', rfl⟩) hFr D hΦ Nat.prime_seven (by norm_num) hperf
  · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h', rfl⟩)) hFr D hΦ Nat.prime_seven
      (by norm_num) hperf
  · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h', rfl⟩)) hFr D hΦ Nat.prime_seven
      (by norm_num) hperf

theorem exists_frobRoot_of_toral_frob {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {e : ℕ} (he : 1 ≤ e) {p : ℕ} (hpq : Nat.Coprime p (2 ^ e)) {u : ModGL τ L} (hup : u ^ p = 1)
    (hfix : entrywiseFrobGL τ L 2 e u = u)
    (hconj : ∃ g ∈ adjointGroup τ L, g⁻¹ * u * g ∈ torusGroup τ L) :
    ∃ (D : LangDatum τ L) (R : FrobRoot D p),
      D.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 (e * p))) ∧ D.q = 2 ^ (e * p) ∧
      R.q0 = 2 ^ e ∧ R.Fr0 = iterateFrobenius L 2 e ∧
      u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom ∧
      R.step0 (D.g0⁻¹ * u * D.g0) = D.g0⁻¹ * u * D.g0 ∧
      ∀ y, R.step0 (D.g0⁻¹ * y * D.g0) = D.g0⁻¹ * Units.map (entrywiseHom R.Fr0) y * D.g0 := by
  obtain ⟨D₀, hΦ₀, -, y, hy, hyu⟩ := exists_langDatum_of_toral_untw e he hpq hup hfix hconj
  obtain ⟨D, R, hΦ, hq, hg0, hRq0, hRFr0, hRz0⟩ := exists_langDatum_frobRoot_pow p D₀ hΦ₀
  have hstep : ∀ y, R.step0 y = D₀.n * D₀.Φ y * D₀.n⁻¹ := fun y => by
    rw [R.step0_apply, hRz0, hRFr0, hΦ₀]
  have hlang : Units.map (entrywiseHom R.Fr0) D₀.g0 = D₀.g0 * D₀.n := by
    rw [hRFr0, ← hΦ₀]
    exact D₀.lang
  have hyd : y = D₀.g0⁻¹ * u * D₀.g0 := by
    have h' : D₀.g0 * y * D₀.g0⁻¹ = u := hyu
    rw [← h']
    group
  have hyfix : R.step0 y = y := by
    rw [hstep]
    exact (mem_twistedTorusOf.1 hy).2
  refine ⟨D, R, hΦ, hq, hRq0, hRFr0, ⟨y, R.mem_torus_of_step0_eq (mem_twistedTorusOf.1 hy).1 hyfix,
    by rw [hg0]; exact hyu⟩, ?_, fun y' => ?_⟩
  · rw [hg0, ← hyd]
    exact hyfix
  · rw [hg0, R.step0_apply, map_mul, map_mul, map_inv, hlang, hRz0]
    group

theorem exists_langSetup_of_toral_datum_of_prime_descent {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L)
    (hDq : D.q = ℓ ^ f) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q)
    {p : ℕ} (hfin : Finite D.model) {C : Type} [Group C] (ι₀ : C →* ModGL τ L)
    (hι₀ : Function.Injective ι₀) (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom)
    (β : MulAut C) {u : ModGL τ L} (hβ : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      rootDiagUnit τ a = D.g0⁻¹ * u * D.g0 ∧ (∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0) ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have h1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← ha, hyu'] at h
    have : u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ := by group
    rw [this, h]
    group
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, ι, rfl, ?_, hap, h1, ?_, hι,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, fun c => ?_⟩
  · exact ha ▸ hy
  · rw [← ha]
    exact hyu'
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · rw [hι, hι, hβ c, ← ha, hyu']
    group

theorem exists_langSetup_frobRoot_untw_of_mon {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (e * p)) (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e))
    (β φ : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹)
    (hφ : ∀ c, (φ c : ModGL τ K) = Units.map (entrywiseHom T) c)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1) (hfix : Units.map (entrywiseHom T) h = h) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧ R.q0 = 2 ^ e ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      ∀ c, ι (φ c) = R.step0 (ι c) := by
  classical
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hcomp : (iterateFrobenius L 2 e).comp ι₁ = ι₁.comp T := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, iterateFrobenius_def, hT, map_pow]
  have hcomm := units_map_entrywiseHom_baseChangeGL_comm (τ := τ) ι₁ (iterateFrobenius L 2 e) T
    hcomp
  set u : ModGL τ L := baseChangeGL ι₁ h with hu
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hfix' : entrywiseFrobGL τ L 2 e u = u := by
    show Units.map (entrywiseHom (iterateFrobenius L 2 e)) (baseChangeGL ι₁ h) = baseChangeGL ι₁ h
    rw [hcomm, hfix]
  have hpq : Nat.Coprime p (2 ^ e) := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right e
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon (Ne.symm hp2)
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hhL hup
  obtain ⟨D, R, hΦ, hq, hRq0, hRFr0, hmem, hfixd, hconjstep⟩ :=
    exists_frobRoot_of_toral_frob he hpq hup hfix' hconj
  set ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι₁).comp (adjointGroup τ K).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 (e * p) c
  have hd := langDescent_of_entrywiseFrobenius hτ hFr D hΦ hperf
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL τ K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL τ K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hep : 2 ≤ e * p := by nlinarith [hp.two_le]
  have hq' : 5 ≤ p ∨ 4 ≤ D.q := Or.inr (by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * p) := Nat.pow_le_pow_right (by norm_num) hep)
  obtain ⟨S, a, ι, rfl, hTa, hap, h1, hda, hι, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime_descent Nat.prime_two (le_trans (by norm_num) hep) D hq
      hp hp2 hq' hd.finite_model ι₀ hι₀inj hd.Γ_eq β hβ' hmem hup hu1
  refine ⟨S, R, a, ι, hq.trans hK.symm, hRq0, ⟨_, hFr, hΦ⟩, hTa, hap, h1, ?_, hinj, hrange,
    hconjι, fun c => ?_⟩
  · rw [hda]
    exact hfixd
  · have h' : ι₀ (φ c) = Units.map (entrywiseHom R.Fr0) (ι₀ c) := by
      rw [hRFr0]
      change baseChangeGL ι₁ (φ c : ModGL τ K) =
        Units.map (entrywiseHom (iterateFrobenius L 2 e)) (baseChangeGL ι₁ (c : ModGL τ K))
      rw [hφ c, hcomm]
    rw [hι (φ c), hι c, hconjstep, h']

end Lang

section Full


theorem exists_langSetup_frobRoot_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (e * p))
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e))
    (β φ : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹)
    (hφ : ∀ c, (φ c : ModGL τ K) = Units.map (entrywiseHom T) c)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1) (hfix : Units.map (entrywiseHom T) h = h) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧ R.q0 = 2 ^ e ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      ∀ c, ι (φ c) = R.step0 (ι c) :=
  exists_langSetup_frobRoot_untw_of_mon hτ hp hp2 he hK
    (monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp hp2) hperf T hT β φ h hhL hβ hφ hp1
    hh1 hfix

end Full

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

end
