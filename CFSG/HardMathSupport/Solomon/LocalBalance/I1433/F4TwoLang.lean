module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.LocalAnalysis.StandardType.GGLangUniform
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartOne.KE

theorem ringChar_algebraicClosure' (K : Type) [Field K] :
    ringChar (AlgebraicClosure K) = ringChar K := by
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  exact ringChar.eq (AlgebraicClosure K) (ringChar K)

set_option linter.unusedSectionVars false


theorem baseChangeGL_mem_adjointGroup_of_mem' {τ : Tag} {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (f : K₁ →+* K₂) {g : ModGL τ K₁} (hg : g ∈ adjointGroup τ K₁) :
    baseChangeGL f g ∈ adjointGroup τ K₂ := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, c, h | h⟩ := hy
    · rw [show y = xUnit τ K₁ i c from Units.ext h, baseChangeGL_xUnit]
      exact xUnit_mem_adjointGroup _ _
    · rw [show y = yUnit τ K₁ i c from Units.ext h, baseChangeGL_yUnit]
      exact yUnit_mem_adjointGroup _ _
  | one => simpa using one_mem _
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

theorem exists_langSetup_of_toral_datum_of_prime_eq {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L)
    (hDq : D.q = ℓ ^ f) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q) {p : ℕ}
    (hfin : Finite D.model) {C : Type} [Group C] (ι₀ : C →* ModGL τ L)
    (hι₀ : Function.Injective ι₀) (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom)
    (β : MulAut C) {u : ModGL τ L} (hβ : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1) (hu1 : u ≠ 1)
    (c₀ : C) (hc₀ : ι₀ c₀ = u) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι c₀ = rootDiagUnit τ a ∧
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
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, ι, rfl, ?_, hap, h1,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, ?_, fun c => ?_⟩
  · exact ha ▸ hy
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · rw [hι, hc₀, ← ha, hyu']
  · rw [hι, hι, hβ c, ← ha, hyu']
    group

theorem exists_langSetup_of_inner_untw_of_prime_eq_frobenius_iota {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀K : ¬ p₀ ∣ Nat.card K) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ Nat.card K)
    (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (x : ↥(adjointGroup τ K)) (hp1 : x ^ p = 1) (hh1 : x ≠ 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p₀) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      (∀ c, ι c = S.D.g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * S.D.g0) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit τ a ∧
      ∀ c, ι (MulAut.conj x c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hqK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ (f : ℕ) c = c ^ Nat.card K := fun c => by
    rw [hqK]
    exact iterateFrobenius_def ℓ (f : ℕ) c
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι₁ y) = baseChangeGL ι₁ y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι₁ = ι₁ := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι₁ c) = ι₁ c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hℓp : ℓ ≠ p := by
    intro h
    apply hpK
    rw [hqK, h]
    exact dvd_pow_self p (by omega)
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) := (Nat.Prime.coprime_iff_not_dvd hp).2 (hqK ▸ hpK)
  set h : ModGL τ K := (x : ModGL τ K) with hh
  set u : ModGL τ L := baseChangeGL ι₁ h with hu
  have hhL : u ∈ adjointGroup τ L := baseChangeGL_mem_adjointGroup_of_mem' ι₁ x.2
  have hup : u ^ p = 1 := by
    rw [hu, ← map_pow, hh, ← Subgroup.coe_pow, hp1]
    exact map_one _
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hℓp
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) hhL hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_untw (f : ℕ) hf1 hpq hup (hFix h) hconj
  set ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι₁).comp (adjointGroup τ K).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd : LangDescent D 7 ι₀ := by
    rcases hτ with h' | h' | h' | h' | h'
    · exact langDescent_exact (Or.inl h') hFr D hΦ hperf
    · exact langDescent_exact (Or.inr h') hFr D hΦ hperf
    · exact langDescent_untw 3 (Or.inl ⟨h', rfl⟩) hFr D hΦ Nat.prime_seven (by norm_num) hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h', rfl⟩)) hFr D hΦ Nat.prime_seven
        (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h', rfl⟩)) hFr D hΦ Nat.prime_seven
        (by norm_num) hperf
  have hβ' : ∀ c, ι₀ (MulAut.conj x c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ ((MulAut.conj x c : ↥(adjointGroup τ K)) : ModGL τ K) =
      baseChangeGL ι₁ h * baseChangeGL ι₁ (c : ModGL τ K) * (baseChangeGL ι₁ h)⁻¹
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul,
      map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq, ← hqK]
    exact hq₀
  have hℓp₀ : ℓ ≠ p₀ := by
    intro h
    apply hp₀K
    rw [hqK, h]
    exact dvd_pow_self p₀ (by omega)
  obtain ⟨S, ι, rfl, hι, hinj, hrange, htor⟩ :=
    CFSG.StandardType.LangRat.exists_langSetup_of_toral_datum_uniform
      hℓ hf1 D hDq hp₀ hℓp₀.symm hq' hd.finite_model ι₀ hι₀inj hd.Γ_eq
  obtain ⟨a, hT, ha, hconjι⟩ := htor u hmem
  have hx : ι x = rootDiagUnit τ a := (hι x).trans ha.symm
  have hdp : rootDiagUnit τ a ^ p = 1 := by
    rw [← hx, ← map_pow, hp1, map_one]
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, hdp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    exact fun i => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) i
  have h1 : rootDiagUnit τ a ≠ 1 := fun h =>
    hh1 (hinj (hx.trans (h.trans (map_one ι).symm)))
  exact ⟨S, a, ι, hDq.trans hqK.symm, ⟨iterateFrobenius L ℓ (f : ℕ), hFr, hΦ⟩,
    hι, hT, hap, h1, hinj, hrange, hx, hconjι (MulAut.conj x) hβ'⟩

theorem exists_langSetup_of_inner_untw_of_prime_eq_frobenius {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀K : ¬ p₀ ∣ Nat.card K) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ Nat.card K)
    (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (x : ↥(adjointGroup τ K)) (hp1 : x ^ p = 1) (hh1 : x ≠ 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p₀) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit τ a ∧
      ∀ c, ι (MulAut.conj x c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  obtain ⟨S, a, ι, hq, hFr, -, hT, hap, h1, hinj, hrange, hx, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime_eq_frobenius_iota hτ hp hpK hp₀ hp₀K hq₀ hmon
      hperf x hp1 hh1
  exact ⟨S, a, ι, hq, hFr, hT, hap, h1, hinj, hrange, hx, hconj⟩

theorem exists_langSetup_of_inner_untw_of_prime_eq {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀K : ¬ p₀ ∣ Nat.card K) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ Nat.card K)
    (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (x : ↥(adjointGroup τ K)) (hp1 : x ^ p = 1) (hh1 : x ≠ 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p₀) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit τ a ∧
      ∀ c, ι (MulAut.conj x c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  obtain ⟨S, a, ι, hq, -, hT, hap, h1, hinj, hrange, hx, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime_eq_frobenius hτ hp hpK hp₀ hp₀K hq₀ hmon
      hperf x hp1 hh1
  exact ⟨S, a, ι, hq, hT, hap, h1, hinj, hrange, hx, hconj⟩

theorem exists_langSetup_F4_of_orderOf_eq_three {K : Type} [Field K] [Finite K]
    (hpK : ¬ 3 ∣ Nat.card K) (x : ↥(adjointGroup Tag.F4 K)) (hx : orderOf x = 3) :
    ∃ (p₀ : ℕ) (S : LangSetup Tag.F4 (AlgebraicClosure K) p₀)
      (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup Tag.F4 K) →* ModGL Tag.F4 (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      rootDiagUnit Tag.F4 a ∈ S.D.torus ∧ (∀ i, a i ^ 3 = 1) ∧ rootDiagUnit Tag.F4 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit Tag.F4 a ∧
      (∀ c, ι (MulAut.conj x c) =
        rootDiagUnit Tag.F4 a * ι c * (rootDiagUnit Tag.F4 a)⁻¹) ∧
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
          Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hperf : commutator ↥(adjointGroup Tag.F4 K) = ⊤ := single_edge_perfect Tag.F4 K (by simp)
  have hmon : MonomialToralAt Tag.F4 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  by_cases hq : 5 ≤ 3 ∨ 4 ≤ Nat.card K
  · obtain ⟨S, a, ι, hDq, hT, hap, h1, hinj, hrange, hι, hconj⟩ :=
      exists_langSetup_of_inner_untw_of_prime_eq (Or.inr (Or.inl rfl)) Nat.prime_three hpK
        Nat.prime_three hpK hq hmon hperf x hx3 hx1
    exact ⟨3, S, a, ι, hDq, hT, hap, h1, hinj, hrange, hι, hconj, langSetup_hTame S hT hap h1⟩
  · have hK1 : 0 < Nat.card K := Nat.card_pos
    have h5K : ¬ 5 ∣ Nat.card K := fun h5 => by
      have := Nat.le_of_dvd hK1 h5
      omega
    obtain ⟨S, a, ι, hDq, hT, hap, h1, hinj, hrange, hι, hconj⟩ :=
      exists_langSetup_of_inner_untw_of_prime_eq (Or.inr (Or.inl rfl)) Nat.prime_three hpK
        Nat.prime_five h5K (Or.inl le_rfl) hmon hperf x hx3 hx1
    exact ⟨5, S, a, ι, hDq, hT, hap, h1, hinj, hrange, hι, hconj,
      langSetup_hTame_of_prime S Nat.prime_three
        (natCast_ne_zero_algebraicClosure Nat.prime_three hpK) (fun h => absurd h (by decide))
        hT hap h1⟩

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
