module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T3
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T1

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement IsMulCommutative

section Arith

theorem q_eq_nine {p n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n) (hN : N ≤ 11)
    (hdvd : (p ^ n * ((p ^ n) ^ 2 - 1)) ∣ N.factorial) : p ^ n = 9 := by
  have h11 : N.factorial ∣ (11).factorial := Nat.factorial_dvd_factorial hN
  have h1 : (p ^ n * ((p ^ n) ^ 2 - 1)) ∣ 39916800 := by
    have : (11).factorial = 39916800 := by decide
    rw [← this]
    exact hdvd.trans h11
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq9 : 9 ≤ p ^ n := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have hqle : p ^ n ≤ 342 := by
    by_contra hcon
    push Not at hcon
    have hle : p ^ n * ((p ^ n) ^ 2 - 1) ≤ 39916800 := Nat.le_of_dvd (by norm_num) h1
    have h1q : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1q] at hle
    nlinarith [hcon]
  have hp19 : p < 19 := by
    by_contra hcon
    push Not at hcon
    have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
    nlinarith [hcon]
  have hn6 : n < 6 := by
    by_contra hcon
    push Not at hcon
    have : 3 ^ 6 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    have h3n : 3 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp3 n
    omega
  clear hq9 hqle hdvd h11
  interval_cases p <;> try (exfalso; norm_num at hp; done)
  all_goals (interval_cases n <;> first | rfl | (exfalso; revert h1; decide))

theorem prime_pow_eq_nine {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (h : p ^ n = 9) : p = 3 ∧ n = 2 := by
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp3
  refine ⟨rfl, ?_⟩
  have h9 : (3 : ℕ) ^ n = 3 ^ 2 := by rw [h]; norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h9

end Arith

section Emb

theorem exists_injective_GL_of_faithful {G : Type} [Group G] {p d : ℕ} (hp : p.Prime)
    {P E : Subgroup G} [IsElementaryAbelian p ↥P] [Finite P] (hPcard : Nat.card ↥P = p ^ d)
    (hnorm : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P)
    (hfaith : ∀ e ∈ E, (∀ x ∈ P, e * x * e⁻¹ = x) → e = 1) :
    ∃ ρ : ↥E →* GL (Fin d) (ZMod p), Function.Injective ρ := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Module.Finite (ZMod p) (Additive ↥P) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) (Additive ↥P) = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive ↥P)
    rw [Nat.card_zmod] at h
    have hV' : Nat.card (Additive ↥P) = p ^ d := by rw [← hPcard]; rfl
    rw [hV'] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let b : Module.Basis (Fin d) (ZMod p) (Additive ↥P) :=
    Module.finBasisOfFinrankEq (ZMod p) (Additive ↥P) hdim
  let act : ↥E → (Additive ↥P →+ Additive ↥P) := fun e =>
    { toFun := fun x => Additive.ofMul (⟨(e : G) * ((Additive.toMul x : ↥P) : G) * (e : G)⁻¹,
        hnorm e e.2 _ (Additive.toMul x : ↥P).2⟩ : ↥P)
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [toMul_add]
        simp [mul_assoc] }
  let f : ↥E →* Module.End (ZMod p) (Additive ↥P) :=
    { toFun := fun e => AddMonoidHom.toZModLinearMap p (act e)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [act]
      map_mul' := fun e₁ e₂ => by
        refine LinearMap.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [act, mul_assoc] }
  have hf1 : ∀ e : ↥E, f e = 1 → e = 1 := by
    intro e he
    apply Subtype.ext
    refine hfaith e e.2 fun x hx => ?_
    have := congrArg (fun T => Additive.toMul (T (Additive.ofMul (⟨x, hx⟩ : ↥P)))) he
    simpa [f, act] using this
  let ρ : ↥E →* GL (Fin d) (ZMod p) :=
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).toMonoidHom.comp
      f.toHomUnits
  refine ⟨ρ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro e he
  have h1 : f.toHomUnits e = 1 := by
    have : (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv) (f.toHomUnits e) =
        (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv) 1 := by
      rw [map_one]; exact he
    exact (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).injective this
  exact hf1 e (congrArg Units.val h1)

theorem card_dvd_card_GL_of_faithful {G : Type} [Group G] {p d : ℕ} (hp : p.Prime)
    {P E : Subgroup G} [IsElementaryAbelian p ↥P] [Finite P] (hPcard : Nat.card ↥P = p ^ d)
    (hnorm : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P)
    (hfaith : ∀ e ∈ E, (∀ x ∈ P, e * x * e⁻¹ = x) → e = 1) :
    Nat.card ↥E ∣ Nat.card (GL (Fin d) (ZMod p)) := by
  obtain ⟨ρ, hρ⟩ := exists_injective_GL_of_faithful hp hPcard hnorm hfaith
  calc Nat.card ↥E = Nat.card ρ.range := Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv
    _ ∣ Nat.card (GL (Fin d) (ZMod p)) := Subgroup.card_subgroup_dvd_card ρ.range

theorem not_seven_dvd_card_GL_four_three : ¬ 7 ∣ Nat.card (GL (Fin 4) (ZMod 3)) := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card]

end Emb

section Div

theorem dvd_card_centralizerBar {G : Type} [Group G] [Finite G] {z : G} {J : Subgroup G}
    (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 2 ≤ n) (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n) :
    (p ^ n * ((p ^ n) ^ 2 - 1)) ∣ Nat.card (CentralizerBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, iF, fF, hFcard, Y, hYC, hYperf, φ, hφs, -⟩ :=
    exists_perfect_lift_of_lieModel hzJ hz hnoc hp hp2 hn hLie
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have hSLq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_card_four' hF4)
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  set O : Subgroup ↥C := pPrimeCore 2 ↥C with hOdef
  have hOodd : Odd (Nat.card ↥O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hmem : ∀ y : ↥Y, ((y : ↥J) : G) ∈ C := by
    intro y
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hYC y.2)
    exact congrArg Subtype.val this
  let f : ↥Y →* ↥C := ((J.subtype.comp Y.subtype).codRestrict C hmem)
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  let ρ : ↥Y →* CentralizerBar z := (QuotientGroup.mk' O).comp f
  have hkodd : ∀ k ∈ ρ.ker, Odd (orderOf k) := by
    intro k hk
    have h1 : (QuotientGroup.mk' O) (f k) = 1 := hk
    have h2 : f k ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : orderOf (f k) = orderOf k := orderOf_injective f hfinj k
    have h4 : orderOf (⟨f k, h2⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
    have h5 : orderOf (⟨f k, h2⟩ : ↥O) = orderOf (f k) := Subgroup.orderOf_mk _ _
    rw [← h3, ← h5]
    exact Odd.of_dvd_nat hOodd h4
  let negOne : SpecialLinearGroup (Fin 2) F := ⟨-1, det_neg_one_two'⟩
  have hker : ρ.ker ≤ φ.ker := by
    have hnorm : (ρ.ker.map φ).Normal := (MonoidHom.normal_ker ρ).map φ hφs
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hSLq hnorm with htop | hcen
    · exfalso
      have hm1 : negOne ∈ ρ.ker.map φ := by
        rw [htop]; trivial
      obtain ⟨k, hk, hkφ⟩ := hm1
      have h2 : (2 : F) ≠ 0 := by
        have hFodd : Odd (Nat.card F) := by
          rw [hFcard]; exact (hp.odd_of_ne_two hp2).pow
        exact two_ne_zero_of_odd_card' hFodd
      have hord : orderOf negOne = 2 := by
        apply orderOf_eq_prime
        · rw [pow_two]
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_mul]
          simp [negOne]
        · intro h
          have := congrArg Subtype.val h
          have e := congrFun (congrFun this 0) 0
          simp [negOne] at e
          apply h2
          linear_combination -e
      have hdvd : orderOf (φ k) ∣ orderOf k := orderOf_map_dvd φ k
      rw [hkφ, hord] at hdvd
      exact absurd (Odd.of_dvd_nat (hkodd k hk) hdvd) (by decide)
    · intro k hk
      have hφk : φ k ∈ center (SpecialLinearGroup (Fin 2) F) := hcen ⟨k, hk, rfl⟩
      have hsq : φ k * φ k = 1 := by
        obtain ⟨r, hr, hrk⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hφk
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, ← hrk, ← map_mul, Matrix.SpecialLinearGroup.coe_one]
        have hr2 : r * r = 1 := by simpa [pow_two] using hr
        rw [hr2, map_one]
      have hdvd : orderOf (φ k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have hdvd' : orderOf (φ k) ∣ orderOf k := orderOf_map_dvd φ k
      have hcop : Nat.gcd 2 (orderOf k) = 1 := Nat.coprime_two_left.mpr (hkodd k hk)
      have h1 : orderOf (φ k) ∣ 1 := hcop ▸ Nat.dvd_gcd hdvd hdvd'
      exact (MonoidHom.mem_ker).mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  have hρs : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hker' : (ρ.rangeRestrict).ker ≤ φ.ker := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  let φb : ↥ρ.range →* SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.lift (ρ.rangeRestrict).ker φ hker').comp
      (QuotientGroup.quotientKerEquivOfSurjective ρ.rangeRestrict hρs).symm.toMonoidHom
  have hφbs : Function.Surjective φb := by
    intro A
    obtain ⟨a, rfl⟩ := hφs A
    refine ⟨(QuotientGroup.quotientKerEquivOfSurjective ρ.rangeRestrict hρs)
      (QuotientGroup.mk a), ?_⟩
    simp [φb]
  have h1 : Nat.card (SpecialLinearGroup (Fin 2) F) ∣ Nat.card ↥ρ.range :=
    Subgroup.card_dvd_of_surjective hφbs
  have h2 : Nat.card ↥ρ.range ∣ Nat.card (CentralizerBar z) := Subgroup.card_subgroup_dvd_card _
  have h3 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  rw [h3, hFcard] at h1
  exact h1.trans h2

end Div

section Sporadic

theorem card_centralizerBar_of_sporadic {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    {N : ℕ} (hN : 2 ≤ N) (hsp : Stage1Sporadic G z S N) :
    Nat.card (CentralizerBar z) = N.factorial := by
  obtain ⟨-, hcard, ⟨e⟩⟩ := hsp.cover
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (CentralizerBar z))
  have h2 : Nat.card (CentralizerBar z ⧸ center (CentralizerBar z)) = N.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
    rw [card_alternatingGroup, Fintype.card_fin]
  rw [h1, h2, hcard]
  exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) hN)

theorem exists_sporadic_of_data {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hdata : Stage1Data G z S k) (hk : k = Kind.mcl ∨ k = Kind.ly) :
    ∃ N : ℕ, 8 ≤ N ∧ N ≤ 11 ∧ Stage1Sporadic G z S N := by
  cases hdata with
  | g2 h => rcases hk with h' | h' <;> cases h'
  | m12 h => rcases hk with h' | h' <;> cases h'
  | psp4 h => rcases hk with h' | h' <;> cases h'
  | l4 ε h => rcases hk with h' | h' <;> cases h'
  | mcl h =>
    obtain ⟨N, hN, hsp⟩ := h
    exact ⟨N, by omega, by omega, hsp⟩
  | ly h =>
    obtain ⟨N, hN, hsp⟩ := h
    exact ⟨N, by omega, by omega, hsp⟩

theorem false_of_sporadic {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}
    {p : ℕ} (hC : Ctx9 G z k S M p) (hk : k = Kind.mcl ∨ k = Kind.ly) {J : Subgroup G} (hzJ : z ∈ J)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n) (hel : IsElementaryAbelian p ↥(Op p M))
    (hcard : Nat.card ↥(Op p M) = p ^ (2 * n)) (hPz : Op p M ⊓ Cen z = ⊥) : False := by
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hz := hC.orderOf_z
  obtain ⟨N, hN8, hN11, hsp⟩ := exists_sporadic_of_data hC.ctx.data hk
  have hCbar := card_centralizerBar_of_sporadic (by omega) hsp
  have hdvd := dvd_card_centralizerBar hzJ hz hnoc hp hp2 hn hLie
  rw [hCbar] at hdvd
  have hq9 := q_eq_nine hp hp2 hn hN11 hdvd
  obtain ⟨hp3, hn2⟩ := prime_pow_eq_nine hp hn hq9
  subst hp3
  subst hn2
  have hcard4 : Nat.card ↥(Op 3 M) = 3 ^ 4 := by simpa using hcard
  have hnorm : ∀ e ∈ Cen z, ∀ x ∈ Op 3 M, e * x * e⁻¹ ∈ Op 3 M := fun e he x hx =>
    (mem_normalizer_iff.mp (le_normalizer_Op' 3 M (hC.cen_le he)) x).mp hx
  have hfaith : ∀ e ∈ Cen z, (∀ x ∈ Op 3 M, e * x * e⁻¹ = x) → e = 1 := by
    intro e he hcent
    have h1 : e ∈ Op 3 M := Ctx9.cent_Op_le hC (hC.cen_le he) hcent
    have h3 : e ∈ Op 3 M ⊓ Cen z := ⟨h1, he⟩
    rw [hPz, Subgroup.mem_bot] at h3
    exact h3
  have hCdvd : Nat.card ↥(Cen z) ∣ Nat.card (GL (Fin 4) (ZMod 3)) :=
    card_dvd_card_GL_of_faithful hp hcard4 hnorm hfaith
  have h7 : 7 ∣ Nat.card (CentralizerBar z) := by
    rw [hCbar]
    exact Nat.dvd_factorial (by norm_num) (by omega)
  have hCbarC : Nat.card (CentralizerBar z) ∣ Nat.card ↥(Cen z) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(Cen z))
    exact ⟨_, h⟩
  exact not_seven_dvd_card_GL_four_three (h7.trans (hCbarC.trans hCdvd))

end Sporadic

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
