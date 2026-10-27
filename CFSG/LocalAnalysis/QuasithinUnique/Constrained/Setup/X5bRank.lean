module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import Mathlib.RingTheory.Artinian.Instances
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.SimpleRing.Principal

public section

open Polynomial CFSG.Quasithin

namespace CFSG.QuasithinUnique.Setup.X5

def annIdeal {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (T : Module.End F V) (w : V) :
    Ideal F[X] where
  carrier := {p | aeval T p w = 0}
  add_mem' := by
    intro a b ha hb
    change aeval T (a + b) w = 0
    change aeval T a w = 0 at ha
    change aeval T b w = 0 at hb
    rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  zero_mem' := by
    change aeval T (0 : F[X]) w = 0
    simp
  smul_mem' := by
    intro c x hx
    change aeval T x w = 0 at hx
    change aeval T (c • x) w = 0
    rw [smul_eq_mul, map_mul, Module.End.mul_apply, hx, map_zero]

theorem mem_annIdeal {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (T : Module.End F V)
    (w : V) (p : F[X]) : p ∈ annIdeal T w ↔ aeval T p w = 0 := Iff.rfl

theorem exists_irreducible_factor_annihilating {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (T : Module.End F V) {P : F[X]} (hP : P ≠ 0) {w : V} (hw : w ≠ 0)
    (h : aeval T P w = 0) :
    ∃ g : F[X], Irreducible g ∧ g ∣ P ∧ ∃ w' : V, w' ≠ 0 ∧
      ∀ p : F[X], aeval T p w' = 0 ↔ g ∣ p := by
  obtain ⟨μ, hμ⟩ := (IsPrincipalIdealRing.principal (annIdeal T w)).principal
  have hPI : P ∈ annIdeal T w := h
  have hI1 : (1 : F[X]) ∉ annIdeal T w := by
    intro h1
    rw [mem_annIdeal, map_one, Module.End.one_apply] at h1
    exact hw h1
  have hμP : μ ∣ P := by
    have : P ∈ Ideal.span {μ} := by
      have h' := hPI
      rw [hμ] at h'
      exact h'
    exact Ideal.mem_span_singleton.mp this
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hμP
    exact hP hμP
  have hμu : ¬ IsUnit μ := by
    intro hu
    apply hI1
    rw [hμ]
    have : Ideal.span {μ} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
    rw [show (F[X] ∙ μ) = Ideal.span {μ} from rfl, this]
    exact Submodule.mem_top
  obtain ⟨g, hg, hgμ⟩ := WfDvdMonoid.exists_irreducible_factor hμu hμ0
  obtain ⟨μ', hμ'⟩ := hgμ
  have hμ'0 : μ' ≠ 0 := by
    rintro rfl
    simp at hμ'
    exact hμ0 hμ'
  have hμI : μ ∈ annIdeal T w := by
    rw [hμ]; exact Ideal.mem_span_singleton_self μ
  obtain ⟨w', hw'⟩ : ∃ w' : V, w' = aeval T μ' w := ⟨_, rfl⟩
  have hw'0 : w' ≠ 0 := by
    intro h0
    have : μ' ∈ annIdeal T w := by rw [mem_annIdeal, ← hw']; exact h0
    rw [hμ] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp this
    have : μ' * (1 - g * c) = 0 := by
      calc μ' * (1 - g * c) = μ' - μ' * (g * c) := by ring
        _ = μ' - μ * c := by rw [hμ']; ring
        _ = 0 := by rw [← hc]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hμ'0 h1
    · have : g * c = 1 := by linear_combination -h1
      exact hg.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, this⟩)
  have hgI : g ∈ annIdeal T w' := by
    rw [mem_annIdeal, hw']
    have : aeval T g (aeval T μ' w) = aeval T (g * μ') w := by
      rw [map_mul, Module.End.mul_apply]
    rw [this, ← hμ']
    exact hμI
  have hI'1 : annIdeal T w' ≠ ⊤ := by
    intro htop
    have : (1 : F[X]) ∈ annIdeal T w' := htop ▸ Submodule.mem_top
    rw [mem_annIdeal, map_one, Module.End.one_apply] at this
    exact hw'0 this
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible hg
  have hle : (F[X] ∙ g) ≤ annIdeal T w' := by
    rw [show (F[X] ∙ g) = Ideal.span {g} from rfl, Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hgI
  have heq : (F[X] ∙ g) = annIdeal T w' := hmax.eq_of_le hI'1 hle
  refine ⟨g, hg, ?_, w', hw'0, fun p => ?_⟩
  · exact dvd_trans ⟨μ', hμ'⟩ hμP
  · rw [← mem_annIdeal, ← heq]
    exact (Ideal.mem_span_singleton (x := p) (y := g)).trans (by rfl)

theorem exists_family_distinct_mod_fixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {T : Module.End (ZMod 2) V} (hT : T ^ ℓ = 1) (hT1 : T ≠ 1) :
    ∃ ι : (ZMod 2)[X]_(orderOf (2 : ZMod ℓ)) → V,
      ∀ r s, T (ι r - ι s) = ι r - ι s → r = s := by
  have hℓodd : ℓ.Coprime 2 := by
    have := (Fact.out : ℓ.Prime)
    exact (Nat.coprime_primes this Nat.prime_two).mpr hℓ2
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : V, T w₀ ≠ w₀ := by
    by_contra hcon
    push Not at hcon
    exact hT1 (LinearMap.ext fun w => by rw [Module.End.one_apply]; exact hcon w)
  set P : (ZMod 2)[X] := cyclotomic ℓ (ZMod 2) with hP
  have hP0 : P ≠ 0 := cyclotomic_ne_zero ℓ (ZMod 2)
  have hP1 : P.eval 1 ≠ 0 := by
    rw [hP, eval_one_cyclotomic_prime]
    intro h
    have h2 : (2 : ℕ) ∣ ℓ := by
      rw [← ZMod.natCast_eq_zero_iff]; exact h
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).mp h2).symm
  have hw₁ : T w₀ - w₀ ≠ 0 := sub_ne_zero.mpr hw₀
  have hPw₁ : aeval T P (T w₀ - w₀) = 0 := by
    have h2 : (T w₀ - w₀) = aeval T (X - 1 : (ZMod 2)[X]) w₀ := by simp
    rw [h2, ← Module.End.mul_apply, ← map_mul, hP, cyclotomic_prime_mul_X_sub_one]
    simp [map_sub, hT]
  obtain ⟨g, hg, hgP, w, hw0, hann⟩ := exists_irreducible_factor_annihilating T hP0 hw₁ hPw₁
  have hdeg : g.natDegree = orderOf (2 : ZMod ℓ) := by
    have hcop : Nat.Coprime 2 ℓ := hℓodd.symm
    have hcard : Fintype.card (ZMod 2) = 2 ^ 1 := by simp [ZMod.card]
    have := Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (K := ZMod 2) (p := 2) (f := 1)
      (n := ℓ) (P := g) hcard hcop hgP hg
    rw [this, ← orderOf_units]
    simp
  have hm0 : 0 < g.natDegree := hg.natDegree_pos
  refine ⟨fun r => aeval T r.1 w, fun r s h => ?_⟩
  have hd : aeval T r.1 w - aeval T s.1 w = aeval T (r.1 - s.1) w := by
    simp [map_sub, LinearMap.sub_apply]
  rw [hd] at h
  have h1 : aeval T ((X - 1) * (r.1 - s.1)) w = 0 := by
    rw [map_mul, Module.End.mul_apply]
    generalize aeval T (r.1 - s.1) w = u at h ⊢
    rw [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply, h, sub_self]
  have hdvd : g ∣ (X - 1) * (r.1 - s.1) := (hann _).mp h1
  rcases hg.prime.dvd_or_dvd hdvd with h2 | h2
  · exfalso
    have h3 : (X - C 1 : (ZMod 2)[X]) ∣ g :=
      hg.dvd_symm (irreducible_X_sub_C (1 : ZMod 2)) (by simpa using h2)
    have hroot : P.IsRoot 1 := dvd_iff_isRoot.mp (dvd_trans h3 hgP)
    exact hP1 hroot
  · have hrs : r.1 - s.1 = 0 := by
      apply eq_zero_of_dvd_of_natDegree_lt h2
      by_cases h0 : r.1 - s.1 = 0
      · rw [h0, natDegree_zero]; exact hm0
      · have hmem : r.1 - s.1 ∈ degreeLT (ZMod 2) (orderOf (2 : ZMod ℓ)) :=
          Submodule.sub_mem _ r.2 s.2
        rw [mem_degreeLT] at hmem
        rw [hdeg]
        exact (natDegree_lt_iff_degree_lt h0).mpr hmem
    exact Subtype.ext (sub_eq_zero.mp hrs)

section Fixed

variable {W : Type*} [CommGroup W]

theorem mem_fixV_zpowers {c : MulAut W} {v : W} : v ∈ fixV (Subgroup.zpowers c) ↔ c v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem fixV_zpowers_inf_le (g h : MulAut W) :
    fixV (Subgroup.zpowers g) ⊓ fixV (Subgroup.zpowers h) ≤ fixV (Subgroup.zpowers (g * h)) := by
  intro v hv
  rw [Subgroup.mem_inf, mem_fixV_zpowers, mem_fixV_zpowers] at hv
  rw [mem_fixV_zpowers, MulAut.mul_apply, hv.2, hv.1]

theorem fixV_antitone {A B : Subgroup (MulAut W)} (h : A ≤ B) : fixV B ≤ fixV A :=
  fun _ hv x hx => hv x (h hx)

theorem index_fixV_mul_le [Finite W] (g h : MulAut W) :
    (fixV (Subgroup.zpowers (g * h))).index ≤
      (fixV (Subgroup.zpowers g)).index * (fixV (Subgroup.zpowers h)).index :=
  (Subgroup.index_antitone (fixV_zpowers_inf_le g h)).trans Subgroup.index_inf_le

theorem index_fixV_conj (k g : MulAut W) :
    (fixV (Subgroup.zpowers (k * g * k⁻¹))).index = (fixV (Subgroup.zpowers g)).index :=
  CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj k g

theorem index_fixV_antitone [Finite W] {A B : Subgroup (MulAut W)} (h : A ≤ B) :
    (fixV A).index ≤ (fixV B).index :=
  Subgroup.index_antitone (fixV_antitone h)

theorem card_mul_card_fixV_lt_iff [Finite W] (A : Subgroup (MulAut W)) :
    Nat.card A * Nat.card (fixV A) < Nat.card W ↔ Nat.card A < (fixV A).index := by
  have h := (fixV A).card_mul_index
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  rw [← h, mul_comm (Nat.card (fixV A)) (fixV A).index]
  exact Nat.mul_lt_mul_right hpos

end Fixed

theorem two_pow_orderOf_le_index_fixV {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {c : MulAut W}
    (hc : c ^ ℓ = 1) (hc1 : c ≠ 1) :
    2 ^ orderOf (2 : ZMod ℓ) ≤ (fixV (Subgroup.zpowers c)).index := by
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    exact hW (Additive.toMul x))
  obtain ⟨T, hTapp⟩ : ∃ T : Module.End (ZMod 2) (Additive W),
      ∀ w : W, T (Additive.ofMul w) = Additive.ofMul (c w) :=
    ⟨AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive c.toMonoidHom), fun w => rfl⟩
  have hTpow : ∀ n : ℕ, ∀ w : W, (T ^ n) (Additive.ofMul w) = Additive.ofMul ((c ^ n) w) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, hTapp, ih, pow_succ, MulAut.mul_apply]
  have hT : T ^ ℓ = 1 := by
    ext x
    obtain ⟨w, rfl⟩ := Additive.ofMul.surjective x
    rw [hTpow, hc]
    rfl
  have hT1 : T ≠ 1 := by
    intro h
    apply hc1
    ext w
    have := congrArg (fun S : Module.End (ZMod 2) (Additive W) => S (Additive.ofMul w)) h
    simpa [hTapp] using this
  obtain ⟨ι, hι⟩ := exists_family_distinct_mod_fixed hℓ2 hT hT1
  have hinj : Function.Injective
      (fun r => (QuotientGroup.mk (Additive.toMul (ι r)) : W ⧸ fixV (Subgroup.zpowers c))) := by
    intro r s hrs
    have h1 : (Additive.toMul (ι r))⁻¹ * Additive.toMul (ι s) ∈ fixV (Subgroup.zpowers c) :=
      QuotientGroup.eq.mp hrs
    rw [mem_fixV_zpowers] at h1
    have h2 : T (ι s - ι r) = ι s - ι r := by
      obtain ⟨a, ha⟩ := Additive.ofMul.surjective (ι r)
      obtain ⟨b, hb⟩ := Additive.ofMul.surjective (ι s)
      rw [← ha, ← hb] at h1 ⊢
      simp only [toMul_ofMul] at h1
      rw [← ofMul_div, hTapp, div_eq_inv_mul]
      exact congrArg Additive.ofMul h1
    exact (hι s r h2).symm
  have hcard : Nat.card (degreeLT (ZMod 2) (orderOf (2 : ZMod ℓ))) =
      2 ^ orderOf (2 : ZMod ℓ) := by
    rw [Nat.card_congr (degreeLTEquiv (ZMod 2) (orderOf (2 : ZMod ℓ))).toEquiv, Nat.card_fun]
    simp
  calc 2 ^ orderOf (2 : ZMod ℓ) = Nat.card (degreeLT (ZMod 2) (orderOf (2 : ZMod ℓ))) := hcard.symm
    _ ≤ Nat.card (W ⧸ fixV (Subgroup.zpowers c)) := Nat.card_le_card_of_injective _ hinj
    _ = (fixV (Subgroup.zpowers c)).index := rfl

end CFSG.QuasithinUnique.Setup.X5
