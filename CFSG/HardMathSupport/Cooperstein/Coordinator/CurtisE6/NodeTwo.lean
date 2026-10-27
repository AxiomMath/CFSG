module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeTab

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Arith

theorem cross_sep {ι : Type*} {r : ℕ} (X β : ι → Fin r → ℤ) (M a b b' g h : ℕ) (hg : 1 ≤ g)
    (hhM : h ∣ M) (hha : h ∣ a) (hhodd : Odd h) (hbig : 2 ^ (g + 1) + 2 < h)
    (hb' : (M : ℤ) ∣ 2 ^ b' - 2 ^ (b + g)) (hbd : ∀ p i, |β p i| ≤ 2)
    (hprim : ∀ p, ∀ d : ℕ, (∀ i, (d : ℤ) ∣ β p i) → d = 1) (p q : ι)
    (hcong : ∀ i, (M : ℤ) ∣ ((a : ℤ) * X p i - 2 ^ b * β p i) - ((a : ℤ) * X q i - 2 ^ b' * β q i)) :
    False := by
  have hhM' : (h : ℤ) ∣ M := Int.natCast_dvd_natCast.2 hhM
  have hha' : (h : ℤ) ∣ a := Int.natCast_dvd_natCast.2 hha
  have hcop : IsCoprime (h : ℤ) ((2 : ℤ) ^ b) := odd_isCoprime_two_pow hhodd b
  have key : ∀ i, β p i = 2 ^ g * β q i := by
    intro i
    have h1 := dvd_trans hhM' (hcong i)
    have h2 : (h : ℤ) ∣ (a : ℤ) * (X p i - X q i) := dvd_mul_of_dvd_left hha' _
    have h3 : (h : ℤ) ∣ 2 ^ b * β p i - 2 ^ b' * β q i := by
      have e : ((a : ℤ) * X p i - 2 ^ b * β p i) - ((a : ℤ) * X q i - 2 ^ b' * β q i) =
          a * (X p i - X q i) - (2 ^ b * β p i - 2 ^ b' * β q i) := by ring
      rw [e] at h1
      have := dvd_sub h2 h1
      rwa [sub_sub_cancel] at this
    have h4 : (h : ℤ) ∣ (2 ^ b' - 2 ^ (b + g)) * β q i := dvd_mul_of_dvd_left (dvd_trans hhM' hb') _
    have h5 : (h : ℤ) ∣ 2 ^ b * (β p i - 2 ^ g * β q i) := by
      have e : (2 : ℤ) ^ b * (β p i - 2 ^ g * β q i) =
          (2 ^ b * β p i - 2 ^ b' * β q i) + (2 ^ b' - 2 ^ (b + g)) * β q i := by
        rw [pow_add]; ring
      rw [e]
      exact dvd_add h3 h4
    have h6 : (h : ℤ) ∣ β p i - 2 ^ g * β q i := hcop.dvd_of_dvd_mul_left h5
    have hb1 := hbd p i
    have hb2 := hbd q i
    rw [abs_le] at hb1 hb2
    have hg2 : (2 : ℤ) ^ g * 2 ≤ 2 ^ (g + 1) := by rw [pow_succ]
    have hgp : (0 : ℤ) < 2 ^ g := by positivity
    have hlt : |β p i - 2 ^ g * β q i| < h := by
      have : (2 : ℤ) ^ (g + 1) + 2 < h := by exact_mod_cast hbig
      rw [abs_lt]
      constructor <;> nlinarith
    have := Int.eq_zero_of_abs_lt_dvd h6 hlt
    linarith
  have hd : ∀ i, ((2 ^ g : ℕ) : ℤ) ∣ β p i := fun i => ⟨β q i, by push_cast; exact key i⟩
  have h1 := hprim p (2 ^ g) hd
  have : 2 ^ g = 2 ^ 0 := by rw [h1]; rfl
  have := Nat.pow_right_injective (le_refl 2) this
  omega

theorem gcd_ge_pow {n g a : ℕ} (hn : 1 ≤ n) (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : (2 ^ n - 1) ∣ (2 ^ g - 1) * a)
    (ha : 0 < a) : 2 ^ (n - g) ≤ Nat.gcd a (2 ^ n - 1) := by
  obtain ⟨t, rfl⟩ := hgn
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hdvd : 2 ^ g - 1 ∣ 2 ^ (g * t) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 t
    rwa [one_pow, ← pow_mul] at this
  obtain ⟨gh, hgh⟩ := hdvd
  have hpos : 0 < 2 ^ g - 1 := by omega
  have hghdvd : gh ∣ a := by
    rw [hgh] at hper
    exact (Nat.dvd_of_mul_dvd_mul_left hpos (by simpa [mul_comm] using hper))
  have hghM : gh ∣ 2 ^ (g * t) - 1 := ⟨2 ^ g - 1, by rw [hgh]; ring⟩
  have hgcd : gh ∣ Nat.gcd a (2 ^ (g * t) - 1) := Nat.dvd_gcd hghdvd hghM
  have hgpos : 0 < Nat.gcd a (2 ^ (g * t) - 1) := Nat.gcd_pos_of_pos_left _ ha
  have hle : gh ≤ Nat.gcd a (2 ^ (g * t) - 1) := Nat.le_of_dvd hgpos hgcd
  have h3 : 2 ^ (g * t - g) ≤ gh := by
    have h4 : (2 ^ g - 1) * 2 ^ (g * t - g) ≤ (2 ^ g - 1) * gh := by
      rw [← hgh]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; simp at hn
        · exact h0
      have h5 : 2 ^ (g * t) = 2 ^ g * 2 ^ (g * t - g) := by
        rw [← pow_add]; congr 1
        have : g ≤ g * t := Nat.le_mul_of_pos_right _ ht1
        omega
      have h6 : 0 < 2 ^ (g * t - g) := by positivity
      rw [h5]
      obtain ⟨y, hy⟩ : ∃ y, 2 ^ g = y + 1 := ⟨2 ^ g - 1, by omega⟩
      rw [hy]
      simp only [Nat.add_sub_cancel]
      have : (y + 1) * 2 ^ (g * t - g) - 1 ≥ y * 2 ^ (g * t - g) := by
        have : (y + 1) * 2 ^ (g * t - g) = y * 2 ^ (g * t - g) + 2 ^ (g * t - g) := by ring
        omega
      exact this
    exact Nat.le_of_mul_le_mul_left h4 hpos
  omega


theorem two_pow_mod_n (n m : ℕ) : 2 ^ (m % n) ≡ 2 ^ m [MOD 2 ^ n - 1] := by
  set M : ℕ := 2 ^ n - 1 with hM
  have h2n : 2 ^ n ≡ 1 [MOD M] := by
    have : (2 ^ n : ℕ) = M + 1 := by
      rw [hM]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [this]
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ M + 1)).2 (by simp)).symm
  have e : 2 ^ m = 2 ^ (m % n) * (2 ^ n) ^ (m / n) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have : (2 ^ n) ^ (m / n) ≡ 1 [MOD M] := by
    simpa using h2n.pow (m / n)
  rw [e]
  calc 2 ^ (m % n) = 2 ^ (m % n) * 1 := (mul_one _).symm
    _ ≡ 2 ^ (m % n) * (2 ^ n) ^ (m / n) [MOD M] := Nat.ModEq.mul_left _ this.symm

theorem shift_mem {n g : ℕ} (hn : 1 ≤ n) {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n)
    (hper : (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ i ∈ J', 2 ^ i) {b : ℕ} (hb : b ∈ J') :
    (b + g) % n ∈ J' := by
  set M : ℕ := 2 ^ n - 1 with hM
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hinj : Set.InjOn (fun i => (i + g) % n) (J' : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := hJ' x hx
    have hy' := hJ' y hy
    simp only at hxy
    have h1 : (x + g) % n = (y + g) % n := hxy
    have h2 : x ≡ y [MOD n] := (Nat.ModEq.add_right_cancel' g h1)
    exact Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'
  set J'' : Finset ℕ := J'.image (fun i => (i + g) % n) with hJ''
  have hJ''n : ∀ i ∈ J'', i < n := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
    exact Nat.mod_lt _ (by omega)
  have hsum : ∑ i ∈ J'', 2 ^ i = ∑ i ∈ J', 2 ^ ((i + g) % n) := Finset.sum_image hinj
  have h2n : 2 ^ n ≡ 1 [MOD M] := by
    have : (2 ^ n : ℕ) = M + 1 := by
      rw [hM]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [this]
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ M + 1)).2 (by simp)).symm
  have hterm : ∀ i, 2 ^ ((i + g) % n) ≡ 2 ^ (i + g) [MOD M] := by
    intro i
    conv_rhs => rw [← Nat.mod_add_div (i + g) n, pow_add, pow_mul]
    have : (2 ^ n) ^ ((i + g) / n) ≡ 1 [MOD M] := by
      simpa using h2n.pow ((i + g) / n)
    calc 2 ^ ((i + g) % n) = 2 ^ ((i + g) % n) * 1 := (mul_one _).symm
      _ ≡ 2 ^ ((i + g) % n) * (2 ^ n) ^ ((i + g) / n) [MOD M] := Nat.ModEq.mul_left _ this.symm
  have hsumeq : ∑ i ∈ J', 2 ^ ((i + g) % n) ≡ 2 ^ g * a [MOD M] := by
    have : 2 ^ g * a = ∑ i ∈ J', 2 ^ (i + g) := by
      rw [ha, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [this]
    exact Nat.ModEq.sum fun i _ => hterm i
  have hag : 2 ^ g * a ≡ a [MOD M] := by
    have h1 : a ≤ 2 ^ g * a := Nat.le_mul_of_pos_left _ (by positivity)
    have h2 : M ∣ 2 ^ g * a - a := by
      have : 2 ^ g * a - a = (2 ^ g - 1) * a := by rw [Nat.sub_one_mul]
      rw [this]; exact hper
    exact ((Nat.modEq_iff_dvd' h1).2 h2).symm
  have hmod : ∑ i ∈ J'', 2 ^ i ≡ a [MOD M] := by
    rw [hsum]; exact hsumeq.trans hag
  have hle1 : ∑ i ∈ J'', 2 ^ i ≤ M := sum_two_pow_le J'' hJ''n
  have hle2 : a ≤ M := sum_two_pow_le J' hJ'
  have hpos1 : 0 < ∑ i ∈ J'', 2 ^ i := by
    have hbm : (b + g) % n ∈ J'' := Finset.mem_image.2 ⟨b, hb, rfl⟩
    exact lt_of_lt_of_le (Nat.two_pow_pos _) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hbm)
  have hpos2 : 0 < a := lt_of_lt_of_le (Nat.two_pow_pos _) (Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) hb)
  have heq : ∑ i ∈ J'', 2 ^ i = a := by
    have hMpos : 0 < M := by omega
    rcases Nat.lt_or_ge (∑ i ∈ J'', 2 ^ i) M with h1 | h1
    · rcases Nat.lt_or_ge a M with h2 | h2
      · exact Nat.ModEq.eq_of_lt_of_lt hmod h1 h2
      · have : a = M := by omega
        rw [this] at hmod
        have h3 := (Nat.modEq_zero_iff_dvd.1 (hmod.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
        have := Nat.le_of_dvd hpos1 h3
        omega
    · have : ∑ i ∈ J'', 2 ^ i = M := by omega
      rw [this] at hmod ⊢
      rcases Nat.lt_or_ge a M with h2 | h2
      · have h3 : M ∣ a := (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
        have := Nat.le_of_dvd hpos2 h3
        omega
      · omega
  have : J'' = J' := Finset.equivBitIndices.symm.injective heq
  rw [← this]
  exact Finset.mem_image.2 ⟨b, hb, rfl⟩

end Arith

section Two


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  {s : N6}

theorem two_dim_lt [Module.Finite k V] (T : NodeTab s)
    (hprim : ∀ i : Fin T.A, ∀ d : ℕ, (∀ c, (d : ℤ) ∣ famB s T.wW i c) → d = 1)
    {n g : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hg : 1 ≤ g)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {a b b' : ℕ}
    (hMo : Odd (2 ^ n - 1)) (ha0 : ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (a : ℤ)))
    (hgcd3 : 3 ≤ Nat.gcd a (2 ^ n - 1)) (hbig : 2 ^ (g + 1) + 2 < Nat.gcd a (2 ^ n - 1))
    (hb' : (((2 ^ n - 1 : ℕ) : ℤ)) ∣ 2 ^ b' - 2 ^ (b + g)) {e e' : V} (he0 : e ≠ 0) (he0' : e' ≠ 0)
    (hew : e ∈ wt ρ ((a : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s))
    (hew' : e' ∈ wt ρ ((a : ℤ) • omegaF s - (2 : ℤ) ^ b' • alphaF s)) :
    2 * (T.A * T.B) ≤ Module.finrank k V := by
  classical
  have hinj : ∀ g' : ↥(e6Data_valid.minGroup K), Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  let bb : Bool → ℕ := fun f => if f then b' else b
  let ee : Bool → V := fun f => if f then e' else e
  have hee0 : ∀ f, ee f ≠ 0 := fun f => by cases f <;> simp [ee, he0, he0']
  have heew : ∀ f, ee f ∈ wt ρ ((a : ℤ) • omegaF s - (2 : ℤ) ^ bb f • alphaF s) := fun f => by
    cases f
    · simpa [ee, bb] using hew
    · simpa [ee, bb] using hew'
  let x : Bool × (Fin T.A × Fin T.B) → N6 → ℤ := fun q =>
    (a : ℤ) • famX s T.wW T.uW q.2.1 q.2.2 - (2 : ℤ) ^ bb q.1 • famB s T.wW q.2.1
  let v : Bool × (Fin T.A × Fin T.B) → V := fun q =>
    ρ (nProd K (T.wW q.2.1 ++ T.uW q.2.2)) (ee q.1)
  have hv : ∀ q, v q ∈ wt ρ (x q) := by
    intro q
    have := wt_nProd ρ (T.wW q.2.1 ++ T.uW q.2.2) (heew q.1)
    rwa [famVec_weight T.wW T.uW a (bb q.1) T.fam_hU q.2.1 q.2.2] at this
  have hv0 : ∀ q, v q ≠ 0 := fun q h0 =>
    hee0 q.1 (hinj (nProd K (T.wW q.2.1 ++ T.uW q.2.2)) (by rw [map_zero]; exact h0))
  have hinjP : ∀ p q : Fin T.A × Fin T.B, famX s T.wW T.uW p.1 p.2 = famX s T.wW T.uW q.1 q.2 →
      famB s T.wW p.1 = famB s T.wW q.1 → p = q := by
    intro p q h1 h2
    obtain ⟨e1, e2⟩ := T.fam_hinj p.1 q.1 p.2 q.2 h1 h2
    exact Prod.ext e1 e2
  have hh3 : 3 ≤ Nat.gcd a (2 ^ n - 1) := hgcd3
  have hli : LinearIndependent k v := by
    refine linearIndependent_of_wt ρ v x hv (fun c => ?_)
    haveI : Subsingleton {q : Bool × (Fin T.A × Fin T.B) // wcls K k (x q) = c} := by
      refine ⟨fun q q' => ?_⟩
      have hd : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣ x q.1 i - x q'.1 i := by
        intro i
        have := dvd_of_wcls_eq (q.2.trans q'.2.symm) i
        rwa [hcard] at this
      obtain ⟨⟨f, p⟩, hq⟩ := q
      obtain ⟨⟨f', p'⟩, hq'⟩ := q'
      simp only at hd
      have hcongA : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣
          (((a : ℤ) * famX s T.wW T.uW p.1 p.2 i - 2 ^ bb f * famB s T.wW p.1 i) -
            ((a : ℤ) * famX s T.wW T.uW p'.1 p'.2 i - 2 ^ bb f' * famB s T.wW p'.1 i)) := by
        intro i
        have := hd i
        simpa [x, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
      have hhM : Nat.gcd a (2 ^ n - 1) ∣ 2 ^ n - 1 := Nat.gcd_dvd_right _ _
      have hha : Nat.gcd a (2 ^ n - 1) ∣ a := Nat.gcd_dvd_left _ _
      have hhodd : Odd (Nat.gcd a (2 ^ n - 1)) := Odd.of_dvd_nat hMo hhM
      have hbdβ : ∀ p : Fin T.A × Fin T.B, ∀ i, |famB s T.wW p.1 i| ≤ 2 :=
        fun p i => T.fam_bdβ p.1 i
      cases f <;> cases f'
      · have := class_sep_gcd (fun p : Fin T.A × Fin T.B => famX s T.wW T.uW p.1 p.2)
          (fun p => famB s T.wW p.1) (2 ^ n - 1) a b hMo hh3
          (fun p q h => T.fam_hβ p.1 q.1 h) (fun p q h => T.fam_hX p.1 q.1 p.2 q.2 h) hinjP ha0
          p p' (by simpa [bb] using hcongA)
        subst this; rfl
      · exfalso
        exact cross_sep (fun p : Fin T.A × Fin T.B => famX s T.wW T.uW p.1 p.2)
          (fun p => famB s T.wW p.1) (2 ^ n - 1) a b b' g _ hg hhM hha hhodd hbig hb' hbdβ
          (fun p d hd => hprim p.1 d hd) p p' (by simpa [bb] using hcongA)
      · exfalso
        refine cross_sep (fun p : Fin T.A × Fin T.B => famX s T.wW T.uW p.1 p.2)
          (fun p => famB s T.wW p.1) (2 ^ n - 1) a b b' g _ hg hhM hha hhodd hbig hb' hbdβ
          (fun p d hd => hprim p.1 d hd) p' p (fun i => ?_)
        have := hcongA i
        simpa [bb] using (dvd_neg.2 this : (((2 ^ n - 1 : ℕ) : ℤ)) ∣ -_)
      · have := class_sep_gcd (fun p : Fin T.A × Fin T.B => famX s T.wW T.uW p.1 p.2)
          (fun p => famB s T.wW p.1) (2 ^ n - 1) a b' hMo hh3
          (fun p q h => T.fam_hβ p.1 q.1 h) (fun p q h => T.fam_hX p.1 q.1 p.2 q.2 h) hinjP ha0
          p p' (by simpa [bb] using hcongA)
        subst this; rfl
    exact liSub _ (fun q => hv0 q.1)
  simpa [mul_comm] using hli.fintype_card_le_finrank

theorem two_dim_eq [Module.Finite k V] (T : NodeTab s)
    (hprim : ∀ i : Fin T.A, ∀ d : ℕ, (∀ c, (d : ℤ) ∣ famB s T.wW i c) → d = 1)
    {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J) {b b' : ℕ} (hbb : b' = b + 1)
    {e e' : V} (he : e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y)
    (he' : e' ∈ orbitSpan (ρ.comp (rankOne6 K s)) y) (he0 : e ≠ 0) (he0' : e' ≠ 0)
    (hew : e ∈ wt ρ (((2 ^ n - 1 : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s))
    (hew' : e' ∈ wt ρ (((2 ^ n - 1 : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b' • alphaF s)) :
    2 * (T.A * T.B) ≤ Module.finrank k V := by
  classical
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have hinj : ∀ g' : ↥(e6Data_valid.minGroup K), Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
  have hM7 : 7 ≤ 2 ^ n - 1 := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  let u' : Fin T.B → WeylGroup Tag.E6 := fun j => (coxeterSystem Tag.E6).wordProd (T.uW j)
  have hu : ∀ j, u' j • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1 := by
    intro j; rw [wordProd_smul_foldr, T.fam_hU2 j]
  have hv₀ : ∀ j, reflect Tag.E6 j T.v0F ≠ T.v0F → j ∉ J := by
    intro j hj
    by_cases hjs : j = s
    · exact hjs ▸ hs
    · exact absurd (T.fam_hv0 j hjs) hj
  have hli : LinearIndependent k (fun j => ρ (canonMin K (u' j)) y) := by
    refine linearIndependent_translates_support hρ ht hv₀ u' ?_
    intro j j' hjj h
    apply T.fam_hdist j j' hjj
    have := h
    simp only [u', wordProd_smul_foldr] at this
    exact this
  let bb : Bool → ℕ := fun f => if f then b' else b
  let ee : Bool → V := fun f => if f then e' else e
  have hee0 : ∀ f, ee f ≠ 0 := fun f => by cases f <;> simp [ee, he0, he0']
  have heeN : ∀ f, ee f ∈ orbitSpan (ρ.comp (rankOne6 K s)) y := fun f => by
    cases f
    · simpa [ee] using he
    · simpa [ee] using he'
  have heew : ∀ f, ee f ∈ wt ρ (((2 ^ n - 1 : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ bb f • alphaF s) :=
    fun f => by
      cases f
      · simpa [ee, bb] using hew
      · simpa [ee, bb] using hew'
  have hcop : ∀ f, LinearIndependent k (fun j => ρ (canonMin K (u' j)) (ee f)) := fun f =>
    copies_linearIndependent hρ ht (s := s) u' hu hli (heeN f) (hee0 f)
  have hmE : ∀ f i, mE (-((2 : ℤ) ^ bb f • (Pi.single s 1 : N6 → ℤ))) i =
      (-((2 : ℤ) ^ bb f • alphaF s)) i := by
    intro f i
    simp only [mE, alphaF, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_neg, Finset.sum_neg_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have heν : ∀ f, ee f ∈ wt ρ (mE (-((2 : ℤ) ^ bb f • (Pi.single s 1 : N6 → ℤ)))) := by
    intro f i t
    rw [heew f i t, hmE]
    congr 1
    have : (((2 ^ n - 1 : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ bb f • alphaF s) i =
        ((2 ^ n - 1 : ℕ) : ℤ) * (if i = s then 1 else 0) + (-((2 : ℤ) ^ bb f • alphaF s)) i := by
      simp only [omegaF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.neg_apply]
      ring
    rw [this, kp_add, kp_mul_card t _ hcard, one_mul]
  have hf : ∀ f j, ρ (canonMin K (u' j)) (ee f) ∈ wt ρ (-((2 : ℤ) ^ bb f • alphaF s)) := by
    intro f j
    have h1 := wt_canonMin ρ (u' j) (heν f)
    have h2 : u' j • (-((2 : ℤ) ^ bb f • (Pi.single s 1 : N6 → ℤ))) =
        -((2 : ℤ) ^ bb f • (Pi.single s 1 : N6 → ℤ)) := by
      rw [smul_neg, smul_comm, hu j]
    rw [h2] at h1
    intro i t
    rw [h1 i t, hmE]
  let x : Bool × (Fin T.A × Fin T.B) → N6 → ℤ := fun q =>
    -((2 : ℤ) ^ bb q.1 • famB s T.wW q.2.1)
  let v : Bool × (Fin T.A × Fin T.B) → V := fun q =>
    ρ (nProd K (T.wW q.2.1)) (ρ (canonMin K (u' q.2.2)) (ee q.1))
  have hv : ∀ q, v q ∈ wt ρ (x q) := by
    intro q
    have := wt_nProd ρ (T.wW q.2.1) (hf q.1 q.2.2)
    rwa [foldr_refE_neg_smul] at this
  have hM2 : ∀ f, ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ bb f) := by
    intro f h
    have h1 : (((2 ^ n - 1 : ℕ) : ℤ) ∣ 1) := by
      have := (odd_isCoprime_two_pow hodd (bb f)).dvd_of_dvd_mul_left
        (by simpa using h : (((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ bb f * 1))
      exact this
    have h2 : 2 ^ n - 1 = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
    omega
  have hbdβ : ∀ p : Fin T.A × Fin T.B, ∀ i, |famB s T.wW p.1 i| ≤ 2 :=
    fun p i => T.fam_bdβ p.1 i
  have hli2 : LinearIndependent k v := by
    refine linearIndependent_of_wt ρ v x hv (fun c => ?_)
    rcases isEmpty_or_nonempty {q : Bool × (Fin T.A × Fin T.B) // wcls K k (x q) = c} with hE | ⟨⟨q0, hq0⟩⟩
    · exact linearIndependent_empty_type
    · have hsame : ∀ q : {q : Bool × (Fin T.A × Fin T.B) // wcls K k (x q) = c},
          q.1.1 = q0.1 ∧ q.1.2.1 = q0.2.1 := by
        intro q
        have hd : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣ x q.1 i - x q0 i := by
          intro i
          have := dvd_of_wcls_eq (q.2.trans hq0.symm) i
          rwa [hcard] at this
        have hfam : q.1.1 = q0.1 := by
          by_contra hne
          have hd' : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣
              (((0 : ℕ) : ℤ) * (0 : ℤ) - 2 ^ bb q.1.1 * famB s T.wW q.1.2.1 i) -
                (((0 : ℕ) : ℤ) * (0 : ℤ) - 2 ^ bb q0.1 * famB s T.wW q0.2.1 i) := by
            intro i
            have := hd i
            have e1 : x q.1 i - x q0 i = (((0 : ℕ) : ℤ) * (0 : ℤ) - 2 ^ bb q.1.1 * famB s T.wW q.1.2.1 i) -
                (((0 : ℕ) : ℤ) * (0 : ℤ) - 2 ^ bb q0.1 * famB s T.wW q0.2.1 i) := by
              simp only [x, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
            rwa [e1] at this
          obtain ⟨⟨f, p⟩, hq⟩ := q
          obtain ⟨f0, p0⟩ := q0
          simp only at hne hd'
          cases f <;> cases f0
          · exact hne rfl
          · refine cross_sep (fun _ _ => (0 : ℤ)) (fun p : Fin T.A × Fin T.B => famB s T.wW p.1)
              (2 ^ n - 1) 0 b b' 1 (2 ^ n - 1) le_rfl dvd_rfl (dvd_zero _) hodd (by omega)
              (by rw [hbb]; simp) hbdβ (fun p d hd => hprim p.1 d hd) p p0
              (fun i => by simpa [bb] using hd' i)
          · refine cross_sep (fun _ _ => (0 : ℤ)) (fun p : Fin T.A × Fin T.B => famB s T.wW p.1)
              (2 ^ n - 1) 0 b b' 1 (2 ^ n - 1) le_rfl dvd_rfl (dvd_zero _) hodd (by omega)
              (by rw [hbb]; simp) hbdβ (fun p d hd => hprim p.1 d hd) p0 p
              (fun i => by simpa [bb] using (dvd_neg.2 (hd' i) : (((2 ^ n - 1 : ℕ) : ℤ)) ∣ -_))
          · exact hne rfl
        refine ⟨hfam, ?_⟩
        apply T.fam_hβinj
        by_contra hne
        have hCB := T.fam_hβ q.1.2.1 q0.2.1 hne
        have hdv : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣
            (2 : ℤ) ^ bb q0.1 * (famB s T.wW q.1.2.1 - famB s T.wW q0.2.1) i := by
          intro i
          have e1 : x q.1 i - x q0 i =
              -((2 : ℤ) ^ bb q0.1 * (famB s T.wW q.1.2.1 - famB s T.wW q0.2.1) i) := by
            simp only [x, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hfam]
            ring
          have := hd i
          rw [e1, dvd_neg] at this
          exact this
        exact hM2 q0.1 (dvd_of_cont2 hCB hodd hdv)
      have hf' : Function.Injective
          (fun q : {q : Bool × (Fin T.A × Fin T.B) // wcls K k (x q) = c} => q.1.2.2) := by
        intro p q hpq
        exact Subtype.ext (Prod.ext ((hsame p).1.trans (hsame q).1.symm)
          (Prod.ext ((hsame p).2.trans (hsame q).2.symm) hpq))
      have hcop' : LinearIndependent k (fun j : Fin T.B =>
          ρ (nProd K (T.wW q0.2.1)) (ρ (canonMin K (u' j)) (ee q0.1))) :=
        (hcop q0.1).map' (ρ (nProd K (T.wW q0.2.1))) (LinearMap.ker_eq_bot.2 (hinj _))
      have := hcop'.comp (fun q : {q : Bool × (Fin T.A × Fin T.B) // wcls K k (x q) = c} => q.1.2.2) hf'
      convert this using 2 with q
      simp only [Function.comp, v]
      rw [(hsame q).1, (hsame q).2]
  simpa [mul_comm] using hli2.fintype_card_le_finrank

end Two

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
