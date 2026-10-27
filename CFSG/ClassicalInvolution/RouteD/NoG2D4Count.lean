module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect
import CFSG.ClassicalInvolution.Phan.PhanS9O3Num

public section

namespace CFSG.ClassicalInvolution.RouteD.G2D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic CFSG.Open
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Groups

theorem card_sup_mul_card_inf_of_commute {H : Type*} [Group H] [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) =
      Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem card_center_sl2_dvd_two {F : Type*} [Field F] :
    Nat.card (Subgroup.center SL(2, F)) ∣ 2 := by
  have hle : Subgroup.center SL(2, F) ≤ Subgroup.zpowers (-1 : SL(2, F)) := by
    intro A hA
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
    obtain ⟨r, hr, hrA⟩ := hA
    rw [Fintype.card_fin] at hr
    have hr' : r * r = 1 := by rw [← pow_two]; exact hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · have : A = 1 := by
        apply Subtype.ext
        rw [← hrA]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [this]
      exact Subgroup.one_mem _
    · have : A = -1 := by
        apply Subtype.ext
        rw [← hrA]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [this]
      exact Subgroup.mem_zpowers _
  refine (Subgroup.card_dvd_of_le hle).trans ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

theorem card_sl2_field {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.ClassicalInvolution.PhanB3.S.card_specialLinear_two

theorem card_inf_dvd_of_commute {Y : Type*} [Group Y] {A B : Subgroup Y}
    (c : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hz : Nat.card (Subgroup.center A) ∣ 2) :
    Nat.card (A ⊓ B : Subgroup Y) ∣ 2 := by
  have hle : (A ⊓ B).subgroupOf A ≤ Subgroup.center A := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hxB : (x : Y) ∈ B := (Subgroup.mem_subgroupOf.mp hx).2
    exact Subtype.ext (c g g.2 x hxB)
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
  exact (Subgroup.card_dvd_of_le hle).trans hz

theorem card_mul_dvd_of_commute_triple {Y : Type*} [Group Y] [Finite Y] {Q A₁ A₂ A₃ : Subgroup Y}
    (h₁ : A₁ ≤ Q) (h₂ : A₂ ≤ Q) (h₃ : A₃ ≤ Q)
    (c₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) (c₁₃ : ∀ x ∈ A₁, ∀ y ∈ A₃, x * y = y * x)
    (c₂₃ : ∀ x ∈ A₂, ∀ y ∈ A₃, x * y = y * x)
    (hz₁ : Nat.card (Subgroup.center A₁) ∣ 2) (hz₂ : Nat.card (Subgroup.center A₂) ∣ 2) :
    Nat.card A₁ * Nat.card A₂ * Nat.card A₃ ∣ 4 * Nat.card Q := by
  set B : Subgroup Y := A₂ ⊔ A₃ with hB
  have hBc : ∀ x ∈ A₁, ∀ y ∈ B, x * y = y * x := by
    have hle : B ≤ Subgroup.centralizer (A₁ : Set Y) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => c₁₂ x hx y hy
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => c₁₃ x hx y hy
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx
  have e₁ := card_sup_mul_card_inf_of_commute A₁ B hBc
  have e₂ := card_sup_mul_card_inf_of_commute A₂ A₃ c₂₃
  have d₁ : Nat.card (A₁ ⊔ B : Subgroup Y) ∣ Nat.card Q :=
    Subgroup.card_dvd_of_le (sup_le h₁ (sup_le h₂ h₃))
  have d₂ : Nat.card (A₁ ⊓ B : Subgroup Y) ∣ 2 := card_inf_dvd_of_commute hBc hz₁
  have d₃ : Nat.card (A₂ ⊓ A₃ : Subgroup Y) ∣ 2 := card_inf_dvd_of_commute c₂₃ hz₂
  calc Nat.card A₁ * Nat.card A₂ * Nat.card A₃
      = Nat.card A₁ * (Nat.card A₂ * Nat.card A₃) := by ring
    _ = Nat.card A₁ * (Nat.card B * Nat.card (A₂ ⊓ A₃ : Subgroup Y)) := by rw [e₂]
    _ = (Nat.card A₁ * Nat.card B) * Nat.card (A₂ ⊓ A₃ : Subgroup Y) := by ring
    _ = (Nat.card (A₁ ⊔ B : Subgroup Y) * Nat.card (A₁ ⊓ B : Subgroup Y)) *
          Nat.card (A₂ ⊓ A₃ : Subgroup Y) := by rw [e₁]
    _ ∣ (Nat.card Q * 2) * 2 := Nat.mul_dvd_mul (Nat.mul_dvd_mul d₁ d₂) d₃
    _ = 4 * Nat.card Q := by ring

end Groups

section Arith

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ := hq
  have h1 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
  have h2 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by omega
  rw [h2]
  exact Nat.mul_dvd_mul_left 4 (Nat.even_mul_succ_self m).two_dvd

theorem padicValNat_two_of_odd {n : ℕ} (hn : Odd n) : padicValNat 2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.mp hn)

theorem padicValNat_two_cube_sub_one {x : ℕ} (hx : Odd x) (hx2 : 2 ≤ x) :
    padicValNat 2 (x ^ 3 - 1) = padicValNat 2 (x - 1) := by
  have h : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    have h1 : (y + 1) ^ 3 = y * ((y + 1) ^ 2 + (y + 1) + 1) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hodd : Odd (x ^ 2 + x + 1) := by
    obtain ⟨m, rfl⟩ := hx
    exact ⟨2 * m ^ 2 + 3 * m + 1, by ring⟩
  rw [h, padicValNat.mul (by omega) (by positivity), padicValNat_two_of_odd hodd, add_zero]

theorem two_pow_padicValNat_dvd_pow_sub_one (x k : ℕ) :
    2 ^ padicValNat 2 (x - 1) ∣ x ^ k - 1 := by
  have h1 : 2 ^ padicValNat 2 (x - 1) ∣ x - 1 := pow_padicValNat_dvd
  have h2 : x - 1 ∣ x ^ k - 1 := by simpa using Nat.sub_dvd_pow_sub_pow x 1 k
  exact h1.trans h2

theorem false_of_dvd_of_padicValNat {N M s : ℕ} (hs : 3 ≤ s) (hN : s ≤ padicValNat 2 N)
    (hM : padicValNat 2 M ≤ 2 * s) (hM0 : M ≠ 0) (h : N * N * N ∣ 4 * M) : False := by
  have h1 : 2 ^ (3 * padicValNat 2 N) ∣ N * N * N := by
    have : 2 ^ padicValNat 2 N ∣ N := pow_padicValNat_dvd
    have := Nat.mul_dvd_mul (Nat.mul_dvd_mul this this) this
    rw [show 3 * padicValNat 2 N = padicValNat 2 N + padicValNat 2 N + padicValNat 2 N by ring,
      pow_add, pow_add]
    exact this
  have h2 : 2 ^ (3 * padicValNat 2 N) ∣ 4 * M := h1.trans h
  have h3 : 3 * padicValNat 2 N ≤ padicValNat 2 (4 * M) := by
    have := (padicValNat_dvd_iff_le (p := 2) (by positivity : 4 * M ≠ 0)).mp h2
    exact this
  rw [padicValNat.mul (by norm_num) hM0] at h3
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  omega

end Arith

section Orders

variable (p e : ℕ) [Fact p.Prime]

theorem map_twistedGroup_eq_graphFixedRootGroup (hp2 : p ≠ 2) (he : 1 ≤ e) :
    (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)).map
        (adjointGroup d4 (GaloisField p (3 * e))).subtype =
      graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
        (iterateFrobenius (GaloisField p (3 * e)) p e) := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set σ := iterateFrobenius K0 p e with hσdef
  have hK3 : Nat.card K0 = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite K0 := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσ : ∀ c : K0, σ c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hK2 : ringChar K0 ≠ 2 := by
    rw [ringChar.eq K0 p]
    exact hp2
  have hq2 : 2 ≤ p ^ e := by
    have := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  let σK : K0 ≃+* K0 := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have h1 := (odd_diagram_fixed_root_group_perfect TwistTag.D4 K0 hK2 σK).2.2
  rw [hσK] at h1
  have h2 := commutator_twistedFixedGroup_eq_map σ hq2 hK3 hσ
  exact h2.symm.trans h1

theorem card_twistedGroup_iterateFrobenius (hp2 : p ≠ 2) (he : 1 ≤ e) :
    Nat.card (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) =
      ordTrialityD4 (p ^ e) := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set σ := iterateFrobenius K0 p e with hσdef
  have hK3 : Nat.card K0 = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite K0 := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσ : ∀ c : K0, σ c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have h3 := map_twistedGroup_eq_graphFixedRootGroup p e hp2 he
  have h4 := CFSG.ClassicalInvolution.card_graphFixedRootGroup_D4_of_ne_two
    (K := K0) (Fact.out : p.Prime) hp2 he hK3 σ hσ
  rw [← h3, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h4
  exact h4

theorem odd_pow_of_ne_two (hp2 : p ≠ 2) (e : ℕ) : Odd (p ^ e) :=
  (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem padicValNat_card_modelUniv (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4) (n : ℕ) (he : 1 ≤ e) :
    padicValNat 2 (Nat.card (modelUniv t n p e Fact.out).K) =
      2 * padicValNat 2 ((p ^ e) ^ 2 - 1) := by
  have hodd : Odd (p ^ e) := odd_pow_of_ne_two p hp2 e
  have hq3 : 3 ≤ p ^ e := by
    have h2 : 2 ≤ p ^ e := by
      have := (Fact.out : p.Prime).two_le
      calc 2 ≤ p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
    rcases hodd with ⟨m, hm⟩
    omega
  have hx : Odd ((p ^ e) ^ 2) := hodd.pow
  have hx2 : 2 ≤ (p ^ e) ^ 2 := by nlinarith
  have hcube : padicValNat 2 ((p ^ e) ^ 6 - 1) = padicValNat 2 ((p ^ e) ^ 2 - 1) := by
    have := padicValNat_two_cube_sub_one hx hx2
    rwa [← pow_mul] at this
  have hne1 : (p ^ e) ^ 2 - 1 ≠ 0 := by
    have : 1 < (p ^ e) ^ 2 := by omega
    omega
  have hne6 : (p ^ e) ^ 6 - 1 ≠ 0 := by
    have : 1 < (p ^ e) ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hne8 : (p ^ e) ^ 8 + (p ^ e) ^ 4 + 1 ≠ 0 := by positivity
  have hodd8 : Odd ((p ^ e) ^ 8 + (p ^ e) ^ 4 + 1) :=
    ((hodd.pow : Odd ((p ^ e) ^ 8)).add_odd (hodd.pow : Odd ((p ^ e) ^ 4))).add_one
  have hmod6 : Odd ((p ^ e) ^ 6) := hodd.pow
  have hmod12 : Odd ((p ^ e) ^ 12) := hodd.pow
  rcases ht with rfl | rfl
  · show padicValNat 2 (Nat.card (adjointGroup .G2 (GaloisField p e))) = _
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, GaloisField.card p e (by omega),
      ordG2, padicValNat.mul (by positivity) hne1, padicValNat.mul (by positivity) hne6,
      padicValNat_two_of_odd hmod6, hcube]
    ring
  · show padicValNat 2 (Nat.card (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) = _
    rw [card_twistedGroup_iterateFrobenius p e hp2 he, ordTrialityD4,
      padicValNat.mul (by positivity) hne1, padicValNat.mul (by positivity) hne6,
      padicValNat.mul (by positivity) hne8, padicValNat_two_of_odd hmod12,
      padicValNat_two_of_odd hodd8, hcube]
    ring

end Orders

section Count

variable {p : ℕ} [Fact p.Prime]

theorem false_of_three_commuting_sl2 (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4) {n e f : ℕ} (hadm : StatedLieAdmissible t n p e)
    (hef : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) {X : Type} [Group X] [Finite X]
    (φ : (modelUniv t n p e Fact.out).K →* X) {A₁ A₂ A₃ : Subgroup X}
    (h₁ : A₁ ≤ φ.range) (h₂ : A₂ ≤ φ.range) (h₃ : A₃ ≤ φ.range)
    (c₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) (c₁₃ : ∀ x ∈ A₁, ∀ y ∈ A₃, x * y = y * x)
    (c₂₃ : ∀ x ∈ A₂, ∀ y ∈ A₃, x * y = y * x)
    (n₁ : Nat.card A₁ = Nat.card SL(2, GaloisField p f))
    (n₂ : Nat.card A₂ = Nat.card SL(2, GaloisField p f))
    (n₃ : Nat.card A₃ = Nat.card SL(2, GaloisField p f))
    (z₁ : Nat.card (Subgroup.center A₁) ∣ 2) (z₂ : Nat.card (Subgroup.center A₂) ∣ 2) :
    False := by
  have he : 1 ≤ e := hadm.2.1
  have hf : 1 ≤ f := by
    rcases hef with rfl | ⟨-, rfl⟩ <;> omega
  have hodd : Odd (p ^ e) := odd_pow_of_ne_two p hp2 e
  have hq3 : 3 ≤ p ^ e := by
    have h2 : 2 ≤ p ^ e := by
      have := (Fact.out : p.Prime).two_le
      calc 2 ≤ p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
    rcases hodd with ⟨m, hm⟩
    omega
  set s := padicValNat 2 ((p ^ e) ^ 2 - 1) with hs
  have hs3 : 3 ≤ s := by
    have h8 : 2 ^ 3 ∣ (p ^ e) ^ 2 - 1 := by
      have := eight_dvd_sq_sub_one hodd
      rwa [show (2 : ℕ) ^ 3 = 8 by norm_num]
    have hne : (p ^ e) ^ 2 - 1 ≠ 0 := by
      have : 1 < (p ^ e) ^ 2 := by nlinarith
      omega
    exact (padicValNat_dvd_iff_le (p := 2) hne).mp h8
  have hM := padicValNat_card_modelUniv p e hp2 ht n he
  have hM0 : Nat.card (modelUniv t n p e Fact.out).K ≠ 0 := by
    intro h0
    rw [h0, padicValNat_zero_right] at hM
    omega
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hN : Nat.card SL(2, GaloisField p f) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [card_sl2_field, hcardF]
  have hx2 : 2 ≤ (p ^ e) ^ 2 := by nlinarith
  have hNs : s ≤ padicValNat 2 (Nat.card SL(2, GaloisField p f)) := by
    have hdvd : 2 ^ s ∣ (p ^ f) ^ 2 - 1 := by
      rcases hef with rfl | ⟨-, rfl⟩
      · exact pow_padicValNat_dvd
      · have h6 : (p ^ (3 * e)) ^ 2 = ((p ^ e) ^ 2) ^ 3 := by ring
        rw [h6]
        exact two_pow_padicValNat_dvd_pow_sub_one ((p ^ e) ^ 2) 3
    have hNne : Nat.card SL(2, GaloisField p f) ≠ 0 := Nat.card_pos.ne'
    refine (padicValNat_dvd_iff_le (p := 2) hNne).mp ?_
    rw [hN]
    exact hdvd.trans (Dvd.intro_left _ rfl)
  have hdvd := card_mul_dvd_of_commute_triple h₁ h₂ h₃ c₁₂ c₁₃ c₂₃ z₁ z₂
  rw [n₁, n₂, n₃] at hdvd
  have hQ : Nat.card φ.range ∣ Nat.card (modelUniv t n p e Fact.out).K := Subgroup.card_range_dvd φ
  have hdvd' : Nat.card SL(2, GaloisField p f) * Nat.card SL(2, GaloisField p f) *
      Nat.card SL(2, GaloisField p f) ∣ 4 * Nat.card (modelUniv t n p e Fact.out).K :=
    hdvd.trans (Nat.mul_dvd_mul_left 4 hQ)
  exact false_of_dvd_of_padicValNat hs3 hNs (by omega) hM0 hdvd'

end Count

end CFSG.ClassicalInvolution.RouteD.G2D4
