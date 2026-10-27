module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneCyc
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneRoot

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix
  CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section Conj

variable {G : Type*} [Group G]

@[expose] def cj (c : G) (E : Subgroup G) : Subgroup G := E.map (MulAut.conj c).toMonoidHom

theorem mem_cj {c x : G} {E : Subgroup G} : x ∈ cj c E ↔ c⁻¹ * x * c ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨c⁻¹ * x * c, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_cj (c d : G) (E : Subgroup G) : cj c (cj d E) = cj (c * d) E := by
  ext x
  simp only [mem_cj, _root_.mul_inv_rev, mul_assoc]

theorem cj_one (E : Subgroup G) : cj 1 E = E := by
  ext x
  simp [mem_cj]

theorem cj_inv_cj (c : G) (E : Subgroup G) : cj c⁻¹ (cj c E) = E := by
  rw [cj_cj, inv_mul_cancel, cj_one]

theorem card_cj (c : G) (E : Subgroup G) : Nat.card (cj c E) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem isElemAbelian_cj {p : ℕ} {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) (c : G) :
    CFSG.Open.IsElemAbelian p (cj c E) := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · have ha := (mem_cj.1 a.2)
    have hb := (mem_cj.1 b.2)
    have h := hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩
    have h' := congrArg (fun y : E => c * (y : G) * c⁻¹) h
    apply Subtype.ext
    simpa [mul_assoc] using h'
  · have h := hE.2 _ (mem_cj.1 hx)
    have h2 := conj_pow (a := c⁻¹) (b := x) (i := p)
    simp only [inv_inv] at h2
    rw [h2] at h
    calc x ^ p = c * (c⁻¹ * x ^ p * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group

end Conj

section WImg

variable (K : Type) [Field K] [Finite K]

@[expose] def wImg (E : Subgroup (adjointGroup Tag.E8 K)) : Subgroup (WeylGroup Tag.E8) :=
  (E.subgroupOf (monomialN K)).map (rhoN K)

variable {K}

theorem mem_wImg {E : Subgroup (adjointGroup Tag.E8 K)} {w : WeylGroup Tag.E8} :
    w ∈ wImg K E ↔ ∃ (x : adjointGroup Tag.E8 K) (hx : x ∈ E) (hxN : x ∈ monomialN K),
      rhoN K ⟨x, hxN⟩ = w := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, y.2, rfl⟩
  · rintro ⟨x, hx, hxN, rfl⟩
    exact ⟨⟨x, hxN⟩, hx, rfl⟩

theorem rhoE_range {E : Subgroup (adjointGroup Tag.E8 K)} (hEN : E ≤ monomialN K) :
    (rhoE hEN).range = wImg K E := by
  ext w
  rw [mem_wImg]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, hEN x.2, rfl⟩
  · rintro ⟨x, hx, hxN, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cj_le_monomialN (n : monomialN K) {E : Subgroup (adjointGroup Tag.E8 K)}
    (hEN : E ≤ monomialN K) : cj (n : adjointGroup Tag.E8 K) E ≤ monomialN K := by
  rintro _ ⟨e, he, rfl⟩
  exact mul_mem (mul_mem n.2 (hEN he)) (inv_mem n.2)

theorem wImg_cj (n : monomialN K) {E : Subgroup (adjointGroup Tag.E8 K)}
    (hEN : E ≤ monomialN K) :
    wImg K (cj (n : adjointGroup Tag.E8 K) E) = cj (rhoN K n) (wImg K E) := by
  ext w
  rw [mem_cj, mem_wImg, mem_wImg]
  constructor
  · rintro ⟨x, hx, hxN, rfl⟩
    have hx' := mem_cj.1 hx
    refine ⟨(n : adjointGroup Tag.E8 K)⁻¹ * x * n, hx', mul_mem (mul_mem (inv_mem n.2) hxN) n.2, ?_⟩
    have : (⟨(n : adjointGroup Tag.E8 K)⁻¹ * x * n, mul_mem (mul_mem (inv_mem n.2) hxN) n.2⟩ :
        monomialN K) = n⁻¹ * ⟨x, hxN⟩ * n := rfl
    rw [this, map_mul, map_mul, map_inv]
  · rintro ⟨x, hx, hxN, hxw⟩
    refine ⟨(n : adjointGroup Tag.E8 K) * x * (n : adjointGroup Tag.E8 K)⁻¹,
      mem_cj.2 (by simpa [mul_assoc] using hx), mul_mem (mul_mem n.2 hxN) (inv_mem n.2), ?_⟩
    have : (⟨(n : adjointGroup Tag.E8 K) * x * (n : adjointGroup Tag.E8 K)⁻¹,
        mul_mem (mul_mem n.2 hxN) (inv_mem n.2)⟩ : monomialN K) = n * ⟨x, hxN⟩ * n⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hxw]
    group

end WImg

section CyclicCases

theorem exists_exp_of_mem_sylowW {r : WeylGroup Tag.E8} (hr : r ∈ sylowW) :
    ∃ i j : Fin 5, e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = r := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨i, j⟩, h⟩ :=
    (mem_closure_pair_iff (p := 5) e8Five_comm e8FiveG1_pow e8FiveG2_pow r).1 hr
  exact ⟨i, j, h⟩

theorem exp_pow_five (i j : ℕ) : (e8FiveG1 ^ i * e8FiveG2 ^ j) ^ 5 = 1 := by
  have hc0 : Commute e8FiveG1 e8FiveG2 := e8Five_comm
  rw [(hc0.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 5, mul_comm j 5, pow_mul,
    pow_mul, e8FiveG1_pow, e8FiveG2_pow]
  simp

variable {K : Type} [Field K] [Finite K] {ζ : K}

theorem cyclic_cases (hζ : IsPrimitiveRoot ζ 5) {E : Subgroup (adjointGroup Tag.E8 K)}
    (hE : CFSG.Open.IsElemAbelian 5 E) (hcard : Nat.card E = 5 ^ 3) (hEN : E ≤ monomialN K)
    (hS : wImg K E ≤ sylowW) (h5 : Nat.card (wImg K E) ≤ 5) :
    NormalizesRGroup (ringChar K) E ∨
      ∃ (a : Fin Tag.E8.rank → Kˣ) (g : adjointGroup Tag.E8 K),
        E = cj g (griessCubeT hζ a) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : Nat.card (wImg K E) ∣ 25 := by
    rw [← card_sylowW]
    exact Subgroup.card_dvd_of_le hS
  have hpos : 0 < Nat.card (wImg K E) := Nat.card_pos
  have hcase : Nat.card (wImg K E) = 1 ∨ Nat.card (wImg K E) = 5 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card (wImg K E) <;> simp_all
  have hfix : ∀ (β : Fin Tag.E8.rank → ℤ), IsRoot Tag.E8 β → wImg K E ≤
      MulAction.stabilizer (WeylGroup Tag.E8) β → NormalizesRGroup (ringChar K) E :=
    fun β hβ hst => normalizesRGroup_of_fixed_root (fun x hx => hEN hx) hβ fun x hx => by
      have : rhoN K ⟨x, hEN hx⟩ ∈ wImg K E := mem_wImg.2 ⟨x, hx, hEN hx, rfl⟩
      exact MulAction.mem_stabilizer_iff.1 (hst this)
  rcases hcase with h1 | h5'
  · left
    have hbot : wImg K E = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact hfix (Pi.single 7 1) (isRoot_single Tag.E8 7) (by rw [hbot]; exact bot_le)
  · obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ wImg K E, r ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : wImg K E = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
      rw [this, Subgroup.card_bot] at h5'
      omega
    obtain ⟨i, j, hij⟩ := exists_exp_of_mem_sylowW (hS hrR)
    have hr5 : r ^ 5 = 1 := by rw [← hij]; exact exp_pow_five i j
    have hord : orderOf r = 5 := orderOf_eq_prime hr5 hr1
    have hRz : Subgroup.zpowers r = wImg K E := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hrR) ?_
      rw [Nat.card_zpowers, hord, h5']
    by_cases hj0 : (j : ℕ) = 0
    · left
      have hi0 : (i : ℕ) ≠ 0 := by
        intro hi
        apply hr1
        rw [← hij, hi, hj0]
        simp
      apply hfix (Pi.single 7 1) (isRoot_single Tag.E8 7)
      rw [← hRz, Subgroup.zpowers_le, ← hij, hj0, pow_zero, mul_one]
      apply pow_mem
      rw [MulAction.mem_stabilizer_iff]
      simpa using g1_pow_smul_single7 1
    by_cases hi0 : (i : ℕ) = 0
    · left
      apply hfix (Pi.single 0 1) (isRoot_single Tag.E8 0)
      rw [← hRz, Subgroup.zpowers_le, ← hij, hi0, pow_zero, one_mul]
      apply pow_mem
      rw [MulAction.mem_stabilizer_iff]
      simpa using g2_pow_smul_single0 1
    right
    have hi5 : ¬ 5 ∣ (i : ℕ) := fun h => hi0 (Nat.eq_zero_of_dvd_of_lt h i.isLt)
    have hj5 : ¬ 5 ∣ (j : ℕ) := fun h => hj0 (Nat.eq_zero_of_dvd_of_lt h j.isLt)
    obtain ⟨a, ha, hconj⟩ := exists_conj_griessW_pow hi5 hj5
    obtain ⟨n, hn⟩ := rhoN_surjective K (xElt a)
    have hE'N : cj (n : adjointGroup Tag.E8 K) E ≤ monomialN K := cj_le_monomialN n hEN
    have hwE' : wImg K (cj (n : adjointGroup Tag.E8 K) E) = Subgroup.zpowers griessW := by
      rw [wImg_cj n hEN, hn, ← hRz]
      have hmap : cj (xElt a) (Subgroup.zpowers r) = Subgroup.zpowers (griessW ^ (j : ℕ)) := by
        rw [cj, MonoidHom.map_zpowers]
        show Subgroup.zpowers (xElt a * r * (xElt a)⁻¹) = _
        rw [← hij, hconj]
      rw [hmap]
      have hw5 : (griessW ^ (j : ℕ)) ^ 5 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, griessW_pow_five, one_pow]
      have hw1 : griessW ^ (j : ℕ) ≠ 1 := by
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [orderOf_griessW] at this
        exact hj5 this
      have hordw : orderOf (griessW ^ (j : ℕ)) = 5 := orderOf_eq_prime hw5 hw1
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact pow_mem (Subgroup.mem_zpowers _) _
      · rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_griessW, hordw]
    obtain ⟨a', ha'⟩ := cyclic_core hζ (isElemAbelian_cj hE _) (by rw [card_cj]; exact hcard) hE'N
      (by rw [rhoE_range, hwE'])
    refine ⟨a', (n : adjointGroup Tag.E8 K)⁻¹, ?_⟩
    rw [← ha', cj_inv_cj]

end CyclicCases

section HeisStatement

@[expose] def HeisReduction : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K - 1 → ∀ {ζ : K}, IsPrimitiveRoot ζ 5 →
    ∀ E : Subgroup (adjointGroup Tag.E8 K), CFSG.Open.IsElemAbelian 5 E → Nat.card E = 5 ^ 3 →
      E ≤ monomialN K → wImg K E = sylowW →
      ∃ c : adjointGroup Tag.E8 K, cj c E ≤ monomialN K ∧ wImg K (cj c E) ≤ sylowW ∧
        Nat.card (wImg K (cj c E)) ≤ 5

end HeisStatement

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
