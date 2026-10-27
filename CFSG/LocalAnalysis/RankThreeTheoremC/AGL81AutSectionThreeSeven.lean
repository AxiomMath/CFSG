module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHMinimal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutFive
import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHPower
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement

section OrbitCount

variable {K : Type*} [Group K] [Finite K] {B Q : Subgroup K}

theorem dvd_card_sdiff_centralizer_of_primeGroup {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hQ : IsPGroup 2 Q) (hB : IsPGroup r B) (hBQ : B ≤ normalizer (Q : Set K)) :
    r ∣ ((Q : Set K) \ ((Q ⊓ centralizer (B : Set K) : Subgroup K) : Set K)).ncard := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Subgroup K := Q ⊓ centralizer (B : Set K)
  change r ∣ ((Q : Set K) \ (F : Set K)).ncard
  have hFQ : F ≤ Q := inf_le_left
  have hFC : F ≤ centralizer (B : Set K) := inf_le_right
  obtain ⟨X, hX⟩ : ∃ X : Set K, X = (Q : Set K) \ (F : Set K) := ⟨_, rfl⟩
  have hXstable : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    rw [hX, Set.mem_sdiff] at hx ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mp hx.1, fun hcon => hx.2 ?_⟩
    refine Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hcomm : b * (b * x * b⁻¹) = (b * x * b⁻¹) * b :=
      (Subgroup.mem_centralizer_iff.mp hcon.2) b hb
    have hxeq : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
        _ = b * x * b⁻¹ := by group
    rw [hxeq]
    exact (Subgroup.mem_centralizer_iff.mp hcon.2) c hc
  let _ : MulAction B X :=
    { smul := fun b x => ⟨(b : K) * (x : K) * (b : K)⁻¹, hXstable (b : K) b.2 (x : K) x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : B) : K) * (x : K) * ((1 : B) : K)⁻¹ = (x : K)
        simp)
      mul_smul := fun b b' x => Subtype.ext (by
        show ((b * b' : B) : K) * (x : K) * ((b * b' : B) : K)⁻¹ =
          (b : K) * ((b' : K) * (x : K) * (b' : K)⁻¹) * (b : K)⁻¹
        simp [mul_assoc]) }
  have hfix_empty : MulAction.fixedPoints B X = (∅ : Set X) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, hx⟩ hfix
    rw [MulAction.mem_fixedPoints] at hfix
    rw [hX, Set.mem_sdiff] at hx
    refine hx.2 ?_
    refine Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hval : c * x * c⁻¹ = x := congrArg Subtype.val (hfix ⟨c, hc⟩)
    exact mul_inv_eq_iff_eq_mul.mp hval
  have hdvdX : r ∣ Nat.card X := by
    have hcong := hB.card_modEq_card_fixedPoints X
    rw [hfix_empty] at hcong
    simp only [Nat.card_of_isEmpty] at hcong
    exact Nat.modEq_zero_iff_dvd.mp hcong
  rwa [← hX]

theorem dvd_relIndex_centralizer_sub_one_of_pGroup {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hQ : IsPGroup 2 Q) (hB : IsPGroup r B) (hBQ : B ≤ normalizer (Q : Set K))
    (hne : ¬ Q ≤ centralizer (B : Set K)) :
    r ∣ (centralizer (B : Set K)).relIndex Q - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Subgroup K := Q ⊓ centralizer (B : Set K)
  have hFQ : F ≤ Q := inf_le_left
  have hrelF : F.relIndex Q = (centralizer (B : Set K)).relIndex Q := by
    rw [show F = Q ⊓ centralizer (B : Set K) from rfl, inf_comm]
    exact Subgroup.inf_relIndex_right (centralizer (B : Set K)) Q
  rw [← hrelF]
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hdvd : F.relIndex Q ∣ 2 ^ m := by
    rw [← hm]
    exact F.relIndex_dvd_card Q
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hn1 : F.relIndex Q ≠ 1 := by
    intro h
    exact hne ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)
  have hFn : Nat.card F = (F : Set K).ncard := (Nat.card_coe_set_eq (F : Set K)).symm
  have hQn : Nat.card Q = (Q : Set K).ncard := (Nat.card_coe_set_eq (Q : Set K)).symm
  have hcardQ' : F.relIndex Q * Nat.card F = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := Q)
    rwa [inf_eq_left.mpr hFQ] at h
  have hcardQ : F.relIndex Q * (F : Set K).ncard = (Q : Set K).ncard := by
    simpa only [hFn, hQn] using hcardQ'
  obtain ⟨X, hX⟩ : ∃ X : Set K, X = (Q : Set K) \ (F : Set K) := ⟨_, rfl⟩
  have hcardX : X.ncard = (F : Set K).ncard * (F.relIndex Q - 1) := by
    have hFsub : (F : Set K) ⊆ (Q : Set K) := fun x hx => hFQ hx
    have h1 : X.ncard = (Q : Set K).ncard - (F : Set K).ncard := by
      rw [hX]
      exact Set.ncard_sdiff hFsub
    rw [h1, ← hcardQ, Nat.mul_comm (F.relIndex Q) ((F : Set K).ncard),
      Nat.mul_sub_left_distrib, Nat.mul_one]
  have hdvdX : r ∣ X.ncard := by
    rw [hX]
    exact dvd_card_sdiff_centralizer_of_primeGroup hr2 hQ hB hBQ
  have hQpow : (Q : Set K).ncard = 2 ^ m := hQn.symm.trans hm
  have hcop : Nat.Coprime r ((F : Set K).ncard) := by
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)]
    intro hdivF
    have hFdvd : (F : Set K).ncard ∣ 2 ^ m := by
      rw [← hQpow, ← hcardQ]
      exact dvd_mul_left ((F : Set K).ncard) (F.relIndex Q)
    have hr2' : r ∣ 2 := Nat.Prime.dvd_of_dvd_pow (Fact.out : r.Prime) (hdivF.trans hFdvd)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp hr2')
  rw [hcardX] at hdvdX
  rw [hs] at hdvdX ⊢
  exact hcop.dvd_of_dvd_mul_left hdvdX

end OrbitCount

section Parity

variable {K : Type*} [Group K] [Finite K]

theorem eq_of_neg_one_pow_eq_of_lt_two {F : Type*} [Field F] (hF : ringChar F ≠ 2)
    {a b : ℕ} (ha : a < 2) (hb : b < 2) (h : (-1 : F) ^ a = (-1 : F) ^ b) : a = b := by
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hF
  interval_cases a <;> interval_cases b <;> simp only [pow_zero, pow_one] at h
  all_goals first
    | rfl
    | exact absurd h hneg
    | exact absurd h.symm hneg

theorem exists_neg_character_witness {N : Subgroup K} (hN8 : N.index = 8)
    {F : Type*} [Field F] (lam : K → K → F)
    (hval : ∀ g x, lam g x = 1 ∨ lam g x = -1)
    (hsymm : ∀ g x, lam g x = lam x g)
    (hnondeg : ∀ x, (∀ g, lam g x = 1) ↔ x ∈ N) :
    ∃ x y : K, x ∉ N ∧ lam x y = -1 := by
  classical
  have htop : N ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hN8
    omega
  obtain ⟨x, hxN⟩ : ∃ x : K, x ∉ N := by
    by_contra hall
    push Not at hall
    exact htop (by ext z; exact ⟨fun _ => Subgroup.mem_top z, fun _ => hall z⟩)
  have hxall : ¬ ∀ g, lam g x = 1 := fun h => hxN ((hnondeg x).mp h)
  push Not at hxall
  obtain ⟨y, hyx⟩ := hxall
  have hxy : lam x y = -1 := by
    rw [hsymm x y]
    rcases hval y x with h | h
    · exact absurd h hyx
    · exact h
  exact ⟨x, y, hxN, hxy⟩

theorem character_kernel_index_two {F : Type*} [Field F] (lam : K → K → F)
    (hval : ∀ g x, lam g x = 1 ∨ lam g x = -1)
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (h1 : ∀ g, lam g 1 = 1) (hinv : ∀ g z, lam g z⁻¹ = (lam g z)⁻¹)
    {a y : K} (hy : lam a y ≠ 1) :
    ∃ H : Subgroup K, (∀ z, z ∈ H ↔ lam a z = 1) ∧ H.index = 2 := by
  classical
  let H : Subgroup K :=
    { carrier := {z | lam a z = 1}
      mul_mem' := by
        intro b c hb hc
        change lam a (b * c) = 1
        rw [hmul_right, hb, hc, mul_one]
      one_mem' := h1 a
      inv_mem' := by
        intro b hb
        change lam a b⁻¹ = 1
        rw [hinv, hb, inv_one] }
  refine ⟨H, fun z => Iff.rfl, ?_⟩
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨y, ?_, fun b => ?_⟩
  · rw [show y ∈ H ↔ lam a y = 1 from Iff.rfl]
    exact hy
  · rcases hval a b with hb | hb
    · right; exact hb
    · left
      change lam a (b * y) = 1
      rw [hmul_right, hb]
      have hay : lam a y = -1 := by
        rcases hval a y with h | h
        · exact absurd h hy
        · exact h
      rw [hay]
      norm_num

theorem exists_z_of_character_kernels {N Hx Hy : Subgroup K} (hN8 : N.index = 8)
    {F : Type*} [Field F] {lam : K → K → F} {x y : K}
    (hHx : ∀ z, z ∈ Hx ↔ lam x z = 1) (hHy : ∀ z, z ∈ Hy ↔ lam y z = 1)
    (hHx2 : Hx.index = 2) (hHy2 : Hy.index = 2)
    (hnondeg : ∀ x, (∀ g, lam g x = 1) ↔ x ∈ N) :
    ∃ z : K, z ∉ N ∧ lam x z = 1 ∧ lam y z = 1 := by
  have hNZ : N ≤ Hx ⊓ Hy := by
    intro n hn
    have h1n : ∀ g, lam g n = 1 := fun g => (hnondeg n).mpr hn g
    exact Subgroup.mem_inf.mpr ⟨(hHx n).mpr (h1n x), (hHy n).mpr (h1n y)⟩
  have hZle : (Hx ⊓ Hy).index ≤ 4 := by
    calc (Hx ⊓ Hy).index ≤ Hx.index * Hy.index := Subgroup.index_inf_le
      _ = 4 := by rw [hHx2, hHy2]
  have hZne : Hx ⊓ Hy ≠ N := by
    intro h
    have h1 : (Hx ⊓ Hy).index = 8 := by rw [h, hN8]
    omega
  obtain ⟨z, hzZ, hzN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hNZ (Ne.symm hZne))
  exact ⟨z, hzN, (hHx z).mp hzZ.1, (hHy z).mp hzZ.2⟩

theorem exists_orthogonal_triple {N : Subgroup K} (hN : N.Normal) (hN8 : N.index = 8)
    {F : Type*} [Field F] (hF : ringChar F ≠ 2)
    (lam : K → K → F) (hval : ∀ g x, lam g x = 1 ∨ lam g x = -1)
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (hself : ∀ x, lam x x = 1) (hsymm : ∀ g x, lam g x = lam x g)
    (hnondeg : ∀ x, (∀ g, lam g x = 1) ↔ x ∈ N) :
    ∃ x y z : K, x ∉ N ∧ z ∉ N ∧ lam x y = -1 ∧ lam x z = 1 ∧ lam y z = 1 := by
  classical
  haveI : N.Normal := hN
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hF
  obtain ⟨x, y, hxN, hxy⟩ := exists_neg_character_witness hN8 lam hval hsymm hnondeg
  have h1 : ∀ g, lam g 1 = 1 := by
    intro g
    have h : lam g 1 = lam g 1 * lam g 1 := by simpa using hmul_right g 1 1
    rcases hval g 1 with h2 | h2
    · exact h2
    · rw [h2] at h
      have h' : (-1 : F) = 1 := by simpa using h
      exact absurd h' hneg
  have hinv : ∀ g z, lam g z⁻¹ = (lam g z)⁻¹ := by
    intro g z
    have h := hmul_right g z z⁻¹
    rw [mul_inv_cancel, h1 g] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hxy' : lam x y ≠ 1 := by rw [hxy]; exact hneg
  obtain ⟨Hx, hHx, hHx2⟩ := character_kernel_index_two lam hval hmul_right h1 hinv hxy'
  have hyx : lam y x = -1 := by rw [← hsymm x y]; exact hxy
  have hyx' : lam y x ≠ 1 := by rw [hyx]; exact hneg
  obtain ⟨Hy, hHy, hHy2⟩ := character_kernel_index_two lam hval hmul_right h1 hinv hyx'
  obtain ⟨z, hzN, hxz, hyz⟩ :=
    exists_z_of_character_kernels hN8 hHx hHy hHx2 hHy2 hnondeg
  exact ⟨x, y, z, hxN, hzN, hxy, hxz, hyz⟩

private def threeCosetProduct (x y z : K) (p : Fin 2 × Fin 2 × Fin 2) : K :=
  x ^ (p.1 : ℕ) * y ^ (p.2.1 : ℕ) * z ^ (p.2.2 : ℕ)

private theorem seven_lam_pow {F : Type*} [Field F] {lam : K → K → F}
    (h1 : ∀ g, lam g 1 = 1)
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x') :
    ∀ (n : ℕ) g w, lam g (w ^ n) = (lam g w) ^ n := by
  intro n g w
  induction n with
  | zero => simpa using h1 g
  | succ n ih => rw [pow_succ, hmul_right, ih, pow_succ]

private theorem seven_P_eval_x {F : Type*} [Field F] {lam : K → K → F} {x y z : K}
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (hxy : lam x y = -1) (hxz : lam x z = 1) (hself : ∀ x, lam x x = 1)
    (hpow : ∀ (n : ℕ) g w, lam g (w ^ n) = (lam g w) ^ n) :
    ∀ p : Fin 2 × Fin 2 × Fin 2,
      lam x (threeCosetProduct (K := K) x y z p) = (-1 : F) ^ (p.2.1 : ℕ) := by
  intro p
  change lam x (x ^ (p.1 : ℕ) * y ^ (p.2.1 : ℕ) * z ^ (p.2.2 : ℕ)) =
    (-1 : F) ^ (p.2.1 : ℕ)
  rw [hmul_right, hmul_right]
  simp only [hpow, hself x, hxy, hxz, one_pow, one_mul, mul_one]

private theorem seven_P_eval_y {F : Type*} [Field F] {lam : K → K → F} {x y z : K}
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (hyx : lam y x = -1) (hyz : lam y z = 1) (hself : ∀ x, lam x x = 1)
    (hpow : ∀ (n : ℕ) g w, lam g (w ^ n) = (lam g w) ^ n) :
    ∀ p : Fin 2 × Fin 2 × Fin 2,
      lam y (threeCosetProduct (K := K) x y z p) = (-1 : F) ^ (p.1 : ℕ) := by
  intro p
  change lam y (x ^ (p.1 : ℕ) * y ^ (p.2.1 : ℕ) * z ^ (p.2.2 : ℕ)) =
    (-1 : F) ^ (p.1 : ℕ)
  rw [hmul_right, hmul_right]
  simp only [hpow, hself y, hyx, hyz, one_pow, one_mul, mul_one]

private theorem seven_lam_congr {N : Subgroup K} [N.Normal] {F : Type*} [Field F]
    {lam : K → K → F}
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (hnondeg : ∀ x, (∀ g, lam g x = 1) ↔ x ∈ N) :
    ∀ {u v : K}, (u : K ⧸ N) = (v : K ⧸ N) → ∀ w, lam w u = lam w v := by
  intro u v huv w
  have hmem : u⁻¹ * v ∈ N := QuotientGroup.eq.mp huv
  calc lam w u = lam w u * 1 := (mul_one _).symm
    _ = lam w u * lam w (u⁻¹ * v) := by rw [(hnondeg (u⁻¹ * v)).mpr hmem w]
    _ = lam w (u * (u⁻¹ * v)) := (hmul_right w u _).symm
    _ = lam w v := by rw [show u * (u⁻¹ * v) = v by group]

private theorem seven_P_injective {F : Type*} [Field F] {N : Subgroup K} [N.Normal]
    (hF : ringChar F ≠ 2) {lam : K → K → F} {x y z : K} (hzN : z ∉ N)
    (hPx : ∀ p : Fin 2 × Fin 2 × Fin 2,
      lam x (threeCosetProduct (K := K) x y z p) = (-1 : F) ^ (p.2.1 : ℕ))
    (hPy : ∀ p : Fin 2 × Fin 2 × Fin 2,
      lam y (threeCosetProduct (K := K) x y z p) = (-1 : F) ^ (p.1 : ℕ))
    (hlam_congr : ∀ {u v : K}, (u : K ⧸ N) = (v : K ⧸ N) → ∀ w, lam w u = lam w v) :
    Function.Injective fun p : Fin 2 × Fin 2 × Fin 2 =>
      (threeCosetProduct (K := K) x y z p : K ⧸ N) := by
  intro p p' hpp
  have hxl : (-1 : F) ^ (p.2.1 : ℕ) = (-1 : F) ^ (p'.2.1 : ℕ) := by
    rw [← hPx p, ← hPx p']; exact hlam_congr hpp x
  have hyl : (-1 : F) ^ (p.1 : ℕ) = (-1 : F) ^ (p'.1 : ℕ) := by
    rw [← hPy p, ← hPy p']; exact hlam_congr hpp y
  have hb : p.2.1 = p'.2.1 :=
    Fin.ext (eq_of_neg_one_pow_eq_of_lt_two hF p.2.1.isLt p'.2.1.isLt hxl)
  have ha : p.1 = p'.1 :=
    Fin.ext (eq_of_neg_one_pow_eq_of_lt_two hF p.1.isLt p'.1.isLt hyl)
  have h1 : (threeCosetProduct (K := K) x y z p : K ⧸ N) =
      (threeCosetProduct (K := K) x y z p' : K ⧸ N) := hpp
  rw [show threeCosetProduct x y z p =
      x ^ (p'.1 : ℕ) * y ^ (p'.2.1 : ℕ) * z ^ (p.2.2 : ℕ) by
    simp only [threeCosetProduct, ha, hb],
    show threeCosetProduct x y z p' =
      x ^ (p'.1 : ℕ) * y ^ (p'.2.1 : ℕ) * z ^ (p'.2.2 : ℕ) by
    simp only [threeCosetProduct, hb]] at h1
  have h2 : (z ^ (p.2.2 : ℕ) : K ⧸ N) = (z ^ (p'.2.2 : ℕ) : K ⧸ N) := by
    apply QuotientGroup.eq.mpr
    have hmem : (x ^ (p'.1 : ℕ) * y ^ (p'.2.1 : ℕ) * z ^ (p.2.2 : ℕ))⁻¹ *
        (x ^ (p'.1 : ℕ) * y ^ (p'.2.1 : ℕ) * z ^ (p'.2.2 : ℕ)) ∈ N :=
      QuotientGroup.eq.mp h1
    rwa [show (x ^ (p'.1 : ℕ) * y ^ (p'.2.1 : ℕ) * z ^ (p.2.2 : ℕ))⁻¹ *
        (x ^ (p'.1 : ℕ) * y ^ (p'.2.1 : ℕ) * z ^ (p'.2.2 : ℕ)) =
        (z ^ (p.2.2 : ℕ))⁻¹ * z ^ (p'.2.2 : ℕ) by group] at hmem
  have hc : p.2.2 = p'.2.2 := by
    let i : Fin 2 := p.2.2
    let j : Fin 2 := p'.2.2
    have h2' : (z ^ (i : ℕ) : K ⧸ N) = (z ^ (j : ℕ) : K ⧸ N) := by
      simpa [i, j] using h2
    have hval : (i : ℕ) = (j : ℕ) := by
      by_cases hi0 : i = 0
      · have hj0 : j = 0 := by
          by_contra hj0
          have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj0
          exact absurd (QuotientGroup.eq_one_iff z |>.mp
            (by simpa [hi0, hj1] using h2'.symm)) hzN
        rw [hi0, hj0]
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi0
        have hj1 : j = 1 := by
          by_contra hj1
          have hj0 : j = 0 := by
            by_contra hj0
            exact hj1 (Fin.eq_one_of_ne_zero j hj0)
          exact absurd (QuotientGroup.eq_one_iff z |>.mp
            (by simpa [hi1, hj0] using h2')) hzN
        rw [hi1, hj1]
    exact Fin.ext hval
  exact Prod.ext ha (Prod.ext hb hc)

theorem false_of_orthogonal_triple {N : Subgroup K} (hN : N.Normal) (hN8 : N.index = 8)
    {F : Type*} [Field F] (hF : ringChar F ≠ 2)
    (lam : K → K → F) (hval : ∀ g x, lam g x = 1 ∨ lam g x = -1)
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (hself : ∀ x, lam x x = 1) (hsymm : ∀ g x, lam g x = lam x g)
    (hnondeg : ∀ x, (∀ g, lam g x = 1) ↔ x ∈ N)
    {x y z : K} (hxN : x ∉ N) (hzN : z ∉ N)
    (hxy : lam x y = -1) (hxz : lam x z = 1) (hyz : lam y z = 1) : False := by
  classical
  haveI : N.Normal := hN
  have h1 : ∀ g, lam g 1 = 1 := by
    intro g
    have h : lam g 1 = lam g 1 * lam g 1 := by simpa using hmul_right g 1 1
    rcases hval g 1 with h2 | h2
    · exact h2
    · rw [h2] at h
      have h' : (-1 : F) = 1 := by simpa using h
      exact absurd h' (Ring.neg_one_ne_one_of_char_ne_two hF)
  have hpow := seven_lam_pow h1 hmul_right
  have hzx : lam z x = 1 := by rw [hsymm z x]; exact hxz
  have hzy : lam z y = 1 := by rw [hsymm z y]; exact hyz
  have hyx : lam y x = -1 := by rw [← hsymm x y]; exact hxy
  have hPx := seven_P_eval_x hmul_right hxy hxz hself hpow
  have hPy := seven_P_eval_y hmul_right hyx hyz hself hpow
  have hP_inj := seven_P_injective hF hzN hPx hPy (seven_lam_congr hmul_right hnondeg)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hcardQ : Fintype.card (K ⧸ N) = 8 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hN8]
  have hbij : Function.Bijective fun p : Fin 2 × Fin 2 × Fin 2 =>
      (threeCosetProduct (K := K) x y z p : K ⧸ N) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hP_inj, by simp [hcardQ]⟩
  have halleq : ∀ g, lam z g = 1 := by
    intro g
    obtain ⟨p, hp⟩ := hbij.2 (g : K ⧸ N)
    have hmem : (threeCosetProduct (K := K) x y z p)⁻¹ * g ∈ N := QuotientGroup.eq.mp hp
    have hg : g = threeCosetProduct (K := K) x y z p *
        ((threeCosetProduct (K := K) x y z p)⁻¹ * g) := by group
    rw [hg, hmul_right, (hnondeg _).mpr hmem z, mul_one]
    simp only [threeCosetProduct, hmul_right, hpow, hzx, hzy, hself z, one_pow, one_mul,
      mul_one]
  have halleq' : ∀ g, lam g z = 1 := fun g => by rw [hsymm g z]; exact halleq g
  exact hzN ((hnondeg z).mp halleq')

theorem false_of_index_eight_alternating_character {N : Subgroup K} (hN : N.Normal)
    (hN8 : N.index = 8) {F : Type*} [Field F] (hF : ringChar F ≠ 2)
    (lam : K → K → F) (hval : ∀ g x, lam g x = 1 ∨ lam g x = -1)
    (hmul_right : ∀ g x x', lam g (x * x') = lam g x * lam g x')
    (hself : ∀ x, lam x x = 1) (hsymm : ∀ g x, lam g x = lam x g)
    (hnondeg : ∀ x, (∀ g, lam g x = 1) ↔ x ∈ N) : False := by
  obtain ⟨x, y, z, hxN, hzN, hxy, hxz, hyz⟩ :=
    exists_orthogonal_triple hN hN8 hF lam hval hmul_right hself hsymm hnondeg
  exact false_of_orthogonal_triple hN hN8 hF lam hval hmul_right hself hsymm hnondeg
    hxN hzN hxy hxz hyz

end Parity

section Linear

open CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

private theorem seven_commutator_facts {Q B : Subgroup (Module.End F W)ˣ}
    (h3 : ⁅Q, Q⁆ ≤ centralizer (Q : Set (Module.End F W)ˣ))
    (h4 : ∀ x ∈ Q, x ^ 2 ∈ centralizer (B : Set (Module.End F W)ˣ))
    (h5 : Q ⊓ centralizer (B : Set (Module.End F W)ˣ) ≤
      centralizer (Q : Set (Module.End F W)ˣ)) :
    (∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆) ∧
      (∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1) := by
  have hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆ :=
    fun g hg x hx h hh =>
      ((Subgroup.mem_centralizer_iff.mp (h3 (Subgroup.commutator_mem_commutator hg hx))) h hh).symm
  refine ⟨hcent, fun g hg x hx => ?_⟩
  have hsqZ : x * g ^ 2 = g ^ 2 * x :=
    (Subgroup.mem_centralizer_iff.mp
      (h5 (Subgroup.mem_inf.mpr ⟨Q.pow_mem hg 2, h4 g hg⟩))) x hx
  have hc : ⁅g, x⁆ * g = g * ⁅g, x⁆ := hcent g hg x hx g hg
  have hgx : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
  have hg2 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by rw [← hsqZ]; group
  have h6 : g ^ 2 * x * (g ^ 2)⁻¹ = ⁅g, x⁆ * ⁅g, x⁆ * x := by
    calc g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by rw [sq]; group
      _ = g * (⁅g, x⁆ * x) * g⁻¹ := by rw [hgx]
      _ = (g * ⁅g, x⁆) * x * g⁻¹ := by group
      _ = (⁅g, x⁆ * g) * x * g⁻¹ := by rw [hc]
      _ = ⁅g, x⁆ * (g * x * g⁻¹) := by group
      _ = ⁅g, x⁆ * ⁅g, x⁆ * x := by rw [hgx, mul_assoc]
  rw [hg2] at h6
  exact mul_right_cancel (h6.symm.trans (one_mul x).symm)

private theorem seven_commutator_bilinear {Q : Subgroup (Module.End F W)ˣ}
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hinv : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1) :
    (∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆) ∧
      (∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁻¹⁆ = ⁅g, q⁆) := by
  have hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, c⁆ * a = a * ⁅g, c⁆ →
      ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆ := by
    intro g hg a ha c hc hcomm
    have hc' : ⁅g, c⁆ * a⁻¹ = a⁻¹ * ⁅g, c⁆ := (Commute.inv_right hcomm).eq
    calc ⁅g, a * c⁆ = g * a * g⁻¹ * (⁅g, c⁆ * a⁻¹) := by group
      _ = g * a * g⁻¹ * (a⁻¹ * ⁅g, c⁆) := by rw [hc']
      _ = ⁅g, a⁆ * ⁅g, c⁆ := by group
  refine ⟨fun g hg a ha c hc => hbil g hg a ha c hc (hcent g hg c hc a ha), ?_⟩
  intro g hg q hq
  have h6 : ⁅g, q * q⁻¹⁆ = ⁅g, q⁆ * ⁅g, q⁻¹⁆ :=
    hbil g hg q hq q⁻¹ (Q.inv_mem hq) (hcent g hg q⁻¹ (Q.inv_mem hq) q hq)
  rw [mul_inv_cancel, commutatorElement_one_right] at h6
  rw [eq_inv_of_mul_eq_one_right h6.symm, inv_eq_of_mul_eq_one_right (hinv g hg q hq)]

private theorem seven_exists_jointEigenProj [Finite F] (hF : ringChar F ≠ 2)
    {Q : Subgroup (Module.End F W)ˣ} [Finite Q]
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hinv : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1)
    {g₀ x₀ : (Module.End F W)ˣ} (hg₀ : g₀ ∈ Q) (hx₀ : x₀ ∈ Q)
    (hne₀ : g₀ * x₀ ≠ x₀ * g₀) :
    ∃ π : Module.End F W, π ≠ 0 ∧
      ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) * π = -π ∧
      (∀ g ∈ Q, ∀ x ∈ Q,
        ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π ∨
          ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = -π) ∧
      (∀ a : Module.End F W, Commute a ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) →
        (∀ g ∈ Q, ∀ x ∈ Q,
          Commute a ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W)) → Commute a π) := by
  classical
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  haveI : Finite W := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F W)ˣ :=
    Finite.of_injective (fun u : (Module.End F W)ˣ => (u : Module.End F W)) Units.val_injective
  have hcQ : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q := fun g hg x hx =>
    Subgroup.commutator_le_self Q (Subgroup.commutator_mem_commutator hg hx)
  let C : Set (Module.End F W) :=
    {a | ∃ g ∈ Q, ∃ x ∈ Q, a = ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W)}
  let S : Finset (Module.End F W) := C.toFinite.toFinset
  have hS : ∀ a ∈ S, ∃ g ∈ Q, ∃ x ∈ Q,
      a = ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) := fun a ha =>
    (Set.Finite.mem_toFinset (Set.toFinite C)).mp ha
  have hmemS : ∀ g ∈ Q, ∀ x ∈ Q, ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) ∈ S :=
    fun g hg x hx => (Set.Finite.mem_toFinset (Set.toFinite C)).mpr ⟨g, hg, x, hx, rfl⟩
  have hcoe2 : ∀ g ∈ Q, ∀ x ∈ Q, ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) *
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) = 1 := fun g hg x hx => by
    rw [← Units.val_mul, hinv g hg x hx, Units.val_one]
  have hcoeQ : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q,
      Commute ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) (h : Module.End F W) :=
    fun g hg x hx h hh => Commute.units_val (hcent g hg x hx h hh)
  have hz1 : ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) ≠ 1 := fun h6 =>
    hne₀ (commutatorElement_eq_one_iff_mul_comm.mp (Units.ext h6))
  obtain ⟨π, hπ0, hzπ, hSπ, hπc⟩ := exists_jointEigenProj hF2 S
    (fun s hs => by obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs; exact hcoe2 g hg x hx)
    (fun s hs t ht => by
      obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs
      obtain ⟨g', hg', x', hx', rfl⟩ := hS t ht
      exact hcoeQ g hg x hx _ (hcQ g' hg' x' hx'))
    (hcoe2 g₀ hg₀ x₀ hx₀) hz1
    (fun s hs => by
      obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs
      exact hcoeQ g₀ hg₀ x₀ hx₀ _ (hcQ g hg x hx))
  exact ⟨π, hπ0, hzπ, fun g hg x hx => hSπ _ (hmemS g hg x hx),
    fun a ha hcomm => hπc a ha (fun s hs => by
      obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs
      exact hcomm g hg x hx)⟩

private theorem seven_eigenproj_chi [Finite F] (hF : ringChar F ≠ 2)
    {Q : Subgroup (Module.End F W)ˣ} {π : Module.End F W} (hπ0 : π ≠ 0)
    (hSπ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π ∨
        ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = -π) :
    ∃ χ : (Module.End F W)ˣ → F,
      (∀ g ∈ Q, ∀ x ∈ Q,
        ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π) ∧
      (∀ u, χ u * χ u = 1) ∧
      (∀ u, χ u = 1 ↔ (u : Module.End F W) * π = π) := by
  classical
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hF
  let χ : (Module.End F W)ˣ → F := fun u => if (u : Module.End F W) * π = π then 1 else -1
  have hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π := by
    intro g hg x hx
    by_cases h6 : ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π
    · simp only [χ, if_pos h6, one_smul, h6]
    · rcases hSπ g hg x hx with h7 | h7
      · exact absurd h7 h6
      · simp only [χ, if_neg h6, neg_one_smul, h7]
  have hχsq : ∀ u, χ u * χ u = 1 := fun u => by
    by_cases h6 : (u : Module.End F W) * π = π <;> simp [χ, h6]
  have hχone : ∀ u, χ u = 1 ↔ (u : Module.End F W) * π = π := by
    intro u
    by_cases h6 : (u : Module.End F W) * π = π
    · rw [show χ u = 1 by simp [χ, h6]]; exact iff_of_true rfl h6
    · rw [show χ u = -1 by simp [χ, h6]]
      exact iff_of_false hneg h6
  exact ⟨χ, hχ, hχsq, hχone⟩

private theorem seven_eigenproj_commute {Q : Subgroup (Module.End F W)ˣ} {π : Module.End F W}
    {g₀ x₀ : (Module.End F W)ˣ}
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hπc : ∀ a : Module.End F W, Commute a ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) →
      (∀ g ∈ Q, ∀ x ∈ Q,
        Commute a ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W)) → Commute a π)
    (hg₀ : g₀ ∈ Q) (hx₀ : x₀ ∈ Q) :
    ∀ g ∈ Q, Commute (((g : (Module.End F W)ˣ) : Module.End F W)) π := by
  intro g hg
  refine hπc _ ?_ ?_
  · exact (Commute.units_val (hcent g₀ hg₀ x₀ hx₀ g hg)).symm
  · intro g' hg' x' hx'
    exact (Commute.units_val (hcent g' hg' x' hx' g hg)).symm

private theorem seven_exists_eigenproj [Finite F] (hF : ringChar F ≠ 2)
    {Q : Subgroup (Module.End F W)ˣ} [Finite Q]
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hinv : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1)
    {g₀ x₀ : (Module.End F W)ˣ} (hg₀ : g₀ ∈ Q) (hx₀ : x₀ ∈ Q)
    (hne₀ : g₀ * x₀ ≠ x₀ * g₀) :
    ∃ (π : Module.End F W) (χ : (Module.End F W)ˣ → F),
      π ≠ 0 ∧ ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) * π = -π ∧
      (∀ g ∈ Q, ∀ x ∈ Q,
        ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π) ∧
      (∀ u, χ u * χ u = 1) ∧
      (∀ u, χ u = 1 ↔ (u : Module.End F W) * π = π) ∧
      (∀ g ∈ Q, Commute (((g : (Module.End F W)ˣ) : Module.End F W)) π) := by
  obtain ⟨π, hπ0, hzπ, hSπ, hπc⟩ := seven_exists_jointEigenProj hF hcent hinv hg₀ hx₀ hne₀
  obtain ⟨χ, hχ, hχsq, hχone⟩ := seven_eigenproj_chi hF hπ0 hSπ
  exact ⟨π, χ, hπ0, hzπ, hχ, hχsq, hχone, seven_eigenproj_commute hcent hπc hg₀ hx₀⟩

private theorem seven_exists_N {B Q : Subgroup (Module.End F W)ˣ} (hmin : HHMinimal B Q)
    (h2 : ⁅Q, Q⁆ ≤ centralizer (B : Set (Module.End F W)ˣ))
    {π : Module.End F W}
    (hπQ : ∀ g ∈ Q, Commute (((g : (Module.End F W)ˣ) : Module.End F W)) π)
    (hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆)
    (hcinv : ∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁻¹⁆ = ⁅g, q⁆) :
    ∃ N : Subgroup (Module.End F W)ˣ,
      (∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
        ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π) ∧
      N ≤ Q ∧ B ≤ normalizer (N : Set (Module.End F W)ˣ) := by
  classical
  let N : Subgroup (Module.End F W)ˣ :=
    { carrier := {w | w ∈ Q ∧ ∀ g ∈ Q,
        ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π}
      mul_mem' := by
        rintro w₁ w₂ ⟨hw₁, hw₁'⟩ ⟨hw₂, hw₂'⟩
        refine ⟨Q.mul_mem hw₁ hw₂, fun g hg => ?_⟩
        rw [hbil g hg w₁ hw₁ w₂ hw₂, Units.val_mul, mul_assoc, hw₂' g hg, hw₁' g hg]
      one_mem' := ⟨Q.one_mem, fun g _ => by
        rw [commutatorElement_one_right, Units.val_one, one_mul]⟩
      inv_mem' := by
        rintro w ⟨hw, hw'⟩
        exact ⟨Q.inv_mem hw, fun g hg => by rw [hcinv g hg w hw]; exact hw' g hg⟩ }
  have hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π := fun _ => Iff.rfl
  have hcB : ∀ g ∈ Q, ∀ x ∈ Q, ∀ b ∈ B, b * ⁅g, x⁆ = ⁅g, x⁆ * b := fun g hg x hx b hb =>
    (Subgroup.mem_centralizer_iff.mp (h2 (Subgroup.commutator_mem_commutator hg hx))) b hb
  have hNB : ∀ b ∈ B, ∀ w ∈ N, b * w * b⁻¹ ∈ N := by
    intro b hb w hw
    obtain ⟨hwQ, hw'⟩ := (hN w).mp hw
    refine (hN _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hmin.normalizes hb) w).mp hwQ,
      fun g hg => ?_⟩
    have hg' : b⁻¹ * g * b ∈ Q := by
      have h6 := (Subgroup.mem_normalizer_iff.mp (hmin.normalizes (inv_mem hb)) g).mp hg
      rwa [inv_inv] at h6
    have hconj : ⁅g, b * w * b⁻¹⁆ = ⁅b⁻¹ * g * b, w⁆ := by
      calc ⁅g, b * w * b⁻¹⁆ = b * ⁅b⁻¹ * g * b, w⁆ * b⁻¹ := by
            rw [conjugate_commutatorElement]
            group
        _ = ⁅b⁻¹ * g * b, w⁆ := by rw [hcB _ hg' w hwQ b hb]; group
    rw [hconj]
    exact hw' _ hg'
  have hBN : B ≤ normalizer (N : Set (Module.End F W)ˣ) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hNB b hb w, fun hw => ?_⟩
    have h6 := hNB b⁻¹ (inv_mem hb) _ hw
    have h7 : b⁻¹ * (b * w * b⁻¹) * b⁻¹⁻¹ = w := by group
    rwa [h7] at h6
  exact ⟨N, hN, fun w hw => ((hN w).mp hw).1, hBN⟩

private theorem seven_N_proper (hF2 : (2 : F) ≠ 0) {N Q : Subgroup (Module.End F W)ˣ}
    {π : Module.End F W}
    (hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π)
    (hπ0 : π ≠ 0)
    {g₀ x₀ : (Module.End F W)ˣ} (hg₀ : g₀ ∈ Q)
    (hzπ : ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) * π = -π) :
    x₀ ∉ N := fun hx =>
  hπ0 (eq_zero_of_mul_eq_self_of_mul_eq_neg hF2 (((hN x₀).mp hx).2 g₀ hg₀) hzπ)

private theorem seven_N_le_centralizer {B Q N : Subgroup (Module.End F W)ˣ} (hmin : HHMinimal B Q)
    (hNQ : N ≤ Q) (hBN : B ≤ normalizer (N : Set (Module.End F W)ˣ))
    {x₀ : (Module.End F W)ˣ} (hx₀N : x₀ ∉ N) (hx₀ : x₀ ∈ Q) :
    N ≤ centralizer (B : Set (Module.End F W)ˣ) := by
  have hbot : ⁅N, B⁆ = ⊥ := by
    by_contra hne'
    exact hx₀N (hmin.minimal N hNQ hBN hne' hx₀)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

private theorem seven_N_eq_inf {B Q N : Subgroup (Module.End F W)ˣ} {π : Module.End F W}
    (h5 : Q ⊓ centralizer (B : Set (Module.End F W)ˣ) ≤
      centralizer (Q : Set (Module.End F W)ˣ))
    (hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π)
    (hNQ : N ≤ Q) (hNC : N ≤ centralizer (B : Set (Module.End F W)ˣ)) :
    N = Q ⊓ centralizer (B : Set (Module.End F W)ˣ) := by
  refine le_antisymm (le_inf hNQ hNC) ?_
  intro w hw
  rw [hN w]
  refine ⟨(Subgroup.mem_inf.mp hw).1, fun g hg => ?_⟩
  have hcen : w ∈ centralizer (Q : Set (Module.End F W)ˣ) := h5 hw
  have hcomm : g * w = w * g := (Subgroup.mem_centralizer_iff.mp hcen) g hg
  have h1 : ⁅g, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  rw [h1, Units.val_one, one_mul]


private theorem seven_coset_eigenvectors [Finite F] {Q N : Subgroup (Module.End F W)ˣ} [Finite Q]
    {π : Module.End F W} {χ : (Module.End F W)ˣ → F} (hπ0 : π ≠ 0)
    (hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π)
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆)
    (hcinv : ∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁻¹⁆ = ⁅g, q⁆)
    (hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π)
    (hχsq : ∀ u, χ u * χ u = 1)
    (hπQ : ∀ g ∈ Q, Commute (((g : (Module.End F W)ˣ) : Module.End F W)) π) :
    ∃ (φ : (Module.End F W)ˣ → Module.End F (Module.End F W))
      (t : ↥Q ⧸ N.subgroupOf Q → (Module.End F W)ˣ → F)
      (v : ↥Q ⧸ N.subgroupOf Q → Module.End F W),
      Function.Injective t ∧ (∀ c, v c ≠ 0) ∧
        (∀ c g, φ g (v c) = t c g • v c) := by
  classical
  haveI : Fintype (↥Q ⧸ N.subgroupOf Q) := Fintype.ofFinite _
  let rep : ↥Q ⧸ N.subgroupOf Q → (Module.End F W)ˣ := fun c => ((Quotient.out c : ↥Q) : _)
  have hrepQ : ∀ c, rep c ∈ Q := fun c => (Quotient.out c).2
  let φ : (Module.End F W)ˣ → Module.End F (Module.End F W) := fun g =>
    if g ∈ Q then LinearMap.mulLeft F ((g : (Module.End F W)ˣ) : Module.End F W) ∘ₗ
      LinearMap.mulRight F (((g⁻¹ : (Module.End F W)ˣ)) : Module.End F W) else 0
  let t : ↥Q ⧸ N.subgroupOf Q → (Module.End F W)ˣ → F := fun c g =>
    if g ∈ Q then χ ⁅g, rep c⁆ else 0
  let v : ↥Q ⧸ N.subgroupOf Q → Module.End F W := fun c =>
    ((rep c : (Module.End F W)ˣ) : Module.End F W) * π
  have hv0 : ∀ c, v c ≠ 0 := by
    intro c h0
    apply hπ0
    have h6 := congrArg (fun a => ((((rep c)⁻¹ : (Module.End F W)ˣ)) : Module.End F W) * a) h0
    simpa [v, ← mul_assoc, ← Units.val_mul] using h6
  have hφv : ∀ c g, φ g (v c) = t c g • v c := by
    intro c g
    by_cases hg : g ∈ Q
    · have hginv : Commute (((g⁻¹ : (Module.End F W)ˣ)) : Module.End F W) π :=
        hπQ g⁻¹ (Q.inv_mem hg)
      have h6 : g * rep c * g⁻¹ = rep c * ⁅g, rep c⁆ := by
        rw [← hcent g hg (rep c) (hrepQ c) (rep c) (hrepQ c), commutatorElement_def]
        group
      simp only [φ, t, v, if_pos hg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply]
      calc ((g : (Module.End F W)ˣ) : Module.End F W) *
            (((rep c : (Module.End F W)ˣ) : Module.End F W) * π *
              (((g⁻¹ : (Module.End F W)ˣ)) : Module.End F W))
          = ((g * rep c * g⁻¹ : (Module.End F W)ˣ) : Module.End F W) * π := by
            rw [mul_assoc ((rep c : (Module.End F W)ˣ) : Module.End F W) π, ← hginv.eq]
            simp only [Units.val_mul, mul_assoc]
        _ = χ ⁅g, rep c⁆ • (((rep c : (Module.End F W)ˣ) : Module.End F W) * π) := by
            rw [h6, Units.val_mul, mul_assoc, hχ g hg (rep c) (hrepQ c), mul_smul_comm]
    · simp only [φ, t, if_neg hg, LinearMap.zero_apply, zero_smul]
  have htinj : Function.Injective t := by
    intro c c' hcc
    have hchar : ∀ g ∈ Q, χ ⁅g, rep c⁆ = χ ⁅g, rep c'⁆ := fun g hg => by
      have h6 := congrFun hcc g
      simpa only [t, if_pos hg] using h6
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show (rep c)⁻¹ * rep c' ∈ N
    refine (hN _).mpr ⟨Q.mul_mem (Q.inv_mem (hrepQ c)) (hrepQ c'), fun g hg => ?_⟩
    rw [hbil g hg ((rep c)⁻¹) (Q.inv_mem (hrepQ c)) (rep c') (hrepQ c'),
      hcinv g hg _ (hrepQ c), Units.val_mul, mul_assoc, hχ g hg _ (hrepQ c'),
      mul_smul_comm, hχ g hg _ (hrepQ c), smul_smul, ← hchar g hg, hχsq, one_smul]
  exact ⟨φ, t, v, htinj, hv0, hφv⟩


private theorem seven_card_quotient_le_finrank [Finite F] {Q N : Subgroup (Module.End F W)ˣ}
    [Finite Q] {π : Module.End F W} {χ : (Module.End F W)ˣ → F} (hπ0 : π ≠ 0)
    (hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π)
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆)
    (hcinv : ∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁻¹⁆ = ⁅g, q⁆)
    (hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π)
    (hχsq : ∀ u, χ u * χ u = 1)
    (hπQ : ∀ g ∈ Q, Commute (((g : (Module.End F W)ˣ) : Module.End F W)) π) :
    Nat.card (↥Q ⧸ N.subgroupOf Q) ≤ Module.finrank F (Module.End F W) := by
  haveI : Fintype (↥Q ⧸ N.subgroupOf Q) := Fintype.ofFinite _
  obtain ⟨φ, t, v, htinj, hv, hφv⟩ :=
    seven_coset_eigenvectors hπ0 hN hcent hbil hcinv hχ hχsq hπQ
  simpa only [Nat.card_eq_fintype_card] using
    (linearIndependent_of_jointEigenvector φ v t hv hφv htinj).fintype_card_le_finrank

private theorem seven_N_relIndex_le [Finite F] (hW : Module.finrank F W ≤ 4)
    {Q N : Subgroup (Module.End F W)ˣ} [Finite Q]
    {π : Module.End F W} {χ : (Module.End F W)ˣ → F} (hπ0 : π ≠ 0)
    (hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π)
    (hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆)
    (hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆)
    (hcinv : ∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁻¹⁆ = ⁅g, q⁆)
    (hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π)
    (hχsq : ∀ u, χ u * χ u = 1)
    (hπQ : ∀ g ∈ Q, Commute (((g : (Module.End F W)ˣ) : Module.End F W)) π) :
    N.relIndex Q ≤ 16 := by
  have hcard := seven_card_quotient_le_finrank hπ0 hN hcent hbil hcinv hχ hχsq hπQ
  have hfin : Module.finrank F (Module.End F W) ≤ 16 :=
    calc Module.finrank F (Module.End F W) = Module.finrank F W * Module.finrank F W :=
          Module.finrank_linearMap F F W W
      _ ≤ 4 * 4 := Nat.mul_le_mul hW hW
      _ = 16 := by norm_num
  calc N.relIndex Q = Nat.card (↥Q ⧸ N.subgroupOf Q) := by
        rw [Subgroup.relIndex, Subgroup.index]
    _ ≤ Module.finrank F (Module.End F W) := hcard
    _ ≤ 16 := hfin


private theorem seven_abelian_case [Finite F] (hF : ringChar F ≠ 2)
    (hW : Module.finrank F W < 7) {B Q : Subgroup (Module.End F W)ˣ} [Finite Q]
    (hQabel : ∀ g ∈ Q, ∀ x ∈ Q, g * x = x * g)
    (h1 : ⁅Q, B⁆ = Q)
    (h4 : ∀ x ∈ Q, x ^ 2 ∈ centralizer (B : Set (Module.End F W)ˣ))
    {k : ℕ} (hBk : ∀ b ∈ B, b ^ (7 ^ k) = 1)
    (hnorm : ∀ b ∈ B, b ∈ normalizer (Q : Set (Module.End F W)ˣ))
    (hnot : ¬ Q ≤ centralizer (B : Set (Module.End F W)ˣ)) : False := by
  classical
  let Ω : Subgroup (Module.End F W)ˣ :=
    { carrier := {x | x ∈ Q ∧ x * x = 1}
      mul_mem' := by
        rintro a c ⟨ha, ha2⟩ ⟨hc, hc2⟩
        refine ⟨Q.mul_mem ha hc, ?_⟩
        calc a * c * (a * c) = a * (c * a) * c := by group
          _ = a * (a * c) * c := by rw [hQabel c hc a ha]
          _ = a * a * (c * c) := by group
          _ = 1 := by rw [ha2, hc2, one_mul]
      one_mem' := ⟨Q.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨Q.inv_mem ha, by rw [← mul_inv_rev, ha2, inv_one]⟩ }
  have hΩ : ∀ x, x ∈ Ω ↔ x ∈ Q ∧ x * x = 1 := fun _ => Iff.rfl
  have hle : ⁅Q, B⁆ ≤ Ω := by
    rw [Subgroup.commutator_le]
    intro q hq b hb
    have hq' : b * q⁻¹ * b⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hnorm b hb) q⁻¹).mp (Q.inv_mem hq)
    have hdecomp : ⁅q, b⁆ = q * (b * q⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    have hcomm : q * (b * q⁻¹ * b⁻¹) = (b * q⁻¹ * b⁻¹) * q := hQabel q hq _ hq'
    have hcb : Commute b (q * q)⁻¹ := by
      have hb2 : b * q ^ 2 = q ^ 2 * b :=
        (Subgroup.mem_centralizer_iff.mp (h4 q hq)) b hb
      rw [sq] at hb2
      exact Commute.inv_right hb2
    have hq'sq : (b * q⁻¹ * b⁻¹) * (b * q⁻¹ * b⁻¹) = (q * q)⁻¹ := by
      calc (b * q⁻¹ * b⁻¹) * (b * q⁻¹ * b⁻¹) = b * (q * q)⁻¹ * b⁻¹ := by group
        _ = (q * q)⁻¹ := by rw [hcb.eq]; group
    refine (hΩ _).mpr ⟨by rw [hdecomp]; exact Q.mul_mem hq hq', ?_⟩
    rw [hdecomp]
    calc q * (b * q⁻¹ * b⁻¹) * (q * (b * q⁻¹ * b⁻¹))
        = q * ((b * q⁻¹ * b⁻¹) * q) * (b * q⁻¹ * b⁻¹) := by group
      _ = q * (q * (b * q⁻¹ * b⁻¹)) * (b * q⁻¹ * b⁻¹) := by rw [← hcomm]
      _ = (q * q) * ((b * q⁻¹ * b⁻¹) * (b * q⁻¹ * b⁻¹)) := by group
      _ = 1 := by rw [hq'sq, mul_inv_cancel]
  have hsq : ∀ x ∈ Q, x * x = 1 := fun x hx => ((hΩ x).mp (hle (h1.ge hx))).2
  exact hnot fun q hq => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    commute_of_sq_eq_one_of_normalizes (by norm_num : Nat.Prime 7) hF hW hsq hQabel
      (hBk b hb) (hnorm b hb) q hq


private theorem seven_relIndex_eq_eight [Finite F] [Finite (Module.End F W)ˣ]
    {B Q L : Subgroup (Module.End F W)ˣ} [Finite Q]
    (hQ : IsPGroup 2 Q) (hB : IsPGroup 7 B) (hmin : HHMinimal B Q)
    (hnot : ¬ Q ≤ centralizer (B : Set (Module.End F W)ˣ))
    (hL : L = Q ⊓ centralizer (B : Set (Module.End F W)ˣ))
    (hrel : L.relIndex Q ≤ 16) : L.relIndex Q = 8 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdivF' : 7 ∣ (centralizer (B : Set (Module.End F W)ˣ)).relIndex Q - 1 :=
    dvd_relIndex_centralizer_sub_one_of_pGroup (K := (Module.End F W)ˣ) (B := B) (Q := Q)
      (r := 7) (by norm_num) hQ hB hmin.normalizes hnot
  have hEq : (Q ⊓ centralizer (B : Set (Module.End F W)ˣ)).relIndex Q =
      (centralizer (B : Set (Module.End F W)ˣ)).relIndex Q := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right _ Q
  have hdiv : 7 ∣ L.relIndex Q - 1 := by
    rw [show L.relIndex Q = (Q ⊓ centralizer (B : Set (Module.End F W)ˣ)).relIndex Q
      from congrArg (fun X => X.relIndex Q) hL, hEq]
    exact hdivF' 
  have hn1 : L.relIndex Q ≠ 1 := by
    intro h
    exact hnot ((Subgroup.relIndex_eq_one.mp h).trans (hL.le.trans inf_le_right))
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hdvd : L.relIndex Q ∣ 2 ^ m := by
    rw [← hm]
    exact L.relIndex_dvd_card Q
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hs4 : s ≤ 4 := by
    by_contra h
    push Not at h
    have h32 : 2 ^ 5 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h
    rw [hs] at hrel
    norm_num at h32
    omega
  rw [hs] at hdiv hn1 ⊢
  interval_cases s
  · norm_num at hn1
  · norm_num at hdiv
  · norm_num at hdiv
  · norm_num
  · norm_num at hdiv

private theorem seven_chi_mul {Q : Subgroup (Module.End F W)ˣ} {a b g : (Module.End F W)ˣ}
    (ha : a ∈ Q) (hb : b ∈ Q) (hg : g ∈ Q) {π : Module.End F W}
    {χ : (Module.End F W)ˣ → F} (hπ0 : π ≠ 0)
    (hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π)
    (hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆) :
    χ ⁅g, a * b⁆ = χ ⁅g, a⁆ * χ ⁅g, b⁆ := by
  have hbilapp : ⁅g, a * b⁆ = ⁅g, a⁆ * ⁅g, b⁆ := hbil g hg a ha b hb
  have h1 := hχ g hg (a * b) (Q.mul_mem ha hb)
  have h1' : ((⁅g, a⁆ * ⁅g, b⁆ : (Module.End F W)ˣ) : Module.End F W) * π =
      χ ⁅g, a * b⁆ • π := by
    rw [← hbilapp]
    exact h1
  have h2 : ((⁅g, a⁆ * ⁅g, b⁆ : (Module.End F W)ˣ) : Module.End F W) * π =
      (χ ⁅g, a⁆ * χ ⁅g, b⁆) • π := by
    rw [Units.val_mul, mul_assoc, hχ g hg b hb, mul_smul_comm, hχ g hg a ha,
      smul_smul, mul_comm]
  exact smul_left_injective F hπ0 (h1'.symm.trans h2)

private theorem seven_chi_inv {Q : Subgroup (Module.End F W)ˣ} {g x : (Module.End F W)ˣ}
    (hg : g ∈ Q) (hx : x ∈ Q) {π : Module.End F W}
    {χ : (Module.End F W)ˣ → F} (hπ0 : π ≠ 0)
    (hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π)
    (hinv : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1) :
    χ ⁅g, x⁆ = χ ⁅x, g⁆ := by
  have hc : ⁅g, x⁆ * ⁅g, x⁆ = 1 := hinv g hg x hx
  have hinvc : ⁅x, g⁆ = ⁅g, x⁆ := by
    rw [← commutatorElement_inv, inv_eq_of_mul_eq_one_right hc]
  have h1 := hχ g hg x hx
  have h2 := hχ x hx g hg
  have h2' : ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π =
      χ ⁅x, g⁆ • π := by
    rw [← hinvc]
    exact h2
  exact smul_left_injective F hπ0 (h1.symm.trans h2')


private theorem seven_parity_application [Finite F] (hF : ringChar F ≠ 2)
    {Q N : Subgroup (Module.End F W)ˣ} [Finite Q]
    {π : Module.End F W} {χ : (Module.End F W)ˣ → F} (hπ0 : π ≠ 0)
    (hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
      ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π)
    (hχ : ∀ g ∈ Q, ∀ x ∈ Q,
      ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π)
    (hχsq : ∀ u, χ u * χ u = 1)
    (hχone : ∀ u, χ u = 1 ↔ (u : Module.End F W) * π = π)
    (hbil : ∀ g ∈ Q, ∀ a ∈ Q, ∀ c ∈ Q, ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆)
    (hinv : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1)
    (hNcenter : N ≤ centralizer (Q : Set (Module.End F W)ˣ))
    (hidx : (N.subgroupOf Q).index = 8) : False := by
  classical
  let lam : ↥Q → ↥Q → F := fun g x =>
    χ ⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆
  have hval : ∀ g x : ↥Q, lam g x = 1 ∨ lam g x = -1 := fun g x =>
    sq_eq_one_iff.mp (by
      simpa [pow_two] using hχsq ⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆)
  have hmul_right : ∀ g x x' : ↥Q, lam g (x * x') = lam g x * lam g x' := by
    intro g x x'
    change χ ⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ) * (x' : (Module.End F W)ˣ))⁆ =
      χ ⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆ *
        χ ⁅((g : (Module.End F W)ˣ)), ((x' : (Module.End F W)ˣ))⁆
    exact seven_chi_mul x.2 x'.2 g.2 hπ0 hχ hbil
  have hchi1 : χ 1 = 1 := (hχone 1).mpr (by simp)
  have hself : ∀ x : ↥Q, lam x x = 1 := by
    intro x
    change χ ⁅((x : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆ = 1
    rw [commutatorElement_self]
    exact hchi1
  have hsymm : ∀ g x : ↥Q, lam g x = lam x g := fun g x =>
    seven_chi_inv g.2 x.2 hπ0 hχ hinv
  have hnondeg : ∀ x : ↥Q, (∀ g : ↥Q, lam g x = 1) ↔ x ∈ N.subgroupOf Q := by
    intro x
    constructor
    · intro h
      rw [Subgroup.mem_subgroupOf]
      refine (hN (x : (Module.End F W)ˣ)).mpr ⟨x.2, fun g hg => ?_⟩
      have h1 : lam ⟨g, hg⟩ x = 1 := h ⟨g, hg⟩
      exact (hχone ⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆).mp h1
    · intro hx g
      have hxN : (x : (Module.End F W)ˣ) ∈ N := Subgroup.mem_subgroupOf.mp hx
      have h1 : ((⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆ :
          (Module.End F W)ˣ) : Module.End F W) * π = π :=
        ((hN (x : (Module.End F W)ˣ)).mp hxN).2 ((g : (Module.End F W)ˣ)) g.2
      exact (hχone ⁅((g : (Module.End F W)ˣ)), ((x : (Module.End F W)ˣ))⁆).mpr h1
  have hNleCenter : N.subgroupOf Q ≤ Subgroup.center ↥Q := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hNcenter (Subgroup.mem_subgroupOf.mp hx)))
      ((g : (Module.End F W)ˣ)) g.2
  haveI : (N.subgroupOf Q).Normal := Subgroup.normal_of_le_center hNleCenter
  exact false_of_index_eight_alternating_character (K := ↥Q) (N := N.subgroupOf Q)
    inferInstance hidx hF lam hval hmul_right hself hsymm hnondeg


private theorem seven_nonabelian_case [Finite F] (hF : ringChar F ≠ 2)
    (hW : Module.finrank F W ≤ 4) {B Q : Subgroup (Module.End F W)ˣ} [Finite Q]
    (hB : IsPGroup 7 B) (hQ : IsPGroup 2 Q) (hmin : HHMinimal B Q)
    (h2 : ⁅Q, Q⁆ ≤ centralizer (B : Set (Module.End F W)ˣ))
    (h3 : ⁅Q, Q⁆ ≤ centralizer (Q : Set (Module.End F W)ˣ))
    (h4 : ∀ x ∈ Q, x ^ 2 ∈ centralizer (B : Set (Module.End F W)ˣ))
    (h5 : Q ⊓ centralizer (B : Set (Module.End F W)ˣ) ≤
      centralizer (Q : Set (Module.End F W)ˣ))
    (hnot : ¬ Q ≤ centralizer (B : Set (Module.End F W)ˣ))
    (hQnab : ¬ ∀ g ∈ Q, ∀ x ∈ Q, g * x = x * g) : False := by
  classical
  haveI : Finite W := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F W)ˣ :=
    Finite.of_injective (fun u : (Module.End F W)ˣ => (u : Module.End F W)) Units.val_injective
  push Not at hQnab
  obtain ⟨g₀, hg₀, x₀, hx₀, hne₀⟩ := hQnab
  obtain ⟨hcent, hinv⟩ := seven_commutator_facts h3 h4 h5
  obtain ⟨hbil, hcinv⟩ := seven_commutator_bilinear hcent hinv
  obtain ⟨π, χ, hπ0, hzπ, hχ, hχsq, hχone, hπQ⟩ :=
    seven_exists_eigenproj hF hcent hinv hg₀ hx₀ hne₀
  obtain ⟨N, hN, hNQ, hBN⟩ := seven_exists_N hmin h2 hπQ hbil hcinv
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hx₀N : x₀ ∉ N := seven_N_proper hF2 hN hπ0 hg₀ hzπ
  have hNC : N ≤ centralizer (B : Set (Module.End F W)ˣ) :=
    seven_N_le_centralizer hmin hNQ hBN hx₀N hx₀
  have hNeq : N = Q ⊓ centralizer (B : Set (Module.End F W)ˣ) :=
    seven_N_eq_inf h5 hN hNQ hNC
  have hNcenter : N ≤ centralizer (Q : Set (Module.End F W)ˣ) := hNeq.le.trans h5
  have hrel : N.relIndex Q ≤ 16 :=
    seven_N_relIndex_le hW hπ0 hN hcent hbil hcinv hχ hχsq hπQ
  have hLrel : (Q ⊓ centralizer (B : Set (Module.End F W)ˣ)).relIndex Q ≤ 16 := by
    rwa [← hNeq]
  have hIdx : (Q ⊓ centralizer (B : Set (Module.End F W)ˣ)).relIndex Q = 8 :=
    seven_relIndex_eq_eight hQ hB hmin hnot rfl hLrel
  have hNrel : N.relIndex Q = 8 := by rw [hNeq]; exact hIdx
  have hidx : (N.subgroupOf Q).index = 8 := hNrel
  exact seven_parity_application hF hπ0 hN hχ hχsq hχone hbil hinv hNcenter hidx


theorem commute_of_seven_normalizes_two [Finite F] (hF : ringChar F ≠ 2)
    (hW : Module.finrank F W ≤ 4) {R : Subgroup (Module.End F W)ˣ} (hR : IsPGroup 2 R)
    {y : (Module.End F W)ˣ} (hy : ∃ k : ℕ, y ^ (7 ^ k) = 1)
    (hyR : y ∈ Subgroup.normalizer (R : Set (Module.End F W)ˣ)) :
    ∀ x ∈ R, y * x = x * y := by
  classical
  obtain ⟨k, hk⟩ := hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite W := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F W)ˣ :=
    Finite.of_injective (fun u : (Module.End F W)ˣ => (u : Module.End F W)) Units.val_injective
  let B : Subgroup (Module.End F W)ˣ := Subgroup.zpowers y
  have hBk : ∀ b ∈ B, b ^ (7 ^ k) = 1 := fun b hb =>
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers hb).trans (orderOf_dvd_of_pow_eq_one hk))
  have hB : IsPGroup 7 B := fun b => ⟨k, Subtype.ext (by simpa using hBk b b.2)⟩
  have hBR : B ≤ normalizer (R : Set (Module.End F W)ˣ) := Subgroup.zpowers_le.mpr hyR
  by_contra hcon
  have hne : ⁅R, B⁆ ≠ ⊥ := by
    intro hbot
    apply hcon
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hx)) y (Subgroup.mem_zpowers y)
  obtain ⟨Q, hQR, hmin⟩ := exists_hhMinimal hBR hne
  haveI : Finite ↥Q := Subtype.finite
  have hQ : IsPGroup 2 Q := hR.to_le hQR
  have h1 : ⁅Q, B⁆ = Q := hhMinimal_commutator_eq_self (by norm_num) hmin hQ hB
  have h2 : ⁅Q, Q⁆ ≤ centralizer (B : Set (Module.End F W)ˣ) :=
    hhMinimal_commutator_le_centralizer hmin hQ
  have h3 : ⁅Q, Q⁆ ≤ centralizer (Q : Set (Module.End F W)ˣ) :=
    hhMinimal_commutator_le_centralizer_self (by norm_num) hmin hQ hB
  have h4 : ∀ x ∈ Q, x ^ 2 ∈ centralizer (B : Set (Module.End F W)ˣ) :=
    hhMinimal_pow_mem_centralizer hmin hQ
  have h5 : Q ⊓ centralizer (B : Set (Module.End F W)ˣ) ≤
      centralizer (Q : Set (Module.End F W)ˣ) :=
    inf_centralizer_le_centralizer_self hmin.normalizes h1 h3 h2
  have hnot : ¬ Q ≤ centralizer (B : Set (Module.End F W)ˣ) := fun hle =>
    hmin.nontrivial (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  by_cases hab : ∀ g ∈ Q, ∀ x ∈ Q, g * x = x * g
  · exact seven_abelian_case hF (by omega) hab h1 h4 hBk hmin.normalizes hnot
  · exact seven_nonabelian_case hF hW hB hQ hmin h2 h3 h4 h5 hnot hab

theorem sevenCentralizesTwoGL {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    SevenCentralizesTwoGL q := by
  intro W _ _ _ hW R hR y hy hyR
  exact commute_of_seven_normalizes_two (by rw [ZMod.ringChar_zmod_n]; exact hq2) hW hR hy hyR

end Linear

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
