module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Polynomial Module Matrix
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator

theorem card_component_quotient_eq_two_pow_mul_odd
    {k : Type} [Field k] [Fintype k] [CharP k 2] {n : ℕ} {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {K : Subgroup (LinearFlag.projectiveSL n k)}
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)))
    {s j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hcardk : Nat.card k = 2 ^ s) (hE : ∃ E : Type, ∃ (_ : Field E) (_ : Fintype E),
      Nat.card E = Nat.card k ^ j ∧ ∃ f : Matrix.SpecialLinearGroup (Fin m) E →* ↥K,
        Function.Surjective f ∧ f.ker ≤ Subgroup.center _) :
    ∃ O : ℕ, Odd O ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 2 ^ (m * (m - 1) / 2 * (s * j)) * O := by
  classical
  obtain ⟨E, hEfield, hEfin, hEcard, f, hf, hker⟩ := hE
  letI := hEfield
  letI := hEfin
  have hq : Nat.card E = 2 ^ (s * j) := by
    rw [hEcard, hcardk, ← pow_mul]
  have hq2 : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  have hsj : s * j ≠ 0 := by
    intro h0
    have h1 : Nat.card E = 1 := by rw [hq, h0, pow_zero]
    omega
  have hqeven : Even (Nat.card E) := by
    rw [hq]
    exact Even.pow_of_ne_zero (by norm_num : Even 2) hsj
  have hcenterless :
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) = ⊥ := by
    by_cases hm2 : m = 2
    · subst hm2
      by_cases hE2 : Nat.card E = 2
      · have hcent : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) = ⊥ := by
          apply Subgroup.eq_bot_of_card_eq
          rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center E 2 (by norm_num), hE2]
          norm_num
        have e : Matrix.SpecialLinearGroup (Fin 2) E ⧸
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) ≃*
            Matrix.SpecialLinearGroup (Fin 2) E :=
          (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
        have hmap := Subgroup.map_center_eq e
        exact (Subgroup.map_injective e.injective)
          (hmap.trans (hcent.trans (Subgroup.map_bot e.toMonoidHom).symm))
      · have hs2 : 2 ≤ s * j := by
          by_contra hlt
          have hle1 : s * j ≤ 1 := by omega
          rcases (by omega : s * j = 0 ∨ s * j = 1) with h0 | h1
          · rw [hq, h0, pow_zero] at hq2
            omega
          · exact hE2 (by rw [hq, h1, pow_one])
        have h4 : 4 ≤ Nat.card E := by
          rw [hq]
          have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hs2
          norm_num at h
          exact h
        haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) E) :=
          CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card E h4
        exact Group.IsPerfect.center_quotient_center_eq_bot _
    · have hm3 : 3 ≤ m := by omega
      haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) :=
        CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm3
      exact Group.IsPerfect.center_quotient_center_eq_bot _
  have hcomap : (Subgroup.center (↥K)).comap f =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) := by
    ext x
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      have hxcent : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) x ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E ⧸
            Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨z, rfl⟩ :=
          QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) y
        rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_iff_div_mem]
        have hcomm : f (x * z) = f (z * x) := by
          rw [map_mul, map_mul]
          exact (Subgroup.mem_center_iff.1 hx) (f z) |>.symm
        have hmem : (x * z) * (z * x)⁻¹ ∈ f.ker := by
          rw [MonoidHom.mem_ker]
          simp [hcomm]
        have hZ : (x * z) * (z * x)⁻¹ ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) := hker hmem
        have hZinv : ((x * z) * (z * x)⁻¹)⁻¹ ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) :=
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)).inv_mem hZ
        simpa [div_eq_mul_inv] using hZinv
      have hxbot : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) x = 1 := by
        have := hxcent
        rw [hcenterless] at this
        simpa using this
      exact (QuotientGroup.eq_one_iff x).1 hxbot
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := hf y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
  have hmap : (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)).map f =
      Subgroup.center (↥K) := by
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective hf (Subgroup.center (↥K))
  let χ : Matrix.SpecialLinearGroup (Fin m) E →* ↥K ⧸ Subgroup.center (↥K) :=
    (QuotientGroup.mk' (Subgroup.center (↥K))).comp f
  have hχ : Function.Surjective χ :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hχker : χ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) := by
    have h : χ.ker = (Subgroup.center (↥K)).comap f := by
      ext x
      change χ x = 1 ↔ f x ∈ Subgroup.center (↥K)
      exact QuotientGroup.eq_one_iff (f x)
    rw [h, hcomap]
  let e : (Matrix.SpecialLinearGroup (Fin m) E ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) ≃*
      (↥K ⧸ Subgroup.center ↥K) :=
    (QuotientGroup.quotientMulEquivOfEq hχker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχ)
  have hcardKZ : Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin m) E) :=
    Nat.card_congr e.symm.toEquiv
  let q := Nat.card E
  let g := Nat.gcd m (q - 1)
  let P := ∏ i ∈ Finset.Icc 2 m, (q ^ i - 1)
  have hq2' : 2 ≤ q := by simpa [q] using hq2
  have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin m) E) = q ^ (m * (m - 1) / 2) * P / g :=
    CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear E m (by omega)
  have hq1odd : Odd (q - 1) := by
    exact Nat.Even.sub_odd (by omega) (by simpa [q] using hqeven) odd_one
  have hgod : Odd g := by
    exact Odd.of_dvd_nat hq1odd (Nat.gcd_dvd_right m (q - 1))
  have hPodd : Odd P := by
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun i hi => ?_)
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hi0 : i ≠ 0 := by omega
    have hqeven' : Even (q ^ i) := by
      simpa [q] using Even.pow_of_ne_zero (by simpa [q] using hqeven) hi0
    have hqi1 : 1 ≤ q ^ i := one_le_pow_of_one_le' (by omega) i
    exact Nat.Even.sub_odd hqi1 hqeven' odd_one
  have hq1dvdP : q - 1 ∣ P := by
    have h2mem : 2 ∈ Finset.Icc 2 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
    exact (Nat.sub_one_dvd_pow_sub_one q 2).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) h2mem)
  have hgdvdP : g ∣ P := (Nat.gcd_dvd_right m (q - 1)).trans hq1dvdP
  have hOddO : Odd (P / g) := by
    obtain ⟨t, ht⟩ := hgdvdP
    have hPt : Odd (g * t) := ht ▸ hPodd
    have hPg : P / g = t := by
      rw [ht]
      exact Nat.mul_div_right t hgod.pos
    rw [hPg]
    exact (Nat.odd_mul.mp hPt).2
  refine ⟨P / g, hOddO, ?_⟩
  rw [hcardKZ, hPSL, Nat.mul_div_assoc _ hgdvdP]
  have hqexp : q ^ (m * (m - 1) / 2) = 2 ^ (m * (m - 1) / 2 * (s * j)) := by
    rw [show q = 2 ^ (s * j) by simpa [q] using hq, ← pow_mul, Nat.mul_comm]
  rw [hqexp]

theorem card_of_catalogIs_isL2n_odd
    {S : Type} [Group S] [Finite S] {r : ℕ} (hr : Odd r)
    (h : catalogIs S (S10.isL2n r)) :
    ∃ O : ℕ, Odd O ∧ Nat.card S = 2 ^ r * O := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isL2n] at hi
  | alternating m hm =>
      simp only [S10.isL2n] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact absurd hr (by norm_num : ¬ Odd 2)
  | sporadic s => simp [S10.isL2n] at hi
  | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A n q =>
          rcases n with _ | _ | n <;> simp [S10.isL2n] at hi
          obtain ⟨hp, hn⟩ := hi
          haveI : Fact q.p.Prime := ⟨hp ▸ Nat.prime_two⟩
          have hcardS : Nat.card S =
              Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
                (GaloisField q.p q.exponent)) :=
            Nat.card_congr
              (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)).toEquiv
          have hfieldcard : Nat.card (GaloisField q.p q.exponent) = 2 ^ r := by
            rw [GaloisField.card (p := q.p) (n := q.exponent) q.exponent_pos.ne', hp, hn]
          have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
                (GaloisField q.p q.exponent)) = 2 ^ r * ((2 ^ r) ^ 2 - 1) := by
            rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear_eq_orderA
              (GaloisField q.p q.exponent) 1]
            rw [hfieldcard]
            exact CatDistinct.orderA_one_eq (k := r) hr.pos
          refine ⟨(2 ^ r) ^ 2 - 1, ?_, hcardS.trans hPSL⟩
          have hEven : Even ((2 ^ r) ^ 2) := by
            rw [pow_two]
            exact Even.mul_left
              (Even.pow_of_ne_zero (by norm_num : Even 2) hr.pos.ne') _
          exact Nat.Even.sub_odd (Nat.succ_le_of_lt (by positivity)) hEven odd_one
      | _ => simp [S10.isL2n] at hi

theorem linear_no_l2_component_of_even_exponent
    {k : Type} [Field k] [Fintype k] [CharP k 2] {n : ℕ} {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (heven : ∃ s : ℕ, Nat.card k = 2 ^ s ∧ Even s)
    {K : Subgroup (LinearFlag.projectiveSL n k)}
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)))
    {r : ℕ} (hr : Odd r)
    (hq : catalogIs (↥K ⧸ Subgroup.center ↥K) (S10.isL2n r)) : False := by
  obtain ⟨s, hs_card, hs_even⟩ := heven
  have hpk : (3 : k) ≠ 0 := by
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    rw [show (3 : k) = 2 + 1 by norm_num, h2, zero_add]
    exact one_ne_zero
  obtain ⟨E, hEfield, hEfin, m, j, hm, hj, -, hEcard, -, f, hf, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_component_type_card
      (p := 3) hpk hA K hK
  have hE' : ∃ E : Type, ∃ (_ : Field E) (_ : Fintype E),
      Nat.card E = Nat.card k ^ j ∧ ∃ f : Matrix.SpecialLinearGroup (Fin m) E →* ↥K,
        Function.Surjective f ∧ f.ker ≤ Subgroup.center _ :=
    ⟨E, hEfield, hEfin, hEcard, f, hf, hker⟩
  obtain ⟨O₁, hO₁, hcard₁⟩ :=
    card_component_quotient_eq_two_pow_mul_odd hA hK hj hm hs_card hE'
  obtain ⟨O₂, hO₂, hcard₂⟩ := card_of_catalogIs_isL2n_odd hr hq
  have heq : 2 ^ (m * (m - 1) / 2 * (s * j)) * O₁ = 2 ^ r * O₂ := by
    rw [← hcard₁, hcard₂]
  obtain ⟨hexp, -⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.FFL.two_pow_mul_odd_inj hO₁ hO₂ heq
  have hevenA : Even (m * (m - 1) / 2 * (s * j)) := by
    obtain ⟨t, rfl⟩ := hs_even
    refine ⟨m * (m - 1) / 2 * (t * j), ?_⟩
    ring
  rw [hexp] at hevenA
  exact (Nat.not_even_iff_odd.mpr hr) hevenA

end CFSG.LocalAnalysis.GLTheoremA

end
