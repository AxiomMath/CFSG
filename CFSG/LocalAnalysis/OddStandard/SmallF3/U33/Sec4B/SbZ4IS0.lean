module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma36

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

private lemma conj_mem_of_comm {N M : Subgroup X} (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N)
    {m : X} (hm : m ∈ M) {n : X} (hn : n ∈ N) : m * n * m⁻¹ ∈ N := by
  have h1 : m * n * m⁻¹ = ⁅m, n⁆ * n := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact N.mul_mem (hcomm m hm n (hNM hn)) hn

private def Cong (N : Subgroup X) (a b : X) : Prop := a * b⁻¹ ∈ N

private lemma cong_symm {N : Subgroup X} {a b : X} (h : Cong N a b) : Cong N b a := by
  simpa [Cong] using N.inv_mem h

private lemma cong_trans {N : Subgroup X} {a b c : X}
    (hab : Cong N a b) (hbc : Cong N b c) : Cong N a c := by
  have h : a * c⁻¹ = (a * b⁻¹) * (b * c⁻¹) := by group
  rw [Cong, h]
  exact N.mul_mem hab hbc

private lemma cong_mul {N M : Subgroup X} (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N)
    {a b c d : X} (hb : b ∈ M) (hab : Cong N a b) (hcd : Cong N c d) :
    Cong N (a * c) (b * d) := by
  have h : (a * c) * (b * d)⁻¹ = (a * b⁻¹) * (b * (c * d⁻¹) * b⁻¹) := by group
  rw [Cong, h]
  exact N.mul_mem hab (conj_mem_of_comm hNM hcomm hb hcd)

private lemma cong_inv {N M : Subgroup X} (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N)
    {a b : X} (ha : a ∈ M) (h : Cong N a b) : Cong N a⁻¹ b⁻¹ := by
  have h' : a⁻¹ * (b⁻¹)⁻¹ = a⁻¹ * (a * b⁻¹)⁻¹ * a := by group
  rw [Cong, h']
  simpa only [inv_inv] using
    conj_mem_of_comm hNM hcomm (M.inv_mem ha) (N.inv_mem h)

private lemma rot3_mem {N M : Subgroup X} (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N) {a b c : X}
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) :
    (a * b * c) * (b * c * a)⁻¹ ∈ N := by
  have h : (a * b * c) * (b * c * a)⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h]
  exact N.mul_mem (hcomm a ha b hb) (conj_mem_of_comm hNM hcomm hb (hcomm a ha c hc))

private lemma rho_conj_rho {ρ : X} (x : X) :
    ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = ρ ^ 2 * x * (ρ ^ 2)⁻¹ := by
  rw [pow_two, mul_inv_rev]
  group

private lemma rho_conj_rho_sq {ρ : X} (hρ3 : ρ ^ 3 = 1) (x : X) :
    ρ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * ρ⁻¹ = x := by
  have h3 : ρ * ρ * ρ = 1 := by
    rw [← pow_three']
    exact hρ3
  have h3inv : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    rw [← pow_three', inv_pow, hρ3, inv_one]
  rw [pow_two, mul_inv_rev]
  calc ρ * (ρ * ρ * x * (ρ⁻¹ * ρ⁻¹)) * ρ⁻¹
      = (ρ * ρ * ρ) * x * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
    _ = x := by rw [h3, h3inv]; group

private lemma rho_sq_conj_rho {ρ : X} (hρ3 : ρ ^ 3 = 1) (x : X) :
    ρ ^ 2 * (ρ * x * ρ⁻¹) * (ρ ^ 2)⁻¹ = x := by
  have h3 : ρ * ρ * ρ = 1 := by
    rw [← pow_three']
    exact hρ3
  have h3inv : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    rw [← pow_three', inv_pow, hρ3, inv_one]
  rw [pow_two, mul_inv_rev]
  calc (ρ * ρ) * (ρ * x * ρ⁻¹) * (ρ⁻¹ * ρ⁻¹)
      = (ρ * ρ * ρ) * x * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
    _ = x := by rw [h3, h3inv]; group

theorem z4i_norm3_mem {N M : Subgroup X} {ρ : X} (hρ3 : ρ ^ 3 = 1) (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hfpf : ∀ x ∈ M, ρ * x * ρ⁻¹ * x⁻¹ ∈ N → x ∈ N) {x : X} (hx : x ∈ M) :
    x * (ρ * x * ρ⁻¹) * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) ∈ N := by
  set b : X := ρ * x * ρ⁻¹
  set c : X := ρ ^ 2 * x * (ρ ^ 2)⁻¹
  have hbM : b ∈ M := hρM x hx
  have hcM : c ∈ M := by
    have h := hρM b hbM
    simpa only [b, rho_conj_rho] using h
  have hnM : x * b * c ∈ M := M.mul_mem (M.mul_mem hx hbM) hcM
  have hconj : ρ * (x * b * c) * ρ⁻¹ = b * c * x := by
    calc ρ * (x * b * c) * ρ⁻¹
        = (ρ * x * ρ⁻¹) * (ρ * b * ρ⁻¹) * (ρ * c * ρ⁻¹) := by group
      _ = b * c * x := by
            rw [show ρ * x * ρ⁻¹ = b from rfl,
              show ρ * b * ρ⁻¹ = c from rho_conj_rho x,
              show ρ * c * ρ⁻¹ = x from rho_conj_rho_sq hρ3 x]
  have hmem : ρ * (x * b * c) * ρ⁻¹ * (x * b * c)⁻¹ ∈ N := by
    rw [hconj]
    have hrot : (x * b * c) * (b * c * x)⁻¹ ∈ N :=
      rot3_mem hNM hcomm hx hbM hcM
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using N.inv_mem hrot
  exact hfpf (x * b * c) hnM hmem

theorem z4i_s3_regular {N M : Subgroup X} {ρ lam : X} (hρ3 : ρ ^ 3 = 1)
    (hl2 : lam * lam = 1) (hlr : lam * ρ * lam⁻¹ = ρ⁻¹) (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hsq : ∀ x ∈ M, x ^ 2 ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hlN : ∀ n ∈ N, lam * n * lam⁻¹ ∈ N) (hlM : ∀ m ∈ M, lam * m * lam⁻¹ ∈ M)
    (hfpf : ∀ x ∈ M, ρ * x * ρ⁻¹ * x⁻¹ ∈ N → x ∈ N) :
    ActsRegularly lam N M := by
  intro x hx hcommx
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hl2
  have hρ2 : ρ ^ 2 = ρ⁻¹ := by
    exact eq_inv_of_mul_eq_one_right (by rw [← pow_succ', hρ3])
  have hρ2inv : (ρ ^ 2)⁻¹ = ρ := by rw [hρ2, inv_inv]
  have hρinv : ρ⁻¹ = ρ ^ 2 := hρ2.symm
  have hlrinv : lam * ρ⁻¹ * lam⁻¹ = ρ := by
    have h1 : ρ⁻¹ = lam * ρ * lam⁻¹ := hlr.symm
    rw [h1, hlinv]
    rw [show lam * (lam * ρ * lam) * lam = (lam * lam) * ρ * (lam * lam) by group, hl2]
    simp
  set x1 : X := ρ * x * ρ⁻¹ with hx1def
  set x2 : X := ρ ^ 2 * x * (ρ ^ 2)⁻¹ with hx2def
  set L : X := lam * x * lam⁻¹ with hLdef
  have hx1M : x1 ∈ M := hρM x hx
  have hx2M : x2 ∈ M := by
    have h := hρM x1 hx1M
    simpa only [x1, x2, rho_conj_rho] using h
  have hLM : L ∈ M := hlM x hx
  have hLx : L * x⁻¹ ∈ N := by
    simpa only [L, commutatorElement_def] using hcommx
  have hconj2 : ∀ n ∈ N, ρ ^ 2 * n * (ρ ^ 2)⁻¹ ∈ N := by
    intro n hn
    have h := hρN n hn
    have h' := hρN (ρ * n * ρ⁻¹) h
    simpa only [pow_two, mul_inv_rev, mul_assoc] using h'
  have hX2 : (ρ ^ 2 * L * (ρ ^ 2)⁻¹) * (ρ ^ 2 * x * (ρ ^ 2)⁻¹)⁻¹ ∈ N := by
    have h := hconj2 (L * x⁻¹) hLx
    rw [show (ρ ^ 2 * L * (ρ ^ 2)⁻¹) * (ρ ^ 2 * x * (ρ ^ 2)⁻¹)⁻¹
        = ρ ^ 2 * (L * x⁻¹) * (ρ ^ 2)⁻¹ by group]
    exact h
  have hu : lam * x1 * lam⁻¹ = ρ ^ 2 * L * (ρ ^ 2)⁻¹ := by
    calc lam * x1 * lam⁻¹
        = (lam * ρ * lam⁻¹) * (lam * x * lam⁻¹) * (lam * ρ⁻¹ * lam⁻¹) := by
          rw [hx1def]; group
      _ = ρ ^ 2 * L * (ρ ^ 2)⁻¹ := by rw [hlr, hlrinv, hρinv, hρ2inv]
  have hnorm : x * x1 * x2 ∈ N := z4i_norm3_mem hρ3 hNM hcomm hρN hρM hfpf hx
  have hA : Cong N x (x1 * x2)⁻¹ := by
    show x * ((x1 * x2)⁻¹)⁻¹ ∈ N
    simpa only [inv_inv, mul_assoc] using hnorm
  have hxin : Cong N x x⁻¹ := by
    show x * (x⁻¹)⁻¹ ∈ N
    simpa only [inv_inv, pow_two] using hsq x hx
  have hB : Cong N x (x1 * x2) := by
    have := cong_inv hNM hcomm hx hA
    simpa only [inv_inv] using cong_trans hxin this
  have hX2C : Cong N (ρ ^ 2 * L * (ρ ^ 2)⁻¹) x2 := hX2
  have hx1inv : Cong N x1⁻¹ x1 := by
    show x1⁻¹ * (x1)⁻¹ ∈ N
    have h := hsq x1 hx1M
    simpa only [pow_two, mul_inv_rev, inv_inv] using N.inv_mem h
  have hC : Cong N (lam * x1 * lam⁻¹ * x1⁻¹) (x2 * x1) := by
    rw [hu]
    exact cong_mul hNM hcomm hx2M hX2C hx1inv
  have hD : Cong N (x1 * x2) (x2 * x1) := by
    show (x1 * x2) * (x2 * x1)⁻¹ ∈ N
    simpa only [commutatorElement_def, mul_inv_rev, mul_assoc] using hcomm x1 hx1M x2 hx2M
  have hE : Cong N x (x2 * x1) := cong_trans hB hD
  have hF : Cong N x (lam * x1 * lam⁻¹ * x1⁻¹) :=
    cong_trans hE (cong_symm hC)
  have hgoal : lam * x1 * lam⁻¹ * x1⁻¹ = ⁅lam, x1⁆ := rfl
  refine ⟨x1, hx1M, ?_⟩
  rw [hgoal] at hF
  simpa only [Cong, commutatorElement_def] using hF

theorem z4i_fpl {Y : Subgroup X} {t : X} (ht2 : t * t = 1) (hYsq : ∀ y ∈ Y, y * y = 1)
    (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (hreg : ActsRegularly t ⊥ Y) {x : X}
    (hx : ⁅t, x⁆ ∈ Y) : ∃ w ∈ Y, t * (w⁻¹ * x) * t⁻¹ = w⁻¹ * x := by
  have htinvt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set u : X := ⁅t, x⁆ with hu_def
  have huY : u ∈ Y := hx
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hYsq u huY)
  have hu_form : u = t * x * t * x⁻¹ := by
    rw [hu_def]
    simp only [commutatorElement_def, htinvt]
  have hu_tt : t * u * t⁻¹ = u⁻¹ := by
    rw [hu_form, htinvt]
    rw [show t * (t * x * t * x⁻¹) * t = x * t * x⁻¹ * t by
      calc t * (t * x * t * x⁻¹) * t = (t * t) * x * t * x⁻¹ * t := by group
        _ = x * t * x⁻¹ * t := by rw [ht2, one_mul]]
    rw [show (t * x * t * x⁻¹)⁻¹ = x * t * x⁻¹ * t by
      rw [mul_inv_rev]
      simp only [mul_inv_rev, inv_inv, htinvt]
      group]
  have hu_fixed : t * u * t⁻¹ = u := by rw [hu_tt, hu_inv]
  replace hreg : ActsRegularly t ⊥ Y := hreg
  have hcu : ⁅t, u⁆ ∈ (⊥ : Subgroup X) := by
    have h1 : ⁅t, u⁆ = 1 := by
      rw [commutatorElement_def, hu_fixed]
      group
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨w, hw, hwreg⟩ := hreg u huY hcu
  have h1 : u * ⁅t, w⁆⁻¹ = 1 := by simpa using hwreg
  have hu_eq : u = ⁅t, w⁆ := eq_of_mul_inv_eq_one h1
  have hw2 : w * w = 1 := hYsq w hw
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hA : t * w * t⁻¹ = u * w := by
    rw [hu_eq]
    simp only [commutatorElement_def]
    group
  have hAinv : t * w⁻¹ * t⁻¹ = w * u := by
    rw [show t * w⁻¹ * t⁻¹ = (t * w * t⁻¹)⁻¹ by group, hA, mul_inv_rev, hwinv, hu_inv]
  have huxt : t * x * t⁻¹ = u * x := by
    rw [hu_def]
    simp only [commutatorElement_def]
    group
  refine ⟨w, hw, ?_⟩
  calc t * (w⁻¹ * x) * t⁻¹ = (t * w⁻¹ * t⁻¹) * (t * x * t⁻¹) := by group
    _ = (w * u) * (u * x) := by rw [hAinv, huxt]
    _ = w⁻¹ * x := by
      rw [show w * u * (u * x) = w * (u * u) * x by group]
      rw [hYsq u huY, hwinv]
      group

theorem z4i_between {Q K Z : Subgroup X} {ρ : X} (hρ3 : ρ ^ 3 = 1) (hQK : Q ≤ K) (hQZ : Q ≤ Z)
    (hZK : Z ≤ K) (hidx : Q.relIndex K = 4)
    (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q) (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K)
    (hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ ∈ Z)
    (hfpf : ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Q → k ∈ Q) : Z = Q ∨ Z = K := by
  classical
  rcases eq_or_ne Z Q with hZQ | hZQ
  · exact Or.inl hZQ
  · right
    have htower : Q.relIndex Z * Z.relIndex K = 4 := by
      rw [Subgroup.relIndex_mul_relIndex (H := Q) (K := Z) (L := K) hQZ hZK, hidx]
    have hne1 : Q.relIndex Z ≠ 1 := by
      intro h1
      exact hZQ (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hQZ)
    have hne2 : Q.relIndex Z ≠ 2 := by
      intro h2
      obtain ⟨a, haZ, haQ, hb⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and).mp h2
      have haK : a ∈ K := hZK haZ
      have hbZ : ρ * a * ρ⁻¹ ∈ Z := hρZ a haZ
      rcases hb (ρ * a * ρ⁻¹) hbZ with hmem | hmem
      · have ha2 : a ^ 2 ∈ Q := by
          have h := Subgroup.sq_mem_of_index_two
            (H := Q.subgroupOf Z) (show (Q.subgroupOf Z).index = 2 from h2) (⟨a, haZ⟩ : Z)
          simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subtype.coe_mk] using h
        have hconj : ρ * a * ρ⁻¹ * a⁻¹ ∈ Q := by
          have h1 : (ρ * a * ρ⁻¹ * a) * (a ^ 2)⁻¹ ∈ Q :=
            Q.mul_mem hmem (Q.inv_mem ha2)
          rwa [show (ρ * a * ρ⁻¹ * a) * (a ^ 2)⁻¹ = ρ * a * ρ⁻¹ * a⁻¹ by group] at h1
        exact haQ (hfpf a haK hconj)
      · have h2' : ρ ^ 2 * (ρ * a * ρ⁻¹) * (ρ ^ 2)⁻¹ ∈ Q := by
          have h := hρQ _ hmem
          have h2 := hρQ _ h
          simpa only [pow_two, mul_inv_rev, mul_assoc] using h2
        exact haQ (by simpa only [rho_sq_conj_rho hρ3 a] using h2')
    have hrel : Q.relIndex Z = 4 := by
      have hle : Q.relIndex Z ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨Z.relIndex K, htower.symm⟩
      interval_cases Q.relIndex Z <;> simp_all <;> omega
    have hlast : Z.relIndex K = 1 := by
      have h := htower
      rw [hrel] at h
      have h2 : 4 * Z.relIndex K = 4 * 1 := by simpa using h
      exact Nat.mul_left_cancel (by norm_num) h2
    exact le_antisymm hZK (Subgroup.relIndex_eq_one.mp hlast)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
