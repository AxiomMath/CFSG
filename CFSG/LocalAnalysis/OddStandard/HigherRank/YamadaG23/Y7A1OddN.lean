module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1OddB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1C6a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_two_elt {C N : Subgroup G} (hC : N ≤ normalizer (C : Set G))
    (hN9 : ∀ ν ∈ N, ν ^ 9 ∈ C) {z : G} (hz : z ∈ N ⊔ C) {j : ℕ} (hzj : z ^ (2 ^ j) = 1) :
    z ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right N C hC, Set.mem_mul] at hz
  obtain ⟨ν, hνN, m, hmC, rfl⟩ := hz
  have hpow : ∀ n : ℕ, ∃ m' ∈ C, (ν * m) ^ n = ν ^ n * m' := by
    intro n
    induction n with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ n ih =>
        obtain ⟨m', hm'C, hmul⟩ := ih
        refine ⟨(ν⁻¹ * m' * ν) * m, C.mul_mem ?_ hmC, ?_⟩
        · simpa only [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp (hC (N.inv_mem hνN)) m').mp hm'C
        · rw [pow_succ, hmul, pow_succ]
          group
  obtain ⟨m', hm'C, h9eq⟩ := hpow 9
  have hz9 : (ν * m) ^ 9 ∈ C := by
    rw [h9eq]
    exact C.mul_mem (hN9 ν hνN) hm'C
  have hzjz : (ν * m) ^ ((2 ^ j : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    exact hzj
  have hcop : Nat.Coprime 9 (2 ^ j) := (by decide : Nat.Coprime 9 2).pow_right j
  obtain ⟨a, b, hbez⟩ : ∃ a b : ℤ, (1 : ℤ) = 9 * a + ((2 ^ j : ℕ) : ℤ) * b := by
    refine ⟨Nat.gcdA 9 (2 ^ j), Nat.gcdB 9 (2 ^ j), ?_⟩
    have h := Nat.gcd_eq_gcd_ab 9 (2 ^ j)
    rw [hcop.gcd_eq_one] at h
    exact h
  have hw_eq : ∀ w : G, w ^ ((2 ^ j : ℕ) : ℤ) = 1 → w = (w ^ 9) ^ a := by
    intro w hwj
    have h9 : w ^ (9 : ℤ) = w ^ 9 := zpow_natCast w 9
    calc w = w ^ (1 : ℤ) := (zpow_one w).symm
      _ = w ^ (9 * a + ((2 ^ j : ℕ) : ℤ) * b) := by rw [hbez]
      _ = w ^ (9 * a) * w ^ (((2 ^ j : ℕ) : ℤ) * b) := by rw [zpow_add]
      _ = (w ^ 9) ^ a * (w ^ (((2 ^ j : ℕ) : ℤ))) ^ b := by
          rw [zpow_mul, zpow_mul, h9]
      _ = (w ^ 9) ^ a * (1 : G) ^ b := by rw [hwj]
      _ = (w ^ 9) ^ a := by rw [one_zpow, mul_one]
  rw [hw_eq (ν * m) hzjz]
  exact C.zpow_mem hz9 a

private lemma y7a_conj_N3_mem (c : Ctx7 G L) (hH : F33Hyp c.s c.e)
    {N₃ : Subgroup G} (hN : Y7AOdd c.s N₃) {m x : G}
    (hm : m ∈ normIn c.s.H c.s.fr.A) (hx : x ∈ N₃) : m * x * m⁻¹ ∈ N₃ := by
  obtain ⟨hmH, hmA⟩ := Subgroup.mem_inf.mp hm
  have hmL : m ∈ normalizer (L : Set G) := s3_H_le_N c.s hH.hS hmH
  obtain ⟨hxL, hxA⟩ := Subgroup.mem_inf.mp (hN.le hx)
  have hconjL : m * x * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hmL x).mp hxL
  have hconjA : m * x * m⁻¹ ∈ normalizer (c.s.fr.A : Set G) :=
    (normalizer (c.s.fr.A : Set G)).mul_mem
      ((normalizer (c.s.fr.A : Set G)).mul_mem hmA hxA)
      ((normalizer (c.s.fr.A : Set G)).inv_mem hmA)
  refine hN.char (m * x * m⁻¹) (Subgroup.mem_inf.mpr ⟨hconjL, hconjA⟩) 2 ?_
  have h9 : (m * x * m⁻¹) ^ 9 = m * x ^ 9 * m⁻¹ := conj_pow
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num, h9]
  exact (Subgroup.mem_normalizer_iff.mp hmA (x ^ 9)).mp (hN.pow9 x hx)

private lemma y7a_norm_N3_of_mem_NHA (c : Ctx7 G L) (hH : F33Hyp c.s c.e)
    {N₃ : Subgroup G} (hN : Y7AOdd c.s N₃) {n : G} (hn : n ∈ normIn c.s.H c.s.fr.A) :
    n ∈ normalizer (N₃ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact y7a_conj_N3_mem c hH hN hn
  · intro hx
    have hnin : n⁻¹ ∈ normIn c.s.H c.s.fr.A := (normIn c.s.H c.s.fr.A).inv_mem hn
    have h := y7a_conj_N3_mem c hH hN hnin hx
    have hx_eq : n⁻¹ * (n * x * n⁻¹) * n = x := by group
    simpa only [inv_inv, hx_eq] using h

theorem y7a_X_norm_N3C6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P)
    {N₃ : Subgroup G} (hN : Y7AOdd c.s N₃) :
    y7aX c ≤ normalizer ((N₃ ⊔ C6 c.e : Subgroup G) : Set G) := by
  have hC6 : C6 c.e ≤ normalizer ((N₃ ⊔ C6 c.e : Subgroup G) : Set G) :=
    le_trans le_sup_right Subgroup.le_normalizer
  have hd : c.d ∈ normalizer ((N₃ ⊔ C6 c.e : Subgroup G) : Set G) :=
    hC6 (y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right c.d_mem))
  have hNHA : normIn c.s.H c.s.fr.A ≤
      normalizer ((N₃ ⊔ C6 c.e : Subgroup G) : Set G) := by
    intro n hn
    have hnN3 : n ∈ normalizer (N₃ : Set G) := y7a_norm_N3_of_mem_NHA c hH hN hn
    have hnC6 : n ∈ normalizer (C6 c.e : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro m
      constructor
      · intro hm
        exact y7a_C6_normal c hH hF n
          (y7a_Y_le_X c hH (s5_NHA_le_Y c.toCtx5 hH hn)) m hm
      · intro hm
        have hnX : n⁻¹ ∈ y7aX c :=
          (y7aX c).inv_mem (y7a_Y_le_X c hH (s5_NHA_le_Y c.toCtx5 hH hn))
        have h := y7a_C6_normal c hH hF n⁻¹ hnX (n * m * n⁻¹) hm
        have hx_eq : n⁻¹ * (n * m * n⁻¹) * n = m := by group
        simpa only [inv_inv, hx_eq] using h
    exact Subgroup.inf_normalizer_le_normalizer_sup N₃ (C6 c.e)
      (Subgroup.mem_inf.mpr ⟨hnN3, hnC6⟩)
  have hY : y7aY c ≤ normalizer ((N₃ ⊔ C6 c.e : Subgroup G) : Set G) := by
    rw [show y7aY c = normIn c.s.H c.s.fr.A ⊔ zpowers c.d from s5_Y_eq c.toCtx5 hH]
    exact sup_le hNHA (Subgroup.zpowers_le.mpr hd)
  intro x hx
  obtain ⟨m, hmC6, y, hyY, rfl⟩ := y7a_X_eq_C6Y c hH hF hP x hx
  exact (normalizer ((N₃ ⊔ C6 c.e : Subgroup G) : Set G)).mul_mem (hC6 hmC6) (hY hyY)

theorem y7a_comm_in_C6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P)
    {N₃ : Subgroup G} (hN : Y7AOdd c.s N₃) {k w : G} (hk : k ∈ N₃) (hw : w ∈ y7aX c) {j : ℕ}
    (hj : ⁅k, w⁆ ^ (2 ^ j) = 1) : ⁅k, w⁆ ∈ C6 c.e := by
  have hnorm := y7a_X_norm_N3C6 c hH hF hP hN
  have hC : N₃ ≤ normalizer (C6 c.e : Set G) := by
    intro ν hν
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      exact y7a_C6_normal c hH hF ν
        (y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH (hN.le hν))) m hm
    · intro hm
      have hνX : ν⁻¹ ∈ y7aX c :=
        (y7aX c).inv_mem (y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH (hN.le hν)))
      have h := y7a_C6_normal c hH hF ν⁻¹ hνX (ν * m * ν⁻¹) hm
      have hx_eq : ν⁻¹ * (ν * m * ν⁻¹) * ν = m := by group
      simpa only [inv_inv, hx_eq] using h
  have hN9 : ∀ ν ∈ N₃, ν ^ 9 ∈ C6 c.e := fun ν hν =>
    y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_left (hN.pow9 ν hν))
  have hz : ⁅k, w⁆ ∈ N₃ ⊔ C6 c.e := by
    rw [commutatorElement_def]
    have hk' : k ∈ N₃ ⊔ C6 c.e := Subgroup.mem_sup_left hk
    have hw' : w * k⁻¹ * w⁻¹ ∈ N₃ ⊔ C6 c.e :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hw) k⁻¹).mp
        (Subgroup.mem_sup_left (N₃.inv_mem hk))
    have h := (N₃ ⊔ C6 c.e).mul_mem hk' hw'
    simpa [mul_assoc] using h
  exact y7a_two_elt hC hN9 hz hj

end CFSG.OddStandard.HigherRank.YamadaG23
