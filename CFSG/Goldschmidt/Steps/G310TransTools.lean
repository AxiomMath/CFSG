module

public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Goldschmidt.Basic
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

open CFSG.SignalizerFunctor.Helpers

section General

variable {X : Type*} [Group X]

theorem sq_eq_one_of_mem_omega1 {A : Subgroup X} (hA : IsMulCommutative A) {x : X}
    (hx : x ∈ Omega1 A) : x ∈ A ∧ x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨A.one_mem, one_pow 2⟩
  | mul y z _ _ hy hz =>
    refine ⟨A.mul_mem hy.1 hz.1, ?_⟩
    rw [(Commute.mul_pow (mul_comm_of_isMulCommutative hA hy.1 hz.1) 2), hy.2, hz.2, one_mul]
  | inv y _ hy => exact ⟨A.inv_mem hy.1, by rw [inv_pow, hy.2, inv_one]⟩

theorem mem_omega1 {A : Subgroup X} {x : X} (hx : x ∈ A) (hx2 : x ^ 2 = 1) : x ∈ Omega1 A :=
  Subgroup.subset_closure ⟨hx, hx2⟩

theorem mem_of_sq_mem_of_odd_index {K N : Subgroup X} (hKN : (K.subgroupOf N).Normal)
    (hodd : Odd (K.subgroupOf N).index) {x : X} (hxN : x ∈ N) (hx2 : x ^ 2 ∈ K) : x ∈ K := by
  let q := QuotientGroup.mk' (K.subgroupOf N)
  have h1 : q ⟨x, hxN⟩ ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (show _ ∈ K.subgroupOf N from hx2)
  have h2 : orderOf (q ⟨x, hxN⟩) ∣ (K.subgroupOf N).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (q ⟨x, hxN⟩) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff (N := K.subgroupOf N) (⟨x, hxN⟩ : N)).mp h3

theorem pow_index_mem {K N : Subgroup X} (hKN : (K.subgroupOf N).Normal) {x : X} (hxN : x ∈ N) :
    x ^ (K.subgroupOf N).index ∈ K := by
  let q := QuotientGroup.mk' (K.subgroupOf N)
  have h : q ⟨x, hxN⟩ ^ (K.subgroupOf N).index = 1 := by
    rw [Subgroup.index_eq_card]
    exact pow_card_eq_one'
  rw [← map_pow] at h
  have h' := (QuotientGroup.eq_one_iff (N := K.subgroupOf N)
    ((⟨x, hxN⟩ : N) ^ (K.subgroupOf N).index)).mp h
  exact h'

end General

section Finite

variable {X : Type*} [Group X] [Finite X]

theorem exists_hyperplane_fixed {E Q : Subgroup X} (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hEab : IsMulCommutative E) (hEne : E ≠ ⊥) (hQ : ¬ 2 ∣ Nat.card Q) (hQne : Q ≠ ⊥)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set X)) :
    ∃ B : Subgroup E, B.index = 2 ∧ ∃ x ∈ Q, x ≠ 1 ∧ ∀ b ∈ B, (b : X) * x = x * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEab
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun e =>
        Subtype.ext (by simpa using hE2 e e.2) }
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
  let _ := conjugationAction E Q hEQ
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := Q) hQ
  by_contra hcon
  push Not at hcon
  have hbot : (⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B Q) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun B hB y hy => ?_)
    rw [Subgroup.mem_bot]
    by_contra hy1
    obtain ⟨b, hbB, hb⟩ := hcon B hB y y.2 (fun h => hy1 (Subtype.ext h))
    apply hb
    have h := congrArg Subtype.val (hy ⟨b, hbB⟩)
    change (b : X) * (y : X) * (b : X)⁻¹ = y at h
    calc (b : X) * y = (b : X) * y * (b : X)⁻¹ * b := by group
      _ = y * b := by rw [h]
  rw [hbot] at hgen
  apply hQne
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : Q) ∈ (⊥ : Subgroup Q) := hgen ▸ Subgroup.mem_top _
  simpa using congrArg Subtype.val ((Subgroup.mem_bot).mp this)

theorem odd_index_of_sylow_le (A : Sylow 2 X) {K N : Subgroup X} (hAK : (A : Subgroup X) ≤ K)
    (hKN : K ≤ N) : Odd (K.subgroupOf N).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (K.subgroupOf N).index ∣ ((A : Subgroup X).subgroupOf N).index :=
    Subgroup.index_dvd_of_le (Subgroup.comap_mono hAK)
  have h2 : ((A : Subgroup X).subgroupOf N).index ∣ (A : Subgroup X).index := by
    rw [← Subgroup.relIndex_mul_index (hAK.trans hKN)]
    exact dvd_mul_right _ _
  have h3 : ¬ 2 ∣ (A : Subgroup X).index := A.not_dvd_index
  exact Nat.not_even_iff_odd.mp fun he => h3 ((even_iff_two_dvd.mp he).trans (h1.trans h2))

theorem eq_top_of_normalizer_le_centralizer_omega1 (A : Sylow 2 X)
    (hA : IsMulCommutative (A : Subgroup X))
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hN : Subgroup.normalizer ((A : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((Omega1 (A : Subgroup X) : Subgroup X) : Set X)) :
    (A : Subgroup X) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((A : Subgroup X) : Set X) with hNdef
  set C := Subgroup.centralizer ((A : Subgroup X) : Set X) with hCdef
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hAC : (A : Subgroup X) ≤ C := Subgroup.le_centralizer_iff_isMulCommutative.mpr hA
  have hnormal : (C.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer' _)
  have hodd : Odd (C.subgroupOf N).index := odd_index_of_sylow_le A hAC hCN
  set m := (C.subgroupOf N).index with hmdef
  have hNC : N ≤ C := by
    intro x hx
    have hxm : x ^ m ∈ C := pow_index_mem hnormal hx
    have key : ∀ n : ℕ, ∀ a ∈ (A : Subgroup X), a ^ 2 ^ n = 1 → x⁻¹ * a * x = a := by
      intro n
      induction n with
      | zero =>
        intro a _ ha
        rw [pow_zero, pow_one] at ha
        rw [ha]
        group
      | succ n ih =>
        intro a ha han
        have h2 : x⁻¹ * a ^ 2 * x = a ^ 2 :=
          ih _ ((A : Subgroup X).pow_mem ha 2) (by rw [← pow_mul, ← pow_succ']; exact han)
        have hxa : x⁻¹ * a * x ∈ (A : Subgroup X) := conj_inv_mem_of_mem_normalizer hx ha
        set z := a⁻¹ * (x⁻¹ * a * x) with hzdef
        have hz : z ∈ (A : Subgroup X) := (A : Subgroup X).mul_mem ((A : Subgroup X).inv_mem ha) hxa
        have hz2 : z ^ 2 = 1 := by
          have hc : Commute a⁻¹ (x⁻¹ * a * x) :=
            mul_comm_of_isMulCommutative hA ((A : Subgroup X).inv_mem ha) hxa
          rw [hzdef, hc.mul_pow, inv_pow]
          have : (x⁻¹ * a * x) ^ 2 = x⁻¹ * a ^ 2 * x := by rw [sq, sq]; group
          rw [this, h2, inv_mul_cancel]
        have hzc : x⁻¹ * z * x = z := by
          have hzO : z ∈ Omega1 (A : Subgroup X) := mem_omega1 hz hz2
          have := Subgroup.mem_centralizer_iff.mp (hN hx) z hzO
          calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
            _ = x⁻¹ * (x * z) := by rw [this]
            _ = z := by group
        have hxaz : x⁻¹ * a * x = a * z := by rw [hzdef]; group
        have hj : ∀ j : ℕ, (x ^ j)⁻¹ * a * x ^ j = a * z ^ j := by
          intro j
          induction j with
          | zero => simp
          | succ j ihj =>
            have hzj : x⁻¹ * z ^ j * x = z ^ j := by
              have := map_pow (MulAut.conj x⁻¹) z j
              simp only [MulAut.conj_apply, inv_inv] at this
              rw [this, hzc]
            calc (x ^ (j + 1))⁻¹ * a * x ^ (j + 1) = x⁻¹ * ((x ^ j)⁻¹ * a * x ^ j) * x := by
                  rw [pow_succ]; group
              _ = x⁻¹ * (a * z ^ j) * x := by rw [ihj]
              _ = (x⁻¹ * a * x) * (x⁻¹ * z ^ j * x) := by group
              _ = a * z * z ^ j := by rw [hxaz, hzj]
              _ = a * z ^ (j + 1) := by rw [pow_succ']; group
        have hm : (x ^ m)⁻¹ * a * x ^ m = a := by
          have := Subgroup.mem_centralizer_iff.mp hxm a ha
          calc (x ^ m)⁻¹ * a * x ^ m = (x ^ m)⁻¹ * (a * x ^ m) := by group
            _ = (x ^ m)⁻¹ * (x ^ m * a) := by rw [this]
            _ = a := by group
        have hzm : z ^ m = 1 := by
          have := (hj m).symm.trans hm
          have h' : a * z ^ m = a * 1 := by rw [mul_one]; exact this
          exact mul_left_cancel h'
        have hz1 : z = 1 := by
          obtain ⟨k, hk⟩ := hodd
          rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul] at hzm
          exact hzm
        rw [hxaz, hz1, mul_one]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨n, hn⟩ := A.isPGroup' ⟨a, ha⟩
    have han : a ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have := key n a ha han
    calc a * x = x * (x⁻¹ * a * x) := by group
      _ = x * a := by rw [this]
  have hP : Subgroup.normalizer ((A : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((A : Subgroup X) : Set X) := hNC
  have hcomp := MonoidHom.ker_transferSylow_isComplement' A hP
  have hodd' := MonoidHom.not_dvd_card_ker_transferSylow A hP
  have hbot : (MonoidHom.transferSylow A hP).ker = ⊥ :=
    hO _ (MonoidHom.normal_ker _) (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd'))
  have hsup := hcomp.sup_eq_top
  rw [hbot, bot_sup_eq] at hsup
  exact hsup

theorem sq_mem_centralizer_of_fixed {E : Subgroup X} (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) {y : X} (hyE : y ∈ Subgroup.normalizer (E : Set X)) {f : X}
    (hf : f ∈ E) (hf1 : f ≠ 1) (hyf : y⁻¹ * f * y = f) :
    y ^ 2 ∈ Subgroup.centralizer (E : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  suffices h : (y ^ 2)⁻¹ * g * y ^ 2 = g by
    calc g * y ^ 2 = y ^ 2 * ((y ^ 2)⁻¹ * g * y ^ 2) := by group
      _ = y ^ 2 * g := by rw [h]
  have hsq : (y ^ 2)⁻¹ * g * y ^ 2 = y⁻¹ * (y⁻¹ * g * y) * y := by rw [sq]; group
  rw [hsq]
  by_cases hg1 : g = 1
  · rw [hg1]; group
  by_cases hgf : g = f
  · rw [hgf, hyf, hyf]
  have hσg : y⁻¹ * g * y ∈ E := conj_inv_mem_of_mem_normalizer hyE hg
  have hσg1 : y⁻¹ * g * y ≠ 1 := by
    intro h
    apply hg1
    calc g = y * (y⁻¹ * g * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hσgf : y⁻¹ * g * y ≠ f := by
    intro h
    apply hgf
    calc g = y * (y⁻¹ * g * y) * y⁻¹ := by group
      _ = y * (y⁻¹ * f * y) * y⁻¹ := by rw [h, hyf]
      _ = f := by group
  have hf2 : f * f = 1 := by rw [← sq]; exact hE2 f hf
  have hfg : f * g ∈ E := E.mul_mem hf hg
  have h1fg : (1 : X) ≠ f * g := by
    intro h
    apply hgf
    calc g = f * (f * g) := by rw [← mul_assoc, hf2, one_mul]
      _ = f := by rw [← h, mul_one]
  have hffg : f ≠ f * g := by
    intro h
    apply hg1
    have := congrArg (f⁻¹ * ·) h
    simpa using this.symm
  have hgfg : g ≠ f * g := by
    intro h
    apply hf1
    have := congrArg (· * g⁻¹) h
    simpa using this.symm
  rcases eq_of_card_four hE4 E.one_mem hf hg hfg (Ne.symm hf1) (Ne.symm hg1) h1fg
    (Ne.symm hgf) hffg hgfg hσg with h | h | h | h
  · exact absurd h hσg1
  · exact absurd h hσgf
  · rw [h, h]
  · rw [h]
    have : y⁻¹ * (f * g) * y = (y⁻¹ * f * y) * (y⁻¹ * g * y) := by group
    rw [this, hyf, h, ← mul_assoc, hf2, one_mul]

theorem exists_conj_of_card_four {E N : Subgroup X} (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hNE : N ≤ Subgroup.normalizer (E : Set X))
    (hsq : ∀ y ∈ N, y ^ 2 ∈ Subgroup.centralizer (E : Set X) →
      y ∈ Subgroup.centralizer (E : Set X))
    {x : X} (hxN : x ∈ N) (hx : x ∉ Subgroup.centralizer (E : Set X)) {e₀ e₁ : X}
    (h0 : e₀ ∈ E) (h1 : e₁ ∈ E) (h01 : e₀ ≠ e₁) (h0' : e₀ ≠ 1) (h1' : e₁ ≠ 1) :
    ∃ y ∈ N, y⁻¹ * e₀ * y = e₁ := by
  have hfpf : ∀ y ∈ N, y ∉ Subgroup.centralizer (E : Set X) → ∀ f ∈ E, f ≠ 1 →
      y⁻¹ * f * y ≠ f := fun y hyN hy f hf hf1 h =>
    hy (hsq y hyN (sq_mem_centralizer_of_fixed hE4 hE2 (hNE hyN) hf hf1 h))
  have hne1 : ∀ y w : X, w ≠ 1 → y⁻¹ * w * y ≠ 1 := by
    intro y w hw h
    apply hw
    calc w = y * (y⁻¹ * w * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group
  set e₀' := x⁻¹ * e₀ * x with he₀'def
  have he₀' : e₀' ∈ E := conj_inv_mem_of_mem_normalizer (hNE hxN) h0
  by_cases h : e₀' = e₁
  · exact ⟨x, hxN, h⟩
  have hx2N : x ^ 2 ∈ N := N.pow_mem hxN 2
  have hx2 : x ^ 2 ∉ Subgroup.centralizer (E : Set X) := fun h' => hx (hsq x hxN h')
  set e₀'' := x⁻¹ * e₀' * x with he₀''def
  have he₀'' : e₀'' ∈ E := conj_inv_mem_of_mem_normalizer (hNE hxN) he₀'
  have hsq' : (x ^ 2)⁻¹ * e₀ * x ^ 2 = e₀'' := by rw [he₀''def, he₀'def, sq]; group
  have hd1 : e₀' ≠ 1 := hne1 x e₀ h0'
  have hd2 : e₀' ≠ e₀ := hfpf x hxN hx e₀ h0 h0'
  have hd3 : e₀'' ≠ 1 := hne1 x e₀' hd1
  have hd4 : e₀'' ≠ e₀' := hfpf x hxN hx e₀' he₀' hd1
  have hd5 : e₀'' ≠ e₀ := by
    have := hfpf (x ^ 2) hx2N hx2 e₀ h0 h0'
    rwa [hsq'] at this
  refine ⟨x ^ 2, hx2N, ?_⟩
  rw [hsq']
  rcases eq_of_card_four hE4 E.one_mem h0 h1 he₀' (Ne.symm h0') (Ne.symm h1') (Ne.symm hd1) h01
    (Ne.symm hd2) (Ne.symm h) he₀'' with h' | h' | h' | h'
  · exact absurd h' hd3
  · exact absurd h' hd5
  · exact h'
  · exact absurd h' hd4

end Finite

end CFSG.Goldschmidt.G310
