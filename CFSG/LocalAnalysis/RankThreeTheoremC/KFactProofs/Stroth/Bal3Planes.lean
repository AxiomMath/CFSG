module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Elem
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open Subgroup

section Powers

variable {X : Type*} [Group X] {p : ℕ}

theorem zpow_eq_one_of_dvd {x : X} (hxp : x ^ p = 1) {k : ℤ} (hk : (p : ℤ) ∣ k) :
    x ^ k = 1 := by
  obtain ⟨t, rfl⟩ := hk
  rw [zpow_mul, zpow_natCast, hxp, one_zpow]

theorem mem_of_zpow_mem_of_not_dvd (hp : p.Prime) {E : Subgroup X} {x : X} (hxp : x ^ p = 1)
    {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) (hx : x ^ k ∈ E) : x ∈ E := by
  obtain ⟨s, t, hst⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hk
  have hx' : x = (x ^ k) ^ t := by
    calc x = x ^ ((p : ℤ) * s + k * t) := by
          rw [show (p : ℤ) * s + k * t = 1 by linarith, zpow_one]
      _ = (x ^ (p : ℤ)) ^ s * (x ^ k) ^ t := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = (x ^ k) ^ t := by rw [zpow_natCast, hxp, one_zpow, one_mul]
  rw [hx']
  exact zpow_mem hx t

theorem exists_zpow_mul_zpow_of_mem_sup {z w x : X} (h : Commute z w)
    (hx : x ∈ zpowers z ⊔ zpowers w) : ∃ a b : ℤ, x = z ^ a * w ^ b := by
  let S : Subgroup X :=
    { carrier := {y | ∃ a b : ℤ, y = z ^ a * w ^ b}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        refine ⟨a + a', b + b', ?_⟩
        calc z ^ a * w ^ b * (z ^ a' * w ^ b') = z ^ a * (w ^ b * z ^ a') * w ^ b' := by
              simp only [mul_assoc]
          _ = z ^ a * (z ^ a' * w ^ b) * w ^ b' := by rw [← (h.zpow_zpow a' b).eq]
          _ = z ^ (a + a') * w ^ (b + b') := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact (h.zpow_zpow (-a) (-b)).eq.symm }
  have hle : zpowers z ⊔ zpowers w ≤ S :=
    sup_le (zpowers_le.2 ⟨1, 0, by simp⟩) (zpowers_le.2 ⟨0, 1, by simp⟩)
  exact hle hx

end Powers

section Planes

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem exists_mem_notMem_zpowers (hp : p.Prime) {E : Subgroup X} {z : X} (hzo : orderOf z = p)
    (hE : Nat.card E = p ^ 2) : ∃ w ∈ E, w ∉ zpowers z := by
  by_contra h
  push Not at h
  have hle : E ≤ zpowers z := fun w hw => h w hw
  have hcard := Subgroup.card_le_of_le hle
  rw [hE, Nat.card_zpowers, hzo] at hcard
  have h2 := hp.two_le
  nlinarith

theorem exists_zpow_mul_zpow_of_card_eq_sq (hp : p.Prime) {E : Subgroup X}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) {z w : X} (hzo : orderOf z = p)
    (hzE : z ∈ E) (hwE : w ∈ E) (hw : w ∉ zpowers z) {x : X} (hx : x ∈ E) :
    ∃ a b : ℤ, x = z ^ a * w ^ b := by
  have : Fact p.Prime := ⟨hp⟩
  have hzw : Commute z w := IsElemAbelian.comm hE hzE hwE
  have hwo : orderOf w = p := orderOf_eq_prime (hE.2 w hwE) (fun h => hw (h ▸ one_mem _))
  have hC : w ∈ centralizer (zpowers z : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (hzw.zpow_left k).eq
  have hsup : Nat.card (zpowers z ⊔ zpowers w : Subgroup X) = p ^ 2 := by
    rw [card_sup_zpowers_of_mem_centralizer hp hwo hC hw, Nat.card_zpowers, hzo, sq]
  have hle : zpowers z ⊔ zpowers w ≤ E := sup_le (zpowers_le.2 hzE) (zpowers_le.2 hwE)
  have heq : zpowers z ⊔ zpowers w = E :=
    eq_of_le_of_card_ge hle (hcard.trans hsup.symm).le
  exact exists_zpow_mul_zpow_of_mem_sup hzw (heq ▸ hx)

theorem exists_conj_eq_zpow_mul (hp : p.Prime) {P : Subgroup X} (hP : IsPGroup p P) {z : X}
    (hzo : orderOf z = p) (hzc : z ∈ centralizer (P : Set X)) {U : Subgroup X}
    (hUe : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) (hzU : z ∈ U)
    (hUn : P ≤ normalizer (U : Set X)) {g : X} (hg : g ∈ P) {u : X} (hu : u ∈ U) :
    ∃ k : ℤ, g * u * g⁻¹ = z ^ k * u := by
  have : Fact p.Prime := ⟨hp⟩
  have hgz : Commute g z := mem_centralizer_iff.1 hzc g hg
  by_cases huz : u ∈ zpowers z
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 huz
    exact ⟨0, by rw [zpow_zero, one_mul]; exact (hgz.zpow_right m).mul_inv_cancel⟩
  · have hgu : g * u * g⁻¹ ∈ U := (mem_normalizer_iff.1 (hUn hg) u).1 hu
    obtain ⟨a, b, hab⟩ := exists_zpow_mul_zpow_of_card_eq_sq hp hUe hUc hzo hzU hu huz hgu
    have hzu : Commute z u := IsElemAbelian.comm hUe hzU hu
    have key : ∀ n : ℕ, ∃ c : ℤ, g ^ n * u * (g ^ n)⁻¹ = z ^ c * u ^ (b ^ n) := by
      intro n
      induction n with
      | zero => exact ⟨0, by simp⟩
      | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨c + a * b ^ n, ?_⟩
        have e1 : g ^ (n + 1) * u * (g ^ (n + 1))⁻¹ = g * (g ^ n * u * (g ^ n)⁻¹) * g⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
        have e2 : MulAut.conj g (z ^ c * u ^ b ^ n) =
            MulAut.conj g z ^ c * (MulAut.conj g u) ^ b ^ n := by
          rw [map_mul, map_zpow, map_zpow]
        simp only [MulAut.conj_apply] at e2
        rw [e1, hc, e2, hab, (hzu.zpow_zpow a b).mul_zpow, ← zpow_mul, ← zpow_mul,
          (hgz.mul_inv_cancel), pow_succ', zpow_add, ← mul_assoc]
    obtain ⟨m, hm⟩ := hP ⟨g, hg⟩
    have hgm : g ^ p ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    obtain ⟨c, hc⟩ := key (p ^ m)
    rw [hgm, one_mul, inv_one, mul_one] at hc
    have h1 : u ^ (1 - b ^ p ^ m) = z ^ c := by
      rw [zpow_sub, zpow_one, mul_inv_eq_iff_eq_mul]
      exact hc
    have hdvd1 : (p : ℤ) ∣ 1 - b ^ p ^ m := by
      by_contra hnd
      refine huz (mem_of_zpow_mem_of_not_dvd hp (hUe.2 u hu) hnd ?_)
      rw [h1]
      exact Subgroup.zpow_mem_zpowers z c
    have hb1 : (p : ℤ) ∣ b - 1 := by
      have h0 : ((1 - b ^ p ^ m : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd1
      push_cast at h0
      rw [ZMod.pow_card_pow] at h0
      have h2 : ((1 : ℤ) : ZMod p) = (b : ZMod p) := by
        rw [Int.cast_one]
        exact sub_eq_zero.1 h0
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub 1 b p).1 h2
    have hub : u ^ b = u := by
      rw [← sub_add_cancel b 1, zpow_add_one, zpow_eq_one_of_dvd (hUe.2 u hu) hb1, one_mul]
    exact ⟨a, by rw [hab, hub]⟩

end Planes

section TwoPlanes

theorem zpow_mul_zpow_neg_eq {X : Type*} [Group X] {z u₁ u₂ : X} (h₁ : Commute z u₁)
    (h₂ : Commute z u₂) (i j : ℤ) :
    (z ^ i * u₁) ^ j * (z ^ j * u₂) ^ (-i) = u₁ ^ j * u₂ ^ (-i) := by
  rw [(h₁.zpow_left i).mul_zpow j, (h₂.zpow_left j).mul_zpow (-i), ← zpow_mul, ← zpow_mul]
  calc z ^ (i * j) * u₁ ^ j * (z ^ (j * -i) * u₂ ^ (-i))
      = z ^ (i * j) * (u₁ ^ j * z ^ (j * -i)) * u₂ ^ (-i) := by simp only [mul_assoc]
    _ = z ^ (i * j) * (z ^ (j * -i) * u₁ ^ j) * u₂ ^ (-i) := by
        rw [← (h₁.zpow_zpow (j * -i) j).eq]
    _ = (z ^ (i * j) * z ^ (j * -i)) * u₁ ^ j * u₂ ^ (-i) := by simp only [mul_assoc]
    _ = u₁ ^ j * u₂ ^ (-i) := by
        rw [← zpow_add, show i * j + j * -i = 0 by ring, zpow_zero, one_mul]

theorem centralizes_of_two_planes {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (_hodd : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p P) {z : X} (hzo : orderOf z = p)
    (_hzP : z ∈ P) (hzc : z ∈ Subgroup.centralizer (P : Set X))
    {D : Subgroup X} (hDP : D ≤ P) (hDe : CFSG.Open.IsElemAbelian p D) (hDc : Nat.card D = p ^ 2)
    (hzD : z ∈ D) (hDself : ∀ x ∈ P, x ∈ Subgroup.centralizer (D : Set X) → x ∈ D)
    {U₁ U₂ : Subgroup X}
    (hU₁P : U₁ ≤ P) (hU₁e : CFSG.Open.IsElemAbelian p U₁) (hU₁c : Nat.card U₁ = p ^ 2)
    (hzU₁ : z ∈ U₁) (hU₁n : P ≤ Subgroup.normalizer (U₁ : Set X))
    (hU₂P : U₂ ≤ P) (hU₂e : CFSG.Open.IsElemAbelian p U₂) (hU₂c : Nat.card U₂ = p ^ 2)
    (hzU₂ : z ∈ U₂) (hU₂n : P ≤ Subgroup.normalizer (U₂ : Set X))
    (hcomm : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a)
    (hint : ∀ u ∈ U₁, u ∈ U₂ → u ∈ Subgroup.zpowers z) :
    ∀ d ∈ D, ∀ u ∈ U₁, d * u = u * d := by
  intro d hd u hu
  have hzp : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
  have hz1 : ∀ y ∈ P, Commute z y := fun y hy => (mem_centralizer_iff.1 hzc y hy).symm
  by_cases hdz : d ∈ zpowers z
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hdz
    exact ((hz1 u (hU₁P hu)).zpow_left k).eq
  obtain ⟨u₁, hu₁, hu₁z⟩ := exists_mem_notMem_zpowers hp hzo hU₁c
  obtain ⟨u₂, hu₂, hu₂z⟩ := exists_mem_notMem_zpowers hp hzo hU₂c
  obtain ⟨i, hi⟩ := exists_conj_eq_zpow_mul hp hP hzo hzc hU₁e hU₁c hzU₁ hU₁n (hDP hd) hu₁
  obtain ⟨j, hj⟩ := exists_conj_eq_zpow_mul hp hP hzo hzc hU₂e hU₂c hzU₂ hU₂n (hDP hd) hu₂
  obtain ⟨v, hvP, hvz, hdv, hvU⟩ : ∃ v : X, v ∈ P ∧ v ∉ zpowers z ∧ d * v = v * d ∧
      ∀ y ∈ U₁, v * y = y * v := by
    by_cases hi0 : z ^ i = 1
    · refine ⟨u₁, hU₁P hu₁, hu₁z, ?_, fun y hy => IsElemAbelian.comm hU₁e hu₁ hy⟩
      rw [hi0, one_mul] at hi
      exact mul_inv_eq_iff_eq_mul.1 hi
    · have hnd : ¬ (p : ℤ) ∣ -i := fun h => hi0 (zpow_eq_one_of_dvd hzp (dvd_neg.1 h))
      refine ⟨u₁ ^ j * u₂ ^ (-i), mul_mem (zpow_mem (hU₁P hu₁) j) (zpow_mem (hU₂P hu₂) (-i)),
        ?_, ?_, ?_⟩
      · intro hv
        have hmem : u₂ ^ (-i) ∈ U₁ := by
          rw [(inv_mul_cancel_left (u₁ ^ j) (u₂ ^ (-i))).symm]
          exact mul_mem (inv_mem (zpow_mem hu₁ j)) (zpowers_le.2 hzU₁ hv)
        exact hu₂z (mem_of_zpow_mem_of_not_dvd hp (hU₂e.2 u₂ hu₂) hnd
          (hint _ hmem (zpow_mem hu₂ (-i))))
      · have e : MulAut.conj d (u₁ ^ j * u₂ ^ (-i)) =
            (MulAut.conj d u₁) ^ j * (MulAut.conj d u₂) ^ (-i) := by
          rw [map_mul, map_zpow, map_zpow]
        simp only [MulAut.conj_apply] at e
        rw [hi, hj, zpow_mul_zpow_neg_eq (hz1 u₁ (hU₁P hu₁)) (hz1 u₂ (hU₂P hu₂)) i j] at e
        exact mul_inv_eq_iff_eq_mul.1 e
      · intro y hy
        have h1 : Commute (u₁ ^ j) y := IsElemAbelian.comm hU₁e (zpow_mem hu₁ j) hy
        have h2 : Commute (u₂ ^ (-i)) y := (hcomm y hy _ (zpow_mem hu₂ (-i))).symm
        exact (h1.mul_left h2).eq
  have hvD : v ∈ centralizer (D : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow_of_card_eq_sq hp hDe hDc hzo hzD hd hdz hx
    have h1 : Commute (z ^ a) v := (hz1 v hvP).zpow_left a
    have h2 : Commute (d ^ b) v := Commute.zpow_left (show Commute d v from hdv) b
    exact (h1.mul_left h2).eq
  obtain ⟨a, b, hdab⟩ := exists_zpow_mul_zpow_of_card_eq_sq hp hDe hDc hzo hzD
    (hDself v hvP hvD) hvz hd
  rw [hdab]
  have h1 : Commute (z ^ a) u := (hz1 u (hU₁P hu)).zpow_left a
  have h2 : Commute (v ^ b) u := Commute.zpow_left (show Commute v u from hvU u hu) b
  exact (h1.mul_left h2).eq

end TwoPlanes

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
