module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathP1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathE2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.OddClosureB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.OddComplement

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

private theorem conj_eq_self_of_mem_centralizer (hD : DHyp A Aa t D) {n v : G}
    (hn : n ∈ centralizer (omega1 D hD.comm : Set G)) (hv : v ∈ omega1 D hD.comm) :
    n * v * n⁻¹ = v := by
  have h : v * n = n * v := mem_centralizer_iff.1 hn v hv
  calc n * v * n⁻¹ = (v * n) * n⁻¹ := by rw [← h]
    _ = v := by group

private theorem vConj_eq_one_of_mem_centralizer (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ centralizer (omega1 D hD.comm : Set G)) : vConj hD n = 1 := by
  refine AbelianSub.end_ext fun v => ?_
  rw [val_vConj_apply hD (Subgroup.centralizer_le_normalizer _ hn)]
  change n * v.val * n⁻¹ = v.val
  exact conj_eq_self_of_mem_centralizer hD hn (AbelianSub.val_mem v)

private theorem Hn_le_N0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) :
    L ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G) ⊓ wComm hD w := by
  intro n hn
  refine ⟨?_, Hn_le_wComm H W W2 hD hwH hn⟩
  refine mem_normalizer_iff.2 (mem_iff_conj_of_conj_le Q (g := n) ?_)
  intro q hq
  simpa using hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) q hq

private theorem pow_eight_mem_wreathP₁ (hD : DHyp A Aa t D) {Q : Subgroup G}
    (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) {w : AddMonoid.End (VSub hD)} {k : G}
    (hk : k ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    k ^ 8 ∈ wreathP₁ hD Q w := by
  have hk2 : k * k ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    Subgroup.mul_mem _ hk hk
  have hzero : phiQ hD Q (k * k) = 0 := by
    rw [QHyp.phiQ_mul hD hQ hq4 hsq hk hk]
    exact VSub.add_self hD _
  have hk2C : k * k ∈ centralizer (Q : Set G) :=
    (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq hk2).1 hzero
  have hk2comm : ∀ q ∈ Q, (k * k) * q = q * (k * k) :=
    fun q hq => (mem_centralizer_iff.1 hk2C q hq).symm
  obtain ⟨O, hO, hdecomp⟩ := QHyp.exists_odd_complement hQ
  obtain ⟨q, hq, o, ho, hko⟩ := hdecomp (k * k) hk2comm
  obtain ⟨hoQ, hoodd⟩ := (hO o).1 ho
  have hqo : Commute q o := (hoQ q hq).symm
  have hk8 : k ^ 8 = o ^ 4 := by
    calc k ^ 8 = (k * k) ^ 4 := by
          rw [show (8 : ℕ) = 2 * 4 from by norm_num, pow_mul,
            show k * k = k ^ 2 from (sq k).symm]
      _ = (q * o) ^ 4 := by rw [hko]
      _ = q ^ 4 * o ^ 4 := hqo.mul_pow 4
      _ = o ^ 4 := by rw [hq4 q hq, one_mul]
  have hoC : o ∈ centralizer (omega1 D hD.comm : Set G) :=
    mem_centralizer_iff.2 fun v hv => (hoQ v (hQ.D_le hv.1)).symm
  have hoV : vConj hD o = 1 := vConj_eq_one_of_mem_centralizer hD hoC
  have hoCQ : o ∈ centralizer (Q : Set G) :=
    mem_centralizer_iff.2 fun q hq => (hoQ q hq).symm
  have hoN₁ : o ∈ wreathN₁ hD Q w := by
    refine (mem_wreathN₁_iff hD).2 ⟨?_, ?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer (Q : Set G) hoCQ
    · refine ⟨Subgroup.centralizer_le_normalizer (omega1 D hD.comm : Set G) hoC, ?_⟩
      rw [hoV, one_mul, mul_one]
    · intro v hv
      exact conj_eq_self_of_mem_centralizer hD hoC (wKer_le_omega1 hD w hv)
  rw [hk8]
  exact Subgroup.pow_mem (wreathP₁ hD Q w) (mem_wreathP₁_of_odd hD hoN₁ hoodd) 4

private theorem exists_pow_mul_eq_of_normal {N P : Subgroup G}
    (hNP : ∀ n ∈ N, ∀ y ∈ P, n * y * n⁻¹ ∈ P) {a b : G} (ha : a ∈ P) (hb : b ∈ N) (n : ℕ) :
    ∃ c ∈ P, (a * b) ^ n = c * b ^ n := by
  induction n with
  | zero => exact ⟨1, P.one_mem, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc, hceq⟩ := ih
      have hbn : b ^ n ∈ N := Subgroup.pow_mem N hb n
      have hconj : b ^ n * a * (b ^ n)⁻¹ ∈ P := hNP _ hbn a ha
      refine ⟨c * (b ^ n * a * (b ^ n)⁻¹), P.mul_mem hc hconj, ?_⟩
      calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := pow_succ _ _
        _ = (c * b ^ n) * (a * b) := by rw [hceq]
        _ = (c * (b ^ n * a * (b ^ n)⁻¹)) * b ^ (n + 1) := by
              rw [pow_succ]
              group

private theorem mem_of_pow_eight_mem_of_odd {P : Subgroup G} {x : G} (h8 : x ^ 8 ∈ P)
    (hodd : Odd (orderOf x)) : x ∈ P := by
  have hcop : Nat.Coprime 8 (orderOf x) := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num]
    exact (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hodd.not_two_dvd_nat).symm
  have hgcd : Nat.gcd 8 (orderOf x) = 1 := hcop
  have hbez : (1 : ℤ) = ((8 : ℕ) : ℤ) * Nat.gcdA 8 (orderOf x) +
      (orderOf x : ℤ) * Nat.gcdB 8 (orderOf x) := by
    have h := Nat.gcd_eq_gcd_ab 8 (orderOf x)
    rw [hgcd] at h
    simpa using h
  have h1 : x ^ (((8 : ℕ) : ℤ) * Nat.gcdA 8 (orderOf x)) =
      (x ^ 8) ^ Nat.gcdA 8 (orderOf x) := by
    rw [zpow_mul, zpow_natCast]
  have h2 : x ^ ((orderOf x : ℤ) * Nat.gcdB 8 (orderOf x)) = 1 := by
    rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hx : x = (x ^ 8) ^ Nat.gcdA 8 (orderOf x) := by
    calc x = x ^ (1 : ℤ) := by rw [zpow_one]
      _ = x ^ (((8 : ℕ) : ℤ) * Nat.gcdA 8 (orderOf x) +
            (orderOf x : ℤ) * Nat.gcdB 8 (orderOf x)) := by rw [hbez]
      _ = x ^ (((8 : ℕ) : ℤ) * Nat.gcdA 8 (orderOf x)) *
            x ^ ((orderOf x : ℤ) * Nat.gcdB 8 (orderOf x)) := zpow_add _ _ _
      _ = (x ^ 8) ^ Nat.gcdA 8 (orderOf x) * 1 := by rw [h1, h2]
      _ = (x ^ 8) ^ Nat.gcdA 8 (orderOf x) := mul_one _
  rw [hx]
  exact Subgroup.zpow_mem P h8 _

theorem ThCyc.exists_mul_mul_mem_NV (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {x : G}
    (hx : x ∈ normalizer (Q : Set G) ⊓ wComm hD w) :
    ∃ p₁ ∈ wreathP₁ hD Q w, ∃ p₂ ∈ wreathP₁ hD Q (w + 1),
      (p₁ * p₂)⁻¹ * x ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
  classical
  obtain ⟨m₁, hm₁, m₂, hm₂, hm₁Ker, hm₂Fix, hact⟩ :=
    H.exists_mul_of_wreath W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hx
  have hm₁N₁ : m₁ ∈ wreathN₁ hD Q w :=
    (mem_wreathN₁_iff hD).2 ⟨hm₁.1, hm₁.2, hm₁Ker⟩
  have hm₂N₂ : m₂ ∈ wreathN₁ hD Q (w + 1) := by
    refine (mem_wreathN₁_iff hD).2 ⟨hm₂.1, ?_, ?_⟩
    · rw [wComm_add_one hD w]
      exact hm₂.2
    · rw [wKer_add_one hD w]
      exact hm₂Fix
  obtain ⟨p₁, hp₁, hp₁eq⟩ :=
    H.exists_wreathP₁_conj_eq W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hm₁N₁
  obtain ⟨p₂, hp₂, hp₂eq⟩ :=
    H.exists_wreathP₁_conj_eq W W2 hD h4 hb
      (fun n hn => commute_add_one_of_commute hD (hwH n hn))
      (add_one_mul_add_one hD hww) (vConj_t_mul_add_one_mul H W W2 hD hτw)
      hQ hgQ (by simpa only [wComm_add_one hD w] using hgw) hgM hm₂N₂
  have hp₁Ker : ∀ v ∈ wKer hD w, p₁ * v * p₁⁻¹ = v :=
    ((mem_wreathN₁_iff hD).1 (wreathP₁_le_wreathN₁ hD Q w hp₁)).2.2
  have hp₂Fix : ∀ v ∈ wFix hD w, p₂ * v * p₂⁻¹ = v :=
    fun v hv => ((mem_wreathN₁_iff hD).1 (wreathP₁_le_wreathN₁ hD Q (w + 1) hp₂)).2.2 v
      (by rw [wKer_add_one]; exact hv)
  have hxV1 : ∀ v ∈ wFix hD w, x * v * x⁻¹ = p₁ * v * p₁⁻¹ := by
    intro v hv
    have h1 : x * v * x⁻¹ = (m₁ * m₂) * v * (m₁ * m₂)⁻¹ :=
      (hact v (wFix_le_omega1 hD w hv)).symm
    have h2 : (m₁ * m₂) * v * (m₁ * m₂)⁻¹ = m₁ * v * m₁⁻¹ := by
      rw [show (m₁ * m₂) * v * (m₁ * m₂)⁻¹ = m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ by group,
        hm₂Fix v hv]
    rw [h1, h2, hp₁eq v hv]
  have hxV2 : ∀ v ∈ wKer hD w, x * v * x⁻¹ = (p₁ * p₂) * v * (p₁ * p₂)⁻¹ := by
    intro v hv
    have h1 : x * v * x⁻¹ = (m₁ * m₂) * v * (m₁ * m₂)⁻¹ :=
      (hact v (wKer_le_omega1 hD w hv)).symm
    have hm₂v : m₂ * v * m₂⁻¹ ∈ wKer hD w := conj_mem_wKer_of_mem_wComm hD hm₂.2 hv
    have h2 : (m₁ * m₂) * v * (m₁ * m₂)⁻¹ = m₂ * v * m₂⁻¹ := by
      rw [show (m₁ * m₂) * v * (m₁ * m₂)⁻¹ = m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ by group,
        hm₁Ker _ hm₂v]
    have hp₂v : p₂ * v * p₂⁻¹ = m₂ * v * m₂⁻¹ :=
      hp₂eq v (by rw [wFix_add_one]; exact hv)
    have h3 : (p₁ * p₂) * v * (p₁ * p₂)⁻¹ = m₂ * v * m₂⁻¹ := by
      calc (p₁ * p₂) * v * (p₁ * p₂)⁻¹ = p₁ * (p₂ * v * p₂⁻¹) * p₁⁻¹ := by group
        _ = p₁ * (m₂ * v * m₂⁻¹) * p₁⁻¹ := by rw [hp₂v]
        _ = m₂ * v * m₂⁻¹ := hp₁Ker _ hm₂v
    rw [h1, h2, h3]
  refine ⟨p₁, hp₁, p₂, hp₂, ?_, ?_⟩
  · exact (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).inv_mem ((normalizer (Q : Set G)).mul_mem
        (wreathP₁_le hD Q w hp₁).1 (wreathP₁_le hD Q (w + 1) hp₂).1)) hx.1
  · refine mem_centralizer_iff.2 fun v hv => ?_
    have hconj : ∀ u ∈ omega1 D hD.comm,
        ((p₁ * p₂)⁻¹ * x) * u * ((p₁ * p₂)⁻¹ * x)⁻¹ = u := by
      intro u hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hu
      have hp₂inv : p₂⁻¹ * u₁ * p₂ = u₁ := by
        have h := congrArg (fun z => p₂⁻¹ * z * p₂) (hp₂Fix u₁ hu₁)
        rw [show p₂⁻¹ * (p₂ * u₁ * p₂⁻¹) * p₂ = u₁ by group] at h
        exact h.symm
      have h1 : p₂⁻¹ * p₁⁻¹ * (x * u₁ * x⁻¹) * p₁ * p₂ = u₁ := by
        rw [hxV1 u₁ hu₁]
        rw [show p₂⁻¹ * p₁⁻¹ * (p₁ * u₁ * p₁⁻¹) * p₁ * p₂ = p₂⁻¹ * u₁ * p₂ by group,
          hp₂inv]
      have h2 : p₂⁻¹ * p₁⁻¹ * (x * u₂ * x⁻¹) * p₁ * p₂ = u₂ := by
        rw [hxV2 u₂ hu₂]
        group
      rw [show ((p₁ * p₂)⁻¹ * x) * (u₁ * u₂) * ((p₁ * p₂)⁻¹ * x)⁻¹ =
            (p₂⁻¹ * p₁⁻¹ * (x * u₁ * x⁻¹) * p₁ * p₂) *
              (p₂⁻¹ * p₁⁻¹ * (x * u₂ * x⁻¹) * p₁ * p₂) by group, h1, h2]
    have h := hconj v hv
    calc v * ((p₁ * p₂)⁻¹ * x)
        = (((p₁ * p₂)⁻¹ * x) * v * ((p₁ * p₂)⁻¹ * x)⁻¹) * ((p₁ * p₂)⁻¹ * x) := by rw [h]
      _ = ((p₁ * p₂)⁻¹ * x) * v := by group

theorem ThCyc.mem_sup_of_odd (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {x : G} (hx : x ∈ normalizer (Q : Set G) ⊓ wComm hD w) (hodd : Odd (orderOf x)) :
    x ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) := by
  have hP1normal : ∀ n ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      ∀ y ∈ wreathP₁ hD Q w, n * y * n⁻¹ ∈ wreathP₁ hD Q w :=
    fun n hn y hy => conj_mem_wreathP₁ hD hn hy
  have hP2normal : ∀ n ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      ∀ y ∈ wreathP₁ hD Q (w + 1), n * y * n⁻¹ ∈ wreathP₁ hD Q (w + 1) := by
    intro n hn y hy
    exact conj_mem_wreathP₁ hD (by rwa [wComm_add_one hD w]) hy
  have hPnormal : ∀ n ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      ∀ y ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1),
        n * y * n⁻¹ ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) := by
    intro n hn y hy
    rw [Subgroup.sup_eq_closure] at hy ⊢
    refine Subgroup.closure_induction (p := fun z _ =>
      n * z * n⁻¹ ∈ Subgroup.closure
        ((wreathP₁ hD Q w : Set G) ∪ (wreathP₁ hD Q (w + 1) : Set G))) ?_ ?_ ?_ ?_ hy
    · rintro z (hz | hz)
      · exact Subgroup.subset_closure (Or.inl (hP1normal n hn z hz))
      · exact Subgroup.subset_closure (Or.inr (hP2normal n hn z hz))
    · simpa using (Subgroup.closure _).one_mem
    · intro a c _ _ ha hc
      rw [show n * (a * c) * n⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹) by group]
      exact (Subgroup.closure _).mul_mem ha hc
    · intro a _ ha
      rw [show n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ by group]
      exact (Subgroup.closure _).inv_mem ha
  obtain ⟨p₁, hp₁, p₂, hp₂, hkNV⟩ :=
    H.exists_mul_mul_mem_NV W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hx
  have hkN0 : (p₁ * p₂)⁻¹ * x ∈ normalizer (Q : Set G) ⊓ wComm hD w := by
    have hvc := vConj_eq_one_of_mem_centralizer hD hkNV.2
    exact ⟨hkNV.1, Subgroup.centralizer_le_normalizer _ hkNV.2,
      by rw [hvc, one_mul, mul_one]⟩
  have hxeq : x = p₁ * p₂ * ((p₁ * p₂)⁻¹ * x) := by group
  have hpk : p₁ * p₂ ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) :=
    (wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1)).mul_mem
      (Subgroup.mem_sup_left hp₁) (Subgroup.mem_sup_right hp₂)
  have hk8 : ((p₁ * p₂)⁻¹ * x) ^ 8 ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) :=
    Subgroup.mem_sup_left (pow_eight_mem_wreathP₁ hD hQ hq4 hsq hkNV)
  have hx8 : x ^ 8 ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) := by
    obtain ⟨c, hc, hceq⟩ :=
      exists_pow_mul_eq_of_normal (P := wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1))
        hPnormal hpk hkN0 8
    rw [hxeq, hceq]
    exact (wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1)).mul_mem hc hk8
  exact mem_of_pow_eight_mem_of_odd hx8 hodd

private theorem phiQ_eq_zero_or_eq_w_of_mem_wreathP₁ (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
       phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    (hcard : Nat.card (wKer hD w) = 16) {c : G} (hc : c ∈ wreathP₁ hD Q w)
    (hcNV : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q c = 0 ∨ phiQ hD Q c = w := by
  have key : ∀ {v : G} (hv : v ∈ wKer hD w),
      phiQ hD Q c = 1 → v ∈ wFix hD w := by
    intro v hv h1
    have hvV : v ∈ omega1 D hD.comm := wKer_le_omega1 hD w hv
    obtain ⟨f, hf, hfv⟩ := hsq v hvV
    have hf2 : f ^ 2 ∈ wKer hD w := by rw [hfv]; exact hv
    have hcf : f⁻¹ * c * f * c⁻¹ ∈ wFix hD w :=
      wreathP₁_comm_mem_wFix hD hww hQ hf hf2 hc
    have h1v : (phiQ hD Q c) (AbelianSub.mk v hvV) = AbelianSub.mk v hvV := by
      rw [h1]
      exact AddMonoid.End.one_apply _
    have hval := QHyp.val_phiQ_apply hD hQ hq4 hsq hcNV hf (AbelianSub.mk v hvV) hfv.symm
    rw [h1v] at hval
    have hval' : v = f⁻¹ * c * f * c⁻¹ := by simpa using hval
    rw [hval']
    exact hcf
  have key' : ∀ {v : G} (hv : v ∈ wKer hD w),
      phiQ hD Q c = w + 1 → v ∈ wFix hD w := by
    intro v hv h1
    have hvV : v ∈ omega1 D hD.comm := wKer_le_omega1 hD w hv
    obtain ⟨f, hf, hfv⟩ := hsq v hvV
    have hf2 : f ^ 2 ∈ wKer hD w := by rw [hfv]; exact hv
    have hcf : f⁻¹ * c * f * c⁻¹ ∈ wFix hD w :=
      wreathP₁_comm_mem_wFix hD hww hQ hf hf2 hc
    have hone : (w + 1 : AddMonoid.End (VSub hD)) (AbelianSub.mk v hvV) =
        AbelianSub.mk v hvV := by
      show w (AbelianSub.mk v hvV) + AbelianSub.mk v hvV = AbelianSub.mk v hvV
      rw [(mem_wKer_iff hD w hvV).1 hv, zero_add]
    have hval := QHyp.val_phiQ_apply hD hQ hq4 hsq hcNV hf (AbelianSub.mk v hvV) hfv.symm
    rw [h1, hone] at hval
    have hval' : v = f⁻¹ * c * f * c⁻¹ := by simpa using hval
    rw [hval']
    exact hcf
  rcases hΦ c hcNV with h0 | h1 | hw' | hw1'
  · exact Or.inl h0
  · exfalso
    have hle : wKer hD w ≤ wFix hD w ⊓ wKer hD w :=
      le_inf (fun v hv => key hv h1) le_rfl
    rw [wFix_inf_wKer_eq_bot] at hle
    have hb : wKer hD w = ⊥ := le_bot_iff.mp hle
    rw [hb, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exact Or.inr hw'
  · exfalso
    have hle : wKer hD w ≤ wFix hD w ⊓ wKer hD w :=
      le_inf (fun v hv => key' hv hw1') le_rfl
    rw [wFix_inf_wKer_eq_bot] at hle
    have hb : wKer hD w = ⊥ := le_bot_iff.mp hle
    rw [hb, Subgroup.card_bot] at hcard
    norm_num at hcard

private theorem phiQ_eq_zero_or_eq_add_one_of_mem_wreathP₂ (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
       phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    (hcard : Nat.card (wFix hD w) = 16) {c : G} (hc : c ∈ wreathP₁ hD Q (w + 1))
    (hcNV : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q c = 0 ∨ phiQ hD Q c = w + 1 := by
  have key : ∀ {v : G} (hv : v ∈ wFix hD w), phiQ hD Q c = 1 → v ∈ wKer hD w := by
    intro v hv h1
    have hvV : v ∈ omega1 D hD.comm := wFix_le_omega1 hD w hv
    obtain ⟨f, hf, hfv⟩ := hsq v hvV
    have hf2 : f ^ 2 ∈ wKer hD (w + 1) := by rw [wKer_add_one, hfv]; exact hv
    have hcf : f⁻¹ * c * f * c⁻¹ ∈ wFix hD (w + 1) :=
      wreathP₁_comm_mem_wFix hD (add_one_mul_add_one hD hww) hQ hf hf2 hc
    rw [wFix_add_one] at hcf
    have h1v : (phiQ hD Q c) (AbelianSub.mk v hvV) = AbelianSub.mk v hvV := by
      rw [h1]
      exact AddMonoid.End.one_apply _
    have hval := QHyp.val_phiQ_apply hD hQ hq4 hsq hcNV hf (AbelianSub.mk v hvV) hfv.symm
    rw [h1v] at hval
    have hval' : v = f⁻¹ * c * f * c⁻¹ := by simpa using hval
    rw [hval']
    exact hcf
  have key' : ∀ {v : G} (hv : v ∈ wFix hD w), phiQ hD Q c = w → v ∈ wKer hD w := by
    intro v hv hw'
    have hvV : v ∈ omega1 D hD.comm := wFix_le_omega1 hD w hv
    obtain ⟨f, hf, hfv⟩ := hsq v hvV
    have hf2 : f ^ 2 ∈ wKer hD (w + 1) := by rw [wKer_add_one, hfv]; exact hv
    have hcf : f⁻¹ * c * f * c⁻¹ ∈ wFix hD (w + 1) :=
      wreathP₁_comm_mem_wFix hD (add_one_mul_add_one hD hww) hQ hf hf2 hc
    rw [wFix_add_one] at hcf
    have hwv : w (AbelianSub.mk v hvV) = AbelianSub.mk v hvV :=
      (mem_wFix_iff hD w hvV).1 hv
    have hval := QHyp.val_phiQ_apply hD hQ hq4 hsq hcNV hf (AbelianSub.mk v hvV) hfv.symm
    rw [hw', hwv] at hval
    have hval' : v = f⁻¹ * c * f * c⁻¹ := by simpa using hval
    rw [hval']
    exact hcf
  rcases hΦ c hcNV with h0 | h1 | hw' | hw1'
  · exact Or.inl h0
  · exfalso
    have hle : wFix hD w ≤ wFix hD w ⊓ wKer hD w :=
      le_inf le_rfl (fun v hv => key hv h1)
    rw [wFix_inf_wKer_eq_bot] at hle
    have hb : wFix hD w = ⊥ := le_bot_iff.mp hle
    rw [hb, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exfalso
    have hle : wFix hD w ≤ wFix hD w ⊓ wKer hD w :=
      le_inf le_rfl (fun v hv => key' hv hw')
    rw [wFix_inf_wKer_eq_bot] at hle
    have hb : wFix hD w = ⊥ := le_bot_iff.mp hle
    rw [hb, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exact Or.inr hw1'

private theorem phiQ_pow_eq_nsmul (hD : DHyp A Aa t D) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (n : ℕ) : phiQ hD Q (c ^ n) = n • phiQ hD Q c := by
  induction n with
  | zero =>
      have h1 : (1 : G) ∈ normalizer (Q : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G) :=
        ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
      rw [pow_zero, zero_nsmul]
      exact (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq h1).2 (Subgroup.one_mem _)
  | succ n ih =>
      rw [pow_succ, QHyp.phiQ_mul hD hQ hq4 hsq (Subgroup.pow_mem _ hc n) hc, ih,
        succ_nsmul]

theorem ThCyc.exists_mem_wreathP₁_phiQ_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (F : SylowFacts L S B Aa) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) (hβ : phiQ hD Q b = 1)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
       phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) :
    ∃ p ∈ wreathP₁ hD Q w,
      p ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ∧
        (∃ k : ℕ, orderOf p = 2 ^ k) ∧ phiQ hD Q p = w := by
  classical
  have hcardker : Nat.card (wKer hD w) = 16 := card_wKer H W W2 hD hww hτw
  have hcardfix : Nat.card (wFix hD w) = 16 := card_wFix H W W2 hD hww hτw
  have hbsup : b ∈ wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) := by
    have hSle : {y : G | y ∈ L ⊓ normalizer (A : Set G) ∧ Odd (orderOf y)} ⊆
        (wreathP₁ hD Q w ⊔ wreathP₁ hD Q (w + 1) : Subgroup G) := by
      rintro y ⟨hyHn, hyodd⟩
      exact H.mem_sup_of_odd W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hq4 hsq
        (Hn_le_N0 H W W2 hD hwH hQ hyHn) hyodd
    exact (Subgroup.closure_le _).2 hSle (ThLocalIn2.b_mem_closure_odd W W2 F)
  have hP2_le_norm : wreathP₁ hD Q (w + 1) ≤ normalizer (wreathP₁ hD Q w : Set G) := by
    intro n hn
    have hnN0 : n ∈ normalizer (Q : Set G) ⊓ wComm hD w := by
      have h := wreathP₁_le hD Q (w + 1) hn
      rwa [wComm_add_one hD w] at h
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_wreathP₁ hD hnN0 hy, fun hy => ?_⟩
    have h : n⁻¹ * (n * y * n⁻¹) * n ∈ wreathP₁ hD Q w := by
      simpa only [inv_inv] using
        conj_mem_wreathP₁ hD ((normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hnN0) hy
    rwa [show n⁻¹ * (n * y * n⁻¹) * n = y by group] at h
  have hbmul : b ∈ (wreathP₁ hD Q w : Set G) * (wreathP₁ hD Q (w + 1) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (wreathP₁ hD Q w)
      (wreathP₁ hD Q (w + 1)) hP2_le_norm]
    exact hbsup
  obtain ⟨p₁, hp₁, p₂, hp₂, hb_eq⟩ := hbmul
  have hbNV : b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    ThCyc.b_mem_NV W W2 hD hb hQ
  have hp₂w : p₂ ∈ wComm hD w := by
    have h := (wreathP₁_le hD Q (w + 1) hp₂).2
    rwa [wComm_add_one hD w] at h
  have hp₂Fix : ∀ v ∈ wFix hD w, p₂ * v * p₂⁻¹ = v :=
    fun v hv => ((mem_wreathN₁_iff hD).1 (wreathP₁_le_wreathN₁ hD Q (w + 1) hp₂)).2.2 v
      (by rw [wKer_add_one]; exact hv)
  have hp₁Ker : ∀ v ∈ wKer hD w, p₁ * v * p₁⁻¹ = v :=
    ((mem_wreathN₁_iff hD).1 (wreathP₁_le_wreathN₁ hD Q w hp₁)).2.2
  have hp₁V1 : ∀ v ∈ wFix hD w, p₁ * v * p₁⁻¹ = v := by
    intro v hv
    have hb' : b * v * b⁻¹ = v :=
      conj_eq_self_of_mem_centralizer hD hbNV.2 (wFix_le_omega1 hD w hv)
    rw [← hb_eq] at hb'
    rw [show (p₁ * p₂) * v * (p₁ * p₂)⁻¹ = p₁ * (p₂ * v * p₂⁻¹) * p₁⁻¹ by group,
      hp₂Fix v hv] at hb'
    exact hb'
  have hp₂V2 : ∀ v ∈ wKer hD w, p₂ * v * p₂⁻¹ = v := by
    intro v hv
    have hb' : b * v * b⁻¹ = v :=
      conj_eq_self_of_mem_centralizer hD hbNV.2 (wKer_le_omega1 hD w hv)
    rw [← hb_eq] at hb'
    have hv' : p₂ * v * p₂⁻¹ ∈ wKer hD w := conj_mem_wKer_of_mem_wComm hD hp₂w hv
    rw [show (p₁ * p₂) * v * (p₁ * p₂)⁻¹ = p₁ * (p₂ * v * p₂⁻¹) * p₁⁻¹ by group,
      hp₁Ker _ hv'] at hb'
    exact hb'
  have hp₁V : ∀ v ∈ omega1 D hD.comm, p₁ * v * p₁⁻¹ = v := by
    intro v hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hv
    rw [show p₁ * (v₁ * v₂) * p₁⁻¹ = (p₁ * v₁ * p₁⁻¹) * (p₁ * v₂ * p₁⁻¹) by group,
      hp₁V1 v₁ hv₁, hp₁Ker v₂ hv₂]
  have hp₂V : ∀ v ∈ omega1 D hD.comm, p₂ * v * p₂⁻¹ = v := by
    intro v hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hv
    rw [show p₂ * (v₁ * v₂) * p₂⁻¹ = (p₂ * v₁ * p₂⁻¹) * (p₂ * v₂ * p₂⁻¹) by group,
      hp₂Fix v₁ hv₁, hp₂V2 v₂ hv₂]
  have hp₁NV : p₁ ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    ⟨(wreathP₁_le hD Q w hp₁).1, mem_centralizer_iff.2 fun v hv => by
      calc v * p₁ = (p₁ * v * p₁⁻¹) * p₁ := by rw [hp₁V v hv]
        _ = p₁ * v := by group⟩
  have hp₂NV : p₂ ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    ⟨(wreathP₁_le hD Q (w + 1) hp₂).1, mem_centralizer_iff.2 fun v hv => by
      calc v * p₂ = (p₂ * v * p₂⁻¹) * p₂ := by rw [hp₂V v hv]
        _ = p₂ * v := by group⟩
  have hbphi : phiQ hD Q b = phiQ hD Q p₁ + phiQ hD Q p₂ := by
    rw [← hb_eq, QHyp.phiQ_mul hD hQ hq4 hsq hp₁NV hp₂NV]
  have hsum : phiQ hD Q p₁ + phiQ hD Q p₂ = 1 := hbphi.symm.trans hβ
  have hPhi1 := phiQ_eq_zero_or_eq_w_of_mem_wreathP₁ (c := p₁) hD hww hQ hq4 hsq hΦ hcardker
  have hPhi2 := phiQ_eq_zero_or_eq_add_one_of_mem_wreathP₂ (c := p₂) hD hww hQ hq4 hsq hΦ
    hcardfix
  have hphip1 : phiQ hD Q p₁ = w := by
    rcases hPhi1 hp₁ hp₁NV with h | h
    · rcases hPhi2 hp₂ hp₂NV with h2 | h2
      · exfalso
        rw [h, h2, add_zero] at hsum
        have hwz : w = 0 := by
          calc w = w * 1 := (mul_one w).symm
            _ = w * 0 := by rw [← hsum]
            _ = 0 := mul_zero w
        exact hw0 hwz
      · exfalso
        rw [h, h2, zero_add] at hsum
        exact absurd (add_right_cancel (hsum.trans (zero_add 1).symm)) hw0
    · rcases hPhi2 hp₂ hp₂NV with h2 | h2
      · exfalso
        rw [h, h2, add_zero] at hsum
        exact absurd hsum hw1
      · exact h
  obtain ⟨k, m, hm_odd, hordeq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos p₁).ne'
  have hm_ne : m ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hordeq
    exact (orderOf_pos p₁).ne' hordeq
  have hdvd : m ∣ orderOf p₁ := by
    rw [hordeq]
    exact ⟨2 ^ k, mul_comm (2 ^ k) m⟩
  refine ⟨p₁ ^ m, Subgroup.pow_mem (wreathP₁ hD Q w) hp₁ m, ?_⟩
  refine ⟨Subgroup.pow_mem (normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    hp₁NV m, ⟨k, ?_⟩, ?_⟩
  · rw [orderOf_pow_of_dvd hm_ne hdvd, hordeq,
      Nat.mul_div_left (2 ^ k) (Nat.pos_of_ne_zero hm_ne)]
  · rw [phiQ_pow_eq_nsmul hD hQ hq4 hsq hp₁NV m, hphip1]
    obtain ⟨j, hj⟩ := hm_odd
    have h2w : (2 : ℕ) • w = 0 := by
      rw [two_nsmul]
      exact VSub.add_self hD w
    have heven : ∀ i : ℕ, (2 * i) • w = 0 := by
      intro i
      induction i with
      | zero => rw [Nat.mul_zero, zero_nsmul]
      | succ i ih =>
          rw [Nat.mul_succ, add_nsmul, ih, zero_add]
          exact h2w
    rw [hj, add_nsmul, heven j, zero_add, one_nsmul]

end CFSG.EvenSporadicStandard.ThStd
