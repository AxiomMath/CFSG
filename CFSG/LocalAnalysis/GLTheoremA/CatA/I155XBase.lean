module

public import CFSG.LocalAnalysis.GLTheoremA.PCompJoin
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem zpow_eq_zpow_emod {x : G} {p : ℕ} (hx : x ^ p = 1) (k : ℤ) :
    x ^ k = x ^ (k % (p : ℤ)) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k p]
  rw [zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]

theorem exists_nat_pow_eq {x : G} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1) (k : ℤ) :
    ∃ n : ℕ, n < p ∧ x ^ k = x ^ n := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have h0 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ hpz
  have h1 : k % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  refine ⟨(k % (p : ℤ)).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod hx k, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem zpow_not_mem_normalizer {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {K : Subgroup G} (hxK : x ∉ Subgroup.normalizer (K : Set G)) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) : x ^ k ∉ Subgroup.normalizer (K : Set G) := by
  intro h
  apply hxK
  have hcop : IsCoprime (p : ℤ) k :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).2 hk
  obtain ⟨u, v, huv⟩ := hcop
  have e : x = (x ^ k) ^ v := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ (u * (p : ℤ) + v * k) := by rw [huv]
      _ = (x ^ (p : ℤ)) ^ u * (x ^ k) ^ v := by
          rw [zpow_add, zpow_mul', zpow_mul']
      _ = (x ^ k) ^ v := by
          rw [zpow_natCast, hx, one_zpow, one_mul]
  rw [e]
  exact Subgroup.zpow_mem _ h v

theorem glbConj_zpow_eq_self {x : G} {p : ℕ} (hx : x ^ p = 1) (K : Subgroup G) {k : ℤ}
    (hk : (p : ℤ) ∣ k) : GLBConj (x ^ k) K = K := by
  obtain ⟨m, rfl⟩ := hk
  have : x ^ ((p : ℤ) * m) = 1 := by
    rw [zpow_mul, zpow_natCast, hx, one_zpow]
  rw [this, gLBConj_one]

theorem glbConj_eq_self_of_mem {X : Subgroup G} {a : G} (ha : a ∈ X) :
    GLBConj a X = X := by
  ext y
  rw [mem_gLBConj]
  constructor
  · intro h
    have := X.mul_mem (X.mul_mem (X.inv_mem ha) h) ha
    simpa [mul_assoc] using this
  · intro h
    exact X.mul_mem (X.mul_mem ha h) (X.inv_mem ha)

theorem glaPComponent_zpow {p : ℕ} {X K : Subgroup G} {x : G} (hx : x ∈ X)
    (hK : GLAPComponent p X K) (k : ℤ) : GLAPComponent p X (GLBConj (x ^ k) K) := by
  have h := glaPComponent_gLBConj hK (x ^ k)
  rwa [glbConj_eq_self_of_mem (X.zpow_mem hx k)] at h

theorem zpow_sub_mem_normalizer_of_glbConj_eq {x : G} (K : Subgroup G) {a b : ℤ}
    (h : GLBConj (x ^ a) K = GLBConj (x ^ b) K) :
    x ^ (a - b) ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, zpow_sub]
  have h1 : GLBConj (x ^ b)⁻¹ (GLBConj (x ^ a) K) = GLBConj (x ^ b)⁻¹ (GLBConj (x ^ b) K) := by
    rw [h]
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h1
  exact h1

theorem glbConj_zpow_ne_of_not_dvd {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {K : Subgroup G} (hxK : x ∉ Subgroup.normalizer (K : Set G)) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) : GLBConj (x ^ k) K ≠ K := by
  intro h
  apply zpow_not_mem_normalizer hp hx hxK hk
  rw [mem_normalizer_iff_gLBConj_eq]
  exact h

theorem glbConj_zpow_ne_of_not_dvd_sub {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {K : Subgroup G} (hxK : x ∉ Subgroup.normalizer (K : Set G)) {i j : ℤ}
    (hij : ¬ (p : ℤ) ∣ i - j) : GLBConj (x ^ i) K ≠ GLBConj (x ^ j) K := by
  intro h
  apply zpow_not_mem_normalizer hp hx hxK hij
  exact zpow_sub_mem_normalizer_of_glbConj_eq K h

theorem glbConj_zpow_le_sup_centMod {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) (k : ℤ) :
    GLBConj (x ^ k) K ≤ K ⊔ centModSubgroup p K := by
  by_cases hd : (p : ℤ) ∣ k
  · rw [glbConj_zpow_eq_self hx K hd]
    exact le_sup_left
  · exact le_trans (le_centModSubgroup_of_ne hp (glaPComponent_zpow hxX hK k) hK
      (glbConj_zpow_ne_of_not_dvd hp hx hxK hd)) le_sup_right

theorem glbConj_zpow_le_closureIn (K : Subgroup G) (x : G) (k : ℤ) :
    GLBConj (x ^ k) K ≤ closureIn K (Subgroup.zpowers x) := by
  have hmem : (x ^ k)⁻¹ ∈ Subgroup.zpowers x := Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x k)
  have e : GLBConj (x ^ k) K = K.map (MulAut.conj (x ^ k)⁻¹).toMonoidHom := rfl
  rw [e]
  exact le_iSup₂_of_le ((x ^ k)⁻¹) hmem le_rfl

theorem closureIn_le_of_glbConj {K H : Subgroup G} {x : G}
    (h : ∀ k : ℤ, GLBConj (x ^ k) K ≤ H) : closureIn K (Subgroup.zpowers x) ≤ H := by
  refine iSup₂_le fun a ha => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have e : K.map (MulAut.conj (x ^ k)).toMonoidHom = GLBConj (x ^ (-k)) K := by
    unfold GLBConj
    rw [zpow_neg, inv_inv]
  rw [e]
  exact h (-k)

theorem closureIn_le_sup_centMod {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) :
    closureIn K (Subgroup.zpowers x) ≤ K ⊔ centModSubgroup p K :=
  closureIn_le_of_glbConj fun k => glbConj_zpow_le_sup_centMod hp hx hxX hK hxK k

theorem closureIn_le_normalizer {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) :
    closureIn K (Subgroup.zpowers x) ≤ Subgroup.normalizer (K : Set G) :=
  (closureIn_le_sup_centMod hp hx hxX hK hxK).trans
    (sup_le Subgroup.le_normalizer fun g hg => hg.1)

theorem le_glaPPrimeCoreOf_of_normal' {p : ℕ} {A N : Subgroup G} (hNA : N ≤ A)
    (hn : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p A := by
  have hnorm : (N.subgroupOf A).Normal := by
    refine ⟨fun n hn' a => ?_⟩
    have := hn a a.2 n hn'
    simpa [Subgroup.mem_subgroupOf] using this
  have hcard : Nat.card (N.subgroupOf A) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
  have h1 : N.subgroupOf A ≤ GLAPPrimeCore p ↥A := le_sSup ⟨hnorm, hcard ▸ hc⟩
  have h2 := Subgroup.map_mono (f := A.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hNA] at h2

theorem commutator_glbConj_le_core {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) {i j : ℤ} (hij : ¬ (p : ℤ) ∣ i - j) :
    ⁅GLBConj (x ^ i) K, GLBConj (x ^ j) K⁆ ≤
      GLAPPrimeCoreOf p (closureIn K (Subgroup.zpowers x)) := by
  set Ks := closureIn K (Subgroup.zpowers x) with hKs
  have hKi : GLBConj (x ^ i) K ≤ Ks := glbConj_zpow_le_closureIn K x i
  have hKj : GLBConj (x ^ j) K ≤ Ks := glbConj_zpow_le_closureIn K x j
  have hc1 : ⁅GLBConj (x ^ i) K, GLBConj (x ^ j) K⁆ ≤ GLAPPrimeCoreOf p X :=
    CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp
      (glaPComponent_zpow hxX hK i) (glaPComponent_zpow hxX hK j)
      (glbConj_zpow_ne_of_not_dvd_sub hp hx hxK hij)
  have hKX : Ks ≤ X := closureIn_le_of_glbConj fun k => by
    unfold GLBConj
    rw [← glbConj_eq_self_of_mem (X.zpow_mem hxX k)]
    exact Subgroup.map_mono (f := (MulAut.conj (x ^ k)⁻¹).toMonoidHom) hK.1
  have hc2 : ⁅GLBConj (x ^ i) K, GLBConj (x ^ j) K⁆ ≤ Ks := by
    refine (Subgroup.commutator_mono hKi hKj).trans (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    rw [commutatorElement_def]
    exact Ks.mul_mem (Ks.mul_mem (Ks.mul_mem ha hb) (Ks.inv_mem ha)) (Ks.inv_mem hb)
  have hO : ∀ a ∈ Ks, ∀ n ∈ GLAPPrimeCoreOf p X ⊓ Ks, a * n * a⁻¹ ∈ GLAPPrimeCoreOf p X ⊓ Ks := by
    intro a ha n hn
    refine ⟨?_, Ks.mul_mem (Ks.mul_mem ha hn.2) (Ks.inv_mem ha)⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X (hKX ha)) n).1 hn.1
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p X ⊓ Ks)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp X))
  have hN : GLAPPrimeCoreOf p X ⊓ Ks ≤ GLAPPrimeCoreOf p Ks :=
    le_glaPPrimeCoreOf_of_normal' inf_le_right hO hcop
  exact (le_inf hc1 hc2).trans hN

end CFSG.LocalAnalysis.GLTheoremA.I155X
