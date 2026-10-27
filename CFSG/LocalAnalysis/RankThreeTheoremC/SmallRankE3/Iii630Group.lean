module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
section R10A1

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_mul_mem_centralizer_of_inverts {F : Subgroup G} {y : G} (hy1 : y ≠ 1)
    (hy2 : y * y = 1) (hinv : ∀ a ∈ F, y * a * y⁻¹ = a⁻¹)
    (hodd : ¬ 2 ∣ Nat.card (centralizer (F : Set G))) :
    ∀ g ∈ normalizer (F : Set G), ∃ c ∈ centralizer (F : Set G),
      c⁻¹ * g ∈ centralizer ({y} : Set G) := by
  intro g hg
  have hyinv : y⁻¹ = y := (eq_inv_of_mul_eq_one_left hy2).symm
  have hconj : ∀ a ∈ F, g⁻¹ * a * g ∈ F := by
    intro a ha
    refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * a * g)).mpr ?_
    have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [e]
    exact ha
  obtain ⟨y', hy'⟩ : ∃ y', y' = g * y * g⁻¹ := ⟨_, rfl⟩
  have hy'2 : y'⁻¹ = y' := by
    rw [hy', show (g * y * g⁻¹)⁻¹ = g * y⁻¹ * g⁻¹ by group, hyinv]
  have hy'inv : ∀ a ∈ F, y' * a * y'⁻¹ = a⁻¹ := by
    intro a ha
    have h1 := hinv (g⁻¹ * a * g) (hconj a ha)
    calc y' * a * y'⁻¹ = g * (y * (g⁻¹ * a * g) * y⁻¹) * g⁻¹ := by rw [hy']; group
    _ = g * (g⁻¹ * a * g)⁻¹ * g⁻¹ := by rw [h1]
    _ = a⁻¹ := by group
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = y' * y := ⟨_, rfl⟩
  have hc₀C : c₀ ∈ centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ F := SetLike.mem_coe.mp ha
    have e1 : y * a = a⁻¹ * y := mul_inv_eq_iff_eq_mul.mp (hinv a ha')
    have e2 : y' * a⁻¹ = a * y' := by
      have h3 := hy'inv a⁻¹ (inv_mem ha')
      rw [inv_inv] at h3
      exact mul_inv_eq_iff_eq_mul.mp h3
    rw [hc₀]
    calc a * (y' * y) = (a * y') * y := by group
    _ = (y' * a⁻¹) * y := by rw [e2]
    _ = y' * (a⁻¹ * y) := by group
    _ = y' * (y * a) := by rw [e1]
    _ = y' * y * a := by group
  have hc₀inv : y * c₀ * y⁻¹ = c₀⁻¹ := by
    rw [hc₀]
    calc y * (y' * y) * y⁻¹ = y * y' := by group
    _ = y⁻¹ * y'⁻¹ := by rw [hyinv, hy'2]
    _ = (y' * y)⁻¹ := (mul_inv_rev y' y).symm
  have hm : ¬ 2 ∣ orderOf c₀ := fun h => hodd (dvd_trans h (Subgroup.orderOf_dvd_natCard _ hc₀C))
  obtain ⟨k, hk⟩ : ∃ k, k = (orderOf c₀ + 1) / 2 := ⟨_, rfl⟩
  have hk2 : k + k = orderOf c₀ + 1 := by omega
  obtain ⟨c, hc⟩ : ∃ c, c = c₀ ^ k := ⟨_, rfl⟩
  have hcC : c ∈ centralizer (F : Set G) := by
    rw [hc]
    exact pow_mem hc₀C k
  have hcc : c * c = c₀ := by
    rw [hc, ← pow_add, hk2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    rw [hc, ← inv_pow, ← hc₀inv, conj_pow]
  have hyc' : y * c⁻¹ * y⁻¹ = c := by
    calc y * c⁻¹ * y⁻¹ = (y * c * y⁻¹)⁻¹ := by group
    _ = c := by rw [hyc, inv_inv]
  have hcyc : c * y * c⁻¹ = y' := by
    calc c * y * c⁻¹ = c * (y * c⁻¹ * y⁻¹) * y := by group
    _ = c * c * y := by rw [hyc']
    _ = c₀ * y := by rw [hcc]
    _ = y' * y * y := by rw [hc₀]
    _ = y' := by rw [mul_assoc, hy2, mul_one]
  refine ⟨c, hcC, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hkey : c⁻¹ * g * y * (c⁻¹ * g)⁻¹ = y := by
    calc c⁻¹ * g * y * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * y * g⁻¹) * c := by group
    _ = c⁻¹ * y' * c := by rw [hy']
    _ = y := by rw [← hcyc]; group
  exact mul_inv_eq_iff_eq_mul.mp hkey

end R10A1

section R10A2

open CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem r10a2_exists_mem_conj {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, ∀ x : G, x ∈ P' ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : G) = (g : G)⁻¹ * x * g := hzx
    have hx : x = (g : G) * z * (g : G)⁻¹ := by
      rw [hzx']
      group
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    exact ⟨g * z * g⁻¹, (key _).mpr (by rw [e]; exact hz), hx.symm⟩

theorem exists_inv_mul_mem_normalizer_of_isSylowOf {C N Q : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hCN : C ≤ N) (hnorm : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C)
    (hQ : IsSylowOf p Q C) :
    ∀ n ∈ N, ∃ c ∈ C, c⁻¹ * n ∈ N ⊓ normalizer (Q : Set G) := by
  intro n hn
  have hQC : Q ≤ C := hQ.le
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
  have hle : Q.map (MulAut.conj n).toMonoidHom ≤ C := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hnorm n hn y (hQC hy)
  have hcard : Nat.card (Q.map (MulAut.conj n).toMonoidHom) =
      p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective hinj, hQ.card_eq]
  obtain ⟨k, hk, hkQ⟩ := r10a2_exists_mem_conj (isSylowOf_of_card hle hcard) hQ
  refine ⟨k⁻¹, C.inv_mem hk, ?_⟩
  rw [inv_inv]
  refine Subgroup.mem_inf.mpr ⟨N.mul_mem (hCN hk) hn, Subgroup.mem_normalizer_iff.mpr ?_⟩
  intro x
  have h1 := hkQ (k * n * x * (k * n)⁻¹)
  have h2 : k⁻¹ * (k * n * x * (k * n)⁻¹) * k = (MulAut.conj n).toMonoidHom x := by
    show k⁻¹ * (k * n * x * (k * n)⁻¹) * k = n * x * n⁻¹
    group
  rw [h2, Subgroup.mem_map_iff_mem hinj] at h1
  exact h1.symm

end R10A2

section R10A3

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mul_self_mem_centralizer_of_mem_normalizer {x m : G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hm : m ∈ normalizer (zpowers x : Set G)) : m * m ∈ centralizer ({x} : Set G) := by
  have hc : m * x * m⁻¹ ∈ zpowers x :=
    (Subgroup.mem_set_normalizer_iff.mp hm x).mp (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have hred : x ^ k = x ^ (k % 3) := by
    have hk' : k = k % 3 + 3 * (k / 3) := by omega
    calc x ^ k = x ^ (k % 3 + 3 * (k / 3)) := congrArg (fun j : ℤ => x ^ j) hk'
      _ = x ^ (k % 3) * (x ^ (3 : ℤ)) ^ (k / 3) := by rw [zpow_add, zpow_mul]
      _ = x ^ (k % 3) := by rw [h3, one_zpow, mul_one]
  have hx2 : x ^ (2 : ℤ) = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 from rfl, h3]
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hred] at hk
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exfalso
    apply hx1
    rw [h0, zpow_zero] at hk
    calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
      _ = 1 := by rw [← hk]; group
  · rw [h1, zpow_one] at hk
    have hc2 : m * x = x * m := by
      calc m * x = (m * x * m⁻¹) * m := by group
        _ = x * m := by rw [← hk]
    calc m * m * x = m * (m * x) := by rw [mul_assoc]
      _ = m * (x * m) := by rw [hc2]
      _ = m * x * m := by rw [mul_assoc]
      _ = x * m * m := by rw [hc2]
      _ = x * (m * m) := by rw [mul_assoc]
  · rw [h2, hx2] at hk
    have hd : m * x⁻¹ = x * m := by
      calc m * x⁻¹ = (m * x * m⁻¹)⁻¹ * m := by group
        _ = (x⁻¹)⁻¹ * m := by rw [← hk]
        _ = x * m := by rw [inv_inv]
    have hc2 : m * x = x⁻¹ * m := by
      calc m * x = (m * x * m⁻¹) * m := by group
        _ = x⁻¹ * m := by rw [← hk]
    calc m * m * x = m * (m * x) := by rw [mul_assoc]
      _ = m * (x⁻¹ * m) := by rw [hc2]
      _ = m * x⁻¹ * m := by rw [mul_assoc]
      _ = x * m * m := by rw [hd]
      _ = x * (m * m) := by rw [mul_assoc]

theorem mem_of_mul_self_mem_of_odd {A : Subgroup G} {h : G} (hodd : ¬ 2 ∣ orderOf h)
    (hh : h * h ∈ A) : h ∈ A := by
  have hk : h = (h * h) ^ ((orderOf h + 1) / 2) := by
    have h2 : 2 * ((orderOf h + 1) / 2) = orderOf h + 1 := by omega
    rw [← pow_two, ← pow_mul, h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmem := pow_mem hh ((orderOf h + 1) / 2)
  rw [← hk] at hmem
  exact hmem

end R10A3

section R10A5

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a5_conj_mem_centralizer {F : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (F : Set G)) (hc : c ∈ centralizer (F : Set G)) :
    n * c * n⁻¹ ∈ centralizer (F : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : n⁻¹ * a * n ∈ (F : Set G) := (Subgroup.mem_set_normalizer_iff''.mp hn a).mp ha
  have key : n⁻¹ * a * n * c = c * (n⁻¹ * a * n) := Subgroup.mem_centralizer_iff.mp hc _ ha'
  calc a * (n * c * n⁻¹) = n * (n⁻¹ * a * n * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [key]
    _ = n * c * n⁻¹ * a := by group

private def r10a5_prod {C Z : Subgroup G} (hZ : ∀ a ∈ Z, ∀ c ∈ C, a * c * a⁻¹ ∈ C) :
    Subgroup G where
  carrier := {g | ∃ c ∈ C, ∃ a ∈ Z, g = c * a}
  mul_mem' := by
    rintro _ _ ⟨c₁, hc₁, a₁, ha₁, rfl⟩ ⟨c₂, hc₂, a₂, ha₂, rfl⟩
    exact ⟨c₁ * (a₁ * c₂ * a₁⁻¹), mul_mem hc₁ (hZ a₁ ha₁ c₂ hc₂), a₁ * a₂,
      mul_mem ha₁ ha₂, by group⟩
  one_mem' := ⟨1, one_mem C, 1, one_mem Z, by simp⟩
  inv_mem' := by
    rintro _ ⟨c, hc, a, ha, rfl⟩
    exact ⟨a⁻¹ * c⁻¹ * a⁻¹⁻¹, hZ a⁻¹ (inv_mem ha) c⁻¹ (inv_mem hc), a⁻¹, inv_mem ha,
      by group⟩

private theorem r10a5_mem_prod {C Z : Subgroup G} (hZ : ∀ a ∈ Z, ∀ c ∈ C, a * c * a⁻¹ ∈ C)
    {g : G} : g ∈ r10a5_prod hZ ↔ ∃ c ∈ C, ∃ a ∈ Z, g = c * a :=
  Iff.rfl

theorem exists_inv_mul_mem_of_odd {M F : Subgroup G} {x y : G} (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hinv : ∀ a ∈ F, y * a * y⁻¹ = a⁻¹) (hodd : ¬ 2 ∣ Nat.card (centralizer (F : Set G)))
    (hyM : centralizer ({y} : Set G) ≤ M) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hxM : x ∈ M)
    (hxC : x ∈ centralizer (F : Set G))
    (hxS : IsSylowOf 3 (zpowers x) (centralizer (F : Set G))) :
    ∀ h ∈ normalizer (F : Set G), ¬ 2 ∣ orderOf h →
      ∃ c ∈ centralizer (F : Set G), c⁻¹ * h ∈ M ⊓ centralizer ({x} : Set G) := by
  intro h hh hoddh
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCN : centralizer (F : Set G) ≤ normalizer (F : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hnorm : ∀ n ∈ normalizer (F : Set G), ∀ c ∈ centralizer (F : Set G),
      n * c * n⁻¹ ∈ centralizer (F : Set G) :=
    fun n hn c hc => r10a5_conj_mem_centralizer hn hc
  obtain ⟨c₁, hc₁, hn₁⟩ := exists_inv_mul_mem_centralizer_of_inverts hy1 hy2 hinv hodd h hh
  have hn₁N : c₁⁻¹ * h ∈ normalizer (F : Set G) := mul_mem (hCN (inv_mem hc₁)) hh
  have hn₁M : c₁⁻¹ * h ∈ M := hyM hn₁
  have hCN' : centralizer (F : Set G) ⊓ M ≤ normalizer (F : Set G) ⊓ M := by
    intro g hg
    exact Subgroup.mem_inf.mpr ⟨hCN (Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2⟩
  have hnormCM : ∀ n ∈ normalizer (F : Set G) ⊓ M, ∀ c ∈ centralizer (F : Set G) ⊓ M,
      n * c * n⁻¹ ∈ centralizer (F : Set G) ⊓ M := by
    intro n hn c hc
    obtain ⟨hnN, hnM⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨hcC, hcM⟩ := Subgroup.mem_inf.mp hc
    exact Subgroup.mem_inf.mpr ⟨hnorm n hnN c hcC, mul_mem (mul_mem hnM hcM) (inv_mem hnM)⟩
  have hxCM : zpowers x ≤ centralizer (F : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxC, hxM⟩)
  have hS' : IsSylowOf 3 (zpowers x) (centralizer (F : Set G) ⊓ M) :=
    hxS.of_le hxCM inf_le_left
  obtain ⟨c₂, hc₂, hm⟩ := exists_inv_mul_mem_normalizer_of_isSylowOf hCN' hnormCM hS'
    (c₁⁻¹ * h) (Subgroup.mem_inf.mpr ⟨hn₁N, hn₁M⟩)
  obtain ⟨m, hmdef⟩ : ∃ m, c₂⁻¹ * (c₁⁻¹ * h) = m := ⟨_, rfl⟩
  rw [hmdef] at hm
  have hhm : h = c₁ * c₂ * m := by
    rw [← hmdef]
    group
  obtain ⟨hmNM, hmZ⟩ := Subgroup.mem_inf.mp hm
  obtain ⟨hmN, hmM⟩ := Subgroup.mem_inf.mp hmNM
  have hcc : c₁ * c₂ ∈ centralizer (F : Set G) :=
    mul_mem hc₁ (Subgroup.mem_inf.mp hc₂).1
  have hmmx : m * m ∈ centralizer ({x} : Set G) :=
    mul_self_mem_centralizer_of_mem_normalizer hx1 hx3 hmZ
  have hZ : ∀ a ∈ (M ⊓ centralizer ({x} : Set G)) ⊓ normalizer (F : Set G),
      ∀ c ∈ centralizer (F : Set G), a * c * a⁻¹ ∈ centralizer (F : Set G) :=
    fun a ha c hc => hnorm a (Subgroup.mem_inf.mp ha).2 c hc
  have hmmZ : m * m ∈ (M ⊓ centralizer ({x} : Set G)) ⊓ normalizer (F : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem hmM hmM, hmmx⟩, mul_mem hmN hmN⟩
  have hhh : h * h ∈ r10a5_prod hZ := by
    refine (r10a5_mem_prod hZ).mpr ⟨c₁ * c₂ * (m * (c₁ * c₂) * m⁻¹),
      mul_mem hcc (hnorm m hmN _ hcc), m * m, hmmZ, ?_⟩
    rw [hhm]
    group
  obtain ⟨c, hc, a, ha, hha⟩ := (r10a5_mem_prod hZ).mp
    (mem_of_mul_self_mem_of_odd (A := r10a5_prod hZ) hoddh hhh)
  refine ⟨c, hc, ?_⟩
  have hca : c⁻¹ * h = a := by
    rw [hha]
    group
  rw [hca]
  exact (Subgroup.mem_inf.mp ha).1

end R10A5

section R10A4

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a4_isPGroup_zpowers {r s : ℕ} {x : G} (hx : x ^ (r ^ s) = 1) :
    IsPGroup r (zpowers x) := by
  intro g
  refine ⟨s, Subtype.ext ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast (x ^ m) (r ^ s), ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem r10a4_mem_of_isCoprime {C : Subgroup G} {h : G} {a b : ℕ}
    (ha : h ^ a ∈ C) (hb : h ^ b ∈ C) (hab : IsCoprime (a : ℤ) (b : ℤ)) : h ∈ C := by
  obtain ⟨u, v, huv⟩ := hab
  have e1 : h ^ ((a : ℤ) * u + (b : ℤ) * v) = (h ^ a) ^ u * (h ^ b) ^ v := by
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have e2 : h ^ ((a : ℤ) * u + (b : ℤ) * v) = h := by
    rw [show (a : ℤ) * u + (b : ℤ) * v = 1 by linear_combination huv, zpow_one]
  have key : h = (h ^ a) ^ u * (h ^ b) ^ v := e2.symm.trans e1
  rw [key]
  exact C.mul_mem (C.zpow_mem ha u) (C.zpow_mem hb v)

private theorem r10a4_isCoprime_pow {r o : ℕ} (hr : r.Prime) (hdvd : ¬ r ∣ o) (s : ℕ) :
    IsCoprime (o : ℤ) ((r ^ s : ℕ) : ℤ) := by
  apply Nat.isCoprime_iff_coprime.2
  exact Nat.Coprime.pow_right s ((Nat.Prime.coprime_iff_not_dvd hr).2 hdvd).symm

theorem exists_pow_isPGroup_not_mem_of_pow_mem {h : G} {C : Subgroup G} {r e : ℕ}
    (hr : r.Prime) (hmod : h ^ (r ^ e) ∈ C) (hh : h ∉ C) :
    ∃ i : ℕ, IsPGroup r (zpowers (h ^ i)) ∧ h ^ i ∉ C := by
  have hpos : 0 < orderOf h := orderOf_pos h
  obtain ⟨s, o', hdvd, hdecomp⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' r hr.one_lt.ne'
  have hpow : (h ^ o') ^ (r ^ s) = 1 := by
    rw [← pow_mul, show o' * r ^ s = orderOf h by rw [hdecomp, Nat.mul_comm]]
    exact pow_orderOf_eq_one h
  refine ⟨o', r10a4_isPGroup_zpowers hpow, fun hA => hh ?_⟩
  exact r10a4_mem_of_isCoprime hA hmod (r10a4_isCoprime_pow hr hdvd e)

private theorem r10a4_exists_aux {C : Subgroup G} (n : ℕ) :
    ∀ h : G, orderOf h = n → h ∉ C →
      ∃ r : ℕ, r.Prime ∧ r ∣ orderOf h ∧ ∃ i : ℕ, IsPGroup r (zpowers (h ^ i)) ∧ h ^ i ∉ C := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn hh
    have hpos : 0 < orderOf h := orderOf_pos h
    have hn0 : n ≠ 0 := by
      rw [← hn]
      exact hpos.ne'
    have hn1 : n ≠ 1 := by
      intro h1
      apply hh
      rw [orderOf_eq_one_iff.1 (hn.trans h1)]
      exact C.one_mem
    obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨s, o', hdvd, hdecomp⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 r hr.one_lt.ne'
    have hs : s ≠ 0 := by
      rintro rfl
      apply hdvd
      rw [pow_zero, one_mul] at hdecomp
      rw [← hdecomp]
      exact hrn
    have ho' : o' ≠ 0 := by
      rintro rfl
      apply hn0
      rw [hdecomp, mul_zero]
    have hoo : o' ∣ n := by
      rw [hdecomp]
      exact dvd_mul_left _ _
    by_cases hA : h ^ o' ∈ C
    · have hh' : h ^ (r ^ s) ∉ C := fun hm =>
        hh (r10a4_mem_of_isCoprime hA hm (r10a4_isCoprime_pow hr hdvd s))
      have hdvd' : orderOf (h ^ (r ^ s)) ∣ o' := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, ← hdecomp, ← hn]
        exact pow_orderOf_eq_one h
      have hlt : orderOf (h ^ (r ^ s)) < n := by
        have h1 : orderOf (h ^ (r ^ s)) ≤ o' := Nat.le_of_dvd (Nat.pos_of_ne_zero ho') hdvd'
        have h2 : 2 ≤ r ^ s := le_trans hr.two_le (Nat.le_self_pow hs r)
        have h3 : 2 * o' ≤ r ^ s * o' := Nat.mul_le_mul h2 (le_refl o')
        have h4 : o' < 2 * o' := by
          have := Nat.pos_of_ne_zero ho'
          omega
        rw [hdecomp]
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le h4 h3)
      obtain ⟨r', hr', hr'd, i', hi1, hi2⟩ :=
        ih (orderOf (h ^ (r ^ s))) hlt (h ^ (r ^ s)) rfl hh'
      refine ⟨r', hr', ?_, r ^ s * i', ?_, ?_⟩
      · rw [hn]
        exact hr'd.trans (hdvd'.trans hoo)
      · rw [pow_mul]
        exact hi1
      · rw [pow_mul]
        exact hi2
    · have hpow : (h ^ o') ^ (r ^ s) = 1 := by
        rw [← pow_mul, show o' * r ^ s = orderOf h by rw [hn, hdecomp, Nat.mul_comm]]
        exact pow_orderOf_eq_one h
      refine ⟨r, hr, ?_, o', r10a4_isPGroup_zpowers hpow, hA⟩
      rw [hn]
      exact hrn

theorem exists_isPGroup_pow_not_mem {h : G} {C : Subgroup G} (hh : h ∉ C) :
    ∃ r : ℕ, r.Prime ∧ r ∣ orderOf h ∧
      ∃ i : ℕ, IsPGroup r (zpowers (h ^ i)) ∧ h ^ i ∉ C :=
  r10a4_exists_aux (orderOf h) h rfl hh

end R10A4

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
