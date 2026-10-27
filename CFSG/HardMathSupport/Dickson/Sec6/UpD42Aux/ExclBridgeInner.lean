module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Excl
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.Mathlib.GroupTheory.SubgroupSupCommute
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem zpowers_subgroupOf_coe {X : Type*} [Group X] (L : Subgroup X) {l : X} (hl : l ∈ L) :
    Subgroup.zpowers (⟨l, hl⟩ : ↥L) = (Subgroup.zpowers l).subgroupOf L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem mem_centralizer_of_conj_eq_inner {X : Type*} [Group X] {L : Subgroup X} {b s : X}
    (hsb : ∀ x ∈ L, b * x * b⁻¹ = s * x * s⁻¹) :
    s⁻¹ * b ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconj : (s⁻¹ * b) * x * (s⁻¹ * b)⁻¹ = x := by
    calc (s⁻¹ * b) * x * (s⁻¹ * b)⁻¹ = s⁻¹ * (b * x * b⁻¹) * s := by group
      _ = s⁻¹ * (s * x * s⁻¹) * s := by rw [hsb x hx]
      _ = x := by group
  calc x * (s⁻¹ * b) = ((s⁻¹ * b) * x * (s⁻¹ * b)⁻¹) * (s⁻¹ * b) := by rw [hconj]
    _ = (s⁻¹ * b) * x := by group

theorem exists_zpow_mul_zpow_of_mem_sup_zpowers {X : Type*} [Group X] {b z c : X}
    (hz : z ∈ Subgroup.center X) (hc : c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z) :
    ∃ i j : ℤ, c = b ^ i * z ^ j := by
  have hzcomm : ∀ v ∈ Subgroup.zpowers z, ∀ u : X, u * v = v * u := by
    intro v hv u
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact Subgroup.mem_center_iff.mp ((Subgroup.center X).zpow_mem hz n) u
  obtain ⟨u, hu, v, hv, hcuv⟩ :=
    (Subgroup.mem_sup_iff_of_forall_commute (fun x _ y hy => hzcomm y hy x)).mp hc
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact ⟨i, j, by rw [hcuv, ← hi, ← hj]⟩

theorem exists_mem_mul_zpow_of_eq_zpow {X : Type*} [Group X] {L : Subgroup X} {b z c s : X}
    {j : ℤ} (hs : s ∈ L) (hb : b = s * c) (hc : c = z ^ j) :
    ∃ ℓ ∈ L, ∃ k : ℤ, b = ℓ * z ^ k := by
  refine ⟨s, hs, j, ?_⟩
  rw [hb, hc]

theorem mem_center_of_eq_mul_zpow {X : Type*} [Group X] {b z c s : X}
    {j : ℤ} (hz : z ∈ Subgroup.center X)
    (hb : b = s * c) (hc : c = b * z ^ j) : s ∈ Subgroup.center X := by
  have hzk : z ^ j ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz j
  have hcomm : Commute b (z ^ j) :=
    (commute_iff_eq b (z ^ j)).mpr (Subgroup.mem_center_iff.mp hzk b)
  have hzc : z ^ (-j) ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz (-j)
  have hs_eq : s = z ^ (-j) := by
    have h1 : b * c⁻¹ = s := by rw [hb]; group
    rw [← h1, hc]
    calc b * (b * z ^ j)⁻¹ = b * ((z ^ j)⁻¹ * b⁻¹) := by rw [mul_inv_rev]
      _ = (b * (z ^ j)⁻¹) * b⁻¹ := by group
      _ = ((z ^ j)⁻¹ * b) * b⁻¹ := by rw [hcomm.inv_right.eq]
      _ = (z ^ j)⁻¹ := by group
      _ = z ^ (-j) := by rw [zpow_neg]
  rw [hs_eq]
  exact hzc

theorem exists_mem_mul_zpow_of_eq_sq_mul_zpow {X : Type*} [Group X] {L : Subgroup X}
    {b z c s : X} {j : ℤ} (hb3 : b ^ 3 = 1) (hz : z ∈ Subgroup.center X) (hs : s ∈ L)
    (hb : b = s * c) (hc : c = b ^ (2 : ℤ) * z ^ j) :
    ∃ ℓ ∈ L, ∃ k : ℤ, b = ℓ * z ^ k := by
  have hzk : z ^ j ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz j
  have hcomm : Commute b (z ^ j) :=
    (commute_iff_eq b (z ^ j)).mpr (Subgroup.mem_center_iff.mp hzk b)
  have hzi : (z ^ j)⁻¹ ∈ Subgroup.center X := (Subgroup.center X).inv_mem hzk
  have hb2nat : b ^ 2 = b⁻¹ := by
    have h : b ^ 2 * b = 1 := by rw [← pow_succ, hb3]
    exact eq_inv_of_mul_eq_one_left h
  have hb2 : b ^ (2 : ℤ) = b⁻¹ := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hb2nat
  have hs2 : s = b⁻¹ * z ^ (-j) := by
    have h1 : b * c⁻¹ = s := by rw [hb]; group
    rw [← h1, hc, hb2]
    calc b * (b⁻¹ * z ^ j)⁻¹ = b * ((z ^ j)⁻¹ * b) := by rw [mul_inv_rev, inv_inv]
      _ = (b * (z ^ j)⁻¹) * b := by group
      _ = ((z ^ j)⁻¹ * b) * b := by rw [hcomm.inv_right.eq]
      _ = (z ^ j)⁻¹ * (b * b) := by group
      _ = (z ^ j)⁻¹ * b⁻¹ := by rw [← pow_two, hb2nat]
      _ = b⁻¹ * z ^ (-j) := by
        rw [zpow_neg]
        exact (Subgroup.mem_center_iff.mp hzi b⁻¹).symm
  have hbinv : b⁻¹ = s * z ^ j := by
    rw [hs2]
    calc b⁻¹ = b⁻¹ * 1 := by rw [mul_one]
      _ = b⁻¹ * (z ^ (-j) * z ^ j) := by
        rw [← zpow_add, show -j + j = 0 by ring, zpow_zero]
      _ = (b⁻¹ * z ^ (-j)) * z ^ j := by group
  refine ⟨s⁻¹, L.inv_mem hs, -j, ?_⟩
  calc b = (b⁻¹)⁻¹ := (inv_inv b).symm
    _ = (s * z ^ j)⁻¹ := by rw [hbinv]
    _ = (z ^ j)⁻¹ * s⁻¹ := by rw [mul_inv_rev]
    _ = z ^ (-j) * s⁻¹ := by rw [zpow_neg]
    _ = s⁻¹ * z ^ (-j) := by
      rw [zpow_neg]
      exact (Subgroup.mem_center_iff.mp hzi s⁻¹).symm

theorem exists_mem_mul_zpow_of_mem_sup {X : Type*} [Group X] {L : Subgroup X} {b z c s : X}
    (hb3 : b ^ 3 = 1) (hz : z ∈ Subgroup.center X) (hs : s ∈ L) (hb : b = s * c)
    (hcL : c ∈ Subgroup.centralizer (L : Set X))
    (hc : c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z)
    (hnt : ∃ y ∈ L, b * y ≠ y * b) :
    ∃ ℓ ∈ L, ∃ k : ℤ, b = ℓ * z ^ k := by
  obtain ⟨i, j, hc'⟩ := exists_zpow_mul_zpow_of_mem_sup_zpowers hz hc
  have hbi : b ^ i = b ^ (i % 3) := zpow_eq_zpow_emod i (by simpa using hb3)
  rcases show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 from by omega with hr | hr | hr
  · exact exists_mem_mul_zpow_of_eq_zpow hs hb (by rw [hc', hbi, hr, zpow_zero, one_mul])
  · exfalso
    obtain ⟨y, hy, hne⟩ := hnt
    have hscen : s ∈ Subgroup.center X :=
      mem_center_of_eq_mul_zpow hz hb (by rw [hc', hbi, hr, zpow_one])
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hcL y hy).symm
    refine hne ?_
    calc b * y = (s * c) * y := by rw [hb]
      _ = s * (c * y) := by group
      _ = s * (y * c) := by rw [hcy]
      _ = (s * y) * c := by group
      _ = (y * s) * c := by rw [Subgroup.mem_center_iff.mp hscen y]
      _ = y * (s * c) := by group
      _ = y * b := by rw [hb]
  · exact exists_mem_mul_zpow_of_eq_sq_mul_zpow hb3 hz hs hb (by rw [hc', hbi, hr])

theorem exists_mem_mul_zpow_of_conj_inner {X : Type} [Group X] {L J : Subgroup X}
    {b z : X} (hLc : Subgroup.center ↥L = ⊥) (hJL : J ≤ L) (hb3 : b ^ 3 = 1)
    (hbnt : ∃ y ∈ L, y * b ≠ b * y) (hz : z ∈ Subgroup.center X)
    (hC : ∀ y ∈ Subgroup.centralizer ({b} : Set X), y ∈ Subgroup.centralizer (J : Set X) →
      ∀ m : ℕ, y ^ 3 ^ m = 1 → y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z)
    {s : X} (hs : s ∈ L) (hsb : ∀ x ∈ L, b * x * b⁻¹ = s * x * s⁻¹) :
    ∃ ℓ ∈ L, ∃ k : ℤ, b = ℓ * z ^ k := by
  set c : X := s⁻¹ * b with hcdef
  have hcL : c ∈ Subgroup.centralizer (L : Set X) := mem_centralizer_of_conj_eq_inner hsb
  have hsc : Commute s c :=
    (commute_iff_eq s c).mpr (Subgroup.mem_centralizer_iff.mp hcL s hs)
  have hb_eq : b = s * c := by rw [hcdef]; group
  have hcube : s ^ 3 * c ^ 3 = 1 := by
    rw [← hsc.mul_pow, ← hb_eq]
    exact hb3
  have hc3inv : c ^ 3 = (s ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hcube
  have hc3L : c ^ 3 ∈ L := by rw [hc3inv]; exact L.inv_mem (L.pow_mem hs 3)
  have hc3center : (⟨c ^ 3, hc3L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    exact (Commute.pow_right ((commute_iff_eq (y : X) c).mpr
      (Subgroup.mem_centralizer_iff.mp hcL (y : X) y.2)) 3).eq
  have hc3bot : c ^ 3 = 1 := by
    have h1 : (⟨c ^ 3, hc3L⟩ : ↥L) = 1 := by
      rw [hLc] at hc3center
      exact Subgroup.mem_bot.mp hc3center
    exact congrArg Subtype.val h1
  have hcb : c ∈ Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    calc b * c = (s * c) * c := by rw [hb_eq]
      _ = (c * s) * c := by rw [hsc.eq]
      _ = c * (s * c) := by group
      _ = c * b := by rw [← hb_eq]
  have hcJ : c ∈ Subgroup.centralizer (J : Set X) := Subgroup.centralizer_le hJL hcL
  have hmem : c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z :=
    hC c hcb hcJ 1 (by simpa using hc3bot)
  have hnt : ∃ y ∈ L, b * y ≠ y * b := by
    obtain ⟨y, hy, h⟩ := hbnt
    exact ⟨y, hy, fun h' => h h'.symm⟩
  exact exists_mem_mul_zpow_of_mem_sup hb3 hz hs hb_eq hcL hmem hnt

theorem eq_mul_zpow_neg_of_eq_mul_zpow {X : Type*} [Group X] {b z ℓ : X} {k : ℤ}
    (hb : b = ℓ * z ^ k) : ℓ = b * z ^ (-k) := by
  rw [hb]
  calc ℓ = ℓ * 1 := by rw [mul_one]
    _ = ℓ * (z ^ k * z ^ (-k)) := by
      rw [← zpow_add, show k + -k = 0 by ring, zpow_zero]
    _ = (ℓ * z ^ k) * z ^ (-k) := by group

theorem conj_mul_zpow_eq {X : Type*} [Group X] {b z ℓ y : X} {k : ℤ}
    (hz : z ∈ Subgroup.center X) (hb : b = ℓ * z ^ k) :
    y * b * y⁻¹ = (y * ℓ * y⁻¹) * z ^ k := by
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  have hconjz : y * z ^ k * y⁻¹ = z ^ k := by
    rw [Subgroup.mem_center_iff.mp hzk y]
    group
  rw [hb]
  calc y * (ℓ * z ^ k) * y⁻¹ = (y * ℓ * y⁻¹) * (y * z ^ k * y⁻¹) := by group
    _ = (y * ℓ * y⁻¹) * z ^ k := by rw [hconjz]

theorem mem_zpowers_of_mem_sup_zpowers_of_mem {X : Type*} [Group X] {L : Subgroup X}
    {b z ℓ : X} {k : ℤ} (hLc : Subgroup.center ↥L = ⊥) (hz : z ∈ Subgroup.center X)
    (hb : b = ℓ * z ^ k) (hℓ : ℓ ∈ L) {y : X} (hyL : y ∈ L)
    (hmem : y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z) :
    y ∈ Subgroup.zpowers ℓ := by
  obtain ⟨i, j, hy'⟩ := exists_zpow_mul_zpow_of_mem_sup_zpowers hz hmem
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  have hcomm : Commute ℓ (z ^ k) :=
    (commute_iff_eq ℓ (z ^ k)).mpr (Subgroup.mem_center_iff.mp hzk ℓ)
  have hbi : b ^ i = ℓ ^ i * z ^ (i * k) := by
    rw [hb, hcomm.mul_zpow, ← zpow_mul, mul_comm k i]
  have hy'' : y = ℓ ^ i * z ^ (i * k + j) := by
    rw [hy', hbi, mul_assoc, ← zpow_add]
  have hzc : z ^ (i * k + j) ∈ Subgroup.center X :=
    (Subgroup.center X).zpow_mem hz (i * k + j)
  have hzL : z ^ (i * k + j) ∈ L := by
    have h1 : z ^ (i * k + j) = y * (ℓ ^ i)⁻¹ := by
      rw [hy'']
      symm
      calc ℓ ^ i * z ^ (i * k + j) * (ℓ ^ i)⁻¹
          = z ^ (i * k + j) * (ℓ ^ i) * (ℓ ^ i)⁻¹ := by
            rw [Subgroup.mem_center_iff.mp hzc (ℓ ^ i)]
        _ = z ^ (i * k + j) := by group
    rw [h1]
    exact L.mul_mem hyL (L.inv_mem (L.zpow_mem hℓ i))
  have hzcenter : (⟨z ^ (i * k + j), hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    ext
    exact Subgroup.mem_center_iff.mp ((Subgroup.center X).zpow_mem hz (i * k + j)) (w : X)
  have hzone : z ^ (i * k + j) = 1 := by
    rw [hLc] at hzcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hzcenter)
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨i, ?_⟩
  rw [hy'', hzone, mul_one]

theorem centralizer_singleton_subgroupOf_mul_zpow {X : Type*} [Group X] {L : Subgroup X}
    {b z ℓ : X} {k : ℤ} (hz : z ∈ Subgroup.center X) (hb : b = ℓ * z ^ k) (hℓ : ℓ ∈ L) :
    Subgroup.centralizer ({⟨ℓ, hℓ⟩} : Set ↥L) =
      (L ⊓ Subgroup.centralizer ({b} : Set X)).subgroupOf L := by
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  have hzi : z ^ (-k) ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz (-k)
  have hℓ_eq : ℓ = b * z ^ (-k) := eq_mul_zpow_neg_of_eq_mul_zpow hb
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 : (x : X) * ℓ = ℓ * x :=
      (congrArg Subtype.val (h ⟨ℓ, hℓ⟩ (by simp))).symm
    calc b * (x : X) = (ℓ * z ^ k) * x := by rw [hb]
      _ = ℓ * (z ^ k * x) := by group
      _ = ℓ * (x * z ^ k) := by rw [Subgroup.mem_center_iff.mp hzk x]
      _ = (ℓ * x) * z ^ k := by group
      _ = (x * ℓ) * z ^ k := by rw [← h1]
      _ = x * (ℓ * z ^ k) := by group
      _ = (x : X) * b := by rw [← hb]
  · rintro ⟨-, hb'⟩ y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 : b * (x : X) = (x : X) * b := hb' b (by simp)
    have h2 : (x : X) * z ^ (-k) = z ^ (-k) * (x : X) :=
      Subgroup.mem_center_iff.mp hzi x
    ext
    calc ℓ * (x : X) = (b * z ^ (-k)) * x := by rw [hℓ_eq]
      _ = (b * x) * z ^ (-k) := by rw [mul_assoc, ← h2, mul_assoc]
      _ = (x * b) * z ^ (-k) := by rw [h1]
      _ = x * (b * z ^ (-k)) := by group
      _ = (x : X) * ℓ := by rw [hℓ_eq]

theorem exists_mul_ne_mul_of_eq_mul_zpow {X : Type*} [Group X] {L : Subgroup X} {b z ℓ : X}
    {k : ℤ} (hz : z ∈ Subgroup.center X) (hb : b = ℓ * z ^ k) (hℓ : ℓ ∈ L)
    (hbnt : ∃ y ∈ L, y * b ≠ b * y) : ∃ a b' : ↥L, a * b' ≠ b' * a := by
  obtain ⟨y, hy, hne⟩ := hbnt
  refine ⟨⟨y, hy⟩, ⟨ℓ, hℓ⟩, ?_⟩
  intro h
  apply hne
  have h1 : y * ℓ = ℓ * y := congrArg Subtype.val h
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  calc y * b = y * (ℓ * z ^ k) := by rw [hb]
    _ = (y * ℓ) * z ^ k := by group
    _ = (ℓ * y) * z ^ k := by rw [h1]
    _ = ℓ * (y * z ^ k) := by group
    _ = ℓ * (z ^ k * y) := by rw [Subgroup.mem_center_iff.mp hzk y]
    _ = (ℓ * z ^ k) * y := by group
    _ = b * y := by rw [← hb]

theorem pow_three_eq_one_of_eq_mul_zpow {X : Type*} [Group X] {L : Subgroup X} {b z ℓ : X}
    {k : ℤ} (hLc : Subgroup.center ↥L = ⊥) (hz : z ∈ Subgroup.center X)
    (hb : b = ℓ * z ^ k) (hℓ : ℓ ∈ L) (hb3 : b ^ 3 = 1) : ℓ ^ 3 = 1 := by
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  have hcomm : Commute ℓ (z ^ k) :=
    (commute_iff_eq ℓ (z ^ k)).mpr (Subgroup.mem_center_iff.mp hzk ℓ)
  have hcube : ℓ ^ 3 * (z ^ k) ^ 3 = 1 := by
    rw [← hcomm.mul_pow, ← hb]
    exact hb3
  have hℓ3cent : ℓ ^ 3 ∈ Subgroup.center X := by
    have h : ℓ ^ 3 = ((z ^ k) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hcube
    rw [h]
    exact (Subgroup.center X).inv_mem ((Subgroup.center X).pow_mem hzk 3)
  have hmem : (⟨ℓ ^ 3, L.pow_mem hℓ 3⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    exact Subgroup.mem_center_iff.mp hℓ3cent (y : X)
  rw [hLc] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

theorem ne_one_of_eq_mul_zpow {X : Type*} [Group X] {L : Subgroup X} {b z ℓ : X} {k : ℤ}
    (hz : z ∈ Subgroup.center X) (hb : b = ℓ * z ^ k)
    (hbnt : ∃ y ∈ L, y * b ≠ b * y) : ℓ ≠ 1 := by
  intro hℓ1
  obtain ⟨y, hy, hne⟩ := hbnt
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  apply hne
  calc y * b = y * (ℓ * z ^ k) := by rw [hb]
    _ = y * z ^ k := by rw [hℓ1, one_mul]
    _ = z ^ k * y := Subgroup.mem_center_iff.mp hzk y
    _ = (ℓ * z ^ k) * y := by rw [hℓ1, one_mul]
    _ = b * y := by rw [← hb]

theorem mem_zpowers_of_mem_centralizer_subgroupOf {X : Type*} [Group X] {L J : Subgroup X}
    {b z ℓ : X} {k : ℤ} (hLc : Subgroup.center ↥L = ⊥) (hz : z ∈ Subgroup.center X)
    (hb : b = ℓ * z ^ k) (hℓ : ℓ ∈ L) (hJL : J ≤ L)
    (hC : ∀ y ∈ Subgroup.centralizer ({b} : Set X), y ∈ Subgroup.centralizer (J : Set X) →
      ∀ m : ℕ, y ^ 3 ^ m = 1 → y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z)
    (y : ↥L) (hyb : y ∈ Subgroup.centralizer ({⟨ℓ, hℓ⟩} : Set ↥L))
    (hyJ : y ∈ Subgroup.centralizer (J.subgroupOf L : Set ↥L)) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers (⟨ℓ, hℓ⟩ : ↥L) := by
  have hzk : z ^ k ∈ Subgroup.center X := (Subgroup.center X).zpow_mem hz k
  have hybx : (y : X) ∈ Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.mem_centralizer_iff] at hyb ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have h1 : ℓ * (y : X) = (y : X) * ℓ := congrArg Subtype.val (hyb ⟨ℓ, hℓ⟩ (by simp))
    calc b * (y : X) = (ℓ * z ^ k) * y := by rw [hb]
      _ = ℓ * (z ^ k * y) := by group
      _ = ℓ * (y * z ^ k) := by rw [Subgroup.mem_center_iff.mp hzk y]
      _ = (ℓ * y) * z ^ k := by group
      _ = (y * ℓ) * z ^ k := by rw [h1]
      _ = y * (ℓ * z ^ k) := by group
      _ = (y : X) * b := by rw [← hb]
  have hyJx : (y : X) ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff] at hyJ ⊢
    intro h hh
    have hhL : h ∈ L := hJL hh
    exact congrArg Subtype.val (hyJ ⟨h, hhL⟩ (Subgroup.mem_subgroupOf.mpr hh))
  have hy3x : (y : X) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hy3
  have hmem : (y : X) ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z :=
    hC y hybx hyJx 1 (by simpa using hy3x)
  have hres : (y : X) ∈ Subgroup.zpowers ℓ :=
    mem_zpowers_of_mem_sup_zpowers_of_mem hLc hz hb hℓ y.2 hmem
  rw [zpowers_subgroupOf_coe L hℓ, Subgroup.mem_subgroupOf]
  simpa using hres

theorem weaklyClosed_subgroupOf_of_mul_zpow {X : Type*} [Group X] {L A : Subgroup X}
    {b z ℓ : X} {k : ℤ} (hLc : Subgroup.center ↥L = ⊥) (hz : z ∈ Subgroup.center X)
    (hb : b = ℓ * z ^ k) (hℓ : ℓ ∈ L) (hAL : A ≤ L)
    (hwc : ∀ y : X, y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z ⊔ A →
      y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z) :
    ∀ y : ↥L, y * ⟨ℓ, hℓ⟩ * y⁻¹ ∈ Subgroup.zpowers ⟨ℓ, hℓ⟩ ⊔ A.subgroupOf L →
      y * ⟨ℓ, hℓ⟩ * y⁻¹ ∈ Subgroup.zpowers ⟨ℓ, hℓ⟩ := by
  intro y hy
  have hℓ_eq : ℓ = b * z ^ (-k) := eq_mul_zpow_neg_of_eq_mul_zpow hb
  have hℓsup : ℓ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z := by
    have h : b * z ^ (-k) ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z :=
      Subgroup.mul_mem_sup (Subgroup.mem_zpowers b) (Subgroup.zpow_mem_zpowers z (-k))
    rwa [← hℓ_eq] at h
  have hyX : (y : X) * ℓ * (y : X)⁻¹ ∈ Subgroup.zpowers ℓ ⊔ A := by
    rw [zpowers_subgroupOf_coe L hℓ,
      ← Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hℓ) hAL,
      Subgroup.mem_subgroupOf] at hy
    simpa using hy
  have hcl : (y : X) * ℓ * (y : X)⁻¹ ∈ (Subgroup.zpowers b ⊔ Subgroup.zpowers z) ⊔ A :=
    (sup_le ((Subgroup.zpowers_le.mpr hℓsup).trans le_sup_left) le_sup_right) hyX
  have hbig : (y : X) * b * (y : X)⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z ⊔ A := by
    rw [conj_mul_zpow_eq hz hb]
    exact ((Subgroup.zpowers b ⊔ Subgroup.zpowers z) ⊔ A).mul_mem hcl
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers z k)))
  have hconjℓ : (y : X) * ℓ * (y : X)⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z := by
    have h1 : (y : X) * ℓ * (y : X)⁻¹
        = ((y : X) * b * (y : X)⁻¹) * z ^ (-k) := by
      rw [conj_mul_zpow_eq hz hb, zpow_neg, mul_inv_cancel_right]
    rw [h1]
    exact (Subgroup.zpowers b ⊔ Subgroup.zpowers z).mul_mem (hwc (y : X) hbig)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers z (-k)))
  have hconjL : (y : X) * ℓ * (y : X)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem y.2 hℓ) (L.inv_mem y.2)
  have hres := mem_zpowers_of_mem_sup_zpowers_of_mem hLc hz hb hℓ hconjL hconjℓ
  rw [zpowers_subgroupOf_coe L hℓ, Subgroup.mem_subgroupOf]
  simpa using hres

theorem false_of_upD42ExclInnAt_of_mem_mul_zpow (hΩ : UpD42ExclInnAt IsOmegaTwoBigIndex)
    {X : Type} [Group X] [Finite X] {L J A : Subgroup X} {b z ℓ : X} {k : ℤ}
    (hLs : IsSimpleGroup ↥L) (hLt : IsCatalogLieIso ↥L IsOmegaTwoBigIndex) (hℓ : ℓ ∈ L)
    (hb : b = ℓ * z ^ k) (hz : z ∈ Subgroup.center X) (hb3 : b ^ 3 = 1)
    (hbnt : ∃ y ∈ L, y * b ≠ b * y)
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b} : Set X)) J)
    (hJD : IsCatalogLieIso ↥J IsD42Index) (hAJ : A ≤ J) (hA : IsElemAbelian 3 A)
    (hA4 : Nat.card A = 3 ^ 4)
    (hC : ∀ y ∈ Subgroup.centralizer ({b} : Set X), y ∈ Subgroup.centralizer (J : Set X) →
      ∀ m : ℕ, y ^ 3 ^ m = 1 → y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z)
    (hwc : ∀ y : X, y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z ⊔ A →
      y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z) : False := by
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hAL : A ≤ L := hAJ.trans hJL
  have hLnab : ∃ a b' : ↥L, a * b' ≠ b' * a :=
    exists_mul_ne_mul_of_eq_mul_zpow hz hb hℓ hbnt
  have hLc : Subgroup.center ↥L = ⊥ := by
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
    obtain ⟨a, b', hab⟩ := hLnab
    exact fun hc => hab (hc.is_comm.comm a b')
  have hℓ3 : ℓ ^ 3 = 1 := pow_three_eq_one_of_eq_mul_zpow hLc hz hb hℓ hb3
  have hℓne : (⟨ℓ, hℓ⟩ : ↥L) ≠ 1 := by
    intro h1
    exact ne_one_of_eq_mul_zpow hz hb hbnt (congrArg Subtype.val h1)
  have hℓ3' : (⟨ℓ, hℓ⟩ : ↥L) ^ 3 = 1 := by
    ext
    simpa using hℓ3
  have hJsub : GLAPComponent 3 (Subgroup.centralizer ({⟨ℓ, hℓ⟩} : Set ↥L))
      (J.subgroupOf L) := by
    have h1 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf Nat.prime_three
      (inf_le_left : L ⊓ Subgroup.centralizer ({b} : Set X) ≤ L) hJ
    rwa [← centralizer_singleton_subgroupOf_mul_zpow hz hb hℓ] at h1
  have hJDsub : IsCatalogLieIso ↥(J.subgroupOf L) IsD42Index :=
    IsCatalogLieIso.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hJD
  have hAsub : IsElemAbelian 3 (A.subgroupOf L) := hA.subgroupOf L
  have hAcard : Nat.card (A.subgroupOf L) = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hA4
  exact hΩ ↥L hLs hLt ⟨ℓ, hℓ⟩ (J.subgroupOf L) (A.subgroupOf L) hℓne hℓ3' hJsub hJDsub
    (Subgroup.subgroupOf_mono L hAJ) hAsub hAcard
    (mem_zpowers_of_mem_centralizer_subgroupOf hLc hz hb hℓ hJL hC)
    (weaklyClosed_subgroupOf_of_mul_zpow hLc hz hb hℓ hAL hwc)

end CFSG.HardMathSupport.Dickson.Sec6

end
