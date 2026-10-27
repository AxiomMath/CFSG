module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightD
import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineSylow

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups Pointwise commutatorElement

section Generic

variable {F : Type*} [Group F]

theorem s38d_exists_odd_pow_sq_eq_one [Finite F] {O : Subgroup F} (hO : Odd (Nat.card O))
    {x : F} (hx : x * x ∈ O) : ∃ n : ℕ, Odd n ∧ x ^ n * x ^ n = 1 := by
  have h1 : orderOf (x * x) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hx
  have hodd : Odd (orderOf (x * x)) := Odd.of_dvd_nat hO h1
  refine ⟨orderOf (x * x), hodd, ?_⟩
  rw [← pow_add, ← two_mul, pow_mul, ← sq]
  have : x ^ 2 = x * x := sq x
  rw [this, pow_orderOf_eq_one]

theorem s38d_dihedral_rel {a ρ : F} (ha : a * a = 1) (hρ : a * ρ * a = ρ⁻¹)
    (hb : ρ * ρ * (ρ * ρ) = 1) :
    (a * ρ) * a * (a * ρ)⁻¹ = a * (ρ * ρ) ∧ (a * ρ) * (ρ * ρ) * (a * ρ)⁻¹ = ρ * ρ ∧
      a * (ρ * ρ) = (ρ * ρ) * a := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc : (ρ * ρ)⁻¹ = ρ * ρ := inv_eq_of_mul_eq_one_right hb
  have hρρ : ρ⁻¹ * ρ⁻¹ = ρ * ρ := by rw [← mul_inv_rev, hc]
  have h2 : a * (ρ * ρ) * a = ρ * ρ := by
    calc a * (ρ * ρ) * a = (a * ρ * a) * (a * ρ * a) := by
          calc a * (ρ * ρ) * a = a * ρ * (a * a) * ρ * a := by rw [ha]; group
            _ = (a * ρ * a) * (a * ρ * a) := by group
      _ = ρ⁻¹ * ρ⁻¹ := by rw [hρ]
      _ = ρ * ρ := hρρ
  have hcomm : a * (ρ * ρ) = (ρ * ρ) * a := by
    calc a * (ρ * ρ) = a * (ρ * ρ) * a * a := by rw [mul_assoc _ a a, ha, mul_one]
      _ = (ρ * ρ) * a := by rw [h2]
  refine ⟨?_, ?_, hcomm⟩
  · calc (a * ρ) * a * (a * ρ)⁻¹ = (a * ρ * a) * ρ⁻¹ * a := by
          rw [mul_inv_rev, hainv]; group
      _ = ρ⁻¹ * ρ⁻¹ * a := by rw [hρ]
      _ = (ρ * ρ) * a := by rw [hρρ]
      _ = a * (ρ * ρ) := hcomm.symm
  · calc (a * ρ) * (ρ * ρ) * (a * ρ)⁻¹ = a * (ρ * ρ) * a := by
          rw [mul_inv_rev, hainv]; group
      _ = ρ * ρ := h2

theorem s38d_dihedral_lift [Finite F] {O K : Subgroup F} [O.Normal] (hO : Odd (Nat.card O))
    {a : F} (ha : a * a = 1) (hKa : ∀ k ∈ K, k * a = a * k)
    {ut bt : F ⧸ O} (hut : ut * ut = 1) (hbtK : bt ∈ K.map (QuotientGroup.mk' O)) (hbt1 : bt ≠ 1)
    (hbtbt : bt * bt = 1)
    (hrel : ut * QuotientGroup.mk' O a * ut * QuotientGroup.mk' O a = bt) :
    ∃ u : F, ∃ b ∈ K, b ≠ 1 ∧ b * b = 1 ∧ u * b * u⁻¹ = b ∧ u * a * u⁻¹ = a * b := by
  classical
  set π := QuotientGroup.mk' O with hπ
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hat : π a * π a = 1 := by rw [← map_mul, ha, map_one]
  have hatinv : (π a)⁻¹ = π a := inv_eq_of_mul_eq_one_right hat
  have hutinv : ut⁻¹ = ut := inv_eq_of_mul_eq_one_right hut
  have hbtinv : bt⁻¹ = bt := inv_eq_of_mul_eq_one_right hbtbt
  have hodd_pow : ∀ (x : F) (n : ℕ), Odd n → π x * π x = 1 → π (x ^ n) = π x := by
    intro x n hn hx
    obtain ⟨k, rfl⟩ := hn
    have h2 : π x ^ 2 = 1 := by rw [sq]; exact hx
    rw [map_pow, pow_succ, pow_mul, h2, one_pow, one_mul]
  obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk'_surjective O ut
  have hu₀sq : u₀ * u₀ ∈ O := by
    have : π (u₀ * u₀) = 1 := by rw [map_mul, hu₀, hut]
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨n₁, hn₁, hu₁⟩ := s38d_exists_odd_pow_sq_eq_one hO hu₀sq
  have hπu₁ : π (u₀ ^ n₁) = ut := by
    rw [hodd_pow u₀ n₁ hn₁ (by rw [hu₀, hut]), hu₀]
  set u₁ := u₀ ^ n₁ with hu₁def
  have hu₁inv : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁
  set r := a * u₁ with hr
  have hara : a * r * a = r⁻¹ := by
    rw [hr, mul_inv_rev, hu₁inv, hainv]
    calc a * (a * u₁) * a = (a * a) * u₁ * a := by group
      _ = u₁ * a := by rw [ha, one_mul]
  have hπb₀ : π (r * r) = bt := by
    have h1 : π (r * r) = π a * ut * π a * ut := by
      rw [hr]
      simp only [map_mul]
      rw [hπu₁]
      group
    rw [h1]
    have h2 : (ut * π a * ut * π a)⁻¹ = π a * ut * π a * ut := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hatinv, hutinv]
      group
    rw [← h2, hrel, hbtinv]
  have hb₀sq : (r * r) * (r * r) ∈ O := by
    have : π ((r * r) * (r * r)) = 1 := by rw [map_mul, hπb₀, hbtbt]
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨m, hm, hb₁⟩ := s38d_exists_odd_pow_sq_eq_one hO hb₀sq
  set ρ := r ^ m with hρdef
  have hρρ : ρ * ρ = (r * r) ^ m := by
    rw [hρdef, ← pow_add, ← two_mul, pow_mul, sq]
  have hπb₁ : π (ρ * ρ) = bt := by
    rw [hρρ, hodd_pow (r * r) m hm (by rw [hπb₀, hbtbt]), hπb₀]
  have hρa : a * ρ * a = ρ⁻¹ := by
    have h1 : a * ρ * a⁻¹ = (a * r * a⁻¹) ^ m := by rw [hρdef]; exact conj_pow.symm
    rw [hainv] at h1
    rw [h1, hara, inv_pow, hρdef]
  have hρb : ρ * ρ * (ρ * ρ) = 1 := by rw [hρρ]; exact hb₁
  obtain ⟨h1, h2, h3⟩ := s38d_dihedral_rel ha hρa hρb
  obtain ⟨j, hjK, hjπ⟩ := hbtK
  have hjsq : j * j ∈ O := by
    have : π (j * j) = 1 := by rw [map_mul, hjπ, hbtbt]
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨n₃, hn₃, hjj⟩ := s38d_exists_odd_pow_sq_eq_one hO hjsq
  have hjjK : j ^ n₃ ∈ K := Subgroup.pow_mem K hjK n₃
  have hπjj : π (j ^ n₃) = bt := by
    rw [hodd_pow j n₃ hn₃ (by rw [hjπ, hbtbt]), hjπ]
  set jj := j ^ n₃ with hjjdef
  have hjjinv : jj⁻¹ = jj := inv_eq_of_mul_eq_one_right hjj
  have hjj1 : jj ≠ 1 := fun h => hbt1 (by rw [← hπjj, h, map_one])
  set b₁ := ρ * ρ with hb₁def
  have hb₁b₁ : b₁ * b₁ = 1 := hρb
  set c := jj⁻¹ * b₁ with hc
  have hcO : c ∈ O := by
    have : π c = 1 := by rw [hc, map_mul, map_inv, hπjj, hπb₁, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hca : c * a = a * c := by
    have h4 : jj⁻¹ * a = a * jj⁻¹ := by
      have h5 := hKa jj hjjK
      calc jj⁻¹ * a = jj⁻¹ * (a * jj) * jj⁻¹ := by group
        _ = jj⁻¹ * (jj * a) * jj⁻¹ := by rw [h5]
        _ = a * jj⁻¹ := by group
    rw [hc]
    calc jj⁻¹ * b₁ * a = jj⁻¹ * (b₁ * a) := by group
      _ = jj⁻¹ * (a * b₁) := by rw [← h3]
      _ = (jj⁻¹ * a) * b₁ := by group
      _ = (a * jj⁻¹) * b₁ := by rw [h4]
      _ = a * (jj⁻¹ * b₁) := by group
  have hb₁c : b₁ = jj * c := by rw [hc, hjjinv, ← mul_assoc, hjj, one_mul]
  have hjjc : jj * c * jj = c⁻¹ := by
    have h6 : (jj * c * jj) * c = 1 := by
      have := hb₁b₁
      rw [hb₁c] at this
      calc jj * c * jj * c = (jj * c) * (jj * c) := by group
        _ = 1 := this
    exact eq_inv_of_mul_eq_one_left h6
  have hcodd : Odd (orderOf c) :=
    Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hcO)
  obtain ⟨e, he⟩ := hcodd
  set y := c ^ e with hy
  have hy2 : y * y = c⁻¹ := by
    have h7 : c ^ (2 * e + 1) = 1 := by rw [← he]; exact pow_orderOf_eq_one c
    rw [hy, ← pow_add, ← two_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact h7
  have hjy : jj * y * jj = y⁻¹ := by
    have h8 : jj * c ^ e * jj⁻¹ = (jj * c * jj⁻¹) ^ e := conj_pow.symm
    rw [hjjinv] at h8
    rw [hy, h8, hjjc, inv_pow]
  have hyjj : y * jj * y⁻¹ = b₁ := by
    calc y * jj * y⁻¹ = jj * (jj * y * jj) * y⁻¹ := by
          calc y * jj * y⁻¹ = (jj * jj) * y * jj * y⁻¹ := by rw [hjj]; group
            _ = jj * (jj * y * jj) * y⁻¹ := by group
      _ = jj * y⁻¹ * y⁻¹ := by rw [hjy]
      _ = jj * (y * y)⁻¹ := by group
      _ = jj * c := by rw [hy2, inv_inv]
      _ = b₁ := by rw [hb₁c]
  have hya : y * a = a * y := by
    have : Commute c a := hca
    exact (this.pow_left e).eq
  refine ⟨y⁻¹ * (a * ρ) * y, jj, hjjK, hjj1, hjj, ?_, ?_⟩
  · calc y⁻¹ * (a * ρ) * y * jj * (y⁻¹ * (a * ρ) * y)⁻¹
        = y⁻¹ * (a * ρ) * (y * jj * y⁻¹) * (a * ρ)⁻¹ * y := by group
      _ = y⁻¹ * ((a * ρ) * b₁ * (a * ρ)⁻¹) * y := by rw [hyjj]; group
      _ = y⁻¹ * b₁ * y := by rw [h2]
      _ = jj := by
        have : jj = y⁻¹ * b₁ * y := by rw [← hyjj]; group
        exact this.symm
  · calc y⁻¹ * (a * ρ) * y * a * (y⁻¹ * (a * ρ) * y)⁻¹
        = y⁻¹ * (a * ρ) * (y * a * y⁻¹) * (a * ρ)⁻¹ * y := by group
      _ = y⁻¹ * ((a * ρ) * a * (a * ρ)⁻¹) * y := by rw [hya]; group
      _ = y⁻¹ * (a * b₁) * y := by rw [h1]
      _ = a * (y⁻¹ * b₁ * y) := by
        have : y⁻¹ * a = a * y⁻¹ := by
          calc y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
            _ = y⁻¹ * (y * a) * y⁻¹ := by rw [hya]
            _ = a * y⁻¹ := by group
        calc y⁻¹ * (a * b₁) * y = (y⁻¹ * a) * b₁ * y := by group
          _ = (a * y⁻¹) * b₁ * y := by rw [this]
          _ = a * (y⁻¹ * b₁ * y) := by group
      _ = a * jj := by
        have : jj = y⁻¹ * b₁ * y := by rw [← hyjj]; group
        rw [← this]

theorem s38d_TOmega [Finite F] {O K : Subgroup F} [O.Normal] (hO : Odd (Nat.card O))
    {a : F} (ha : a * a = 1) (ha1 : a ≠ 1)
    (hKa : ∀ k ∈ K, k * a = a * k)
    (hKn : ∀ c : F, c * a = a * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hKq : CFSG.Open.IsQuasisimple K)
    (hZO : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z ∈ O)
    {u b : F} (hbK : b ∈ K) (hb1 : b ≠ 1) (hbb : b * b = 1)
    (hub : u * b * u⁻¹ = b) (hua : u * a * u⁻¹ = a * b) :
    ∀ o ∈ O, ∀ k ∈ K, o * k = k * o := by
  classical
  have hbO : b ∉ O := by
    intro hb
    have h2 : orderOf b = 2 := orderOf_eq_prime (by rwa [sq]) hb1
    have h3 := Subgroup.orderOf_dvd_natCard O hb
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 h3)
  have hKO : ∀ z ∈ K ⊓ O, ∀ k ∈ K, z * k = k * z := by
    haveI : ((K ⊓ O).subgroupOf K).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem g.2 (Subgroup.mem_inf.1 hn).1) (inv_mem g.2), ?_⟩
      have := (inferInstance : O.Normal).conj_mem _ (Subgroup.mem_inf.1 hn).2 (g : F)
      simpa using this⟩
    rcases s38d_quasisimple_normal hKq (inferInstance : ((K ⊓ O).subgroupOf K).Normal) with h | h
    · exfalso
      have : (⟨b, hbK⟩ : K) ∈ (K ⊓ O).subgroupOf K := by rw [h]; exact Subgroup.mem_top _
      exact hbO (Subgroup.mem_inf.1 (mem_subgroupOf.1 this)).2
    · intro z hz k hk
      have := Subgroup.mem_center_iff.1 (h (show (⟨z, (Subgroup.mem_inf.1 hz).1⟩ : K) ∈
        (K ⊓ O).subgroupOf K from hz)) ⟨k, hk⟩
      exact congrArg Subtype.val this.symm
  have hi : ∀ x ∈ O, x * a = a * x → ∀ k ∈ K, x * k = k * x := by
    set C : Subgroup F := O ⊓ centralizer ({a} : Set F) with hC
    have hKC : ⁅K, C⁆ ≤ centralizer (K : Set F) := by
      rw [commutator_le]
      intro k hk c hc
      have hcO : c ∈ O := (Subgroup.mem_inf.1 hc).1
      have hca : c * a = a * c := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2
      have hmem : ⁅k, c⁆ ∈ K ⊓ O := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have e : ⁅k, c⁆ = k * (c * k⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
          rw [e]
          exact mul_mem hk (hKn c hca k⁻¹ (inv_mem hk))
        · have e : ⁅k, c⁆ = (k * c * k⁻¹) * c⁻¹ := by rw [commutatorElement_def]
          rw [e]
          exact mul_mem ((inferInstance : O.Normal).conj_mem c hcO k) (inv_mem hcO)
      rw [mem_centralizer_iff]
      intro k' hk'
      exact (hKO _ hmem k' hk').symm
    have hP : Group.IsPerfect ↥K := (Group.isPerfect_def (G := ↥K)).2 hKq.1
    have h2 : ⁅⁅K, C⁆, K⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      exact hKC
    have h3 := CFSG.LocalCores.perfect_double_commutator (P := K) (X := C) hP h2
    rw [commutator_eq_bot_iff_le_centralizer] at h3
    intro x hx hxa k hk
    have : x ∈ C := Subgroup.mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxa⟩
    exact (mem_centralizer_iff.1 (h3 hk) x this)
  have hne : a ≠ b := by
    intro hab
    rw [← hab] at hua
    have : a = 1 := by
      have h1 : u * a * u⁻¹ = 1 := by rw [hua, ha]
      simpa using h1
    exact ha1 this
  have hab : a * b = b * a := (hKa b hbK).symm
  have hnormO : ∀ g : F, g ∈ normalizer (O : Set F) := fun g =>
    mem_normalizer_fintype fun n hn => (inferInstance : O.Normal).conj_mem n hn g
  have hcent : ∀ x ∈ O, b * x = x * b := by
    refine CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.commute_of_four_group_centralizers
      hO ha hbb hab ha1 hb1 hne (hnormO a) (hnormO b) ?_ ?_ ?_
    · intro x hx hxa
      exact (hi x hx hxa b hbK).symm
    · intro x _ hxb
      exact hxb.symm
    · intro x hx hxab
      have hx' : u⁻¹ * x * u ∈ O := by
        have := (inferInstance : O.Normal).conj_mem x hx u⁻¹
        simpa using this
      have hxa' : (u⁻¹ * x * u) * a = a * (u⁻¹ * x * u) := by
        calc (u⁻¹ * x * u) * a = u⁻¹ * (x * (u * a * u⁻¹)) * u := by group
          _ = u⁻¹ * (x * (a * b)) * u := by rw [hua]
          _ = u⁻¹ * ((a * b) * x) * u := by rw [hxab]
          _ = u⁻¹ * ((u * a * u⁻¹) * x) * u := by rw [hua]
          _ = a * (u⁻¹ * x * u) := by group
      have h5 := hi _ hx' hxa' b hbK
      calc b * x = (u * b * u⁻¹) * x := by rw [hub]
        _ = u * (b * (u⁻¹ * x * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * x * u) * b) * u⁻¹ := by rw [← h5]
        _ = x * (u * b * u⁻¹) := by group
        _ = x * b := by rw [hub]
  have hT : ((centralizer (O : Set F)).subgroupOf K).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    refine mem_centralizer_iff.2 fun o ho => ?_
    have hgo : (g : F)⁻¹ * o * g ∈ O := by
      have := (inferInstance : O.Normal).conj_mem o ho (g : F)⁻¹
      simpa using this
    have h6 := mem_centralizer_iff.1 hn _ hgo
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc o * ((g : F) * n * (g : F)⁻¹) = (g : F) * ((g : F)⁻¹ * o * g * n) * (g : F)⁻¹ := by group
      _ = (g : F) * (n * ((g : F)⁻¹ * o * g)) * (g : F)⁻¹ := by rw [h6]
      _ = (g : F) * n * (g : F)⁻¹ * o := by group⟩
  rcases s38d_quasisimple_normal hKq hT with htop | hcen
  · intro o ho k hk
    have : (⟨k, hk⟩ : K) ∈ (centralizer (O : Set F)).subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact mem_centralizer_iff.1 (mem_subgroupOf.1 this) o ho
  · exfalso
    have hbc : (⟨b, hbK⟩ : K) ∈ (centralizer (O : Set F)).subgroupOf K := by
      rw [mem_subgroupOf]
      exact mem_centralizer_iff.2 fun o ho => (hcent o ho).symm
    have := hcen hbc
    apply hbO
    refine hZO b hbK fun k hk => ?_
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 this) ⟨k, hk⟩).symm

end Generic

section Generic2

theorem s38o_exists_involution {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ∃ x : Q, x ≠ 1 ∧ x * x = 1 := by
  by_contra hcon
  push_neg at hcon
  have hodd : Odd (Nat.card Q) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card Q := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 h2
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx
      omega
    have hxx : x * x = 1 := by
      rw [← sq, ← hx]
      exact pow_orderOf_eq_one x
    exact hcon x hx1 hxx
  have hsolv : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI hperf : Group.IsPerfect Q := (Group.isPerfect_def (G := Q)).2 hQ.1
  haveI : Nontrivial Q := by
    haveI := hQ.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (center Q)).nontrivial
  exact Group.IsPerfect.not_isSolvable Q hsolv

theorem s38o_hom_dichotomy {J : Type*} [Group J] [Finite J] [IsSimpleGroup J]
    (hZ : ∀ z : J, (∀ y, z * y = y * z) → z = 1) (p q : J →* J)
    (hc : ∀ x y, p x * q y = q y * p x) (hpq : ∀ x, p x * q x = x) :
    (∀ x, p x = 1) ∨ (∀ x, p x = x) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p.ker with hk | hk
  · right
    have hinj : Function.Injective p := (MonoidHom.ker_eq_bot_iff p).1 hk
    have hsurj : Function.Surjective p := Finite.injective_iff_surjective.1 hinj
    intro y
    have hq1 : q y = 1 := by
      apply hZ
      intro g
      obtain ⟨x, rfl⟩ := hsurj g
      exact (hc x y).symm
    have := hpq y
    rwa [hq1, mul_one] at this
  · left
    intro x
    have : x ∈ p.ker := by rw [hk]; exact Subgroup.mem_top x
    exact MonoidHom.mem_ker.1 this

theorem s38o_diag_fixed_trivial {J : Type*} [Group J] [Finite J] [IsSimpleGroup J]
    (hZ : ∀ z : J, (∀ y, z * y = y * z) → z = 1) (σ : MulAut (J × J))
    (hσ : ∀ j : J, σ (j, j) = (j, j)) {n : ℕ} (hn : Odd n) (hσn : σ ^ n = 1) : σ = 1 := by
  classical
  let σh : J × J →* J × J := σ.toMonoidHom
  let pa : J →* J := (MonoidHom.fst J J).comp (σh.comp (MonoidHom.inl J J))
  let pb : J →* J := (MonoidHom.snd J J).comp (σh.comp (MonoidHom.inl J J))
  let qa : J →* J := (MonoidHom.fst J J).comp (σh.comp (MonoidHom.inr J J))
  let qb : J →* J := (MonoidHom.snd J J).comp (σh.comp (MonoidHom.inr J J))
  have hsplit : ∀ x y : J, ((x, y) : J × J) = (x, 1) * (1, y) := by
    intro x y; simp
  have hxx : ∀ x : J, σ (x, 1) * σ (1, x) = (x, x) := by
    intro x
    rw [← map_mul, ← hsplit, hσ]
  have hcomm : ∀ x y : J, σ (x, 1) * σ (1, y) = σ (1, y) * σ (x, 1) := by
    intro x y
    rw [← map_mul, ← map_mul]
    congr 1
    simp
  have hpqa : ∀ x, pa x * qa x = x := by
    intro x
    have := congrArg Prod.fst (hxx x)
    simpa [pa, qa, σh] using this
  have hpqb : ∀ x, pb x * qb x = x := by
    intro x
    have := congrArg Prod.snd (hxx x)
    simpa [pb, qb, σh] using this
  have hca : ∀ x y, pa x * qa y = qa y * pa x := by
    intro x y
    have := congrArg Prod.fst (hcomm x y)
    simpa [pa, qa, σh] using this
  have hcb : ∀ x y, pb x * qb y = qb y * pb x := by
    intro x y
    have := congrArg Prod.snd (hcomm x y)
    simpa [pb, qb, σh] using this
  have hσ1 : ∀ x : J, σ (x, 1) = (pa x, pb x) := fun x => rfl
  have hσ2 : ∀ y : J, σ (1, y) = (qa y, qb y) := fun y => rfl
  rcases s38o_hom_dichotomy hZ pa qa hca hpqa with ha | ha <;>
    rcases s38o_hom_dichotomy hZ pb qb hcb hpqb with hb | hb
  ·
    exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : J)
    have h1 : σ (x, 1) = σ 1 := by rw [hσ1, ha, hb, map_one]; rfl
    have h2 := σ.injective h1
    exact hx (congrArg Prod.fst h2)
  ·
    have hqa' : ∀ x, qa x = x := by
      intro x
      have := hpqa x
      rwa [ha, one_mul] at this
    have hqb' : ∀ x, qb x = 1 := by
      intro x
      have := hpqb x
      rw [hb] at this
      exact (mul_eq_left.1 this)
    have hswap : ∀ x y : J, σ (x, y) = (y, x) := by
      intro x y
      rw [hsplit, map_mul, hσ1, hσ2, ha, hb, hqa', hqb']
      simp
    have hσsq : σ ^ 2 = 1 := by
      ext ⟨x, y⟩ <;> simp [sq, hswap]
    obtain ⟨k, rfl⟩ := hn
    rw [pow_succ, pow_mul, hσsq, one_pow, one_mul] at hσn
    exact hσn
  ·
    have hqa' : ∀ x, qa x = 1 := by
      intro x
      have := hpqa x
      rw [ha] at this
      exact (mul_eq_left.1 this)
    have hqb' : ∀ x, qb x = x := by
      intro x
      have := hpqb x
      rwa [hb, one_mul] at this
    ext ⟨x, y⟩
    · rw [hsplit, map_mul, hσ1, hσ2, ha, hb, hqa', hqb']
      simp
    · rw [hsplit, map_mul, hσ1, hσ2, ha, hb, hqa', hqb']
      simp
  ·
    exfalso
    have hqa' : ∀ x, qa x = 1 := by
      intro x
      have := hpqa x
      rw [ha] at this
      exact (mul_eq_left.1 this)
    obtain ⟨y, hy⟩ := exists_ne (1 : J)
    have hqb' : ∀ x, qb x = 1 := by
      intro x
      have := hpqb x
      rw [hb] at this
      exact (mul_eq_left.1 this)
    have h1 : σ (1, y) = σ 1 := by rw [hσ2, hqa', hqb', map_one]; rfl
    have h2 := σ.injective h1
    exact hy (congrArg Prod.snd h2)


theorem s38o_prod_dihedral {H : Type*} [Group H] {J : Subgroup H} {a : H}
    (hP : ProdLayer J a) (haa : a * a = 1) {x : H} (hxJ : x ∈ J) (hxx : x * x = 1) :
    ∃ u : H, u * u = 1 ∧ u * a * u * a = x := by
  obtain ⟨ψ, hψ1, hψ2⟩ := hP.psi
  have hxD : x ∈ normalClosure (J : Set H) := subset_normalClosure hxJ
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set x' : J := ⟨x, hxJ⟩ with hx'
  have hx'x' : x' * x' = 1 := Subtype.ext hxx
  set u : normalClosure (J : Set H) := ψ.symm (x', 1) with hu
  have hψu : ψ u = (x', 1) := by rw [hu]; exact ψ.apply_symm_apply _
  refine ⟨(u : H), ?_, ?_⟩
  · have h1 : u * u = 1 := by
      apply ψ.injective
      rw [map_mul, hψu, map_one]
      ext <;> simp [hx'x']
    exact congrArg Subtype.val h1
  · haveI : (normalClosure (J : Set H)).Normal := normalClosure_normal
    have hda : a⁻¹ * (u : H) * a ∈ normalClosure (J : Set H) := by
      have := (inferInstance : (normalClosure (J : Set H)).Normal).conj_mem _ u.2 a⁻¹
      simpa using this
    have h2 := hψ2 (u : H) u.2 hda
    have h3 : ψ ⟨a⁻¹ * (u : H) * a, hda⟩ = (1, x') := by
      rw [h2]
      have : ψ ⟨(u : H), u.2⟩ = (x', 1) := hψu
      rw [this]; rfl
    have h4 : (⟨a⁻¹ * (u : H) * a, hda⟩ : normalClosure (J : Set H)) = ψ.symm (1, x') := by
      apply ψ.injective
      rw [h3, ψ.apply_symm_apply]
    have h5 : u * ψ.symm (1, x') = ⟨x, hxD⟩ := by
      apply ψ.injective
      rw [map_mul, hψu, ψ.apply_symm_apply, hψ1 x hxJ hxD]
      ext <;> simp [hx']
    have h6 := congrArg Subtype.val h5
    rw [← h4] at h6
    simp only [Subgroup.coe_mul] at h6
    rw [hainv] at h6
    calc (u : H) * a * (u : H) * a = (u : H) * (a * (u : H) * a) := by group
      _ = x := h6

theorem s38o_prod_odd_trivial {H : Type*} [Group H] [Finite H] {J : Subgroup H} {a : H}
    (hP : ProdLayer J a) [IsSimpleGroup J] {i : H} (hiJ : ∀ j ∈ J, i * j = j * i) {n : ℕ}
    (hn : Odd n) (hin : i ^ n = 1) : i = 1 := by
  obtain ⟨ψ, hψ1, -⟩ := hP.psi
  haveI : (normalClosure (J : Set H)).Normal := normalClosure_normal
  set σ₀ : MulAut (normalClosure (J : Set H)) := MulAut.conjNormal i with hσ₀
  set σ : MulAut (J × J) := MulAut.congr ψ σ₀ with hσ
  have hσ' : ∀ j : J, σ (j, j) = (j, j) := by
    intro j
    have hjD : (j : H) ∈ normalClosure (J : Set H) := subset_normalClosure j.2
    have h1 : ψ ⟨(j : H), hjD⟩ = (j, j) := hψ1 j j.2 hjD
    have h2 : ψ.symm (j, j) = ⟨(j : H), hjD⟩ := by rw [← h1]; exact ψ.symm_apply_apply _
    have h3 : σ₀ ⟨(j : H), hjD⟩ = ⟨(j : H), hjD⟩ := by
      apply Subtype.ext
      rw [hσ₀, MulAut.conjNormal_apply]
      have := hiJ j j.2
      calc i * (j : H) * i⁻¹ = (j : H) * i * i⁻¹ := by rw [this]
        _ = j := by group
    show ψ (σ₀ (ψ.symm (j, j))) = (j, j)
    rw [h2, h3, h1]
  have hσn : σ ^ n = 1 := by
    rw [hσ, ← map_pow, hσ₀, ← map_pow, hin, map_one, map_one]
  have h1 : σ = 1 := s38o_diag_fixed_trivial hP.center_eq_bot σ hσ' hn hσn
  have h2 : σ₀ = 1 := by
    have : MulAut.congr ψ σ₀ = MulAut.congr ψ 1 := by rw [map_one]; exact h1
    exact (MulAut.congr ψ).injective this
  have hic : i ∈ centralizer (normalClosure (J : Set H) : Set H) := by
    rw [mem_centralizer_iff]
    intro d hd
    have h3 := congrArg (fun τ : MulAut (normalClosure (J : Set H)) => ((τ ⟨d, hd⟩ : _) : H)) h2
    simp only [hσ₀, MulAut.conjNormal_apply, MulAut.one_apply] at h3
    have h4 : i * d = d * i := mul_inv_eq_iff_eq_mul.1 h3
    exact h4.symm
  rw [hP.centr, Subgroup.mem_bot] at hic
  exact hic


theorem s38o_not_odd_of_involution {Q : Type*} [Group Q] [Finite Q] {y : Q} (hy1 : y ≠ 1)
    (hyy : y * y = 1) : ¬ Odd (Nat.card Q) := by
  have hord : orderOf y = 2 := orderOf_eq_prime (by rwa [sq]) hy1
  have h2 : orderOf y ∣ Nat.card Q := orderOf_dvd_natCard y
  rw [hord] at h2
  exact fun hodd => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem s38o_involution_not_mem {Q : Type*} [Group Q] [Finite Q] {O : Subgroup Q}
    (hO : Odd (Nat.card O)) {y : Q} (hy1 : y ≠ 1) (hyy : y * y = 1) : y ∉ O := by
  intro hy
  have hord : orderOf y = 2 := orderOf_eq_prime (by rwa [sq]) hy1
  have h2 : orderOf y ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hy
  rw [hord] at h2
  exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 h2)

theorem s38o_quot_equiv_image {F F' : Type*} [Group F] [Group F'] [Finite F] (θ : F →* F')
    (hθ : Odd (Nat.card θ.ker)) {K : Subgroup F} (hK : CFSG.Open.IsQuasisimple K)
    (hKev : ¬ Odd (Nat.card K)) (hZ : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → θ z = 1) :
    Nonempty (K ⧸ center K ≃* K.map θ) := by
  classical
  let φ : K →* K.map θ := (θ.comp K.subtype).codRestrict (K.map θ) (fun k => ⟨k, k.2, rfl⟩)
  have hφ : ∀ k : K, ((φ k : K.map θ) : F') = θ k := fun _ => rfl
  have hφs : Function.Surjective φ := by
    rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩
  have hker : φ.ker = center K := by
    apply le_antisymm
    · rcases s38d_quasisimple_normal hK (MonoidHom.normal_ker φ) with h | h
      · exfalso
        have hKle : K ≤ θ.ker := fun k hk => by
          have : φ ⟨k, hk⟩ = 1 := by
            have := (h ▸ Subgroup.mem_top (⟨k, hk⟩ : K) : (⟨k, hk⟩ : K) ∈ φ.ker)
            exact this
          have h2 := congrArg Subtype.val this
          rw [hφ] at h2
          exact h2
        exact hKev (Odd.of_dvd_nat hθ (Subgroup.card_dvd_of_le hKle))
      · exact h
    · intro z hz
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      refine (hφ z).trans (hZ z z.2 fun y hy => ?_)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩


theorem s38o_simple_generic {H : Type} [Group H] [Finite H]
    (hL3 : CaseBParts.L3AutOddStatement) (hL3d : CaseBParts.L3DihedralStatement) {f : ℕ}
    (hf : 2 ≤ f) {J : Subgroup H} {a : H}
    (hout : GMSK.SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * f)) H J a)
    (hs : IsSimpleGroup (CFSG.layer H)) (hJ : LieModel J .PSU 3 2 f)
    (haa : a * a = 1) (haJ : ∀ j ∈ J, a * j = j * a) :
    (∀ (i : H) {n : ℕ}, Odd n → i ^ n = 1 → (∀ j ∈ J, i * j = j * i) → i = 1) ∧
    ∃ u : H, u * u = 1 ∧ u * a * u * a ≠ 1 ∧ (u * a * u * a) * (u * a * u * a) = 1 ∧
      u * a * u * a ∈ J := by
  classical
  haveI hchar : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨hX, hτout⟩ := hout.2 hs
  have hJL : J ≤ CFSG.layer H := hout.1.2.2.1
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hcen : centralizer (CFSG.layer H : Set H) = ⊥ := by
    have h1 := hout.1.2.2.2.2.1
    rwa [hout.1.2.2.2.1] at h1
  have hAmodel : LieModel (J.subgroupOf (CFSG.layer H)) .PSU 3 2 f :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hJ
  set τ : MulAut (CFSG.layer H) := MulAut.conjNormal a with hτ
  have hτ1 : τ ≠ 1 := fun h1 => hτout ⟨1, by rw [map_one]; exact h1.symm⟩
  have hτsq : τ ^ 2 = 1 := by
    rw [hτ, ← map_pow, sq, haa, map_one]
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime hτsq hτ1
  have hτA : ∀ x ∈ J.subgroupOf (CFSG.layer H), τ x = x := by
    intro x hx
    apply Subtype.ext
    rw [hτ, MulAut.conjNormal_apply]
    have hxJ : ((x : CFSG.layer H) : H) ∈ J := mem_subgroupOf.1 hx
    have := haJ _ hxJ
    calc a * (x : H) * a⁻¹ = (x : H) * a * a⁻¹ := by rw [this]
      _ = x := by group
  refine ⟨?_, ?_⟩
  · intro i n hn hin hiJ
    set σ : MulAut (CFSG.layer H) := MulAut.conjNormal i with hσ
    have hσn : σ ^ n = 1 := by rw [hσ, ← map_pow, hin, map_one]
    have hσodd : Odd (orderOf σ) := Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one hσn)
    have hσA : ∀ x ∈ J.subgroupOf (CFSG.layer H), σ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hσ, MulAut.conjNormal_apply]
      have hxJ : ((x : CFSG.layer H) : H) ∈ J := mem_subgroupOf.1 hx
      have := hiJ _ hxJ
      calc i * (x : H) * i⁻¹ = (x : H) * i * i⁻¹ := by rw [this]
        _ = x := by group
    have hσ1 : σ = 1 :=
      hL3 f hf (CFSG.layer H) (J.subgroupOf (CFSG.layer H)) hX hAmodel τ hτ2 hτA hτout σ hσA hσodd
    have hic : i ∈ centralizer (CFSG.layer H : Set H) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h3 := congrArg (fun τ : MulAut (CFSG.layer H) => ((τ ⟨x, hx⟩ : _) : H)) hσ1
      simp only [hσ, MulAut.conjNormal_apply, MulAut.one_apply] at h3
      have h4 : i * x = x * i := mul_inv_eq_iff_eq_mul.1 h3
      exact h4.symm
    rw [hcen, Subgroup.mem_bot] at hic
    exact hic
  · obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hL3d f hf (CFSG.layer H) (J.subgroupOf (CFSG.layer H)) hX
      hAmodel τ hτ2 hτA hτout
    have hb : (u : H) * a * (u : H) * a = ((u * τ u : CFSG.layer H) : H) := by
      rw [hτ, Subgroup.coe_mul, MulAut.conjNormal_apply, hainv]
      group
    refine ⟨(u : H), congrArg Subtype.val hu1, ?_, ?_, ?_⟩
    · rw [hb]
      intro h1
      exact hu2 (Subtype.ext h1)
    · rw [hb]
      exact congrArg Subtype.val hu3
    · rw [hb]
      exact mem_subgroupOf.1 hu4

end Generic2

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s38o_centralizes (hi : d.Sec38Input) {ut bt : Bar d.E ⧸ OE d}
    (hut : ut * ut = 1) (hbtK : bt ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)))
    (hbt1 : bt ≠ 1) (hbtbt : bt * bt = 1)
    (hrel : ut * QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) * ut *
      QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) = bt) :
    ∀ o ∈ OE d, ∀ k ∈ bar d.E d.N₂, o * k = k * o := by
  have hO : Odd (Nat.card (OE d)) := GMSK.odd_card_standardComponentOddCore (Bar d.E)
  have hord := hi.order_two
  have ha1 : proj d.E ⟨d.t, hi.t_mem⟩ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have haa : proj d.E ⟨d.t, hi.t_mem⟩ * proj d.E ⟨d.t, hi.t_mem⟩ = 1 := by
    rw [← sq, ← hord]
    exact pow_orderOf_eq_one _
  have hKa : ∀ k ∈ bar d.E d.N₂, k * proj d.E ⟨d.t, hi.t_mem⟩ = proj d.E ⟨d.t, hi.t_mem⟩ * k :=
    fun k hk => mem_centralizer_iff.1 hi.centralizes k hk
  have hKn : ∀ c : Bar d.E, c * proj d.E ⟨d.t, hi.t_mem⟩ = proj d.E ⟨d.t, hi.t_mem⟩ * c →
      ∀ k ∈ bar d.E d.N₂, c * k * c⁻¹ ∈ bar d.E d.N₂ := by
    intro c hc k hk
    have hcC : c ∈ centralizer ({proj d.E ⟨d.t, hi.t_mem⟩} : Set (Bar d.E)) :=
      mem_centralizer_singleton_iff.2 hc
    have hkC : k ∈ centralizer ({proj d.E ⟨d.t, hi.t_mem⟩} : Set (Bar d.E)) :=
      mem_centralizer_singleton_iff.2 (hKa k hk)
    have := hi.normal.conj_mem ⟨k, hkC⟩ (mem_subgroupOf.2 hk) ⟨c, hcC⟩
    exact mem_subgroupOf.1 this
  have hZO : ∀ z ∈ bar d.E d.N₂, (∀ k ∈ bar d.E d.N₂, z * k = k * z) → z ∈ OE d := by
    intro z hz hzc
    have hzc' : (⟨z, hz⟩ : bar d.E d.N₂) ∈ center (bar d.E d.N₂) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2).symm
    exact hi.centre_le ⟨_, hzc', rfl⟩
  obtain ⟨u, b, hbK, hb1, hbb, hub, hua⟩ := s38d_dihedral_lift hO haa hKa hut hbtK hbt1 hbtbt hrel
  exact s38d_TOmega hO haa ha1 hKa hKn hi.quasisimple hZO hbK hb1 hbb hub hua

theorem s38o_bar_L₂_le (d : Data G h) :
    bar d.E d.L₂ ≤ normalClosure ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) := by
  set Y := normalClosure ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) with hY
  have hLY : d.L₂ ≤ lift Y := by
    refine sup_le (le_lift Y) ((closure_le _).2 ?_)
    rintro _ ⟨g, hg, n, hn, rfl⟩
    have hgn : g * n * g⁻¹ ∈ normalizer (d.E : Set G) :=
      mul_mem (mul_mem hg (d.N₂_le_normalizer_E hn)) (inv_mem hg)
    refine mem_lift_iff.2 ⟨hgn, ?_⟩
    have e : (⟨g * n * g⁻¹, hgn⟩ : normalizer (d.E : Set G)) =
        (⟨g, hg⟩ : normalizer (d.E : Set G)) * ⟨n, d.N₂_le_normalizer_E hn⟩ *
          (⟨g, hg⟩ : normalizer (d.E : Set G))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (normalClosure_normal : (normalClosure ((bar d.E d.N₂ : Subgroup (Bar d.E)) :
      Set (Bar d.E))).Normal).conj_mem _ (subset_normalClosure (proj_mem_bar hn)) _
  calc bar d.E d.L₂ ≤ bar d.E (lift Y) := bar_mono hLY
    _ = Y := bar_lift Y

theorem s38o_centralizes_L₂ (d : Data G h)
    (hc : ∀ o ∈ OE d, ∀ k ∈ bar d.E d.N₂, o * k = k * o) :
    ∀ o ∈ OE d, ∀ y ∈ bar d.E d.L₂, o * y = y * o := by
  have h1 : bar d.E d.N₂ ≤ centralizer (OE d : Set (Bar d.E)) := by
    intro k hk
    rw [mem_centralizer_iff]
    intro o ho
    exact hc o ho k hk
  haveI : (centralizer (OE d : Set (Bar d.E))).Normal := Subgroup.normal_centralizer
  have h2 : normalClosure ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) ≤
      centralizer (OE d : Set (Bar d.E)) := normalClosure_le_normal h1
  intro o ho y hy
  exact mem_centralizer_iff.1 (h2 (s38o_bar_L₂_le d hy)) o ho

theorem s38o_comm_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hI : ∀ (i : G) (hi : i ∈ d.I₂), proj d.E ⟨i, s38d_I₂_le_normalizer_E hGMS hd hi⟩ ∈ OE d)
    (hc : ∀ o ∈ OE d, ∀ y ∈ bar d.E d.L₂, o * y = y * o) : ⁅d.L₂, d.I₂⁆ ≤ d.E := by
  rw [commutator_le]
  intro x hx i hi'
  have hxN : x ∈ normalizer (d.E : Set G) := d.L₂_le_normalizer_E hx
  have hiN : i ∈ normalizer (d.E : Set G) := s38d_I₂_le_normalizer_E hGMS hd hi'
  have hxb : proj d.E ⟨x, hxN⟩ ∈ bar d.E d.L₂ := proj_mem_bar hx
  have h1 := hc _ (hI i hi') _ hxb
  have h2 : proj d.E ⁅(⟨x, hxN⟩ : normalizer (d.E : Set G)), ⟨i, hiN⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm
  have h3 := proj_eq_one_iff.1 h2
  exact h3

theorem s38o_oddCore_le (hp : d.CaseHyp) :
    (standardComponentOddCore (centralizer (d.I₂ : Set G))).map
      (centralizer (d.I₂ : Set G)).subtype ≤ centralizer (d.N₂ : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro n hn
  have hnM : n ∈ d.M₂ := le_normalClosureIn d.N₂_le_centralizer_I₂ hn
  exact (hp.s39a1_odd a ha n hnM).symm


theorem s38o_I₂_image (hp : d.CaseHyp) {i : G} (hI : i ∈ d.I₂) :
    (∀ j ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)),
      QuotientGroup.mk' (OE d) (proj d.E ⟨i, s38d_I₂_le_normalizer_E hp.gms hp.hyp hI⟩) * j =
        j * QuotientGroup.mk' (OE d) (proj d.E ⟨i, s38d_I₂_le_normalizer_E hp.gms hp.hyp hI⟩)) ∧
    (QuotientGroup.mk' (OE d)
      (proj d.E ⟨i, s38d_I₂_le_normalizer_E hp.gms hp.hyp hI⟩)) ^ (Nat.card d.I₂) = 1 := by
  have hN := s38d_I₂_le_normalizer_E hp.gms hp.hyp hI
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hc : i * (y : G) = (y : G) * i :=
      mem_centralizer_iff.1 (d.N₂_le_centralizer_I₂ (mem_subgroupOf.1 hy)) i hI
    have h1 : proj d.E (⟨i, hN⟩ : normalizer (d.E : Set G)) * proj d.E y =
        proj d.E y * proj d.E (⟨i, hN⟩ : normalizer (d.E : Set G)) := by
      rw [← map_mul, ← map_mul]
      exact congrArg (proj d.E) (Subtype.ext hc)
    rw [← map_mul (QuotientGroup.mk' (OE d)), ← map_mul (QuotientGroup.mk' (OE d)), h1]
  · have hin : i ^ (Nat.card d.I₂) = 1 := by
      have := pow_card_eq_one' (G := d.I₂) (x := (⟨i, hI⟩ : d.I₂))
      exact congrArg Subtype.val this
    have h1 : (⟨i, hN⟩ : normalizer (d.E : Set G)) ^ (Nat.card d.I₂) = 1 :=
      Subtype.ext (by simpa using hin)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem s38o_prod_alt (hp : d.CaseHyp) (hi : d.Sec38Input)
    (hP : ProdLayer ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d)))
      (QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩))) :
    (∀ (i : G) (hI : i ∈ d.I₂),
      proj d.E ⟨i, s38d_I₂_le_normalizer_E hp.gms hp.hyp hI⟩ ∈ OE d) ∧
    ∃ ut bt : Bar d.E ⧸ OE d, ut * ut = 1 ∧
      bt ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) ∧ bt ≠ 1 ∧ bt * bt = 1 ∧
      ut * QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) * ut *
        QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) = bt := by
  have hO : Odd (Nat.card (OE d)) := GMSK.odd_card_standardComponentOddCore (Bar d.E)
  obtain ⟨y, hy1, hyy⟩ := s38o_exists_involution hi.quasisimple
  have hKev : ¬ Odd (Nat.card (bar d.E d.N₂)) := s38o_not_odd_of_involution hy1 hyy
  have hθ : Odd (Nat.card (QuotientGroup.mk' (OE d)).ker) := by
    rw [QuotientGroup.ker_mk']; exact hO
  haveI hJs : IsSimpleGroup ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))) :=
    s38d_simple_image (QuotientGroup.mk' (OE d)) hθ hi.quasisimple hKev hP.center_eq_bot
  have hord := hi.order_two
  have haa : QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) *
      QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) = 1 := by
    rw [← map_mul, ← sq, ← hord, pow_orderOf_eq_one, map_one]
  set x : Bar d.E ⧸ OE d := QuotientGroup.mk' (OE d) (y : Bar d.E) with hx
  have hxJ : x ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) := ⟨y, y.2, rfl⟩
  have hyy' : (y : Bar d.E) * (y : Bar d.E) = 1 := congrArg Subtype.val hyy
  have hy1' : (y : Bar d.E) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hxx : x * x = 1 := by rw [hx, ← map_mul, hyy', map_one]
  have hx1 : x ≠ 1 := by
    intro h
    exact s38o_involution_not_mem hO hy1' hyy' ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨u, hu, hrel⟩ := s38o_prod_dihedral hP haa hxJ hxx
  refine ⟨?_, u, x, hu, hxJ, hx1, hxx, hrel⟩
  intro i hI
  obtain ⟨hcomm, hpow⟩ := s38o_I₂_image hp hI
  have h1 := s38o_prod_odd_trivial hP hcomm (s38d_odd_I₂ d) hpow
  exact (QuotientGroup.eq_one_iff _).1 h1


theorem s38o_simple_alt (hL3 : CaseBParts.L3AutOddStatement)
    (hL3d : CaseBParts.L3DihedralStatement) (hp : d.CaseHyp) (hi : d.Sec38Input)
    (hout : GMSK.SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * f)) (Bar d.E ⧸ OE d)
      ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d)))
      (QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩)))
    (hs : IsSimpleGroup (CFSG.layer (Bar d.E ⧸ OE d))) :
    (∀ (i : G) (hI : i ∈ d.I₂),
      proj d.E ⟨i, s38d_I₂_le_normalizer_E hp.gms hp.hyp hI⟩ ∈ OE d) ∧
    ∃ ut bt : Bar d.E ⧸ OE d, ut * ut = 1 ∧
      bt ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) ∧ bt ≠ 1 ∧ bt * bt = 1 ∧
      ut * QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) * ut *
        QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) = bt := by
  have hO : Odd (Nat.card (OE d)) := GMSK.odd_card_standardComponentOddCore (Bar d.E)
  have hf : 2 ≤ f := hp.hyp.setting.two_le
  obtain ⟨y, hy1, hyy⟩ := s38o_exists_involution hi.quasisimple
  have hKev : ¬ Odd (Nat.card (bar d.E d.N₂)) := s38o_not_odd_of_involution hy1 hyy
  have hθ : Odd (Nat.card (QuotientGroup.mk' (OE d)).ker) := by
    rw [QuotientGroup.ker_mk']; exact hO
  have hZ : ∀ z ∈ bar d.E d.N₂, (∀ y ∈ bar d.E d.N₂, z * y = y * z) →
      QuotientGroup.mk' (OE d) z = 1 := by
    intro z hz hzc
    have hzc' : (⟨z, hz⟩ : bar d.E d.N₂) ∈ center (bar d.E d.N₂) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2).symm
    exact (QuotientGroup.eq_one_iff z).2 (hi.centre_le ⟨_, hzc', rfl⟩)
  obtain ⟨e⟩ := s38o_quot_equiv_image (QuotientGroup.mk' (OE d)) hθ hi.quasisimple hKev hZ
  have hJmodel : LieModel ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))) .PSU 3 2 f :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hi.model
  have hord := hi.order_two
  have haa : QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) *
      QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) = 1 := by
    rw [← map_mul, ← sq, ← hord, pow_orderOf_eq_one, map_one]
  have haJ : ∀ j ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)),
      QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) * j =
        j * QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact (mem_centralizer_iff.1 hi.centralizes k hk).symm
  obtain ⟨hI1, u, hu1, hu2, hu3, hu4⟩ := s38o_simple_generic hL3 hL3d hf hout hs hJmodel haa haJ
  refine ⟨?_, u, _, hu1, hu4, hu2, hu3, rfl⟩
  intro i hI
  obtain ⟨hcomm, hpow⟩ := s38o_I₂_image hp hI
  exact (QuotientGroup.eq_one_iff _).1 (hI1 _ (s38d_odd_I₂ d) hpow hcomm)

theorem sec38_odd (hL3 : CaseBParts.L3AutOddStatement) (hL3d : CaseBParts.L3DihedralStatement)
    (hp : d.CaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input) (hnn : d.Sec38NotNormal)
    (ho : d.Sec38Outcome) : d.Sec38Odd := by
  obtain ⟨ht, hout⟩ := ho
  have hdata : (∀ (i : G) (hI : i ∈ d.I₂),
      proj d.E ⟨i, s38d_I₂_le_normalizer_E hp.gms hp.hyp hI⟩ ∈ OE d) ∧
      ∃ ut bt : Bar d.E ⧸ OE d, ut * ut = 1 ∧
        bt ∈ (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) ∧ bt ≠ 1 ∧ bt * bt = 1 ∧
        ut * QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) * ut *
          QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩) = bt := by
    by_cases hs : IsSimpleGroup (CFSG.layer (Bar d.E ⧸ OE d))
    · exact s38o_simple_alt hL3 hL3d hp hi hout hs
    · exact s38o_prod_alt hp hi (s38d_prodLayer hout.1 hs)
  obtain ⟨hIO, ut, bt, hut, hbtK, hbt1, hbtbt, hrel⟩ := hdata
  exact ⟨s38o_comm_le hp.gms hp.hyp hIO
      (s38o_centralizes_L₂ d (s38o_centralizes hi hut hbtK hbt1 hbtbt hrel)),
    s38o_oddCore_le hp⟩

end Data

namespace CaseBParts

theorem sec38Odd : Sec38OddStatement :=
  fun hL3 hL3d _ _ _ _ _ _ _ _ hp ha hi hnn ho => Data.sec38_odd hL3 hL3d hp ha hi hnn ho

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
