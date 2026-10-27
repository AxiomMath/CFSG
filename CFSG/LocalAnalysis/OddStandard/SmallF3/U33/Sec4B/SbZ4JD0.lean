module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JF1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

@[expose] def IsZJMh (y z v₁ v₂ : H) (Mh : Subgroup H) : Prop :=
  ∀ g : H, g ∈ Mh ↔ zjMat y z v₁ v₂ g ∈ ZJFin.Mlist

private theorem range_card_index {N α : Type*} [Group N] (K : Subgroup N) (f : N → α)
    (hf : ∀ n m : N, f n = f m ↔ n⁻¹ * m ∈ K) : Nat.card (Set.range f) = K.index := by
  let g : N ⧸ K → α := Quotient.lift f fun a b hab =>
    (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((hf _ _).mp hab)
  have hrange : Set.range f = Set.range g := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : N ⧸ K), rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H n => exact ⟨n, rfl⟩
  rw [hrange, Nat.card_range_of_injective hg]
  rfl

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem exists_Mh : ∃ Mh : Subgroup H, IsZJMh y z v₁ v₂ Mh := by
  refine ⟨⟨⟨⟨{g : H | zjMat y z v₁ v₂ g ∈ ZJFin.Mlist}, ?_⟩, ?_⟩, ?_⟩, fun g => Iff.rfl⟩
  · intro a b ha hb
    rw [Set.mem_setOf_eq] at ha hb ⊢
    rw [h.mat_mul]
    exact ZJFin.M_mul _ ha _ hb
  · rw [Set.mem_setOf_eq, h.mat_one]
    exact ZJFin.one_mem_M
  · intro a ha
    rw [Set.mem_setOf_eq] at ha ⊢
    have hmul : ZJFin.mmul (zjMat y z v₁ v₂ a) (zjMat y z v₁ v₂ a⁻¹) = ZJFin.one := by
      rw [← h.mat_mul, mul_inv_cancel, h.mat_one]
    exact ZJFin.M_inv _ ha _ (h.mat_mem_P a⁻¹) hmul

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

theorem Mh_normal {g x : H} (hx : x ∈ Mh) : g * x * g⁻¹ ∈ Mh := by
  rw [hMh]
  have hs : zjMat y z v₁ v₂ g ∈ ZJFin.S48 := h.mat_mem_S48 g
  have hm : zjMat y z v₁ v₂ x ∈ ZJFin.Mlist := (hMh x).mp hx
  obtain ⟨m', hm', heq⟩ := ZJFin.M_normal _ hs _ hm
  obtain ⟨a, ha⟩ := h.exists_mat (ZJFin.M_sub _ hm')
  have h1 : zjMat y z v₁ v₂ (g * x * g⁻¹) =
      ZJFin.mmul (ZJFin.mmul (zjMat y z v₁ v₂ g) (zjMat y z v₁ v₂ x))
        (zjMat y z v₁ v₂ g⁻¹) := by
    rw [show g * x * g⁻¹ = (g * x) * g⁻¹ by group, h.mat_mul (g * x) g⁻¹,
      h.mat_mul g x]
  rw [h1, heq, ← ha, ← h.mat_mul a g, ← h.mat_mul (a * g) g⁻¹,
    show (a * g) * g⁻¹ = a by group, ha]
  exact hm'

theorem E_le_Mh {e : H} (he : e ∈ centralizer (Y : Set H)) : e ∈ Mh := by
  rw [hMh]
  have h1 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ e :=
    (h.mat_eq_iff 1 e).mpr (by simpa using he)
  rw [← h1, h.mat_one]
  exact ZJFin.one_mem_M

theorem t_not_mem_Mh : t ∉ Mh := by
  intro ht
  have hmem : zjMat y z v₁ v₂ t ∈ ZJFin.Mlist := (hMh t).mp ht
  rw [h.mat_t] at hmem
  exact ZJFin.T_not_M hmem

theorem l_not_mem_Mh : l ∉ Mh := by
  intro ht
  have hmem : zjMat y z v₁ v₂ l ∈ ZJFin.Mlist := (hMh l).mp ht
  rw [h.mat_l] at hmem
  exact ZJFin.L_not_M hmem

theorem tl_not_mem_Mh : t * l ∉ Mh := by
  intro ht
  have hmem : zjMat y z v₁ v₂ (t * l) ∈ ZJFin.Mlist := (hMh (t * l)).mp ht
  rw [h.mat_mul, h.mat_t, h.mat_l] at hmem
  exact ZJFin.TL_not_M hmem

theorem card_Mh : Nat.card Mh = 512 := by
  have hE : centralizer (Y : Set H) ≤ Mh := fun e he => E_le_Mh h hMh he
  let K : Subgroup Mh := (centralizer (Y : Set H)).subgroupOf Mh
  let f : Mh → ℕ := fun g => zjMat y z v₁ v₂ (g : H)
  have hf : ∀ n m : Mh, f n = f m ↔ n⁻¹ * m ∈ K := by
    intro n m
    rw [Subgroup.mem_subgroupOf]
    have hcoe : (((n⁻¹ * m : Mh)) : H) = (n : H)⁻¹ * (m : H) := rfl
    rw [hcoe]
    exact h.mat_eq_iff (n : H) (m : H)
  have hrange : Set.range f = {x : ℕ | x ∈ ZJFin.Mlist} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (hMh (g : H)).mp g.2
    · intro hx
      obtain ⟨a, ha⟩ := h.exists_mat (ZJFin.M_sub x hx)
      refine ⟨⟨a, ?_⟩, ha⟩
      exact (hMh a).mpr (by rw [ha]; exact hx)
  have hcard4 : Nat.card (Set.range f) = 4 := by
    rw [hrange]
    rw [show {x : ℕ | x ∈ ZJFin.Mlist} = (↑ZJFin.Mlist.toFinset : Set ℕ) by ext x; simp]
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup ZJFin.M_card.2,
      ZJFin.M_card.1]
  have hidx : K.index = 4 := by
    rw [← range_card_index K f hf, hcard4]
  have hKcard : Nat.card K = 128 := by
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
    rw [hc]
    exact h.card_E
  have hmain : K.index * Nat.card K = Nat.card Mh := Subgroup.index_mul_card K
  calc Nat.card Mh = K.index * Nat.card K := hmain.symm
    _ = 4 * 128 := by rw [hidx, hKcard]
    _ = 512 := by norm_num

theorem Mh_isPGroup : IsPGroup 2 Mh := by
  refine IsPGroup.of_card (n := 9) ?_
  rw [card_Mh h hMh]
  norm_num

theorem cent_rho_Mh {m : H} (hm : m ∈ Mh) (hc : ρ * m * ρ⁻¹ = m) :
    m ∈ centralizer (Y : Set H) := by
  have hcomm : ρ * m = m * ρ := by
    calc ρ * m = (ρ * m * ρ⁻¹) * ρ := by group
      _ = m * ρ := by rw [hc]
  have h1 : ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ m) =
      ZJFin.mmul (zjMat y z v₁ v₂ m) (zjMat y z v₁ v₂ ρ) := by
    rw [← h.mat_mul ρ m, ← h.mat_mul m ρ, hcomm]
  have hmM : zjMat y z v₁ v₂ m ∈ ZJFin.Mlist := (hMh m).mp hm
  have hmone : zjMat y z v₁ v₂ m = ZJFin.one := by
    rcases h.mat_rho with hR | hR
    · rw [hR] at h1
      exact ZJFin.M_fpf _ hmM h1.symm
    · rw [hR] at h1
      exact ZJFin.M_fpf2 _ hmM h1.symm
  have h2 : zjMat y z v₁ v₂ (1 : H) = zjMat y z v₁ v₂ m := by
    rw [h.mat_one, hmone]
  have h3 := (h.mat_eq_iff 1 m).mp h2
  simpa using h3

theorem Mh_inf_cent_rho : Mh ⊓ centralizer ({ρ} : Set H) = zpowers τ := by
  apply le_antisymm
  · intro m hm
    obtain ⟨hmMh, hmC⟩ := Subgroup.mem_inf.mp hm
    have hcomm : ρ * m * ρ⁻¹ = m := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hmC
      calc ρ * m * ρ⁻¹ = (m * ρ) * ρ⁻¹ := by rw [hc]
        _ = m := by group
    have hE := cent_rho_Mh h hMh hmMh hcomm
    have hmem : m ∈ centralizer ({ρ} : Set H) ⊓ centralizer (Y : Set H) :=
      Subgroup.mem_inf.mpr ⟨hmC, hE⟩
    rwa [h.centralizer_rho_inf_E] at hmem
  · refine Subgroup.zpowers_le.mpr ?_
    exact Subgroup.mem_inf.mpr
      ⟨E_le_Mh h hMh h.tau_mem_E,
        Subgroup.mem_centralizer_singleton_iff.mpr h.tau_rho⟩

theorem Mh_le_comm_sup : Mh ≤ ⁅Mh, zpowers ρ⁆ ⊔ zpowers τ := by
  have hcardA : Nat.card (zpowers ρ) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h.rho_pow_three
  obtain ⟨k, -, hk'⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card (zpowers ρ) ∣ 3 ^ 1 by simpa using hcardA)
  have hP : IsPGroup 3 (zpowers ρ) := IsPGroup.of_card (n := k) hk'
  have hρ_norm : ρ ∈ normalizer (Mh : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Mh_normal h hMh hx
    · intro hx
      have h2 := Mh_normal h hMh (g := ρ⁻¹) hx
      rwa [show ρ⁻¹ * (ρ * x * ρ⁻¹) * (ρ⁻¹)⁻¹ = x by group] at h2
  have hnorm : zpowers ρ ≤ normalizer (Mh : Set H) := Subgroup.zpowers_le.mpr hρ_norm
  have hcard : ¬ 3 ∣ Nat.card Mh := by
    rw [card_Mh h hMh]
    norm_num
  have hdec := CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_commutator_sup_inf_centralizer
    (p := 3) Nat.prime_three (P := zpowers ρ) (R := Mh) hP hnorm hcard
  have hinf : Mh ⊓ centralizer (↑(zpowers ρ) : Set H) ≤ zpowers τ := by
    refine (inf_le_inf_left Mh ?_).trans (le_of_eq (Mh_inf_cent_rho h hMh))
    exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_zpowers ρ)
  calc Mh ≤ ⁅Mh, zpowers ρ⁆ ⊔ Mh ⊓ centralizer (↑(zpowers ρ) : Set H) := hdec
    _ ≤ ⁅Mh, zpowers ρ⁆ ⊔ zpowers τ := sup_le_sup_left hinf _

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
