module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK0
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem z4i_sq_eq_one_of_card_four {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 4)
    (α : MulAut T) (hα3 : α ^ 3 = 1) (hfpf : ∀ t : T, α t = t → t = 1) (x : T) :
    x * x = 1 := by
  by_contra hx
  have hx1 : x ≠ 1 := fun h => hx (by rw [h, mul_one])
  have hdvd : orderOf x ∣ 4 := by rw [← hcard]; exact orderOf_dvd_natCard x
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hne2 : orderOf x ≠ 2 := by
    intro h
    refine hx ?_
    rw [← pow_two, ← h]
    exact pow_orderOf_eq_one x
  have horder : orderOf x = 4 := by
    have hdvd' : orderOf x ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    interval_cases k
    · exact absurd (by simpa using hk) hne1
    · exact absurd (by simpa using hk) hne2
    · simpa using hk
  haveI hcyc : IsCyclic T := isCyclic_of_orderOf_eq_card x (by rw [horder, hcard])
  have hαdvd : orderOf α ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hα3
  have hαne1 : orderOf α ≠ 1 := by
    intro h
    have hα1 : α = 1 := orderOf_eq_one_iff.mp h
    exact hx1 (hfpf x (by simp [hα1]))
  have hαorder : orderOf α = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hαdvd with h1 | h3
    · exact absurd h1 hαne1
    · exact h3
  have h3dvd : 3 ∣ Nat.card (MulAut T) := by
    rw [← hαorder]; exact orderOf_dvd_natCard α
  have hcardAut : Nat.card (MulAut T) = 2 := by
    rw [IsCyclic.card_mulAut T, hcard]
    decide
  rw [hcardAut] at h3dvd
  norm_num at h3dvd

private noncomputable def z4iQAut [Finite X] (N M : Subgroup X) (ρ : X)
    [(N.subgroupOf M).Normal]
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M) :
    MulAut (↥M ⧸ N.subgroupOf M) :=
  z4i_quotAut (z4i_conjAut ρ M hρM) (N.subgroupOf M)
    (z4i_map_eq_of_forall_mem (z4i_conjAut ρ M hρM) (N.subgroupOf M) (fun n hn => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [z4i_conjAut_apply]
      exact hρN (n : X) hn))

private lemma z4iQAut_mk [Finite X] (N M : Subgroup X) (ρ : X) [(N.subgroupOf M).Normal]
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M) (m : ↥M) :
    z4iQAut N M ρ hρN hρM (QuotientGroup.mk m) =
      QuotientGroup.mk (z4i_conjAut ρ M hρM m) := rfl

private lemma z4iQAut_pow_three [Finite X] (N M : Subgroup X) (ρ : X) [(N.subgroupOf M).Normal]
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M) (hρ3 : ρ ^ 3 = 1) :
    z4iQAut N M ρ hρN hρM ^ 3 = 1 := by
  unfold z4iQAut
  exact z4i_quotAut_pow_three (z4i_conjAut ρ M hρM)
    (z4i_conjAut_pow_three ρ M hρM hρ3) (N.subgroupOf M) _

private lemma z4iQAut_fpf [Finite X] (N M : Subgroup X) (ρ : X) [(N.subgroupOf M).Normal]
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hfpf : ∀ x ∈ M, ρ * x * ρ⁻¹ * x⁻¹ ∈ N → x ∈ N) :
    ∀ t : ↥M ⧸ N.subgroupOf M, z4iQAut N M ρ hρN hρM t = t → t = 1 := by
  intro t ht
  induction t using QuotientGroup.induction_on with
  | _ m =>
    rw [z4iQAut_mk] at ht
    have hmem : (z4i_conjAut ρ M hρM m) / m ∈ N.subgroupOf M :=
      (QuotientGroup.eq_iff_div_mem).mp ht
    have hX : ρ * (m : X) * ρ⁻¹ * (m : X)⁻¹ ∈ N := by
      have h4 := Subgroup.mem_subgroupOf.mp hmem
      rwa [show ((z4i_conjAut ρ M hρM m / m : ↥M) : X) =
          ρ * (m : X) * ρ⁻¹ * (m : X)⁻¹ by
        rw [Subgroup.coe_div, z4i_conjAut_apply, div_eq_mul_inv]] at h4
    exact (QuotientGroup.eq_one_iff m).mpr
      (Subgroup.mem_subgroupOf.mpr (hfpf (m : X) m.2 hX))

private lemma z4iQAut_comm [Finite X] (N M : Subgroup X) (ρ τ : X) [(N.subgroupOf M).Normal]
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) (hτM : ∀ m ∈ M, τ * m * τ⁻¹ ∈ M)
    (hτρ : τ * ρ = ρ * τ) :
    z4iQAut N M ρ hρN hρM * z4iQAut N M τ hτN hτM =
      z4iQAut N M τ hτN hτM * z4iQAut N M ρ hρN hρM := by
  apply MulEquiv.ext
  intro t
  induction t using QuotientGroup.induction_on with
  | _ m =>
    rw [MulAut.mul_apply, MulAut.mul_apply, z4iQAut_mk, z4iQAut_mk, z4iQAut_mk, z4iQAut_mk]
    congr 1
    apply Subtype.ext
    rw [z4i_conjAut_apply, z4i_conjAut_apply, z4i_conjAut_apply, z4i_conjAut_apply]
    calc ρ * (τ * (m : X) * τ⁻¹) * ρ⁻¹ = (ρ * τ) * (m : X) * (ρ * τ)⁻¹ := by group
      _ = (τ * ρ) * (m : X) * (τ * ρ)⁻¹ := by rw [← hτρ]
      _ = τ * (ρ * (m : X) * ρ⁻¹) * τ⁻¹ := by group

private lemma z4iQAut_mul_self [Finite X] (N M : Subgroup X) (τ : X) [(N.subgroupOf M).Normal]
    (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) (hτM : ∀ m ∈ M, τ * m * τ⁻¹ ∈ M) (hτ2 : τ * τ = 1) :
    z4iQAut N M τ hτN hτM * z4iQAut N M τ hτN hτM = 1 := by
  apply MulEquiv.ext
  intro t
  induction t using QuotientGroup.induction_on with
  | _ m =>
    rw [MulAut.mul_apply, z4iQAut_mk, z4iQAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [z4i_conjAut_apply, z4i_conjAut_apply]
    calc τ * (τ * (m : X) * τ⁻¹) * τ⁻¹ = (τ * τ) * (m : X) * (τ * τ)⁻¹ := by group
      _ = (m : X) := by rw [hτ2]; simp

private lemma z4i_inv_mul_mem {N M : Subgroup X}
    (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) {a b : X} (hb : b ∈ M)
    (h : a * b⁻¹ ∈ N) : b⁻¹ * a ∈ N := by
  have h1 : b⁻¹ * (a * b⁻¹) * (b⁻¹)⁻¹ ∈ N := hNn b⁻¹ (M.inv_mem hb) (a * b⁻¹) h
  rwa [show b⁻¹ * (a * b⁻¹) * (b⁻¹)⁻¹ = b⁻¹ * a by group] at h1

theorem z4i_sq_mem_of_relIndex_four [Finite X] {N M : Subgroup X} {ρ : X} (hρ3 : ρ ^ 3 = 1)
    (hNM : N ≤ M) (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hidx : N.relIndex M = 4) (hfpf : ∀ x ∈ M, ρ * x * ρ⁻¹ * x⁻¹ ∈ N → x ∈ N) {x : X}
    (hx : x ∈ M) : x ^ 2 ∈ N := by
  haveI hNnorm : (N.subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hNn (g : X) g.2 (n : X) hn⟩
  have hcardT : Nat.card (↥M ⧸ N.subgroupOf M) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have h := z4i_sq_eq_one_of_card_four hcardT (z4iQAut N M ρ hρN hρM)
    (z4iQAut_pow_three N M ρ hρN hρM hρ3) (z4iQAut_fpf N M ρ hρN hρM hfpf)
    (QuotientGroup.mk ⟨x, hx⟩)
  rw [← QuotientGroup.mk_mul] at h
  have hmul : (⟨x, hx⟩ : ↥M) * ⟨x, hx⟩ ∈ N.subgroupOf M :=
    (QuotientGroup.eq_one_iff _).mp h
  rw [pow_two]
  simpa using Subgroup.mem_subgroupOf.mp hmul

theorem z4i_cover_mod [Finite X] {N M : Subgroup X} {ρ : X} (hρ3 : ρ ^ 3 = 1)
    (hNM : N ≤ M) (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hidx : N.relIndex M = 4) (hfpf : ∀ x ∈ M, ρ * x * ρ⁻¹ * x⁻¹ ∈ N → x ∈ N) {x₀ : X}
    (hx₀ : x₀ ∈ M) (hx₀N : x₀ ∉ N) {x : X} (hx : x ∈ M) :
    ∃ n ∈ N, x = n ∨ x = x₀ * n ∨ x = (ρ * x₀ * ρ⁻¹) * n ∨
      x = (ρ ^ 2 * x₀ * (ρ ^ 2)⁻¹) * n := by
  haveI hNnorm : (N.subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hNn (g : X) g.2 (n : X) hn⟩
  have hcardT : Nat.card (↥M ⧸ N.subgroupOf M) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hρM2 : ∀ m ∈ M, ρ ^ 2 * m * (ρ ^ 2)⁻¹ ∈ M := by
    intro m hm
    have h1 : ρ * m * ρ⁻¹ ∈ M := hρM m hm
    simpa [pow_two, mul_assoc] using hρM (ρ * m * ρ⁻¹) h1
  let m₀ : ↥M := ⟨x₀, hx₀⟩
  have ht : QuotientGroup.mk m₀ ≠ 1 := fun h =>
    hx₀N (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff m₀).mp h))
  have hcov := z4i_cover_of_card_four hcardT (z4iQAut N M ρ hρN hρM)
    (z4iQAut_pow_three N M ρ hρN hρM hρ3) (z4iQAut_fpf N M ρ hρN hρM hfpf) ht
    (QuotientGroup.mk ⟨x, hx⟩)
  rcases hcov with h1 | h1 | h1 | h1
  · have hxN : x ∈ N := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨x, hx⟩).mp h1)
    exact ⟨x, hxN, Or.inl rfl⟩
  · have hmem : (⟨x, hx⟩ : ↥M) / m₀ ∈ N.subgroupOf M := (QuotientGroup.eq_iff_div_mem).mp h1
    have hX : x * x₀⁻¹ ∈ N := by
      simpa [m₀, div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmem
    exact ⟨x₀⁻¹ * x, z4i_inv_mul_mem hNn hx₀ hX, Or.inr (Or.inl (by group))⟩
  · have hαt : z4iQAut N M ρ hρN hρM (QuotientGroup.mk m₀) =
        QuotientGroup.mk (⟨ρ * x₀ * ρ⁻¹, hρM x₀ hx₀⟩ : ↥M) := by
      rw [z4iQAut_mk]
      congr 1
    rw [hαt] at h1
    have hmem : (⟨x, hx⟩ : ↥M) / (⟨ρ * x₀ * ρ⁻¹, hρM x₀ hx₀⟩ : ↥M) ∈ N.subgroupOf M :=
      (QuotientGroup.eq_iff_div_mem).mp h1
    have hX : x * (ρ * x₀ * ρ⁻¹)⁻¹ ∈ N := by
      simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmem
    exact ⟨(ρ * x₀ * ρ⁻¹)⁻¹ * x, z4i_inv_mul_mem hNn (hρM x₀ hx₀) hX,
      Or.inr (Or.inr (Or.inl (by group)))⟩
  · have hα2t : z4iQAut N M ρ hρN hρM (z4iQAut N M ρ hρN hρM (QuotientGroup.mk m₀)) =
        QuotientGroup.mk (⟨ρ ^ 2 * x₀ * (ρ ^ 2)⁻¹, hρM2 x₀ hx₀⟩ : ↥M) := by
      rw [z4iQAut_mk, z4iQAut_mk]
      congr 1
      apply Subtype.ext
      rw [z4i_conjAut_apply, z4i_conjAut_apply]
      change ρ * (ρ * x₀ * ρ⁻¹) * ρ⁻¹ = ρ ^ 2 * x₀ * (ρ ^ 2)⁻¹
      rw [pow_two]
      group
    rw [hα2t] at h1
    have hmem : (⟨x, hx⟩ : ↥M) / (⟨ρ ^ 2 * x₀ * (ρ ^ 2)⁻¹, hρM2 x₀ hx₀⟩ : ↥M) ∈
        N.subgroupOf M := (QuotientGroup.eq_iff_div_mem).mp h1
    have hX : x * (ρ ^ 2 * x₀ * (ρ ^ 2)⁻¹)⁻¹ ∈ N := by
      simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmem
    exact ⟨(ρ ^ 2 * x₀ * (ρ ^ 2)⁻¹)⁻¹ * x, z4i_inv_mul_mem hNn (hρM2 x₀ hx₀) hX,
      Or.inr (Or.inr (Or.inr (by group)))⟩

theorem z4i_comm_invol_trivial [Finite X] {N M : Subgroup X} {ρ τ : X} (hρ3 : ρ ^ 3 = 1)
    (hNM : N ≤ M) (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hidx : N.relIndex M = 4) (hfpf : ∀ x ∈ M, ρ * x * ρ⁻¹ * x⁻¹ ∈ N → x ∈ N)
    (hτ2 : τ * τ = 1) (hτρ : τ * ρ = ρ * τ) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    (hτM : ∀ m ∈ M, τ * m * τ⁻¹ ∈ M) {x : X} (hx : x ∈ M) : τ * x * τ⁻¹ * x⁻¹ ∈ N := by
  haveI hNnorm : (N.subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hNn (g : X) g.2 (n : X) hn⟩
  have hcardT : Nat.card (↥M ⧸ N.subgroupOf M) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  let α := z4iQAut N M ρ hρN hρM
  let β := z4iQAut N M τ hτN hτM
  have hα3 : α ^ 3 = 1 := z4iQAut_pow_three N M ρ hρN hρM hρ3
  have hα3' : ∀ y, α (α (α y)) = y := by
    intro y
    have h := congrArg (fun f : MulAut (↥M ⧸ N.subgroupOf M) => f y) hα3
    simpa [pow_succ, MulAut.mul_apply] using h
  have hfpfT : ∀ t, α t = t → t = 1 := z4iQAut_fpf N M ρ hρN hρM hfpf
  have hβ2 : β * β = 1 := z4iQAut_mul_self N M τ hτN hτM hτ2
  have hcomm : β * α = α * β := (z4iQAut_comm N M ρ τ hρN hρM hτN hτM hτρ).symm
  have hββ : ∀ s, β (β s) = s := fun s => by
    have h := congrArg (fun f : MulAut (↥M ⧸ N.subgroupOf M) => f s) hβ2
    simpa [MulAut.mul_apply] using h
  have hcomm' : ∀ y, β (α y) = α (β y) := fun y => by
    have h := congrArg (fun f : MulAut (↥M ⧸ N.subgroupOf M) => f y) hcomm
    simpa [MulAut.mul_apply] using h
  have hβfix : ∀ s : ↥M ⧸ N.subgroupOf M, β s = s := by
    intro s
    by_cases hs : s = 1
    · rw [hs, map_one]
    · rcases z4i_cover_of_card_four hcardT α hα3 hfpfT hs (β s) with h1 | h1 | h1 | h1
      · exact absurd (by have h := hββ s; rw [h1, map_one] at h; exact h.symm) hs
      · exact h1
      · exact absurd (by
          have h := hββ s
          rw [h1] at h
          rw [hcomm' s, h1] at h
          have h4 := congrArg α h
          rw [hα3' s] at h4
          exact hfpfT s h4.symm) hs
      · exact absurd (by
          have h := hββ s
          rw [h1] at h
          rw [hcomm' (α s), hcomm' s, h1] at h
          rw [hα3' (α s)] at h
          exact hfpfT s h) hs
  have hxfix : z4iQAut N M τ hτN hτM (QuotientGroup.mk ⟨x, hx⟩) =
      QuotientGroup.mk ⟨x, hx⟩ := hβfix (QuotientGroup.mk ⟨x, hx⟩)
  rw [z4iQAut_mk] at hxfix
  have hmem : (z4i_conjAut τ M hτM ⟨x, hx⟩) / ⟨x, hx⟩ ∈ N.subgroupOf M :=
    (QuotientGroup.eq_iff_div_mem).mp hxfix
  have h4 := Subgroup.mem_subgroupOf.mp hmem
  rwa [show ((z4i_conjAut τ M hτM ⟨x, hx⟩ / ⟨x, hx⟩ : ↥M) : X) =
      τ * x * τ⁻¹ * x⁻¹ by
    rw [Subgroup.coe_div, z4i_conjAut_apply, div_eq_mul_inv]] at h4

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
