module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasicHW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypesHW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubCPrimeA
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace Hyp52W

variable (h : Hyp52W H)

omit [Finite H] in
private theorem card_subgroupOf_eq (A C : Subgroup H) :
    Nat.card (A.subgroupOf C) = Nat.card ↥(A ⊓ C) := by
  rw [← inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

theorem sylow_kernel : h.B ≤ coreActionKernel h.V ∧
    ∃ R : Sylow 2 ↥(coreActionKernel h.V),
      (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel h.V with hC
  set D := normalizer (h.B : Set H) ⊓ C with hD
  have hBD : h.B ≤ D := h.B_le_kernel
  have hBC : h.B ≤ C := hBD.trans inf_le_right
  refine ⟨hBC, ?_⟩
  obtain ⟨n, hn⟩ := (Hyp52W.isPGroup_B h).exists_card_eq
  have hcardB : Nat.card (h.B.subgroupOf C) = 2 ^ n := by
    rw [card_subgroupOf_eq, inf_of_le_left hBC, hn]
  obtain ⟨R₀, hR₀⟩ := h.B_sylow_kernel
  have hR₀card : Nat.card R₀ = 2 ^ n := by
    rw [show Nat.card R₀ = Nat.card (R₀ : Subgroup D) from rfl, hR₀, card_subgroupOf_eq,
      inf_of_le_left hBD, hn]
  have hDfac : (Nat.card D).factorization 2 = n := by
    have h1 := R₀.card_eq_multiplicity
    rw [hR₀card] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hnD : ¬ 2 ^ (n + 1) ∣ Nat.card D := by
    rw [← hDfac]
    exact Nat.pow_succ_factorization_not_dvd hD0 Nat.prime_two
  have hnC : ¬ 2 ^ (n + 1) ∣ Nat.card C := by
    intro hdvd
    have h1 := Sylow.prime_pow_dvd_card_normalizer hdvd hcardB
    rw [← subgroupOf_normalizer_eq hBC, card_subgroupOf_eq] at h1
    exact hnD h1
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card C).factorization 2 = n := by
    have hle : n ≤ (Nat.card C).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hC0).mp
        (hcardB ▸ Subgroup.card_subgroup_dvd_card _)
    have hlt : ¬ n + 1 ≤ (Nat.card C).factorization 2 := fun h1 =>
      hnC ((Nat.prime_two.pow_dvd_iff_le_factorization hC0).mpr h1)
    omega
  exact ⟨Sylow.ofCard (h.B.subgroupOf C) (by rw [hcardB, hfac]), rfl⟩

end Hyp52W

namespace B5aHW

variable (h : Hyp59W H)

theorem conj_x_mem {b : H} (hb : b ∈ h.B) :
    h.x⁻¹ * b * h.x ∈ h.toHyp52W.T ∧ h.x * b * h.x⁻¹ ∈ h.toHyp52W.Q := by
  have hxS : h.x ∈ h.S := h.x_mem
  have hxJ : h.x ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le hxS)).2
  have hbP : b ∈ h.toHyp52W.P := h.B_le hb
  have hPx : ∀ y ∈ h.toHyp52W.P,
      h.x⁻¹ * y * h.x ∈ h.toHyp52W.P ∧ h.x * y * h.x⁻¹ ∈ h.toHyp52W.P := by
    intro y hy
    obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
    refine ⟨mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hxS) hyS) hxS,
      conj_mem_coreActionKernel hxJ hyC⟩,
      mem_inf.mpr ⟨mul_mem (mul_mem hxS hyS) (inv_mem hxS), ?_⟩⟩
    have h1 := conj_mem_coreActionKernel (inv_mem hxJ) hyC
    rwa [inv_inv] at h1
  have hbQ : b ∈ h.toHyp52W.Q := (Hyp52W.B_le_T h.toHyp52W hb).1
  have hQ : h.x⁻¹ * b * h.x ∈ h.toHyp52W.Q ∧ h.x * b * h.x⁻¹ ∈ h.toHyp52W.Q := by
    rcases h.x_cond with hx | ⟨hPQ, -⟩
    · have hxN := (mem_inf.mp hx).2
      refine ⟨?_, (mem_normalizer_iff.mp hxN b).mp hbQ⟩
      have h1 := (mem_normalizer_iff.mp (inv_mem hxN) b).mp hbQ
      rwa [inv_inv] at h1
    · exact ⟨hPQ (hPx b hbP).1, hPQ (hPx b hbP).2⟩
  exact ⟨mem_inf.mpr ⟨hQ.1, (hPx b hbP).1⟩, hQ.2⟩

end B5aHW

namespace Hyp59W

variable (h : Hyp59W H)

theorem embeds_T_quot :
    ∃ f : ↥h.B →* ↥h.toHyp52W.T ⧸ h.B.subgroupOf h.toHyp52W.T, Function.Injective f := by
  have hmem : ∀ b : h.B,
      ((MulAut.conj h.x⁻¹).toMonoidHom.comp h.B.subtype) b ∈ h.toHyp52W.T := by
    intro b
    show h.x⁻¹ * b * h.x⁻¹⁻¹ ∈ h.toHyp52W.T
    rw [inv_inv]
    exact (B5aHW.conj_x_mem h b.2).1
  let g : ↥h.B →* ↥h.toHyp52W.T :=
    ((MulAut.conj h.x⁻¹).toMonoidHom.comp h.B.subtype).codRestrict h.toHyp52W.T hmem
  refine ⟨(QuotientGroup.mk' (h.B.subgroupOf h.toHyp52W.T)).comp g, ?_⟩
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at hb
  have hb' : h.x⁻¹ * b * h.x ∈ h.B := by
    have h1 : ((g b : h.toHyp52W.T) : H) = h.x⁻¹ * b * h.x⁻¹⁻¹ := rfl
    rwa [h1, inv_inv] at hb
  have h2 : h.x⁻¹ * b * h.x ∈ h.B ⊓ conjugate h.B h.x :=
    mem_inf.mpr ⟨hb', conj_mem_conjugate b.2 h.x⟩
  rw [h.inf_conjugate_x, mem_bot] at h2
  apply Subtype.ext
  show (b : H) = 1
  have h3 : (b : H) = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
  rw [h3, h2, mul_one, mul_inv_cancel]

end Hyp59W

theorem sylowKernelStatementHW : SylowKernelStatementHW := fun _ _ _ h => h.sylow_kernel

theorem embedsTQuotStatementHW : EmbedsTQuotStatementHW := fun _ _ _ h => h.embeds_T_quot

end CFSG.ComponentClassification.GSThmB
