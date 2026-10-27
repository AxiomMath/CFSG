module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6FixP2Aut

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide CFSG.Monster.B.CTIB CFSG.EvenSmallLie.TwoE6
  CFSG.LieType.Chevalley.C2E6Std


theorem e6fix_two_pow_dvd_NE {y : ↥Eam} (hy : y ∈ NE) :
    2 ^ 21 ∣ Nat.card ↥(centralizer ({y} : Set ↥Eam) ⊓ commutator ↥Eam) := by
  have : Finite NE := Nat.finite_of_card_ne_zero (by rw [bFix_natCard_NE]; norm_num)
  have hz : ∀ n : NE, n * (⟨xhatEam, bFix_xhatEam_mem_NE⟩ : NE) =
      ⟨xhatEam, bFix_xhatEam_mem_NE⟩ * n := fun n => by
    have h := xhat_comm_of_mem_Jhat (Ehat_le_Jhat (N1_le_Ehat (bFix_coe_mem_N1_of_mem_NE n.2)))
    refine Subtype.ext (Subtype.ext ?_)
    show ((n : ↥Eam) : Dfull) * ((xhatEam : ↥Eam) : Dfull) =
      ((xhatEam : ↥Eam) : Dfull) * ((n : ↥Eam) : Dfull)
    rw [coe_xhatEam]
    exact h
  have hz2 : (⟨xhatEam, bFix_xhatEam_mem_NE⟩ : NE) * ⟨xhatEam, bFix_xhatEam_mem_NE⟩ = 1 :=
    Subtype.ext (Subtype.ext (by
      show ((xhatEam : ↥Eam) : Dfull) * ((xhatEam : ↥Eam) : Dfull) = 1
      rw [coe_xhatEam]
      exact xhat_mul_self))
  have hC := e6fix_card_le_two_mul_card_centralizer hz hz2 bFix_sq_or_of_mem_NE
    bFix_comm_or_of_mem_NE (⟨y, hy⟩ : NE)
  rw [bFix_natCard_NE] at hC
  have hdvd : Nat.card ↥(centralizer ({(⟨y, hy⟩ : NE)} : Set NE)) ∣ 2 ^ 22 := by
    rw [← bFix_natCard_NE]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj21 : 21 ≤ j := by
    by_contra h
    push Not at h
    have h1 : 2 ^ j ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hjeq] at hC
    omega
  have h2dvd : 2 ^ 21 ∣ Nat.card ↥(centralizer ({(⟨y, hy⟩ : NE)} : Set NE)) := by
    rw [hjeq]
    exact pow_dvd_pow 2 hj21
  refine h2dvd.trans ?_
  have hle : (centralizer ({(⟨y, hy⟩ : NE)} : Set NE)).map NE.subtype ≤
      centralizer ({y} : Set ↥Eam) ⊓ commutator ↥Eam := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨?_, bFix_NE_le_commutator c.2⟩
    exact mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc))
  rw [← Subgroup.card_map_of_injective NE.subtype_injective]
  exact Subgroup.card_dvd_of_le hle

theorem e6fix_card_centralizer_outer {y : ↥Eam} (hy : y ∉ commutator ↥Eam) (hy2 : y * y = 1) :
    Nat.card (centralizer ({y} : Set ↥Eam)) = 13244506413465600 ∨
      Nat.card (centralizer ({y} : Set ↥Eam)) = 190253629440 := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨-, -, b, x, -, -, -, -, -, -, -, -, -, -, -, -, hcl1, hcl2, -, -, -, -, -, -, -, -,
    hc1, hc2, hc3, hc4, -⟩ := native_H_outer_involution_classes hρ
  have hcard : ∀ (a : vStab cv0) (n : ℕ), Nat.card (centralizer ({a} : Set (vStab cv0))) = n →
      ∀ w : ↥Eam, IsConj w (vStabEam a) → Nat.card (centralizer ({w} : Set ↥Eam)) = n :=
    fun a n h w hw => by
      rw [e6fix_card_centralizer_conj_eq hw, e6fix_card_centralizer_mulEquiv vStabEam a, h]
  rcases isConj_of_outer_involution hρ hcl1 hcl2 hy hy2 with (h | h) | (h | h)
  · exact Or.inl (hcard _ _ hc1 y h)
  · exact Or.inl (hcard _ _ hc2 y h)
  · exact Or.inr (hcard _ _ hc3 y h)
  · exact Or.inr (hcard _ _ hc4 y h)

theorem e6fix_two_pow_dvd_outer {y : ↥Eam} (hy : y ∉ commutator ↥Eam) (hy2 : y * y = 1) :
    2 ^ 25 ∣ Nat.card ↥(centralizer ({y} : Set ↥Eam) ⊓ commutator ↥Eam) := by
  have h26 : 2 ^ 26 ∣ Nat.card (centralizer ({y} : Set ↥Eam)) := by
    rcases e6fix_card_centralizer_outer hy hy2 with h | h <;> rw [h] <;> norm_num
  obtain ⟨hidx, -⟩ := short_F4_derived_standard_perfect_cover
  have hr : (commutator ↥Eam).relIndex (centralizer ({y} : Set ↥Eam)) ∣ 2 :=
    (Subgroup.relIndex_dvd_index_of_normal _ _).trans (by rw [hidx])
  have hmul := Subgroup.relIndex_mul_card (H := commutator ↥Eam)
    (K := centralizer ({y} : Set ↥Eam))
  rw [inf_comm] at hmul
  rw [← hmul] at h26
  rcases (Nat.dvd_prime Nat.prime_two).1 hr with h1 | h1
  · rw [h1, one_mul] at h26
    exact (pow_dvd_pow 2 (by norm_num : 25 ≤ 26)).trans h26
  · rw [h1] at h26
    have h27 : 2 * 2 ^ 25 ∣ 2 * Nat.card ↥(centralizer ({y} : Set ↥Eam) ⊓ commutator ↥Eam) := by
      rw [← pow_succ']
      exact h26
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h27

theorem e6fix_two_pow_dvd {y : ↥Eam} (hyy : y * y = 1) (hy : y ∈ NE ∨ y ∉ commutator ↥Eam) :
    2 ^ 20 ∣ Nat.card ↥(centralizer ({y} : Set ↥Eam) ⊓ commutator ↥Eam) := by
  rcases hy with hy | hy
  · exact (pow_dvd_pow 2 (by norm_num : 20 ≤ 21)).trans (e6fix_two_pow_dvd_NE hy)
  · exact (pow_dvd_pow 2 (by norm_num : 20 ≤ 25)).trans (e6fix_two_pow_dvd_outer hy hyy)

theorem e6fix_exists_subgroup_card_pow_of_dvd_range {G H : Type*} [Group G] [Group H] [Finite H]
    (f : G →* H) {p n : ℕ} [Fact p.Prime] (h : p ^ n ∣ Nat.card f.range) :
    ∃ B : Subgroup H, Nat.card B = p ^ n ∧ ∀ b ∈ B, ∃ g : G, f g = b := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := f.range) p h
  refine ⟨K.map f.range.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective f.range.subtype_injective, hK]
  · rintro _ ⟨k, -, rfl⟩
    obtain ⟨g, hg⟩ := k.2
    exact ⟨g, hg⟩

theorem e6fix_dvd_aux {k r d : ℕ} (hk : k ∣ 2) (hd : 2 ^ 20 ∣ d) (h : k * r = d) : 2 ^ 19 ∣ r := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hk with h1 | h1
  · rw [h1, one_mul] at h
    rw [← h] at hd
    exact (pow_dvd_pow 2 (by norm_num : 19 ≤ 20)).trans hd
  · rw [h1] at h
    rw [← h] at hd
    have h2 : 2 * 2 ^ 19 ∣ 2 * r := by
      rw [← pow_succ']
      exact hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2

theorem e6fix_exists_fixed_subgroup {y : ↥Eam} (hyy : y * y = 1)
    (hy : y ∈ NE ∨ y ∉ commutator ↥Eam) :
    ∃ B : Subgroup ↥stdGroup, Nat.card B = 2 ^ 19 ∧ ∀ b ∈ B, e6fix_rho y b = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinE : Finite ↥(commutator ↥Eam) := derived_Eam_facts.2.1
  have hZ2 : Nat.card (center ↥(commutator ↥Eam)) = 2 := derived_Eam_facts.2.2.1
  have hD := e6fix_two_pow_dvd hyy hy
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup ↥Eam, D = centralizer ({y} : Set ↥Eam) ⊓ commutator ↥Eam :=
    ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDle : D ≤ commutator ↥Eam := hDdef ▸ inf_le_right
  obtain ⟨D', hD'def⟩ : ∃ D' : Subgroup ↥(commutator ↥Eam), D' = D.subgroupOf (commutator ↥Eam) :=
    ⟨_, rfl⟩
  have hD'card : Nat.card D' = Nat.card D := by
    rw [hD'def]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range (e6fix_pi.comp D'.subtype)
  have hker : Nat.card (e6fix_pi.comp D'.subtype).ker ∣ 2 := by
    let ψ : ↥(e6fix_pi.comp D'.subtype).ker →* ↥(center ↥(commutator ↥Eam)) :=
      ((D'.subtype).comp (e6fix_pi.comp D'.subtype).ker.subtype).codRestrict _
        (fun d => e6fix_ker_pi.le d.2)
    have hψ : Function.Injective ψ := fun a b h =>
      Subtype.ext (Subtype.ext (congrArg
        (fun z : ↥(center ↥(commutator ↥Eam)) => (z : ↥(commutator ↥Eam))) h))
    exact (Subgroup.card_dvd_of_injective ψ hψ).trans (dvd_of_eq hZ2)
  have h19 : 2 ^ 19 ∣ Nat.card ↥(e6fix_pi.comp D'.subtype).range :=
    e6fix_dvd_aux hker hD (hmul.trans hD'card)
  obtain ⟨B, hB, hBg⟩ := e6fix_exists_subgroup_card_pow_of_dvd_range (p := 2)
    (e6fix_pi.comp D'.subtype) h19
  refine ⟨B, hB, fun b hb => ?_⟩
  obtain ⟨d, rfl⟩ := hBg b hb
  have hmemD : ∀ e : ↥(commutator ↥Eam), e ∈ D' → (e : ↥Eam) ∈ D := fun e he => by
    rw [hD'def] at he
    exact he
  have hd1 : ((d : ↥(commutator ↥Eam)) : ↥Eam) ∈ D := hmemD _ d.2
  have hdD : ((d : ↥(commutator ↥Eam)) : ↥Eam) ∈ centralizer ({y} : Set ↥Eam) := by
    rw [hDdef] at hd1
    exact hd1.1
  have hcomm : MulAut.conjNormal y (d : ↥(commutator ↥Eam)) = (d : ↥(commutator ↥Eam)) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have h1 := mem_centralizer_singleton_iff.1 hdD
    calc y * ((d : ↥(commutator ↥Eam)) : ↥Eam) * y⁻¹ =
        ((d : ↥(commutator ↥Eam)) : ↥Eam) * y * y⁻¹ := by rw [← h1]
      _ = ((d : ↥(commutator ↥Eam)) : ↥Eam) := by group
  exact (e6fix_pi_conj y (d : ↥(commutator ↥Eam))).symm.trans (congrArg e6fix_pi hcomm)

end CFSG.EvenSporadicStandard.Induction.Hyp
