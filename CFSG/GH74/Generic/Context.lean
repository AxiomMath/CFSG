module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.L5U5.ModelsBridge

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
  CFSG.GH74.Filter.ClassicalOdd

section Context

variable {G : Type} [Group G]

theorem xbar_comm (x : G) (c : CentralizerBar x) : c * xbar x = xbar x * c :=
  Subgroup.mem_center_iff.1 (xbar_mem_center x) c

theorem xbar_not_mem_of_center_eq_bot [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hc : center ↥K = ⊥) : xbar x ∉ K := by
  intro hmem
  have hcen : (⟨xbar x, hmem⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (xbar_mem_center x) (g : CentralizerBar x))
  rw [hc, Subgroup.mem_bot] at hcen
  exact xbar_ne_one hx (congrArg Subtype.val hcen)

theorem not_rankCertified_three_of_xbar_not_mem [Finite G] (hG : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hK : xbar x ∉ K) :
    ¬ RankCertified ↥K 3 :=
  not_rankCertified_three_of_gen4 (gen4_centralizerBar hG x) (xbar_comm x)
    (xbar_mul_self hx) hK

theorem xbar_mem_of_q8q8 [Finite G] (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (φ : Q8 × Q8 →* ↥K) (hφ : Function.Injective φ) :
    xbar x ∈ K := by
  let Φ : Q8 × Q8 →* CentralizerBar x := K.subtype.comp φ
  have hΦ : Function.Injective Φ := K.subtype_injective.comp hφ
  have hT : Subgroup.zpowers (xbar x) ≤ Φ.range :=
    q8q8_commuting_two_subgroup_le (gen4_centralizerBar hG x) Φ hΦ _
      (isPGroup_zpowers_of_orderOf_eq_two (orderOf_xbar hx))
      (fun a t ht => commute_of_mem_zpowers_xbar x (Φ a) ht)
  obtain ⟨a, ha⟩ := hT (Subgroup.mem_zpowers _)
  rw [← ha]
  exact (φ a).2

theorem xbar_mem_of_isSL4Model [Finite G] (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hK : IsSL4Model ↥K) : xbar x ∈ K := by
  obtain ⟨z, φ, -, -, hφ, -⟩ := hK.exists_center_q8q8
  exact xbar_mem_of_q8q8 hG hx φ hφ

end Context

noncomputable def mulEquivOfCenterBot {K : Type*} [Group K] (h : center K = ⊥) :
    K ≃* K ⧸ center K :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)

theorem nonempty_mulEquiv_of_center_eq_bot {K S : Type*} [Group K] [Group S] (h : center K = ⊥)
    (e : K ⧸ center K ≃* S) : Nonempty (K ≃* S) :=
  ⟨(mulEquivOfCenterBot h).trans e⟩

theorem eq_three_of_pow_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : p ^ f = 3) :
    p = 3 ∧ f = 1 := by
  have hdvd : p ∣ 3 := h ▸ dvd_pow_self p (by omega)
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h)⟩

section Extract

variable {S : Type} [Group S] {n p f : ℕ}

theorem stated_of_lieModel_PSL (h : LieModel S .PSL n p f) : StatedClassicalModel S .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem stated_of_lieModel_PSU (h : LieModel S .PSU n p f) : StatedClassicalModel S .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem stated_of_lieModel_PSp (h : LieModel S .PSp n p f) : StatedClassicalModel S .PSp n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem lieModel_psl_data (h : LieModel S .PSL n p f) :
    p.Prime ∧ 1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (S ≃* StatedProj (StatedSL n F)) := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, e⟩ := stated_of_lieModel_PSL h
  exact ⟨hp, hf, F, inferInstance, inferInstance, hF, e⟩

theorem lieModel_psu_data (h : LieModel S .PSU n p f) :
    p.Prime ∧ 1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ f) ^ 2 ∧
      Nonempty (S ≃* StatedProj (StatedSU n (p ^ f) F)) := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, e⟩ := stated_of_lieModel_PSU h
  exact ⟨hp, hf, F, inferInstance, inferInstance, hF, e⟩

theorem lieModel_psp_data (h : LieModel S .PSp n p f) :
    p.Prime ∧ 1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (S ≃* StatedProj (StatedSp n F)) := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, e⟩ := stated_of_lieModel_PSp h
  exact ⟨hp, hf, F, inferInstance, inferInstance, hF, e⟩

end Extract

theorem ringChar_ne_two_of_card_eq {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : ringChar F ≠ 2 := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  exact ringChar_ne_two_of_two_ne_zero (two_ne_zero_of_odd_card hodd)

end CFSG.GH74.Generic
