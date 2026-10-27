module

public import CFSG.CGT.T75E.Excl
public import CFSG.CGT.Timmesfeld75.SimpleAssembly
public import CFSG.CGT.Timmesfeld75.ListWCL2
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.CGT.Timmesfeld75.BenderInputs3
public import CFSG.CGT.T75E.Reduce

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Open

section Basic

variable {K : Type} [Group K] {T : Subgroup K}

theorem mul_self_eq_one_of_mem_conjSubgroup (hT : IsElemAbelian 2 T) {g x : K}
    (hx : x ∈ conjSubgroup g T) : x * x = 1 := by
  have h := hT.2 _ (mem_conjSubgroup.1 hx)
  calc x * x = g * ((g⁻¹ * x * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
    _ = 1 := by rw [h]; group

theorem two_trans_of_conjTwoTransitive (h : ConjTwoTransitive K T) :
    ∀ U₁ U₂ V₁ V₂ : Subgroup K, (∃ x : K, U₁ = conjSubgroup x T) →
      (∃ x : K, U₂ = conjSubgroup x T) → (∃ x : K, V₁ = conjSubgroup x T) →
      (∃ x : K, V₂ = conjSubgroup x T) → U₁ ≠ U₂ → V₁ ≠ V₂ →
        ∃ g : K, conjSubgroup g U₁ = V₁ ∧ conjSubgroup g U₂ = V₂ := by
  rintro _ _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h1 h2
  obtain ⟨g, hg1, hg2⟩ := h a b c d h1 h2
  exact ⟨g, by rw [conjSubgroup_conjSubgroup]; exact hg1,
    by rw [conjSubgroup_conjSubgroup]; exact hg2⟩

end Basic

section Strong

variable {K : Type} [Group K] {T : Subgroup K}

theorem strongWC_of_degenerate (hyp : Lemma26Hyp K T) (hdeg : ¬ Lemma26Nondeg T) :
    StrongWC T := by
  refine strongWC_of_normIn_eq_bot hyp.1 fun g hg => ?_
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  by_contra ht1
  obtain ⟨htT, htN⟩ := mem_normIn.1 ht
  by_cases hcomm : ∀ y ∈ conjSubgroup g T, t * y = y * t
  · apply hg
    refine (hyp.1.2 t htT ht1).2 g fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hcomm y hy
  push Not at hcomm
  obtain ⟨y, hy, hne⟩ := hcomm
  have hyg : g⁻¹ * y * g ∈ T := mem_conjSubgroup.1 hy
  have hy1 : y ≠ 1 := fun h => hne (by rw [h, mul_one, one_mul])
  have hyD : y ∈ classD T := ⟨g⁻¹, g⁻¹ * y * g, hyg, fun h => hy1 (by
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h]; group), by group⟩
  have htD : t ∈ classD T := mem_classD_of_mem htT ht1
  have htt : t * t = 1 := by simpa [pow_two] using hyp.1.1.2 t htT
  have hyy : y * y = 1 := mul_self_eq_one_of_mem_conjSubgroup hyp.1.1 hy
  apply hdeg ⟨t, htD, y, hyD, ?_⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hyt : t * y * t⁻¹ ∈ conjSubgroup g T :=
    ((Subgroup.mem_normalizer_iff.1 htN y).1 hy)
  have hz : (t * y) * (t * y) ∈ conjSubgroup g T := by
    have : (t * y) * (t * y) = (t * y * t⁻¹) * y := by rw [hti]; group
    rw [this]
    exact Subgroup.mul_mem _ hyt hy
  have hzz : ((t * y) * (t * y)) * ((t * y) * (t * y)) = 1 :=
    mul_self_eq_one_of_mem_conjSubgroup hyp.1.1 hz
  have hz1 : (t * y) * (t * y) ≠ 1 := by
    intro h1
    apply hne
    have h2 := eq_inv_of_mul_eq_one_left h1
    rw [_root_.mul_inv_rev, hti, inv_eq_of_mul_eq_one_right hyy] at h2
    exact h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : orderOf (t * y) = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [pow_two] using hz1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]; exact hzz)
  simpa using h4

end Strong

section Bender

variable {K : Type} [Group K] [Finite K] {T : Subgroup K}

theorem lemma26SimpleConcl_of_bender (hB : IsBenderGroup K)
    (hT : IsWC T) (hT1 : T ≠ ⊥) : Lemma26SimpleConcl K T := by
  rcases hB with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · have hM := statedClassicalModel_psl2_of_mulEquiv hn e
    exact ⟨Or.inl ⟨2, n, le_rfl, by omega, hM⟩, fun _ =>
      two_trans_of_conjTwoTransitive (psl2_wc hM hT hT1).1.2.2.1⟩
  · have hM := lieModel_twistedB2_of_mulEquiv_szModel ha e
    exact ⟨Or.inr (Or.inr (Or.inl ⟨2 * a + 1, odd_two_mul_add_one a, by omega, hM⟩)), fun _ =>
      two_trans_of_conjTwoTransitive (sz_wc hM hT hT1).1.2.2.1⟩
  · have hM := statedClassicalModel_psu3_of_mulEquiv hn e
    exact ⟨Or.inr (Or.inl ⟨n, hn, hM⟩), fun _ =>
      two_trans_of_conjTwoTransitive (psu3_wc hn hM hT hT1).1.2.2.1⟩

variable [IsSimpleGroup K]

theorem lemma26SimpleConcl_of_degenerate
    (hAsc : AschbacherNoPolarInput) (hyp : Lemma26Hyp K T) (hdeg : ¬ Lemma26Nondeg T) :
    Lemma26SimpleConcl K T := by
  have hT1 : T ≠ ⊥ := hyp_ne_bot hyp
  have hSW : StrongWC T := strongWC_of_degenerate hyp hdeg
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hna : ∃ a b : K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    exact hyp_classD_inf_center hyp (mem_classD_of_mem ht ht1')
      (Subgroup.mem_center_iff.2 fun g => hcomm g t)
  have hord : orderOf t = 2 := orderOf_eq_prime (hyp.1.1.2 t ht) ht1'
  have heven : Even (Nat.card K) := even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard t)
  rcases lemma25_top hAsc hSW (hyp_normalClosure_eq_top hyp) with hZ | hB
  · exact absurd hZ (not_zStarCase_of_simple K hna heven)
  · have hc : Subgroup.center K = ⊥ := center_eq_bot_of_simple_nonabelian K hna
    have hBender : IsBenderGroup K :=
      isBenderGroup_of_mulEquiv
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)) hB
    exact lemma26SimpleConcl_of_bender hBender hyp.1 hT1

end Bender

end CFSG.CGT.T75E
