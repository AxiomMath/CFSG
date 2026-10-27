module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ASig4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma baseGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (generators_mem_L h).1
  · exact (generators_mem_L h).2.1

theorem rho_conj_mem_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) : rho * f * rho⁻¹ ∈ fourGrp x₁ x₂ := by
  have hρnormB : rho ∈ Subgroup.normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hmem : rho ∈ Subgroup.normalizer (⁅ctxW t x₁ x₂, zpowers rho⁆ : Subgroup G) :=
      Subgroup.normalizer_commutator_ge_right (H₁ := ctxW t x₁ x₂) (H₂ := zpowers rho)
        (Subgroup.mem_zpowers rho)
    rwa [h.comm_rho] at hmem
  have hfB : f ∈ baseGrp x₁ x₂ := by
    have hfeq := hf
    rw [(h.wreath.fourGrp_eq_omega).1] at hfeq
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1) hfeq
  have hf2 : f ^ 2 = 1 := (h.wreath.fourGrp_eq_omega).2.1.2 f hf
  have hconjB : rho * f * rho⁻¹ ∈ baseGrp x₁ x₂ :=
    (Subgroup.mem_normalizer_iff.mp hρnormB f).mp hfB
  have hconj2 : (rho * f * rho⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hf2, mul_one, mul_inv_cancel]
  rw [(h.wreath.fourGrp_eq_omega).1]
  exact Subgroup.subset_closure ⟨hconjB, hconj2⟩

private lemma rho_mem_normalizer_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) :
    rho ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hle : (fourGrp x₁ x₂).map (MulAut.conj rho).toMonoidHom ≤ fourGrp x₁ x₂ := by
    rw [Subgroup.map_le_iff_le_comap]
    intro f hf
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using rho_conj_mem_fourGrp h hf
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj rho).injective).ge)

theorem eq_one_of_commute_rho_of_mem_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) (hc : rho * f = f * rho) : f = 1 := by
  have hfB : f ∈ baseGrp x₁ x₂ := by
    have hfeq := hf
    rw [(h.wreath.fourGrp_eq_omega).1] at hfeq
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1) hfeq
  have hfL : f ∈ L := baseGrp_le_L h hfB
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hfB
  have hfC : f ∈ Subgroup.centralizer ({rho} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
  have hfP : f ∈ twoCore t := by
    have hmem : f ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨hfW, hfC⟩
    rwa [h.cent_rho] at hmem
  have hmem : f ∈ twoCore t ⊓ L := ⟨hfP, hfL⟩
  rwa [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem

theorem mem_fourGrp_cases_rho (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) :
    f = 1 ∨ f = (x₁ * x₂) ^ 2 ∨ f = rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∨
      f = rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
  have hcomm : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := y_commute_z h.wreath
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h).1
  have hzne1 : (x₁ * x₂) ^ 2 ≠ 1 := (z_mul_self_ne_one h).2
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzpF : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    rho_conj_mem_fourGrp h hzF
  have hρnorm : rho ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    rho_mem_normalizer_fourGrp h
  have hzppF : rho⁻¹ * (x₁ * x₂) ^ 2 * rho ∈ fourGrp x₁ x₂ := by
    have hmem :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρnorm) ((x₁ * x₂) ^ 2)).mp hzF
    simpa using hmem
  have hzp_ne_one : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ 1 := by
    intro h1
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      calc (x₁ * x₂) ^ 2
          = rho⁻¹ * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) * rho := by group
        _ = rho⁻¹ * 1 * rho := by rw [h1]
        _ = 1 := by group
    exact hzne1 hz1
  have hzpp_ne_one : rho⁻¹ * (x₁ * x₂) ^ 2 * rho ≠ 1 := by
    intro h1
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      calc (x₁ * x₂) ^ 2
          = rho * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) * rho⁻¹ := by group
        _ = rho * 1 * rho⁻¹ := by rw [h1]
        _ = 1 := by group
    exact hzne1 hz1
  have hzp_ne_z : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ (x₁ * x₂) ^ 2 := by
    intro h1
    have hc : rho * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * rho := by
      have := congrArg (fun u => u * rho) h1
      simpa [mul_assoc] using this
    exact hzne1 (eq_one_of_commute_rho_of_mem_fourGrp h hzF hc)
  have hzpp_ne_z : rho⁻¹ * (x₁ * x₂) ^ 2 * rho ≠ (x₁ * x₂) ^ 2 := by
    intro h1
    have hc : rho * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * rho := by
      have := congrArg (fun u => rho * u) h1
      have h2 : (x₁ * x₂) ^ 2 * rho = rho * (x₁ * x₂) ^ 2 := by
        simpa [mul_assoc] using this
      exact h2.symm
    exact hzne1 (eq_one_of_commute_rho_of_mem_fourGrp h hzF hc)
  have hzp_ne_zpp : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
    intro h1
    have hρ3 : rho ^ 3 = 1 := by
      rw [← h.ord_rho]
      exact pow_orderOf_eq_one rho
    have hρ2m : rho ^ 2 * rho = 1 := by
      rw [← pow_succ]
      exact hρ3
    have hρm2 : rho * rho ^ 2 = 1 := by
      rw [← pow_succ']
      exact hρ3
    have hρinv : rho⁻¹ = rho ^ 2 := inv_eq_of_mul_eq_one_right hρm2
    have hρinvsq : (rho ^ 2)⁻¹ = rho := inv_eq_of_mul_eq_one_right hρ2m
    have hρsq : rho * rho = rho⁻¹ := by rw [← pow_two, ← hρinv]
    have hρinvsq2 : rho⁻¹ * rho⁻¹ = rho := by
      rw [← mul_inv_rev, ← pow_two, hρinvsq]
    have hconj : (x₁ * x₂) ^ 2 = rho⁻¹ * rho⁻¹ * (x₁ * x₂) ^ 2 * (rho * rho) := by
      have h := congrArg (fun u => rho⁻¹ * u * rho) h1
      calc (x₁ * x₂) ^ 2 = rho⁻¹ * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) * rho := by group
        _ = rho⁻¹ * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) * rho := by rw [h]
        _ = rho⁻¹ * rho⁻¹ * (x₁ * x₂) ^ 2 * (rho * rho) := by group
    have hconj' : (x₁ * x₂) ^ 2 = rho * (x₁ * x₂) ^ 2 * rho⁻¹ := by
      rw [hρinvsq2, hρsq] at hconj
      exact hconj
    have hc : rho * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * rho := by
      have := congrArg (fun u => u * rho) hconj'
      simpa [mul_assoc] using this.symm
    exact hzne1 (eq_one_of_commute_rho_of_mem_fourGrp h hzF hc)
  have hcases := mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) hcomm hy2 hz2 hf
  have hzp_cases :=
    mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) hcomm hy2 hz2 hzpF
  have hzpp_cases :=
    mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) hcomm hy2 hz2 hzppF
  have hy_cases : x₁ ^ 2 = rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∨
      x₁ ^ 2 = rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
    rcases hzp_cases with h1 | h1 | h1 | h1
    · exact absurd h1 hzp_ne_one
    · exact Or.inl h1.symm
    · exact absurd h1 hzp_ne_z
    · rcases hzpp_cases with h2 | h2 | h2 | h2
      · exact absurd h2 hzpp_ne_one
      · exact Or.inr h2.symm
      · exact absurd h2 hzpp_ne_z
      · exact absurd (h1.trans h2.symm) hzp_ne_zpp
  have hyz_cases : x₁ ^ 2 * (x₁ * x₂) ^ 2 = rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∨
      x₁ ^ 2 * (x₁ * x₂) ^ 2 = rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
    rcases hzp_cases with h1 | h1 | h1 | h1
    · exact absurd h1 hzp_ne_one
    · rcases hzpp_cases with h2 | h2 | h2 | h2
      · exact absurd h2 hzpp_ne_one
      · exact absurd (h1.trans h2.symm) hzp_ne_zpp
      · exact absurd h2 hzpp_ne_z
      · exact Or.inr h2.symm
    · exact absurd h1 hzp_ne_z
    · exact Or.inl h1.symm
  rcases hcases with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rcases hy_cases with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (h1.trans h2)))
    · exact Or.inr (Or.inr (Or.inr (h1.trans h2)))
  · exact Or.inr (Or.inl h1)
  · rcases hyz_cases with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (h1.trans h2)))
    · exact Or.inr (Or.inr (Or.inr (h1.trans h2)))

theorem card_closure_y_z_rho (h : Ctx0 t L S x₁ x₂ lam rho) :
    Nat.card (closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Subgroup G) = 12 := by
  have hAeq : (closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Subgroup G) =
      fourGrp x₁ x₂ ⊔ zpowers rho := by
    have hset : ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Set G) =
        ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) ∪ {rho} := by
      ext g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure rho, fourGrp]
  have hcardF : Nat.card (fourGrp x₁ x₂) = 4 := (h.wreath.fourGrp_eq_omega).2.2
  have hcardZ : Nat.card (zpowers rho) = 3 := by rw [Nat.card_zpowers, h.ord_rho]
  have hdisj : Disjoint (fourGrp x₁ x₂) (zpowers rho) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hcardF, hcardZ]
    decide
  have hnormal : zpowers rho ≤ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (rho_mem_normalizer_fourGrp h)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (fourGrp x₁ x₂) (zpowers rho) hnormal hdisj
  rw [hAeq, hcard, hcardF, hcardZ]

theorem closure_y_z_rho_eq_oddOrderGrp (h : Ctx t L S x₁ x₂ lam rho tau) :
    (closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Subgroup G) =
      oddOrderGrp (L ⊓ centralizer ({tau} : Set G)) := by
  obtain ⟨φ⟩ := h.perm_four
  refine eq_oddOrderGrp_of_card φ ?_ (card_closure_y_z_rho h.toCtx0)
  rw [Subgroup.closure_le]
  intro g hg
  have hg' : g = x₁ ^ 2 ∨ g = (x₁ * x₂) ^ 2 ∨ g = rho := by simpa using hg
  rcases hg' with rfl | rfl | rfl
  · exact Subgroup.mem_inf.mpr ⟨(y_z_mem_L h.toCtx0).1,
      Subgroup.mem_centralizer_singleton_iff.mpr (tau_commute_y h).symm⟩
  · exact Subgroup.mem_inf.mpr ⟨(y_z_mem_L h.toCtx0).2,
      Subgroup.mem_centralizer_singleton_iff.mpr (tau_commute_z h).symm⟩
  · exact Subgroup.mem_inf.mpr ⟨h.rho_mem,
      Subgroup.mem_centralizer_singleton_iff.mpr h.tau_rho.symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
