module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusTr

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36 Certificates.FzFus

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G} {π : Model →* G}

private lemma fzfus_lab_wreath_le_L
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    wreathGrp x₁ x₂ lam ≤ L := by
  rw [← h.ctx.inf_eq]
  exact inf_le_right

private lemma fzfus_lab_gen_mem_L
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    x₁ ∈ L ∧ x₂ ∈ L ∧ lam ∈ L := by
  have hW : wreathGrp x₁ x₂ lam ≤ L := fzfus_lab_wreath_le_L h
  exact ⟨hW (Subgroup.subset_closure (by simp)), hW (Subgroup.subset_closure (by simp)),
    hW (Subgroup.subset_closure (by simp))⟩

private lemma fzfus_lab_lam_conj
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) :
    ∃ c ∈ L, c * (x₁ * x₂) ^ 2 * c⁻¹ = lam := by
  obtain ⟨-, -, hlam⟩ := fzfus_lab_gen_mem_L h
  have hinv := (hd.isInvM_iff lamM).mp label_facts.1
  rw [hd.lam_eq] at hinv
  have h2 : lam * lam = 1 := by
    have hh := h.shape.lam_sq
    rwa [pow_two] at hh
  exact h.ctx.invol_L lam hlam h2 hinv.2

theorem fzfus_L1 (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) :
    IsConj ((x₁ * x₂) ^ 2) (π (rep .z12)) ∧ IsConj ((x₁ * x₂) ^ 2) (π (rep .z3)) ∧
      IsConj ((x₁ * x₂) ^ 2) (π (rep .lam)) := by
  obtain ⟨hx₁, hx₂, hlam⟩ := fzfus_lab_gen_mem_L h
  have hz12 : π (rep .z12) = x₁ ^ 2 := by
    have hh : π z1M = π (x1M * x1M) := (hd.eq_iff z1M (x1M * x1M)).mpr z1M_keq
    rw [map_mul, hd.x₁_eq] at hh
    rw [show rep .z12 = z1M from rfl, hh, pow_two]
  have hinv12 : π (rep .z12) * π (rep .z12) = 1 ∧ π (rep .z12) ≠ 1 := by
    have hh := (hd.isInvM_iff z1M).mp label_facts.2.1
    rw [show rep .z12 = z1M from rfl]
    exact hh
  have hz12L : π (rep .z12) ∈ L := by
    rw [hz12]
    exact pow_mem hx₁ 2
  have h1 : IsConj ((x₁ * x₂) ^ 2) (π (rep .z12)) := by
    obtain ⟨c, -, hc⟩ := h.ctx.invol_L _ hz12L hinv12.1 hinv12.2
    exact isConj_iff.mpr ⟨c, hc⟩
  have hz3 : π (rep .z3) = (x₁ * x₂) ^ 2 := by
    have hh : π z3M = π (x1M * x2M * (x1M * x2M)) := (hd.eq_iff _ _).mpr z3M_keq
    rw [show rep .z3 = z3M from rfl, hh]
    rw [show x1M * x2M * (x1M * x2M) = (x1M * x2M) ^ 2 from (pow_two _).symm]
    simp only [map_pow, map_mul, hd.x₁_eq, hd.x₂_eq]
  have h2 : IsConj ((x₁ * x₂) ^ 2) (π (rep .z3)) := by
    simpa [hz3] using IsConj.refl ((x₁ * x₂) ^ 2)
  have hπl : π (rep .lam) = lam := by
    rw [show rep .lam = lamM from rfl, hd.lam_eq]
  have hinvl : lam * lam = 1 ∧ lam ≠ 1 := by
    have hh := (hd.isInvM_iff lamM).mp label_facts.1
    rw [hd.lam_eq] at hh
    exact hh
  have h3 : IsConj ((x₁ * x₂) ^ 2) (π (rep .lam)) := by
    rw [hπl]
    obtain ⟨c, -, hc⟩ := h.ctx.invol_L lam hlam hinvl.1 hinvl.2
    exact isConj_iff.mpr ⟨c, hc⟩
  exact ⟨h1, h2, h3⟩

theorem fzfus_L2 (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) : IsConj t (π (rep .oI)) := by
  obtain ⟨c, hcL, hc⟩ := fzfus_lab_lam_conj h hd
  have hct : c * t = t * c :=
    Subgroup.mem_centralizer_iff.mp h.ctx.hyp.mem_centralizer c hcL
  have hπ : π (rep .oI) = t * lam := by
    rw [show rep .oI = tM * lamM from rep_oI_eq, map_mul, hd.t_eq, hd.lam_eq]
  refine isConj_iff.mpr ⟨c * a₃₂, ?_⟩
  rw [hπ]
  calc (c * a₃₂) * t * (c * a₃₂)⁻¹ = c * (a₃₂ * t * a₃₂⁻¹) * c⁻¹ := by group
    _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [a32_conj_t h]
    _ = t * lam := by
          rw [← hc]
          calc c * (t * (x₁ * x₂) ^ 2) * c⁻¹
              = (c * t) * (x₁ * x₂) ^ 2 * c⁻¹ := by group
            _ = (t * c) * (x₁ * x₂) ^ 2 * c⁻¹ := by rw [hct]
            _ = t * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group

private lemma fzfus_lab_conj_tau
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) {m : Model}
    (hm : IsInvM m) (hcomm : KEq (m * tM) (tM * m)) (hphi : phi 0 1 m ≠ 1) :
    IsConj tau (π m) ∨ IsConj (t * tau) (π m) := by
  have hinv := (hd.isInvM_iff m).mp hm
  have hwt : π m * t = t * π m := by
    have hh : π (m * tM) = π (tM * m) := (hd.eq_iff (m * tM) (tM * m)).mpr hcomm
    simpa only [map_mul, hd.t_eq] using hh
  have hwH : π m ∈ invCent t := by
    rw [invCent, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hwt.symm
  have hwT : π m ∈ T₂ := hd.mem_T₂_iff.mpr ⟨m, rfl⟩
  have hwS : π m ∈ S := by
    rw [fzfus_S_eq h]
    exact ⟨hwT, hwH⟩
  have hwPL : π m ∉ twoCore t ⊔ L := by
    intro hPL
    have hmem : π m ∈ S ⊓ (twoCore t ⊔ L) := ⟨hwS, hPL⟩
    rw [h.ctx.inf_PL] at hmem
    have hle : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ ((phi 0 1).ker.map π) := by
      refine sup_le ?_ ?_
      · intro p hp
        rcases fzFus_eq_one_or_eq_t_of_mem h hp with hp1 | hp1
        · rw [hp1]
          exact one_mem _
        · rw [hp1]
          exact Subgroup.mem_map.mpr ⟨tM, phiQ_facts.1, hd.t_eq⟩
      · refine (Subgroup.closure_le ((phi 0 1).ker.map π)).mpr ?_
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · exact Subgroup.mem_map.mpr ⟨x1M, phiQ_facts.2.1, hd.x₁_eq⟩
        · exact Subgroup.mem_map.mpr ⟨x2M, phiQ_facts.2.2.1, hd.x₂_eq⟩
        · exact Subgroup.mem_map.mpr ⟨lamM, phiQ_facts.2.2.2.1, hd.lam_eq⟩
    obtain ⟨m', hm'ker, hm'm⟩ := Subgroup.mem_map.mp (hle hmem)
    have hker' : phi 0 1 m' = 1 := hm'ker
    have hkeq : KEq m' m := (hd.eq_iff m' m).mp hm'm
    rcases hkeq with rfl | hmm
    · exact hphi hker'
    · rw [hmm, map_mul, phi_zeta 0 1, mul_one] at hker'
      exact hphi hker'
  have hwSq : (π m) ^ 2 ∈ twoCore t := by
    rw [pow_two, hinv.1]
    exact one_mem _
  obtain ⟨k, -, p, hp, hconj⟩ := h.ctx.invol_outer (π m) hwH hwPL hwSq
  rcases fzFus_eq_one_or_eq_t_of_mem h hp with hp1 | hp1
  · left
    refine IsConj.symm (isConj_iff.mpr ⟨k, ?_⟩)
    rw [hconj, hp1, one_mul]
  · right
    refine IsConj.symm (isConj_iff.mpr ⟨k, ?_⟩)
    rw [hconj, hp1]

theorem fzfus_L3 (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) :
    (IsConj tau (π (rep .oJ)) ∨ IsConj (t * tau) (π (rep .oJ))) ∧
      (IsConj tau (π (rep .oK)) ∨ IsConj (t * tau) (π (rep .oK))) := by
  exact ⟨fzfus_lab_conj_tau h hd label_facts.2.2.2.2.1 label_facts.2.2.2.2.2.2.1
      phiQ_facts.2.2.2.2.1,
    fzfus_lab_conj_tau h hd label_facts.2.2.2.2.2.1 label_facts.2.2.2.2.2.2.2
      phiQ_facts.2.2.2.2.2⟩

end CFSG.OddStandard.SmallF3.FritzII
