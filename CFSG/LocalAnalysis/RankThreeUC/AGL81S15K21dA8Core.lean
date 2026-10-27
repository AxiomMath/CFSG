module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Trans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Mat
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dA8Proof

open CFSG.Quasithin.H13.C1294

theorem concl_E0 : K21dConcl upperSub E0 := by
  refine ⟨eA, eA_mem, eAB, eAB_mem, eA_ne_one, eAB_ne_one, ?_⟩
  have h1 : Nat.card ↥(upperSub ⊓ Subgroup.normalizer (E0 : Set SL4) ⊓
      Subgroup.centralizer ({eAB} : Set SL4)) = 1 := by
    rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
    exact eq_one_of_commute_eAB hg.1.1 hg.1.2 hg.2
  have h2 : 1 < Nat.card ↥(upperSub ⊓ Subgroup.normalizer (E0 : Set SL4) ⊓
      Subgroup.centralizer ({eA} : Set SL4)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hmem : s2 ∈ (upperSub ⊓ Subgroup.normalizer (E0 : Set SL4) ⊓
        Subgroup.centralizer ({eA} : Set SL4)) :=
      ⟨⟨s2_mem_upper, s2_mem_normalizer⟩, s2_mem_centralizer⟩
    rw [hbot] at hmem
    exact s2_ne_one (Subgroup.mem_bot.1 hmem)
  omega


theorem factorization_576_three : Nat.factorization 576 3 = 2 := by
  have h1 : (576 : ℕ) = 3 ^ 2 * 64 := by norm_num
  rw [h1, Nat.factorization_mul (show (3 : ℕ) ^ 2 ≠ 0 by norm_num)
    (show (64 : ℕ) ≠ 0 by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 ∣ 64) by norm_num)]
  simp

theorem exists_conj_of_card_nine {G : Type} [Group G] [Finite G] {D E E' : Subgroup G}
    (hD : Nat.card D = 576) (hE : E ≤ D) (hE' : E' ≤ D) (h9 : Nat.card E = 9)
    (h9' : Nat.card E' = 9) : ∃ d ∈ D, E = E'.map (MulAut.conj d).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ {F : Subgroup G}, F ≤ D → Nat.card F = 9 →
      Nat.card (F.subgroupOf D) = 3 ^ (Nat.card D).factorization 3 := by
    intro F hF h
    rw [hD, factorization_576_three, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv, h]
    norm_num
  let P : Sylow 3 D := Sylow.ofCard (E.subgroupOf D) (hc hE h9)
  let P' : Sylow 3 D := Sylow.ofCard (E'.subgroupOf D) (hc hE' h9')
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D P' P
  refine ⟨d, d.2, ?_⟩
  have hsm : ((d • P' : Sylow 3 D) : Subgroup D) =
      (P' : Subgroup D).map (MulAut.conj d).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have h1 : (P : Subgroup D) = E.subgroupOf D := rfl
  have h2 : (P' : Subgroup D) = E'.subgroupOf D := rfl
  rw [← hd, hsm, h2] at h1
  have h3 := congrArg (Subgroup.map D.subtype) h1
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE] at h3
  have h4 : (E'.subgroupOf D).map D.subtype = E' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE']
  have h5 : D.subtype.comp (MulAut.conj d).toMonoidHom =
      (MulAut.conj (d : G)).toMonoidHom.comp D.subtype := by
    ext x
    rfl
  calc E = Subgroup.map (D.subtype.comp (MulAut.conj d).toMonoidHom) (E'.subgroupOf D) := h3.symm
    _ = Subgroup.map ((MulAut.conj (d : G)).toMonoidHom.comp D.subtype) (E'.subgroupOf D) := by
      rw [h5]
    _ = Subgroup.map (MulAut.conj (d : G)).toMonoidHom ((E'.subgroupOf D).map D.subtype) := by
      rw [← Subgroup.map_map]
    _ = Subgroup.map (MulAut.conj (d : G)).toMonoidHom E' := by rw [h4]


theorem map_conj_mul {G : Type} [Group G] (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_inv_conj {G : Type} [Group G] (H : Subgroup G) (q : G) :
    (H.map (MulAut.conj q).toMonoidHom).map (MulAut.conj q⁻¹).toMonoidHom = H := by
  rw [← map_conj_mul, inv_mul_cancel]
  ext x
  simp

theorem map_conj_of_mem_normalizer {G : Type} [Group G] {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj n).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 hn

theorem concl_of_D {D E : Subgroup SL4}
    (hD : ∀ g : SL4, g ∈ D ↔ (g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 3 0 = 0 ∧ g 3 1 = 0))
    (hD576 : Nat.card D = 576) (hE : E ≤ D) (h9 : Nat.card E = 9) : K21dConcl upperSub E := by
  have hE0 : E0 ≤ D := by
    rintro g ⟨i, j, hg⟩
    rw [hD]
    have h20 : (g : M4) 2 0 = 0 := by rw [hg]; simp [ofBl]
    have h21 : (g : M4) 2 1 = 0 := by rw [hg]; simp [ofBl]
    have h30 : (g : M4) 3 0 = 0 := by rw [hg]; simp [ofBl]
    have h31 : (g : M4) 3 1 = 0 := by rw [hg]; simp [ofBl]
    exact ⟨h20, h21, h30, h31⟩
  obtain ⟨d, hdD, hdE⟩ := exists_conj_of_card_nine hD576 hE hE0 h9 card_E0
  obtain ⟨h20, h21, h30, h31⟩ := (hD d).1 hdD
  obtain ⟨q, hq, n, hn, hdqn⟩ := decomp h20 h21 h30 h31
  rw [hdqn, map_conj_mul, map_conj_of_mem_normalizer hn] at hdE
  have hU : upperSub.map (MulAut.conj q⁻¹).toMonoidHom = upperSub :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer (upperSub.inv_mem hq))
  have hE' : E.map (MulAut.conj q⁻¹).toMonoidHom = E0 := by
    rw [hdE, map_conj_inv_conj]
  have := concl_E0
  rw [← hU, ← hE'] at this
  exact K21dConcl.of_map (MulAut.conj q⁻¹) this

end K21dA8Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
