module

public import CFSG.GH74.Generic.S3.L3Cert
public import CFSG.GH74.Generic.Context
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint Subgroup

theorem isSimpleGroup_of_lieModel_L3 {K : Type} [Group K] {p f : ℕ}
    (h : LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f) : IsSimpleGroup K := by
  rcases h with h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity K 3 p f (stated_of_lieModel_PSL h)).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity K 3 p f (stated_of_lieModel_PSU h)).2

theorem rankCertified_two_of_eps {K : Type} [Group K]
    (he : ∃ p f : ℕ, (LieModel K .PSL 3 p f ∧ p ^ f % 4 = 1) ∨
      (LieModel K .PSU 3 p f ∧ p ^ f % 4 = 3)) : RankCertified K 2 := by
  obtain ⟨p, f, h | h⟩ := he
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h.1
    exact (rankCertified_L3_lin (by rw [hF]; omega)).of_mulEquiv e.symm
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data h.1
    exact (rankCertified_U3 hF h.2).of_mulEquiv e.symm

theorem cyclic_of_rankCertified {X : Type} [Group X] [Finite X] (hX : Gen4 X) {K P : Subgroup X}
    (hK : RankCertified ↥K 2) (hKP : ∀ k ∈ K, ∀ p ∈ P, k * p = p * k) (hinf : K ⊓ P = ⊥)
    (hP2 : IsPGroup 2 ↥P) : IsCyclic ↥P := by
  by_contra hnc
  have hP1 : RankCertified ↥P 1 := by
    apply rankCertified_of_not_sectionalTwoRankLE
    intro hle
    apply hnc
    obtain ⟨s, hs, hcl⟩ := hle ⊤ (hP2.of_equiv Subgroup.topEquiv.symm)
    by_cases hne : s.Nonempty
    · obtain ⟨a, ha⟩ := hne
      have hs1 : (s : Set ↥P) = {a} := by
        ext b
        simp only [Finset.mem_coe, Set.mem_singleton_iff]
        exact ⟨fun hb => Finset.card_le_one.1 hs b hb a ha, fun hb => hb ▸ ha⟩
      rw [hs1, ← Subgroup.zpowers_eq_closure] at hcl
      exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨a, hcl⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.coe_empty, Subgroup.closure_empty] at hcl
      have : Subsingleton ↥P := by
        refine ⟨fun a b => ?_⟩
        have ha : a ∈ (⊥ : Subgroup ↥P) := hcl ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup ↥P) := hcl ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      exact isCyclic_of_subsingleton
  let φ : ↥K × ↥P →* X :=
    MonoidHom.noncommCoprod K.subtype P.subtype (fun k p => hKP _ k.2 _ p.2)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, p⟩ hkp
    have h1 : (k : X) * p = 1 := hkp
    have hk : (k : X) ∈ K ⊓ P := by
      refine ⟨k.2, ?_⟩
      have : (k : X) = (p : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact P.inv_mem p.2
    rw [hinf, Subgroup.mem_bot] at hk
    have hp : (p : X) = 1 := by rw [hk, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hk) (Subtype.ext hp)
  exact ((hK.prod hP1).of_injective φ hφ).not_gen4 (by norm_num) hX

end CFSG.GH74.Generic.S3
