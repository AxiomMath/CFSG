module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444n

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setup5_F4
open CFSG.Quasithin.H13.L1444.Setup5_F4
open CFSG.Quasithin.H13.L1444.Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5_F4 G T L V V₂ g D Q₁ Q₂)
include S

theorem exists_swap_invol_F4 {A : Subgroup G}
    (hA : A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g) (helem : IsElemAbelian 2 A)
    (h8 : 8 < Nat.card A) :
    ∃ σ ∈ CFSG.conjugate (l32nW T V V₂) g, σ ∉ pCoreOf 2 (l32nH T V) ∧ σ * σ = 1 ∧
      (∀ q ∈ Q₁, σ * q * σ⁻¹ ∈ Q₂) ∧ (∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁) := by
  have hns : ¬ ∀ x ∈ CFSG.conjugate (l32nW T V V₂) g, x ∉ pCoreOf 2 (l32nH T V) →
      x ∈ Subgroup.normalizer (Q₁ : Set G) ∧ x ∈ Subgroup.normalizer (Q₂ : Set G) := fun h => by
    have := S.card_le_eight_of_not_swap h hA helem
    omega
  push Not at hns
  obtain ⟨x, hxW, hxQ, hxN⟩ := hns
  have hxU : ∀ q ∈ Q₁ ⊔ Q₂, x * q * x⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq => by
    rw [S.sup] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      (L14332.l32nH_le_normalizer_fsuU T V (S.Wg_le_H hxW)) q).mp hq
  rcases S.cfg.map_conj_cases hxU with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (Q8SqE9.mem_normalizer_of_map_eq h2) (hxN (Q8SqE9.mem_normalizer_of_map_eq h1))
  have hx12 : ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₂ := fun q hq => by
    rw [← h1]
    exact ⟨q, hq, by simp⟩
  have hx21 : ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₁ := fun q hq => by
    rw [← h2]
    exact ⟨q, hq, by simp⟩

  obtain ⟨v, hv, hxv⟩ := S.exists_invol hxW hxQ
  have hvU : v ∈ Q₁ ⊔ Q₂ := S.sup ▸ V_le_U hv
  have hv₁ : v ∈ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.le_centralizer_iff.mp S.cfg.comm).trans
      (Subgroup.centralizer_le_normalizer _)) hvU
  have hv₂ : v ∈ Subgroup.normalizer (Q₂ : Set G) :=
    sup_le (S.cfg.comm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer hvU
  refine ⟨x * v, (CFSG.conjugate (l32nW T V V₂) g).mul_mem hxW (S.V_le_Wg hv), fun h => hxQ ?_,
    hxv, fun q hq => ?_, fun q hq => ?_⟩
  · have := (pCoreOf 2 (l32nH T V)).mul_mem h ((pCoreOf 2 (l32nH T V)).inv_mem (S.V_le_Q hv))
    simpa using this
  · have h3 : v * q * v⁻¹ ∈ Q₁ := (Subgroup.mem_normalizer_iff.mp hv₁ q).mp hq
    have h4 := hx12 _ h3
    rwa [show x * (v * q * v⁻¹) * x⁻¹ = x * v * q * (x * v)⁻¹ by group] at h4
  · have h3 : v * q * v⁻¹ ∈ Q₂ := (Subgroup.mem_normalizer_iff.mp hv₂ q).mp hq
    have h4 := hx21 _ h3
    rwa [show x * (v * q * v⁻¹) * x⁻¹ = x * v * q * (x * v)⁻¹ by group] at h4

theorem card_le_eight_F4 {A : Subgroup G} (hA : A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g)
    (helem : IsElemAbelian 2 A) : Nat.card A ≤ 8 := by
  by_contra h
  push Not at h
  obtain ⟨σ, hσW, hσQ, hσ2, h12, h21⟩ := S.exists_swap_invol_F4 hA helem h
  obtain ⟨c, hcK, -, hcfpf, hσc⟩ := S.exists_c0 S.K9 (S.Wg_le_H hσW) hσ2 h12 h21
  exact S.not_split_F4 (S.exists_complement_L_F4 hσW hσQ hσ2 hcK (hcfpf (cN hcK)) hσc)

end Setup5_F4

end L1444

open L1444 in

theorem lemma1444Six_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4) (hCTL : Lemma1444CTL_F4) : Lemma1444Six_F4 := by
  intro G _ _ T L V h hext h32 hG2
  classical
  refine ⟨?_, fun V₂ g hV₂ hgP hgH A hA helem => ?_⟩
  · have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
    have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
    obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
    obtain ⟨D, Q₁, Q₂, S⟩ := exists_setup5_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL h hext
      h32 hG2 hV₂ hgP hgH
    exact S.not_split_F4
  · obtain ⟨D, Q₁, Q₂, S⟩ := exists_setup5_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL h hext
      h32 hG2 hV₂ hgP hgH
    exact S.card_le_eight_F4 hA helem

open L1444 in

theorem fsuU_eq_pCoreOf_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4) (hCTL : Lemma1444CTL_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
      CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
      ¬ LieModel G .G2 0 3 1 → fsuU T V = pCoreOf 2 (l32nH T V) := by
  intro G _ _ T L V h hext h32 hG2
  classical
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  obtain ⟨D, Q₁, Q₂, S⟩ := exists_setup5_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL h hext
    h32 hG2 hV₂ hgP hgH
  exact S.QU

end CFSG.Quasithin.H13
