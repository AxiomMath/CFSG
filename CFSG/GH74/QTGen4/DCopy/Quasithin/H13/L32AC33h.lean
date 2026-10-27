module

public import CFSG.Quasithin.H13.L32AC33h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem false_of_sz_F4 (h7 : Lemma14_7_7_F4) (h30 : Lemma14_7_30_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (h29 : Thm14_7_29_F4) (hSzB : SzAutBorelThree)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) {e : ℕ}
    (hSz : IsSz e (cStar K)) : False := by
  obtain ⟨-, -, S₀, -⟩ := h30 G T L V H S K hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun s hs k hk =>
    H.mul_mem (H.mul_mem (hTH hs) (hKH hk)) (H.inv_mem (hTH hs))
  have hH₀H : conjClosure K T ⊔ (l1 T L V ⊔ T) ≤ H := sup_le hK₀H S.hz.1.1
  have hKH₀ : K ≤ conjClosure K T ⊔ (l1 T L V ⊔ T) := (le_conjClosure K T).trans le_sup_left
  have hK₀ : K ∈ cComp (conjClosure K T ⊔ (l1 T L V ⊔ T)) := mem_cComp_of_le_of_le hK hKH₀ hH₀H
  have h121 := lemma_1_2_1_three S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian hA37 hA38
    S₀.hz.1.2 hK₀
  have hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G) :=
    fun y hy hy3 =>
      mem_normalizer_of_cube hKH₀ (h121.imp_right fun h => h.1) (Setting147.l1H' S₀ hy) hy3
  have hc : ∀ y ∈ l1 T L V, y ^ 3 = 1 → ∀ k ∈ K,
      y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ (l1 T L V ⊔ T)) := by
    intro y hy hy3 k hk
    by_cases hA : ∃ r ∈ T, r ∈ Subgroup.normalizer (K : Set G) ∧
        r ∉ L32NSet14.trivSub V (fsuV1 T V)
    · obtain ⟨r, hrT, hrN, hrn⟩ := hA
      exact comm_of_inv_F4 h1222 h1332 h1334 S₀ hK₀ hSz hrT hrN hrn hy hy3 (hyN y hy hy3) hk
    · push Not at hA
      have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
      have : IsMulCommutative ↥V := (hMod G T L V S₀.hyp.hyp S₀.hyp.fsu).1.1
      obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S₀.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
      have S14 := Hyp147.set14_F4 S₀.hyp h1222 h1332 h1334 hV2
      obtain ⟨t₀, ht₀T, ht₀n⟩ := S14.exists_T_not_triv_F4
      have ht₀N : t₀ ∉ Subgroup.normalizer (K : Set G) := fun h => ht₀n (hA t₀ ht₀T h)
      have ht₀H : t₀ ∈ conjClosure K T ⊔ (l1 T L V ⊔ T) := Setting147.TH' S₀ ht₀T
      have h2 : (conjSubgroupsBy (conjClosure K T ⊔ (l1 T L V ⊔ T)) K).ncard = 2 := by
        rcases h121 with hn | ⟨h2, -⟩
        · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH₀).mp hn ht₀H) ht₀N
        · exact h2
      have C : CtxB T L V (conjClosure K T ⊔ (l1 T L V ⊔ T)) K t₀ :=
        ⟨S₀, hK₀, ht₀T, ht₀N, mem_normalizer_or_of_ncard h2 ht₀H ht₀N, hyN, hA⟩
      exact C.comm_F4 hSzB hA37 h29 h1222 h1332 h1334 hSz hy hy3 hk
  have hc' := comm_of_cube_F4 h1222 h1332 h1334 S₀ hKH₀ hc
  exact false_of_l1_comm_F4 h7 h1332 S₀ (l1T_le_normalizer_conjClosure_F4 h1222 h1332 h1334 S₀ hyN)
    (comm_conjClosure_F4 h1332 S₀ hKH₀ hc') hK₀ hSz

theorem lemma14_7_33_of_F4 (h7 : Lemma14_7_7_F4) (h30 : Lemma14_7_30_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (h29 : Thm14_7_29_F4) (hSzB : SzAutBorelThree) : Lemma14_7_33_F4 := by
  intro G _ _ T L V H S K hK n hn
  exact false_of_sz_F4 h7 h30 h1222 h1332 h1334 hA37 hA38 h29 hSzB S hK hn

end CFSG.Quasithin.H13.L32A.C
