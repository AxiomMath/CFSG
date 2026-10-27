module

public import CFSG.Quasithin.H13.L32AC38p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A5Props
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38o

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem false_of_one_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h2 : Lemma14_7_2_F4) (h4 : Lemma14_7_4_two_three_F4) (h11 : Lemma14_7_11_F4)
    {Ks : Fin 1 → Subgroup (MulAut (IntMod C.Wt C.hUe))}
    (hsup : (⨆ i, Ks i) = conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H)))
    (hcommV : (⨆ i, commV (Ks i)) = ⊤) (hmod : ∀ i, G64.ModuleType (Ks i) (commV (Ks i)))
    (hGK : autI C.hUe (tildeOf (fsuV1 T V) H) = conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H))) : False := by
  have hrange : C.ψ.range ≤ ((H1 H b).subgroupOf H).map C.ψ := by
    rw [C.range_ψ, C.map_H1]
    exact hGK.le
  have hW := C.Wt_eq_of_range_le_F4 h1222 h1332 h1334 hrange
  have hrK : C.ψ.range = Ks 0 := by
    rw [C.range_ψ, ← iSup_fin_one' Ks, hsup]
    exact hGK
  have hcV : commV (Ks 0) = ⊤ := by
    rw [← hcommV, iSup_fin_one' (fun i => commV (Ks i))]
  have hm := hmod 0
  rw [hcV] at hm
  rcases hm with ⟨n, -, -, hnat⟩ | ⟨n, hn5, hn8, ⟨π₀, hπ⟩⟩ | ⟨n, hn, ⟨π₀, hπ⟩⟩
  · exact C.false_of_binaryNaturalSL_F4 h1222 h1332 h1334 h4 hW hrK.symm.le hnat
  · have hπi := FFModel.RealizesVia.injective_of_faithful (G64.symDn_faithful hn5) hπ
    interval_cases n
    · exact C.false_of_perm_five_F4 h1222 h1332 h1334 hW hrK hπ
    · exact C.false_of_perm_six_F4 h11 hW hrK hπi hπ.1
    · exact C.false_of_perm_seven_F4 h1222 h1332 h1334 h2 h4 hW hrK hπ
    · exact C.false_of_perm_eight_F4 h1222 h1332 h1334 h4 hW hrK
        (Z := Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8) hπi hπ
  · have hπi := FFModel.RealizesVia.injective_of_faithful
      (G64.symCore_faithful (by rcases hn with rfl | rfl <;> norm_num)) hπ
    rcases hn with rfl | rfl
    · exact C.false_of_perm_six_F4 h11 hW hrK hπi hπ.1
    · exact C.false_of_perm_eight_F4 h1222 h1332 h1334 h4 hW hrK (Z := ⊥) hπi hπ

theorem false_of_two_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (h29 : Thm14_7_29_F4)
    {Ks : Fin 2 → Subgroup (MulAut (IntMod C.Wt C.hUe))}
    (hsup : (⨆ i, Ks i) = conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H)))
    (hind : iSupIndep Ks) (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Ks i, ∀ y ∈ Ks j, x * y = y * x)
    (hcommV : (⨆ i, commV (Ks i)) = ⊤) (hfixV : ∀ i j, i ≠ j → commV (Ks j) ≤ fixV (Ks i))
    (hmod : ∀ i, G64.ModuleType (Ks i) (commV (Ks i))) (hfac : ∀ i, G64.FactorType (Ks i))
    {t : MulAut (IntMod C.Wt C.hUe)} (htG : t ∈ autI C.hUe (tildeOf (fsuV1 T V) H))
    (ht2 : t ^ 2 = 1)
    (hGt : autI C.hUe (tildeOf (fsuV1 T V) H) = conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H)) ⊔ Subgroup.zpowers t)
    (hswap : ∀ i j, i ≠ j → (Ks i).map (MulAut.conj t).toMonoidHom = Ks j) : False := by
  have hKeq : conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H)) = ((H1 H b).subgroupOf H).map C.ψ := C.map_H1.symm
  have hK01 : Ks 0 ⊔ Ks 1 = conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H)) := by rw [← iSup_fin_two' Ks, hsup]
  have hK₀ : Ks 0 ≤ ((H1 H b).subgroupOf H).map C.ψ := hKeq ▸ hK01 ▸ le_sup_left
  have hK₁ : Ks 1 ≤ ((H1 H b).subgroupOf H).map C.ψ := hKeq ▸ hK01 ▸ le_sup_right
  have hdisj : Ks 0 ⊓ Ks 1 = ⊥ := (hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)).eq_bot
  have hc01 := hcomm 0 1 (by decide)
  have h3₀ := exists_three_of_factorType (hfac 0)
  have h3₁ := exists_three_of_factorType (hfac 1)
  have haG : C.ψ ⟨b, C.bH⟩ ∈ autI C.hUe (tildeOf (fsuV1 T V) H) := by
    rw [← C.range_ψ]
    exact ⟨_, rfl⟩
  have hKG : conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
      (autI C.hUe (tildeOf (fsuV1 T V) H)) ≤ autI C.hUe (tildeOf (fsuV1 T V) H) :=
    conjClosure_zpowers_le Subgroup.le_normalizer haG
  have hsq : ∀ g ∈ C.ψ.range, g ^ 2 ∈ ((H1 H b).subgroupOf H).map C.ψ := by
    intro g hg
    have hg' : g ∈ conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩))
        (autI C.hUe (tildeOf (fsuV1 T V) H)) ⊔ Subgroup.zpowers t := by
      rw [← hGt, ← C.range_ψ]
      exact hg
    rw [← hKeq]
    exact sq_mem_of_mem_sup_zpowers ht2 (le_normalizer_conjClosure _ _ htG) hg'
  have hW := C.Wt_eq_of_two_F4 h1222 h1332 h1334 hK₀ hK₁ hc01 hdisj h3₀ h3₁ hsq
  have hmemR : ∀ {e : MulAut (IntMod C.Wt C.hUe)}, e ∈ ((H1 H b).subgroupOf H).map C.ψ →
      e ∈ C.ψ.range := fun he => Subgroup.map_le_range _ _ he

  have hsolv : Group.IsSolvable ↥(Ks 0) → Group.IsSolvable ↥(Ks 1) → False := by
    intro hs0 hs1
    have hG' : Group.IsSolvable ↥(autI C.hUe (tildeOf (fsuV1 T V) H)) :=
      isSolvable_sup_zpowers hs0 hs1 hc01 htG (hK01 ▸ hKG) (by rw [hK01]; exact hGt)
        (by rw [hK01]; exact le_normalizer_conjClosure _ _)
    exact C.false_of_isSolvable_range_F4 h29 hW (by rw [C.range_ψ]; exact hG')
  have hmapS : ∀ i j, i ≠ j → Group.IsSolvable ↥(Ks i) → Group.IsSolvable ↥(Ks j) := by
    intro i j hij hs
    rw [← hswap i j hij]
    exact Group.isSolvable_of_surjective
      (MonoidHom.subgroupMap_surjective (MulAut.conj t).toMonoidHom (Ks i))
  rcases C.fix3_or_solvable (hmod 0) with hs0 | hf0
  · exact hsolv hs0 (hmapS 0 1 (by decide) hs0)
  rcases C.fix3_or_solvable (hmod 1) with hs1 | hf1
  · exact hsolv (hmapS 1 0 (by decide) hs1) hs1

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨-, a, -, -, -, ha, haV, -, -⟩ := S14.exists_basis_F4
  set w₀ : IntMod C.Wt C.hUe :=
    IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW (le_conjClosure V H (hV2.2.1 ha))⟩ with hw₀
  have hw₀s : w₀ ∈ commV (Ks 0) ⊔ commV (Ks 1) := by
    rw [← iSup_fin_two' (fun i => commV (Ks i)), hcommV]
    exact Subgroup.mem_top _
  obtain ⟨u₀, hu₀, u₁, hu₁, hu⟩ := Subgroup.mem_sup.mp hw₀s
  obtain ⟨e₀, he₀, h30, h10, hf₀⟩ := hf0 u₀ hu₀
  obtain ⟨e₁, he₁, h31, h11, hf₁⟩ := hf1 u₁ hu₁
  have hfix₀ : e₀ w₀ = w₀ := by
    have h1 := (mem_fixV.mp (hfixV 0 1 (by decide) hu₁)) e₀ he₀
    rw [← hu, map_mul, hf₀, h1]
  have hfix₁ : e₁ w₀ = w₀ := by
    have h0 := (mem_fixV.mp (hfixV 1 0 (by decide) hu₀)) e₁ he₁
    rw [← hu, map_mul, hf₁, h0]
  exact C.false_of_e9_fix_F4 h1222 h1332 h1334 h4 hV2 hW (hmemR (hK₀ he₀)) (hmemR (hK₁ he₁))
    h30 h31 (hc01 _ he₀ _ he₁)
    (indep_of_inf_eq_bot hdisj he₀ he₁ h30 h10 h31 h11) ha haV hfix₀ hfix₁

theorem false_of_concl_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h2 : Lemma14_7_2_F4) (h4 : Lemma14_7_4_two_three_F4) (h11 : Lemma14_7_11_F4) (h29 : Thm14_7_29_F4)
    (hG64 : G64.LemmaG64) : False := by
  obtain ⟨s, Ks, -, hsup, hind, hcomm, hcommV, hfixV, -, -, -, hmod, h3, -⟩ := C.concl hG64
  rcases h3 with ⟨rfl, hGK⟩ | ⟨rfl, hfac, t, htG, -, ht2, hGt, hswap⟩
  · exact C.false_of_one_F4 h1222 h1332 h1334 h2 h4 h11 hsup hcommV hmod hGK
  · exact C.false_of_two_F4 h1222 h1332 h1334 h4 h29 hsup hind hcomm hcommV hfixV hmod hfac htG ht2
      hGt hswap

end Ctx38

theorem lemma14_7_38_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (h2 : Lemma14_7_2_F4)
    (h4 : Lemma14_7_4_two_three_F4) (h11 : Lemma14_7_11_F4) (h29 : Thm14_7_29_F4)
    (hG64 : G64.LemmaG64) : Lemma14_7_38_F4 := by
  intro G _ _ T L V H S γ γ' g s
  have hle : F8.Dγ V (fsuV1 T V) H (g : G) ≤ F8.Uγ V H (g : G) := centralizerMod_le_left _ _ _
  refine lt_of_le_of_ne hle fun hD => ?_
  have hF := hypF98_of_F4 h1222 h1332 h1334 hA37 hA38 hA39 S
  obtain ⟨b, hbH, hbQ, c, hcU, hcV, htr⟩ := exists_transvection_of_eq hF s hD.symm
  exact (Ctx38.mk S hF hbH hbQ hcU hcV htr).false_of_concl_F4 h1222 h1332 h1334 h2 h4 h11 h29 hG64

end CFSG.Quasithin.H13.L32A.C
