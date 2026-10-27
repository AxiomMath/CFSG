module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC40f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC48b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]

theorem isIrrPlus_top_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h38 : Lemma14_7_38_F4) (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHKT : H = K ⊔ T) (hA5 : IsAlt 5 (cStar K))
    (hl1K : l1 T L V ≤ K) :
    XMod.IsIrrPlus ↥(autIH (fsuV1 T V) V H (conjClosure K T))
      (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := hK₀ ▸ hF.K₀_normal
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  set Φ := phiU hF with hΦ
  have hLb : autIH (fsuV1 T V) V H (conjClosure K T) = (K.subgroupOf H).map Φ := by
    rw [autIH_eq_map hF hF.K₀_le_H, hK₀]
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  obtain ⟨I, hV₁I, hIU, W, -, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hI : subM (fsuV1 T V) (conjClosure V H) I ∈ IrrPlusOn
      (autIH (fsuV1 T V) V H (conjClosure K T)) W (autIH (fsuV1 T V) V H T) := hirrU
  obtain ⟨⟨-, hinv, hcomm, hirr⟩, -⟩ := hI
  set Ĩ := subM (fsuV1 T V) (conjClosure V H) I with hĨ
  suffices hT : Ĩ = ⊤ by
    rw [← hT]
    exact ⟨hinv, hcomm, hirr⟩
  by_contra hne

  have hYinv : ∀ l ∈ (K.subgroupOf H).map Φ, ∀ y ∈ Ĩ, l y ∈ Ĩ := by
    intro l hl y hy
    rw [← hLb] at hl
    exact hinv ⟨l, hl⟩ y hy
  have hntY : ∃ l ∈ (K.subgroupOf H).map Φ, ∃ y ∈ Ĩ, l y * y⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : Ĩ = ⊥ := by
      rw [eq_bot_iff, ← hcomm]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a, l, hl, rfl⟩
      have ha : (a : MulAut _) ∈ (K.subgroupOf H).map Φ := hLb ▸ a.2
      exact Subgroup.mem_bot.mpr (hall _ ha l hl)
    have h1 := hirr.1
    rw [hbot] at h1
    exact not_lt_bot h1

  have hLn : ∀ h : ↥H, ∀ l ∈ (K.subgroupOf H).map Φ,
      Φ h * l * (Φ h)⁻¹ ∈ (K.subgroupOf H).map Φ := by
    rintro h _ ⟨k, hk, rfl⟩
    refine ⟨h * k * h⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKnH h.2) k).mp (Subgroup.mem_subgroupOf.mp hk)
  by_cases hinvH : ∀ h : ↥H, ∀ w ∈ Ĩ, Φ h w ∈ Ĩ
  ·
    have hIH : ∀ h ∈ H, ∀ a ∈ I, h * a * h⁻¹ ∈ I := by
      intro h hh a ha
      have h1 := hinvH ⟨h, hh⟩ (modMk hUN a (hIU ha)) ((modMk_mem_subM_iff hUN hV₁I _).mpr ha)
      rw [hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)] at h1
      exact (modMk_mem_subM_iff hUN hV₁I _).mp h1
    have hVI : ¬ V ≤ I := by
      intro hVI
      apply hne
      refine eq_top_iff.mpr fun w _ => ?_
      have hUI : conjClosure V H ≤ I :=
        conjClosure_le fun h hh v hv => hIH h hh v (hVI hv)
      exact secImg_mono hUI w.2

    obtain ⟨l, hl, v, hv, hlv⟩ : ∃ l ∈ l1 T L V, ∃ v ∈ V, l * v * l⁻¹ * v⁻¹ ∉ I := by
      by_contra hall
      push Not at hall
      apply hVI
      refine (le_commutator_l1_F4 h1222 h1332 h1334 S.hyp).trans ?_
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have h1 := I.inv_mem (hall l hl v hv)
      have e : ⁅v, l⁆ = (l * v * l⁻¹ * v⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h1
    have hvU : v ∈ conjClosure V H := le_conjClosure V H hv
    refine false_of_two_factors_F4 h1222 h1332 h1334 h38 S hF hK₀ hHKT hA5 hl1K (Y := Ĩ) (Z := ⊤)
      le_top hYinv (fun _ _ _ _ => trivial) hntY ?_
    refine ⟨Φ ⟨l, hL1H hl⟩, ⟨⟨l, hL1H hl⟩, Subgroup.mem_subgroupOf.mpr (hl1K hl), rfl⟩,
      modMk hUN v hvU, trivial, ?_⟩
    rw [hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)]
    intro hmem
    apply hlv
    have hmem' : modMk hUN (l * v * l⁻¹ * v⁻¹) ((conjClosure V H).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (hL1H hl)) v).mp hvU)
        ((conjClosure V H).inv_mem hvU)) ∈ Ĩ := by
      convert hmem using 1
      apply Subtype.ext
      simp only [modMk, Subgroup.coe_mul, Subgroup.coe_inv, ← map_inv, ← map_mul]
      rfl
    exact (modMk_mem_subM_iff hUN hV₁I _).mp hmem'
  ·
    push Not at hinvH
    obtain ⟨h, w, hw, hhw⟩ := hinvH
    set J := Ĩ.map (Φ h).toMonoidHom with hJ
    have hJinv : ∀ l ∈ (K.subgroupOf H).map Φ, ∀ y ∈ J, l y ∈ J := by
      rintro l hl _ ⟨y, hy, rfl⟩
      refine ⟨((Φ h)⁻¹ * l * Φ h) y, ?_, ?_⟩
      · have hl' : (Φ h)⁻¹ * l * Φ h ∈ (K.subgroupOf H).map Φ := by
          have := hLn h⁻¹ l hl
          simpa [map_inv] using this
        exact hYinv _ hl' y hy
      · simp [MulAut.mul_apply]
    have hZinv : ∀ l ∈ (K.subgroupOf H).map Φ, ∀ z ∈ Ĩ ⊔ J, l z ∈ Ĩ ⊔ J := by
      intro l hl z hz
      have h1 : (Ĩ ⊔ J).map l.toMonoidHom ≤ Ĩ ⊔ J := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          exact hYinv l hl y hy
        · rintro _ ⟨y, hy, rfl⟩
          exact hJinv l hl y hy
      exact h1 ⟨z, hz, rfl⟩
    refine false_of_two_factors_F4 h1222 h1332 h1334 h38 S hF hK₀ hHKT hA5 hl1K (Y := Ĩ)
      (Z := Ĩ ⊔ J) le_sup_left hYinv hZinv hntY ?_
    by_contra hall
    push Not at hall
    apply hhw

    have hle : XMod.commOf ↥(autIH (fsuV1 T V) V H (conjClosure K T)) Ĩ ≤
        Ĩ.comap (Φ h).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a, y, hy, rfl⟩
      have ha : (a : MulAut _) ∈ (K.subgroupOf H).map Φ := hLb ▸ a.2
      have h1 := hall (Φ h * a * (Φ h)⁻¹) (hLn h _ ha) (Φ h y)
        (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)
      show Φ h (a • y * y⁻¹) ∈ Ĩ
      convert h1 using 1
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rfl
    rw [hcomm] at hle
    exact hle hw

end CFSG.Quasithin.H13.L32A.C
