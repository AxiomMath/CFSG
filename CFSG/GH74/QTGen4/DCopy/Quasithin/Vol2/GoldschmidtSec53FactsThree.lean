module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsMod
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsTwo
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Lemmas
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsExt
import CFSG.Quasithin.Vol2.Ch5Sec1Basic
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

open CFSG.Quasithin.H13.F431 in
theorem facts_i_of_ext_finY_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} {Y : Type} [Group Y] [Finite Y]
    (h531 : Stmt5_3_1_F4) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T t m f)
    (hpar : IsSec53Param t m f) (E : LieExt Y (sec53M1 L) (sec53M2 H)) (hX : ExtFacts E) :
    perfectCore (sec53M1 L) = L ∧ perfectCore (sec53M2 H) = oTwoUpper H ∧
      pCoreOf 2 (sec53M12 L H) = sec53S T L := by
  obtain ⟨-, -, ⟨hN1, -, -⟩, ⟨hLM, hKM⟩⟩ := h531 G T M L V H B D L₂ n t m f hyp hty hpar
  have := hX.solv
  have hsolv : Group.IsSolvable ↥(sec53M12 L H) :=
    Group.isSolvable_of_isSolvable_injective (f := E.phi12.toMonoidHom) E.phi12.injective
  have hLG : L ≤ sec53M1 L := Subgroup.le_normalizer
  have hKG : oTwoUpper H ≤ sec53M2 H := Subgroup.le_normalizer
  have hL1 : perfectCore (sec53M1 L) = L := by
    have hAn : (L.subgroupOf (sec53M1 L)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr le_rfl
    exact le_antisymm (perfectCore_le_of_sup_solvable hLG hAn hLM.symm hsolv)
      (le_perfectCore_of_perfect hLG hyp.toHyp5_1_8.toHyp5_0_1.commutator_eq)
  have hK2 : perfectCore (sec53M2 H) = oTwoUpper H := by
    have hAn : ((oTwoUpper H).subgroupOf (sec53M2 H)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr le_rfl
    exact le_antisymm (perfectCore_le_of_sup_solvable hKG hAn hKM.symm hsolv)
      (le_perfectCore_of_perfect hKG hty.2.1.2.1.2.1)
  refine ⟨hL1, hK2, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxM : x ∈ sec53M12 L H := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have hT1 : T ≤ sec53M1 L := hyp.T_le.trans hyp.normal
    have hT2 : T ≤ sec53M2 H := hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
    have hTM : T ≤ sec53M12 L H := le_inf hT1 hT2
    have hSyl : IsSylowTwoOf T (sec53M12 L H) := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM
    have hxT : x ∈ T :=
      hSyl.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hx
    have h12 := (mem_pCoreOf_iff_of_equiv E.phi12 ⟨x, hxM⟩).mp hx
    have h1 : ((E.phi12 ⟨x, hxM⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut Y) ∈ perfectCore E.N1 := hX.core h12
    have hxL : x ∈ L := by
      have e1 := E.phi1_phi12 ⟨x, hxM⟩
      have := (mem_perfectCore_iff_of_equiv E.phi1 ⟨x, hxM.1⟩).mpr (by rw [e1]; exact h1)
      rwa [hL1] at this
    exact ⟨hxT, hxL⟩
  · have hSM : sec53S T L ≤ sec53M12 L H := hN1 ▸ Subgroup.le_normalizer
    have hn : (sec53S T L).subgroupOf (sec53M12 L H) |>.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mpr hN1.symm.le
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hSM hn
      (hyp.toHyp5_1_8.toHyp5_0_1.sylow.1.to_le inf_le_left)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}
  {P : Type} [Group P] [Finite P] {N₁ N₂ : Subgroup P}
  (Φ : (RankTwoAmalgam.ofSubgroups (fG1 M L H B) (fG2 M L H D)).Iso
    (RankTwoAmalgam.ofSubgroups N₁ N₂))

include Φ

theorem centerOf_L_le_centerOf_S_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hpc : perfectCore (fG1 M L H B) = L)
    (hZ : centerOf (perfectCore N₁) ≤ pCoreOf 2 (N₁ ⊓ N₂)) :
    centerOf L ≤ centerOf (sec53S T L) := by
  intro z hz
  have hL : L ≤ fG1 M L H B := le_sup_left.trans le_sup_left
  have hzL : z ∈ L := (Subgroup.mem_inf.mp hz).1
  have ha := (mem_centerOf_iff_of_equiv (isoφ1 Φ) hL (perfectCore_le N₁) (mem_L_iff Φ hpc)
    ⟨z, hL hzL⟩).mp hz
  have hU := hZ ha
  have hz2 : z ∈ fG2 M L H D := mem_fG2_of_mem Φ ⟨z, hL hzL⟩
    (Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hU)).2
  have hz12 : z ∈ fG1 M L H B ⊓ fG2 M L H D := ⟨hL hzL, hz2⟩
  have hS : z ∈ sec53S T L := by
    rw [mem_S_iff_F4 Φ h527 hyp ⟨z, hz12⟩, coe_isoφ12_eq_φ1 Φ ⟨z, hz12⟩]
    exact hU
  exact ⟨hS, Subgroup.mem_centralizer_iff.mpr fun s hs =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s (Subgroup.mem_inf.mp hs).2⟩

theorem centerOf_K_le_centerOf_S_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hpc : perfectCore (fG2 M L H D) = oTwoUpper H)
    (hZ : centerOf (perfectCore N₂) ≤ pCoreOf 2 (N₁ ⊓ N₂)) :
    centerOf (oTwoUpper H) ≤ centerOf (sec53S T L) := by
  intro z hz
  have hK : oTwoUpper H ≤ fG2 M L H D := le_sup_right
  have hzK : z ∈ oTwoUpper H := (Subgroup.mem_inf.mp hz).1
  have ha := (mem_centerOf_iff_of_equiv (isoφ2 Φ) hK (perfectCore_le N₂) (mem_K_iff Φ hpc)
    ⟨z, hK hzK⟩).mp hz
  have hU := hZ ha
  have hz1 : z ∈ fG1 M L H B := mem_fG1_of_mem Φ ⟨z, hK hzK⟩
    (Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hU)).1
  have hz12 : z ∈ fG1 M L H B ⊓ fG2 M L H D := ⟨hz1, hK hzK⟩
  have hS : z ∈ sec53S T L := by
    rw [mem_S_iff_F4 Φ h527 hyp ⟨z, hz12⟩, coe_isoφ12_eq_φ2 Φ ⟨z, hz12⟩]
    exact hU
  exact ⟨hS, Subgroup.mem_centralizer_iff.mpr fun s hs =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s
      (sec53S_le_K_F4 h527 hyp hs)⟩

theorem centerOf_inf_eq_bot_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hpc1 : perfectCore (fG1 M L H B) = L) (hpc2 : perfectCore (fG2 M L H D) = oTwoUpper H)
    (hS : SplitFacts N₁ N₂) : centerOf L ⊓ centerOf (oTwoUpper H) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hxS : x ∈ sec53S T L :=
    (Subgroup.mem_inf.mp (centerOf_L_le_centerOf_S_F4 Φ h527 hyp hpc1 hS.le₁ hx1)).1
  have hx12 : x ∈ fG1 M L H B ⊓ fG2 M L H D := sec53S_le_fG12_F4 h527 hyp hxS
  have hL : L ≤ fG1 M L H B := le_sup_left.trans le_sup_left
  have hK : oTwoUpper H ≤ fG2 M L H D := le_sup_right
  have ha1 := (mem_centerOf_iff_of_equiv (isoφ1 Φ) hL (perfectCore_le N₁) (mem_L_iff Φ hpc1)
    ⟨x, (Subgroup.mem_inf.mp hx12).1⟩).mp hx1
  have ha2 := (mem_centerOf_iff_of_equiv (isoφ2 Φ) hK (perfectCore_le N₂) (mem_K_iff Φ hpc2)
    ⟨x, (Subgroup.mem_inf.mp hx12).2⟩).mp hx2
  have e1 := coe_isoφ12_eq_φ1 Φ ⟨x, hx12⟩
  have e2 := coe_isoφ12_eq_φ2 Φ ⟨x, hx12⟩
  have h0 : ((isoφ12 Φ ⟨x, hx12⟩ : ↥(N₁ ⊓ N₂)) : P) = 1 :=
    hS.inf _ (by rw [e1]; exact ha1) (by rw [e2]; exact ha2)
  have h1 : isoφ12 Φ ⟨x, hx12⟩ = 1 := Subtype.ext h0
  have h2 : (⟨x, hx12⟩ : ↥(fG1 M L H B ⊓ fG2 M L H D)) = 1 :=
    (isoφ12 Φ).map_eq_one_iff.mp h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

theorem third_transitive_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hpc1 : perfectCore (fG1 M L H B) = L) (hpc2 : perfectCore (fG2 M L H D) = oTwoUpper H)
    (hS : SplitFacts N₁ N₂) :
    ∀ x ∈ centerOf (sec53S T L), ∀ y ∈ centerOf (sec53S T L), x ∉ centerOf L →
      x ∉ centerOf (oTwoUpper H) → y ∉ centerOf L → y ∉ centerOf (oTwoUpper H) →
      ∃ c ∈ B ⊔ D, c * x * c⁻¹ = y := by
  intro x hx y hy hx1 hx2 hy1 hy2
  have hL : L ≤ fG1 M L H B := le_sup_left.trans le_sup_left
  have hK : oTwoUpper H ≤ fG2 M L H D := le_sup_right
  have hBD : B ⊔ D ≤ Subgroup.normalizer (sec53S T L : Set G) := by
    intro g hg
    have hg' : g ∈ fG1 M L H B ⊓ fG2 M L H D := by
      rw [fG12_eq_F4 h527 hyp]
      exact Subgroup.mem_sup_right hg
    rw [← pCoreOf_fG12_F4 h527 hyp]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg'
  have hR : ∀ w : ↥(fG1 M L H B ⊓ fG2 M L H D),
      ((w : G) ∉ centerOf L ∧ (w : G) ∉ centerOf (oTwoUpper H)) ↔
        (((isoφ12 Φ w : ↥(N₁ ⊓ N₂)) : P) ∉ centerOf (perfectCore N₁) ∧
          ((isoφ12 Φ w : ↥(N₁ ⊓ N₂)) : P) ∉ centerOf (perfectCore N₂)) := by
    intro w
    have c1 := mem_centerOf_iff_of_equiv (isoφ1 Φ) hL (perfectCore_le N₁) (mem_L_iff Φ hpc1)
      ⟨w, (Subgroup.mem_inf.mp w.2).1⟩
    have c2 := mem_centerOf_iff_of_equiv (isoφ2 Φ) hK (perfectCore_le N₂) (mem_K_iff Φ hpc2)
      ⟨w, (Subgroup.mem_inf.mp w.2).2⟩
    rw [← coe_isoφ12_eq_φ1 Φ w] at c1
    rw [← coe_isoφ12_eq_φ2 Φ w] at c2
    exact and_congr (not_congr c1) (not_congr c2)
  exact exists_conj_of_equiv (isoφ12 Φ) hBD (fG12_eq_F4 h527 hyp)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (mem_S_iff_F4 Φ h527 hyp)
    (R := fun w => w ∉ centerOf L ∧ w ∉ centerOf (oTwoUpper H))
    (R' := fun a => a ∉ centerOf (perfectCore N₁) ∧ a ∉ centerOf (perfectCore N₂)) hR
    (fun a ha ha' a' ha'' ha''' => hS.third a ha a' ha'' ha'.1 ha'.2 ha'''.1 ha'''.2)
    hx hy ⟨hx1, hx2⟩ ⟨hy1, hy2⟩

theorem facts_iii_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ} (hty : IsOfLieType52 M L H B D T t m f)
    (hF : TransFacts N₁ N₂) (hS : SplitFacts N₁ N₂) :
    ∀ u ∈ sec53ZS T L, u ≠ 1 → ∃ g ∈ B ⊔ D, g * u * g⁻¹ ∈ centerOf T := by
  have hsol := isSolvable_fG12 Φ hF.solv
  have hpc1 := perfectCore_fG1 hyp hsol
  have hpc2 := perfectCore_fG2 hyp hty hsol
  have h2 := facts_ii_F4 Φ h527 hyp hty hF
  exact exists_conj_mem_centerOf_of_transitive (S := sec53S T L) (T := T) (C := B ⊔ D)
    (Z₁ := centerOf L) (Z₂ := centerOf (oTwoUpper H)) inf_le_left (T_le_normalizer_S hyp)
    hyp.toHyp5_1_8.toHyp5_0_1.sylow.1
    (centerOf_L_le_centerOf_S_F4 Φ h527 hyp hpc1 hS.le₁)
    (centerOf_K_le_centerOf_S_F4 Φ h527 hyp hpc2 hS.le₂)
    (centerOf_L_ne_bot Φ hpc1 hS.ne₁) (centerOf_K_ne_bot Φ hpc2 hS.ne₂)
    (centerOf_inf_eq_bot_F4 Φ h527 hyp hpc1 hpc2 hS)
    ((T_le_normalizer_L hyp).trans (normalizer_le_normalizer_centerOf L))
    ((T_le_normalizer_K hyp).trans (normalizer_le_normalizer_centerOf (oTwoUpper H)))
    (fun x hx y hy hx1 hy1 => h2.1 x hx hx1 y hy hy1)
    (fun x hx y hy hx1 hy1 => h2.2 x hx hx1 y hy hy1)
    (third_transitive_F4 Φ h527 hyp hpc1 hpc2 hS)

end CFSG.Quasithin.H13.Sec53F
