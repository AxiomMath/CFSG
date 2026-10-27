module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJSec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJAct
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrFrameB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem omega1_le_self (T : Subgroup G) : omega1 T ≤ T := by
  rw [omega1, closure_le]
  rintro y ⟨hy, -⟩
  exact hy

theorem lf18_3e_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_3e s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  obtain ⟨h11, h12, h13, h14, h15, h16, h17, h18, h19, h110⟩ := s.facts
  obtain ⟨⟨h18_1_1, h18_1_2⟩, -, h18_3, -, -⟩ := h18
  obtain ⟨-, -, hB3, hB4, -⟩ := h18_3
  have h14' : s.fr'.Fact14 := h14
  obtain ⟨-, -, h14_3, -, -, -, -⟩ := h14
  obtain ⟨-, -, -, -, -, -, -, -, hcen_omega, -⟩ := h14_3
  have hBL : s.fr.B ≤ L := (s3_B_le_S s).trans (s3_S_le_L s)
  have hB2 : IsPGroup 2 ↥s.fr.B := s3_isPGroup_of_le s (s3_B_le_S s)
  have hB'_2 : IsPGroup 2 ↥s.fr'.B := by
    rw [← s3_jSub_B hS hZ s]
    exact isPGroup_jSub L hB2
  have hcenL : cen s.fr.B ≤ L := (s3_cenB_le_B s).trans hBL
  have hJ0L : thompsonSubgroup s.fr.B ≤ L := (s3_J0B_le_B s).trans hBL
  have hcen2 : IsPGroup 2 ↥(cen s.fr.B) :=
    s3_isPGroup_of_le s ((s3_cenB_le_B s).trans (s3_B_le_S s))
  have hJ02 : IsPGroup 2 ↥(thompsonSubgroup s.fr.B) :=
    s3_isPGroup_of_le s ((s3_J0B_le_B s).trans (s3_B_le_S s))
  have hcenJ0 : cen s.fr.B ≤ thompsonSubgroup s.fr.B :=
    le_of_jSub_le hZ hcenL hcen2 hJ0L hJ02 (by
      rw [s3_jSub_cenB hS hZ s, s3_jSub_J0B hS hZ s, hcen_omega]
      exact omega1_le_self _)
  have hSec : SecProp (normIn L s.fr.B) (zL L ⊔ s.fr.B)
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
    have hV : normIn L s.fr.B ≤ normalizer (L : Set G) :=
      (inf_le_left : normIn L s.fr.B ≤ L).trans Subgroup.le_normalizer
    have hNV : zL L ⊔ s.fr.B ≤ normIn L s.fr.B :=
      sup_le (zL_le_normIn hBL) (le_inf hBL Subgroup.le_normalizer)
    have hK : ∀ x ∈ normIn L s.fr.B, x ∈ centralizer (L : Set G) → x ∈ zL L ⊔ s.fr.B := by
      intro x hx hxC
      exact Subgroup.mem_sup_left
        ((mem_zL_iff (L := L)).mpr ⟨(Subgroup.mem_inf.mp hx).1, hxC⟩)
    refine (secProp_jSub (L := L) hV hNV hK (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))
      (fun Y Y' _ _ e => ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩)).mpr ?_
    rw [jSub_normIn hZ hBL hB2, jSub_self (L := L), s3_jSub_B hS hZ s,
      jSub_sup_zL hBL, s3_jSub_B hS hZ s]
    exact hB3
  intro k hkN hk3 hkz
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkN).1
  obtain ⟨κ, hkκ⟩ : ∃ κ : MulAut (L ⧸ center L), ActsAs L k κ :=
    ⟨jHom L ⟨k, Subgroup.le_normalizer hkL⟩,
      jHom_actsAs L ⟨k, Subgroup.le_normalizer hkL⟩⟩
  have hk3κ : IsPGroup 3 ↥(zpowers κ) := isPGroup_zpowers_of_actsAs hkκ hk3
  have hκne : κ ≠ 1 := ne_one_of_actsAs_of_not_mem_zL hkL hkκ hkz
  have hκN' : κ ∈ normIn (innerAut (L ⧸ center L)) s.fr'.B := by
    refine ⟨?_, ?_⟩
    · have : κ ∈ jSub L L := (mem_jSub L).mpr ⟨k, hkL, hkκ⟩
      rwa [jSub_self (L := L)] at this
    · have hkN_B : k ∈ normalizer (s.fr.B : Set G) := (Subgroup.mem_inf.mp hkN).2
      have : κ ∈ normalizer (jSub L s.fr.B : Set (MulAut (L ⧸ center L))) :=
        (mem_normalizer_iff_jSub hZ hBL hB2 hkκ).mp hkN_B
      rwa [s3_jSub_B hS hZ s] at this
  have hKN' : s.fr'.B ≤ normIn (innerAut (L ⧸ center L)) s.fr'.B := by
    have hS'L' : s.fr'.S ≤ innerAut (L ⧸ center L) := by
      rw [← h18_1_2]
      exact inf_le_left
    exact le_inf ((inf_le_left : s.fr'.B ≤ s.fr'.S).trans hS'L') Subgroup.le_normalizer
  have hisSylow : IsSylowIn 3 (normIn (innerAut (L ⧸ center L)) s.fr'.B) (zpowers κ) :=
    isSylowIn_zpowers_of_secProp_perm3 hB3 hKN' hB'_2 hκN' hk3κ hκne
  have hreg := hB4 (zpowers κ) hisSylow
  have ht1 : ActsTransitively (zpowers k) (cen s.fr.B) ⊥ :=
    actsTransitively_of_jSub hZ hkL hkκ hcenL hcen2 bot_le (by
      rw [s3_jSub_cenB hS hZ s, jSub_bot (L := L)]
      exact hreg.1)
  have ht2 : ActsTransitively (zpowers k) (thompsonSubgroup s.fr.B) (cen s.fr.B) :=
    actsTransitively_of_jSub hZ hkL hkκ hJ0L hJ02 hcenJ0 (by
      rw [s3_jSub_J0B hS hZ s, s3_jSub_cenB hS hZ s]
      exact hreg.2)
  refine ⟨?_, ht1, ht2⟩
  let K : Subgroup G := zL L ⊔ s.fr.B
  let a : G := s.fr.a₁ * s.fr.b₁ * s.fr.b₂
  let M : Subgroup G := K ⊔ zpowers k ⊔ zpowers a
  have hKM : K ≤ M := le_sup_left.trans le_sup_left
  have ha2 : IsPGroup 2 ↥(zpowers a) := by
    simpa [a] using s3_isPGroup_zpowers s (s3_a₁b₁b₂_mem_S s)
  have haN : a ∈ normIn L s.fr.B := by
    have haL : a ∈ L := s3_S_le_L s (s3_a₁b₁b₂_mem_S s)
    have ha'n : s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂ ∈
        normalizer (s.fr'.B : Set (MulAut (L ⧸ center L))) := by
      have ha'S : s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂ ∈ s.fr'.S :=
        mul_mem
          (mul_mem (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))
      have h1 : s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂ ∈
          normIn (innerAut (L ⧸ center L)) s.fr'.B := by
        have h2 : s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂ ∈
            normIn (innerAut (L ⧸ center L)) s.fr'.S := by
          rw [h18_1_2]
          exact ha'S
        rw [h18_1_1] at h2
        exact (Subgroup.mem_inf.mp h2).2
      exact (Subgroup.mem_inf.mp h1).2
    exact (mem_normIn_iff_jSub hZ hBL hB2 haL (s3_actsAs_a₁b₁b₂ s)).mpr (by
      rwa [s3_jSub_B hS hZ s])
  have hMN : M ≤ normIn L s.fr.B :=
    sup_le (sup_le (sup_le (zL_le_normIn hBL) (le_inf hBL Subgroup.le_normalizer))
      (Subgroup.zpowers_le.mpr hkN)) (Subgroup.zpowers_le.mpr haN)
  have hkM : k ∈ M :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers k))
  have haM : a ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hkK : k ∉ K := by
    intro hkK
    have hκB' : κ ∈ s.fr'.B := by
      have : κ ∈ jSub L (zL L ⊔ s.fr.B) := (mem_jSub L).mpr ⟨k, hkK, hkκ⟩
      rwa [jSub_sup_zL hBL, s3_jSub_B hS hZ s] at this
    have hκ2 : IsPGroup 2 ↥(zpowers κ) := hB'_2.to_le (Subgroup.zpowers_le.mpr hκB')
    have hdisj : Disjoint (zpowers κ) (zpowers κ) :=
      IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hκ2 hk3κ
    have hbot : (zpowers κ : Subgroup (MulAut (L ⧸ center L))) = ⊥ :=
      hdisj.eq_bot_of_le le_rfl
    exact hκne (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers κ))
  have haK : a ∉ K := by
    intro haK
    have haB : a ∈ s.fr.B := mem_of_mem_zL_sup hZ hBL hB2 haK ha2
    have ha'B : s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂ ∈ s.fr'.B := by
      have : s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂ ∈ jSub L s.fr.B :=
        (mem_jSub L).mpr ⟨a, haB, s3_actsAs_a₁b₁b₂ s⟩
      rwa [s3_jSub_B hS hZ s] at this
    exact frame_a₁b₁b₂_not_mem_B s.fr' (innerAut (L ⧸ center L)) h11 h14' ha'B
  change normIn L s.fr.B = M
  exact (eq_of_secProp_perm3 hSec hKM hMN hkM hkK hk3 haM haK ha2).symm

end CFSG.OddStandard.HigherRank.YamadaG23
