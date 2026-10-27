module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326L
public import CFSG.Quasithin.Vol2.Ch3T326P
public import CFSG.Quasithin.Background.F918M6
public import CFSG.Quasithin.Vol2.Ch3T326N
public import CFSG.Quasithin.Vol2.Ch3T326O
public import CFSG.Quasithin.Vol2.Ch3T326S

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Ctx

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem case_d36_F4 (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hD36 : D36c) (hL38 : D3L38) (hG : T326ActsGlued_F4)
    [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hV₀ : V₀ ≠ conjClosure V₀ T)
    (hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
    (hii : ∀ (s : G) (hs : s ∈ T), s ∉ Subgroup.normalizer (L : Set G) → ∀ x ∈ T,
      D3Std (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) →
      (CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) <
        orbSup (autOn T (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))))
          ((CFSG.conjugate V₀ x).subgroupOf
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) →
      (∀ v ∈ (CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))),
        ∀ g ∈ conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
          (autOn L (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))), g v = v) →
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
        Subgroup.centralizer (CFSG.conjugate L s : Set G) →
      D36L32
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) →
      Concl326Cii T L V₀) :
    Concl326C3 T L V₀ := by
  obtain ⟨s, hs, hsn⟩ := c.exists_t
  obtain ⟨x, hx, hDx, hC⟩ := c.d36_label h316 hA37 hA38 hD36 hV₀ hV hs hsn
  have hMp := c.autOn_L₀_eq hA37 hA38 hs hsn
  have htn := c.not_mem_normalizer hA37 hs hsn
  have horb := c.orbSup_conjugate hx
  have hcard := c.card_subgroupOf_conjugate hx
  have hLVM := c.L_le_NVM
  have hLsVM : CFSG.conjugate L s ≤ Subgroup.normalizer (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) :=
    (Vol2.Ch10.SecA.conjugate_le_fsuL0 hs).trans c.L₀_le_NVM
  have hsVM := c.T_le_NVM (T.inv_mem hs)
  have hUVM := Subgroup.le_normalizer_iff_commutator_le_left.mp hLVM
  have hV₀VM := (T325.V₀_le_V T V₀).trans (T325.V_le_VM T (conjClosure L T) V₀)
  have hxVM : CFSG.conjugate V₀ x ≤ conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) :=
    le_of_le_of_eq (Subgroup.map_mono hV₀VM) (c.conjugate_VM (c.T_le_M hx))
  have hcomm := commSub_top_autOn (VM := conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G))) hLVM
  have hV₀lt : V₀.subgroupOf (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))) < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hV₀ ?_
    exact le_antisymm (T325.V₀_le_V T V₀) (hV.le.trans (Subgroup.subgroupOf_eq_top.mp h))
  have horb' : orbSup (autOn T (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))))
      ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) = ⊤ := by
    rw [horb, Subgroup.subgroupOf_eq_top.mpr hV.ge]
  have hconj : conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
      (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) =
      autOn (CFSG.conjugate L s)
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :=
    (autOn_conjugate hLVM hsVM).symm
  have htT : conjAct (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∈
      autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :=
    Setup.mem_autOn_iff.mpr ⟨⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩, T.inv_mem hs, rfl⟩
  have hIlt : (CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) <
      orbSup (autOn T (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) := by
    rw [horb']
    refine lt_of_le_of_ne le_top fun h => hV₀lt.ne ?_
    exact Subgroup.eq_of_le_of_card_ge le_top
      ((congrArg (fun H : Subgroup ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) => Nat.card ↥H) h.symm).trans hcard).le
  obtain ⟨htriv, ⟨-, hUfix⟩, -, h3⟩ := hC
  rw [horb', hcomm, hconj] at hUfix
  have hU := le_centralizer_of_forall_fix hLsVM hUVM hUfix
  have ha := c.concl_a hA37 hA38 hs hsn hU
  obtain ⟨h1, h2, h3'⟩ := ha s hs hsn
  have hrk : 2 < rk ↥((⁅conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
    have h := d36_rank hL38 ⟨hDx, hIlt, htT, htn, hMp, htriv⟩
    rw [horb', hcomm] at h
    have e : Nat.card ↥(((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
          (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))).subgroupOf ⊤) =
        Nat.card ↥((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    unfold rk at h ⊢
    rwa [e] at h
  have hacts := c.qhatStar_acts_F4 hA37 hA38 hG hs hsn h1 h2 h3' hrk
  refine ⟨⟨ha, hacts, c.qhat_U h316 hA37 hA38 hacts⟩, ?_⟩
  rcases h3 with h3 | h3
  ·
    rw [horb', hcomm] at h3
    have h4 := Subgroup.subgroupOf_inj.mp h3
    rw [inf_of_le_left hUVM, inf_of_le_left hxVM] at h4
    exact Or.inl ⟨x, hx, h4, hV⟩
  ·
    exact Or.inr (Or.inl (hii s hs hsn x hx hDx hIlt htriv hU h3))

end Ctx

end CFSG.Quasithin.H13.T326
