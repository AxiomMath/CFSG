module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4S1
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz
public import CFSG.RankThree.Literature.FSmithForm

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow

variable {G : Type} [Group G] [Finite G]

theorem sec4Q_of_sylModel {A R : Subgroup G} {g : G} {E F S₁ Q E' F' U : Subgroup G} {z : G}
    {k : ℕ} (hset : Sec4Setting G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) (hS : IsSylowOf 2 S₁ ⊤)
    (hm : SylModel S₁ Q E' F' U z k)
    (hq : (∃ φ : ↥S₁ →* DihedralGroup 4, Function.Surjective φ ∧ φ.ker = Q.subgroupOf S₁) ∨
      ∃ φ : ↥S₁ →* DihedralGroup 8, Function.Surjective φ ∧ φ.ker = Q.subgroupOf S₁) :
    Sec4Q G A R g E F S₁ Q z where
  setting := hset
  sylowN := hSN
  sylow := hS
  le := hm.QX
  extraspecial := hm.extraspecial
  card := hm.cardQ
  order_z := hm.order_z
  center_Q := hm.center_Q
  center_S₁ := hm.center_X
  unique Q' hle hext hcard hcen := by
    refine hm.unique Q' hle hcard (fun x hx => ?_) (fun x hx y hy => ?_)
    · have h1 := CFSG.RankThree.Literature.FSmith.sq_mem_center hext ⟨x, hx⟩
      rw [← hm.center_X, ← hcen]
      refine mem_centerIn.mpr ⟨Q'.pow_mem hx 2, mem_centralizer_iff.mpr fun w hw => ?_⟩
      exact congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)
    · have h1 : (⟨x, hx⟩ : Q') * ⟨y, hy⟩ * (⟨x, hx⟩ : Q')⁻¹ * (⟨y, hy⟩ : Q')⁻¹ ∈ center Q' := by
        rw [← hext.2.1]
        exact commutator_mem_commutator (mem_top _) (mem_top _)
      rw [← hm.center_X, ← hcen]
      refine mem_centerIn.mpr
        ⟨Q'.mul_mem (Q'.mul_mem (Q'.mul_mem hx hy) (Q'.inv_mem hx)) (Q'.inv_mem hy), ?_⟩
      rw [mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)
  normE := by
    have hEle : E ≤ S₁ := le_sup_left.trans (sup_le_of_isSylowOf_normalizer hset hSN)
    rcases hm.uniqE E hEle hset.frame.elemE (by rw [hset.frame.cardE]; norm_num) with h | h
    · rw [h]
      exact hm.normE
    · rw [h]
      exact hm.normF
  normF := by
    have hFle : F ≤ S₁ := le_sup_right.trans (sup_le_of_isSylowOf_normalizer hset hSN)
    rcases hm.uniqE F hFle hset.frame.elemF (by rw [hset.frame.cardF]; norm_num) with h | h
    · rw [h]
      exact hm.normE
    · rw [h]
      exact hm.normF
  quot := hq
  plus := ⟨U, hm.UQ, hm.elemU, hm.cardU⟩

theorem step45_of
    (h43 : Step43) (h44 : Step44ii) : Step45 := by
  intro G _ _ A R g E F hset S₁ hSN
  have hS := h43 G A R g E F hset S₁ hSN
  refine ⟨(h44 G A R g E F hset S₁ hSN).imp (fun h => h.2) (fun h => h.2), ?_⟩
  obtain ⟨Q, E', F', U, z, k, hk, hm⟩ := exists_sylModel_of_step44 h44 hset hSN
  refine ⟨Q, z, sec4Q_of_sylModel hset hSN hS hm ?_⟩
  rcases hk with rfl | rfl
  · exact Or.inl hm.quot
  · exact Or.inr hm.quot

end CFSG.ComponentClassification.AS81
