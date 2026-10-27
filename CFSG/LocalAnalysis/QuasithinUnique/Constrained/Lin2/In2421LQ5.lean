module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section LQ5

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem exists_V (hc : centerOf L = ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) {a : G} (haT : a ∈ T)
    (haR : a ∉ thompsonJ S) (hacent : ∀ y ∈ lin2Z L (thompsonJ S), a * y = y * a) {g z : G}
    (hz : z ∈ lin2Z L (thompsonJ S)) (hg : a = g⁻¹ * z * g) :
    ⁅conjR (lin2Z L (thompsonJ S)) g, lin2Z L (thompsonJ S)⁆ = ⊥ ∧
      lin2Z L (thompsonJ S) ⊓ conjR (lin2Z L (thompsonJ S)) g = ⊥ ∧
      ∃ m ∈ M, lin2Z L (thompsonJ S) ⊔ conjR (lin2Z L (thompsonJ S)) g = conjR (blockU L) m := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have ha1 : a ≠ 1 := fun h => haR (by rw [h]; exact one_mem _)
  have haZg : a ∈ conjR Z g := mem_conjR_iff'.2 ⟨z, hz, hg⟩
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hZR : Z ≤ thompsonJ S := (lin2Z_le_centerOf E.h16 hcfg hZdef).trans inf_le_left
  obtain ⟨hZel, hZcard, -⟩ := E.Zbasic hcfg hZdef
  have hTIZ := E.ZTI hcfg hZdef
  have hTIZ' : fusionIsTI (conjR Z g) := fusionIsTI_conjR hTIZ g
  have hZ'el : IsElemAbelian 2 (conjR Z g) := (isElemAbelian_conjR_iff Z g).2 hZel
  have hCZ : Z ≤ Subgroup.centralizer ({a} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hacent y hy).symm
  have hNP : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (conjR Z g : Set G) :=
    centralizer_le_normalizer_of_TI hTIZ' haZg ha1
  have hZN : Z ≤ Subgroup.normalizer (conjR Z g : Set G) := hCZ.trans hNP
  have hp2Z : IsPGroup 2 Z := hcfg.sylowT.isPGroup.to_le (hZR.trans hRT)
  have hp2Z' : IsPGroup 2 (conjR Z g) := (isPGroup_conjR_iff 2).2 hp2Z
  have hsup : IsPGroup 2 ↥(Z ⊔ conjR Z g) := isPGroup_sup_of_le_normalizer hZN hp2Z hp2Z'
  have hM : Subgroup.normalizer (Z : Set G) = M := E.N_Z_eq_M hcfg hZdef hc
  have hNV : conjR Z g ⊓ Subgroup.normalizer (Z : Set G) ≠ ⊥ := by
    intro hbot
    have : a ∈ conjR Z g ⊓ Subgroup.normalizer (Z : Set G) := ⟨haZg, hM ▸ hcfg.T_le_M haT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  have hcomm : ⁅conjR Z g, Z⁆ = ⊥ := by
    refine tiAbelianTwoGroupCommute G (conjR Z g) Z hZ'el hZel (by rw [card_conjR])
      hTIZ' hTIZ ?_ ?_ hNV
    · intro h hne
      have := fusionIsTI_iff_conjR.1 hTIZ' (g⁻¹ * h)
        (by rwa [conjR_conjR, mul_inv_cancel_left])
      rw [conjR_conjR, mul_inv_cancel_left] at this
      rwa [inf_comm]
    · rw [sup_comm]; exact hsup
  have hinf : Z ⊓ conjR Z g = ⊥ := by
    by_contra hne
    have := conjR_eq_of_inf_ne_bot hTIZ hne
    apply haR
    exact hZR (this ▸ haZg)
  have hcommel : ∀ y ∈ Z, ∀ w ∈ conjR Z g, y * w = w * y := fun y hy w hw => by
    have := Subgroup.commutator_mem_commutator hw hy
    rw [hcomm, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  have hVel : IsElemAbelian 2 (Z ⊔ conjR Z g) := isElemAbelian_sup_commute hZel hZ'el hcommel
  have hVcard : Nat.card (Z ⊔ conjR Z g : Subgroup G) = Nat.card (blockU L) := by
    have h := card_sup_mul_card_inf hZN
    rw [hinf, Subgroup.card_bot, mul_one, card_conjR, hZcard] at h
    rw [h, E.card_U' hcfg, hc, Subgroup.card_bot, mul_one, ← pow_add]
    congr 1
    omega
  have hVM : Z ⊔ conjR Z g ≤ M := by
    have h1 : Z ⊔ conjR Z g ≤ Subgroup.centralizer (Z : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact IsElemAbelian.comm hZel hw hy
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact hcommel w hw y hy
    exact fun y hy => hM ▸ Subgroup.centralizer_le_normalizer (Z : Set G) (h1 hy)
  obtain ⟨m, hm, hmT⟩ := exists_le_conjR_of_isSylowTwoOf hcfg.cs.setting.isSylowTwoOf_M hVM hsup
  refine ⟨hcomm, hinf, ?_⟩
  rcases E.eq_or_eq_of_card_eq_of_le_conjR_T hcfg hx hxS hVel hVcard hmT with h | h
  · exact ⟨m, hm, h⟩
  · rw [conjR_conjR] at h
    exact ⟨x * m, M.mul_mem (hcfg.T_le_M hx) hm, h⟩

end LQ5

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
