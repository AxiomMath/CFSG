module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocBase
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import Certificates.Certificate22228

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.QuasithinUnique.Id2519.HSAut (outerC outerE e1 e2)

theorem hsW_pow :
    (e1 * e2) ^ 6 = 1 ∧ (e1 * e2) ^ 2 ≠ 1 ∧ (e1 * e2) ^ 3 ≠ 1 := by
  set w := e1 * e2 with hw
  have h1 : ComponentClassification.PSL3Four.TabRep hsW1 w :=
    QuasithinUnique.Id2519.HSAut.tabRep_e1.comp QuasithinUnique.Id2519.HSAut.tabRep_e2
  have h2 : ComponentClassification.PSL3Four.TabRep hsW2 (w ^ 2) := by
    rw [sq]
    exact h1.comp h1
  have h3 : ComponentClassification.PSL3Four.TabRep hsW3 (w ^ 3) := by
    rw [pow_succ]
    exact h2.comp h1
  have h6 : ComponentClassification.PSL3Four.TabRep hsW6 (w ^ 6) := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add]
    exact h3.comp h3
  have hc := (Certificates.certificate22228 : hsOrderSixOK = true)
  simp only [hsOrderSixOK, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hc6, hc2⟩, hc3⟩ := hc
  have hid := (ComponentClassification.PSL3Four.TabRep.idTab :
    ComponentClassification.PSL3Four.TabRep (CFSG.PSL3Four.Native.idTab 3850)
      (1 : Equiv.Perm (Fin 3850)))
  refine ⟨(h6.beq_iff hid).1 hc6, fun h => ?_, fun h => ?_⟩
  · rw [(h2.beq_iff hid).2 h] at hc2
    exact absurd hc2 (by decide)
  · rw [(h3.beq_iff hid).2 h] at hc3
    exact absurd hc3 (by decide)

theorem hsW_mem : e1 * e2 ∈ outerE :=
  outerE.mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem not_statedClassicalModel_commutator_outerC :
    ¬ StatedClassicalModel ↥(commutator ↥outerC) .PSL 3 2 2 := by
  intro hX
  obtain ⟨-, hcent, -⟩ := ComponentClassification.PSL3Four.excludes_alternating_models_stated.{0}
    _ hX
  have hw : e1 * e2 ∈ (commutator ↥outerC).map outerC.subtype := by
    rw [QuasithinUnique.Id2519.HSAut.map_commutator_outerC]
    exact hsW_mem
  obtain ⟨c, hc, hcw⟩ := hw
  let b : ↥(commutator ↥outerC) := ⟨c, hc⟩
  have hcoe : ∀ k : ℕ,
      (((b ^ k : ↥(commutator ↥outerC)) : ↥outerC) : Equiv.Perm (Fin 3850)) = (e1 * e2) ^ k := by
    intro k
    rw [← hcw]
    simp [b]
  have hinj : ∀ y z : ↥(commutator ↥outerC),
      ((y : ↥outerC) : Equiv.Perm (Fin 3850)) = ((z : ↥outerC) : Equiv.Perm (Fin 3850)) → y = z :=
    fun y z h => Subtype.ext (Subtype.ext h)
  obtain ⟨h6, h2, h3⟩ := hsW_pow
  have hb6 : b ^ 6 = 1 := hinj _ _ (by rw [hcoe]; exact h6)
  have hb2 : b ^ 2 ≠ 1 := fun h => h2 (by rw [← hcoe, h]; rfl)
  have hb3 : b ^ 3 ≠ 1 := fun h => h3 (by rw [← hcoe, h]; rfl)
  have hx : orderOf (b ^ 3) = 2 :=
    orderOf_eq_prime (by rw [← pow_mul]; exact hb6) hb3
  have hy : b ^ 2 ∈ centralizer ({b ^ 3} : Set ↥(commutator ↥outerC)) :=
    mem_centralizer_singleton_iff.mpr (by rw [← pow_add, ← pow_add])
  have hy3 : orderOf (⟨b ^ 2, hy⟩ : centralizer ({b ^ 3} : Set ↥(commutator ↥outerC))) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [← pow_mul]; exact hb6) hb2
  have h3dvd := orderOf_dvd_natCard
    (⟨b ^ 2, hy⟩ : centralizer ({b ^ 3} : Set ↥(commutator ↥outerC)))
  rw [hy3, hcent _ hx] at h3dvd
  exact absurd h3dvd (by decide)

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {α : G} {J : Subgroup G}

theorem Hyp.false_of_HS
    (h : Hyp N α J)
    (hs : NativeSporadic.IsSporadic N .HS) : False := by
  obtain ⟨e⟩ := hs
  let θ : N ≃* hsP := e.trans hsPermEquiv
  set σ : MulAut hsP := MulAut.congr θ (beta N α) with hσdef
  have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, h.beta_sq, map_one]
  have hσ1 : σ ≠ 1 := fun h1 =>
    h.beta_ne_one ((MulAut.congr θ).injective (by rw [← hσdef, h1, map_one]))
  obtain ⟨r, hr, g, -, x, -, -, hfix⟩ := QuasithinUnique.Id2519.SporHS.fix_data σ hσ2 hσ1
  let Ψ : fixedSubgroup (beta N α) ≃*
      ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) :=
    (Sporadic.HeldB.fixedSubgroupCongr θ (beta N α)).trans
      (QuasithinUnique.Id2519.SporHS.fixEquiv hfix)
  have hcard : Nat.card (fixedSubgroup (beta N α)) = r.centOrder := by
    rw [Nat.card_congr Ψ.toEquiv]
    obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
    exact (hrows r hr).2.2.2.2.1
  have hd := h.dvd_card_fixed
  rw [hcard] at hd
  rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h1 | ⟨-, -, h1, -⟩ | ⟨hrep, -⟩ | h1
  · rw [h1] at hd
    exact absurd hd (by decide)
  · rw [h1] at hd
    exact absurd hd (by decide)
  swap
  · rw [h1] at hd
    exact absurd hd (by decide)
  have hO : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) = outerC := by
    rw [hrep]
    rfl
  let Ψ' : fixedSubgroup (beta N α) ≃* ↥outerC := Ψ.trans (MulEquiv.subgroupCongr hO)
  set L := (J.subgroupOf N).subgroupOf (fixedSubgroup (beta N α)) with hLdef
  have hB := CFSG.LocalCores.isComponent_map_mulEquiv Ψ' h.isComponent_fixed
  have : IsSimpleGroup ↥(commutator ↥outerC) := QuasithinUnique.Id2519.HSAut.commutator_simple'
  have hBle := QuasithinUnique.Id2519.le_commutator_of_isQuasisimple hB.1
  have htop := QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup
    (CFSG.LocalCores.component_overgroup hB hBle)
  have hBeq : L.map Ψ'.toMonoidHom = commutator ↥outerC :=
    le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
  let eX : ↥J ≃* ↥(commutator ↥outerC) :=
    ((subgroupOfEquivOfLe h.le_N).symm.trans (subgroupOfEquivOfLe h.le_fixed).symm).trans
      ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans (MulEquiv.subgroupCongr hBeq))
  have hZ : center ↥(commutator ↥outerC) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(commutator ↥outerC)) with hZ | hZ
    · exact hZ
    · exfalso
      have hq := Nat.card_congr (quotCenterCongr eX).toEquiv
      rw [h.card_quot, hZ] at hq
      have h1 : Nat.card (↥(commutator ↥outerC) ⧸ (⊤ : Subgroup ↥(commutator ↥outerC))) = 1 :=
        Subgroup.index_top
      omega
  apply not_statedClassicalModel_commutator_outerC
  refine CatLeaf.statedClassicalModel_of_lieModel_psl
    (LieType.CurtisTits.lieModel_of_mulEquiv ?_ h.lie)
  exact (quotCenterCongr eX).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

end CFSG.ComponentClassification.GSThmB.Soc
