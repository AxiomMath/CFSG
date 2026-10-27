module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLQuot

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

namespace SwapShape

noncomputable def commutatorEquivAlt8 (h : SwapShape t Sg V) :
    (⁅Sg, Sg⁆ : Subgroup X) ≃* alternatingGroup (Fin 8) := by
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  have hmap : (_root_.commutator Sg).map eS.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    simp only [Subgroup.map_top_of_surjective eS.toMonoidHom eS.surjective]
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact ((Subgroup.equivMapOfInjective (_root_.commutator Sg) Sg.subtype
        Sg.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator Sg))).symm.trans
    ((Subgroup.equivMapOfInjective (_root_.commutator Sg) eS.toMonoidHom
        eS.injective).trans
      (MulEquiv.subgroupCongr hmap))

theorem centralizer_le_normalizer_commutator (h : SwapShape t Sg V) :
    centralizer ({t} : Set X) ≤ normalizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
  rw [h.cent_eq]
  refine sup_le ?_ ?_
  · intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hcomm := h.mul_comm_of_mem_v_of_mem_sg hv (Subgroup.commutator_le_self Sg ha)
      have heq : v * a * v⁻¹ = a := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]
      exact ha
    · intro ha
      have hb : v * a * v⁻¹ ∈ (⁅Sg, Sg⁆ : Subgroup X) := ha
      have hcomm := h.mul_comm_of_mem_v_of_mem_sg (V.inv_mem hv)
        (Subgroup.commutator_le_self Sg hb)
      have heq : a = v * a * v⁻¹ := by
        calc a = v⁻¹ * (v * a * v⁻¹) * v := by group
          _ = v * a * v⁻¹ := by rw [hcomm]; group
      rwa [heq]
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hmem : ⁅s, a⁆ ∈ (⁅Sg, Sg⁆ : Subgroup X) :=
        Subgroup.commutator_mem_commutator hs (Subgroup.commutator_le_self Sg ha)
      have heq : s * a * s⁻¹ = ⁅s, a⁆ * a := by rw [commutatorElement_def]; group
      rw [heq]
      exact (⁅Sg, Sg⁆).mul_mem hmem ha
    · intro ha
      have hb : s * a * s⁻¹ ∈ (⁅Sg, Sg⁆ : Subgroup X) := ha
      have hmem : ⁅s⁻¹, s * a * s⁻¹⁆ ∈ (⁅Sg, Sg⁆ : Subgroup X) :=
        Subgroup.commutator_mem_commutator (Sg.inv_mem hs)
          (Subgroup.commutator_le_self Sg hb)
      have heq : s⁻¹ * (s * a * s⁻¹) * s = ⁅s⁻¹, s * a * s⁻¹⁆ * (s * a * s⁻¹) := by
        rw [commutatorElement_def]; group
      have h2 : s⁻¹ * (s * a * s⁻¹) * s ∈ (⁅Sg, Sg⁆ : Subgroup X) := by
        rw [heq]; exact (⁅Sg, Sg⁆).mul_mem hmem hb
      have heqa : a = s⁻¹ * (s * a * s⁻¹) * s := by group
      rwa [heqa]

theorem injective_restrict_commutator (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) :
    Function.Injective
      ((QuotientGroup.mk' (center K)).domRestrict ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)) := by
  let φ := (QuotientGroup.mk' (center K)).domRestrict ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)
  haveI hA_simple : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := h.isSimpleGroup_commutator_sg
  haveI hsimple : IsSimpleGroup ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) :=
    (Subgroup.subgroupOfEquivOfLe hA).isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hker | hker
  · exact (MonoidHom.ker_eq_bot_iff φ).mp hker
  · exfalso
    have hle_center : ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) ≤ Subgroup.center K := by
      intro x hx
      have hxker : (⟨x, hx⟩ : ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)) ∈ φ.ker := by
        rw [hker]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hxker
      exact (QuotientGroup.eq_one_iff x).mp hxker
    haveI : IsMulCommutative ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) :=
      isMulCommutative_anti hle_center
    have hprime : (Nat.card ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)).Prime :=
      (Group.is_simple_iff_prime_card).mp hsimple
    have hcard : Nat.card ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) = 20160 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, h.card_commutator_sg]
    rw [hcard] at hprime
    have hnot : ¬ Nat.Prime 20160 := by
      intro hp
      rcases hp.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 20160) with h' | h' <;>
        exact absurd h' (by norm_num)
    exact hnot hprime

end SwapShape

@[expose] def quotAbar (Sg K : Subgroup X) : Subgroup (K ⧸ center K) :=
  ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K).map (QuotientGroup.mk' (center K))

theorem SwapShape.quotAbar_equiv (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) :
    Nonempty (↥(quotAbar Sg K) ≃* alternatingGroup (Fin 8)) := by
  let φ := (QuotientGroup.mk' (center K)).domRestrict ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)
  have hφ : Function.Injective φ := SwapShape.injective_restrict_commutator h hA
  have hrange : quotAbar Sg K = φ.range := by
    rw [quotAbar]
    exact (MonoidHom.domRestrict_range ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)
      (QuotientGroup.mk' (center K))).symm
  exact ⟨((MulEquiv.subgroupCongr hrange).trans
    (MonoidHom.ofInjective hφ).symm).trans
    ((Subgroup.subgroupOfEquivOfLe hA).trans h.commutatorEquivAlt8)⟩

theorem SwapShape.quotConj_ne_one [K.Normal] (h : SwapShape t Sg V) (hK : ⁅K, K⁆ = K)
    (hne : ⁅Sg, Sg⁆ ≠ K) (hA : ⁅Sg, Sg⁆ ≤ K) : quotConj K t ≠ 1 := by
  intro hq
  have hKC : K ≤ centralizer ({t} : Set X) := le_centralizer_of_quotConj_eq_one hK hq
  have h1 : ⁅K, K⁆ ≤ ⁅Sg, Sg⁆ := by
    have hmono : ⁅K, K⁆ ≤ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ :=
      Subgroup.commutator_mono hKC hKC
    exact hmono.trans h.commutator_centralizer_le
  rw [hK] at h1
  exact hne (le_antisymm hA h1)

end CFSG.OddStandard.AltStdSec.SwapPartner
