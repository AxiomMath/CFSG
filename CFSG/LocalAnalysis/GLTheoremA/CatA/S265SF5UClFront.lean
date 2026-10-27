module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ESLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ESetupA
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)


theorem exists_cls_data_of_qsnl {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 5 S B T x D K) (hK : catalogIs (PSimple 5 K) (tyFUni 5))
    (hZK : Subgroup.center ↥K = ⊥)
    (h25 : ∀ (m : ℕ) (F : Type) [Field F] (hF : UnitaryFieldData 2 m F),
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) →
      ¬ 25 ∣ 2 ^ m + 1)
    {lab : GLALabel} (hlab : InnLabelOf B S lab)
    (hnd : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (β : MulAut G) (J : Subgroup G) (e : ℕ),
      CFSG.StandardType.MarkedModel lab G ∧ β ∈ innAutDerived G ∧ β ^ 5 = 1 ∧ β ≠ 1 ∧
      IsComponentOf J (fixSubgroup β) ∧ Subgroup.center ↥J = ⊥ ∧
      Nat.card J = ordTwistedA 4 (2 ^ e) ∧ 5 ∣ 2 ^ e + 1 ∧ ¬ 25 ∣ 2 ^ e + 1 := by
  have cfg := h.cfg
  haveI hSn : S.Normal := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top g
  obtain ⟨d₀, hd₀B, -, hd₀C, hKcomp⟩ := s265e_exists_d0 cfg
  have hβ1 := CanonSubcomp.centerQuotAut_conjAut_ne_one (hnorm d₀) hd₀C cfg.quasi.1
  have hβ5 : Y10F.centerQuotAut ↥S (Y10F.conjAut S d₀ (hnorm d₀)) ^ 5 = 1 := by
    rw [s265e_centerQuotAut_conjAut S (hnorm d₀), ← map_pow, inv_pow, cfg.elem.2 d₀ hd₀B,
      inv_one, map_one]
  have hLl : HasLabel ↥S (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hlab
  have hMd : MarkedInnDiag S d₀ lab :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ h => ⟨h.1, h.2.2 d₀ hd₀B⟩) hlab
  have hKb := CanonInn.isComponentOf_fixSubgroup_conjAut S (hnorm d₀) hKcomp
  have hJcomp := CanonInn.isComponentOf_map_centerQuot _ hKb
  have hKS : K ≤ S := hKcomp.1.trans inf_le_left
  have hZK' : Subgroup.center ↥(K.subgroupOf S) = ⊥ := by
    rw [← Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hKS).symm, hZK, Subgroup.map_bot]
  set π := QuotientGroup.mk' (Subgroup.center ↥S)
  have hinj : Function.Injective (π.subgroupMap (K.subgroupOf S)) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkZ : (k : ↥S) ∈ Subgroup.center ↥S :=
      (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hk)
    have hk' : k ∈ Subgroup.center ↥(K.subgroupOf S) := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (Subgroup.mem_center_iff.1 hkZ (g : ↥S))
    rw [hZK'] at hk'
    exact Subgroup.mem_bot.1 hk'
  let eJ := MulEquiv.ofBijective _ ⟨hinj, π.subgroupMap_surjective (K.subgroupOf S)⟩
  have hZJ : Subgroup.center ↥((K.subgroupOf S).map π) = ⊥ := by
    rw [← Subgroup.map_center_eq eJ, hZK', Subgroup.map_bot]
  obtain ⟨m, F, _, hF, h5, -, -, ⟨eK⟩⟩ := SF.exists_psu_model hKcomp.2.2 hK
  have := hF.finite
  have hmod : StatedClassicalModel (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
      .PSU 5 2 m :=
    ⟨⟨Nat.prime_two, hF.one_le, by norm_num, by simp⟩, F, inferInstance, inferInstance,
      hF.card_eq_sq, ⟨(CFSG.StandardType.InndiagSU.projEquiv hF (by norm_num)).symm⟩⟩
  have hcard : Nat.card ↥((K.subgroupOf S).map π) = ordTwistedA 4 (2 ^ m) := by
    rw [← Nat.card_congr eJ.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv,
      ← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZK).trans
        QuotientGroup.quotientBot).toEquiv, Nat.card_congr eK.toEquiv]
    exact (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  exact ⟨↥S ⧸ Subgroup.center ↥S, inferInstance, inferInstance, _, _, m,
    CanonSubcomp.markedModel_of_hasLabel hLl, s265e_mem_innAutDerived (hnorm d₀) hMd hnd, hβ5,
    hβ1, hJcomp, hZJ, hcard, h5, h25 m F hF ⟨eK⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
