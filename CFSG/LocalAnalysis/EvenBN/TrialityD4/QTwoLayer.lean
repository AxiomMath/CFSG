module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroLayer
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoQTwoCat

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamada_5_4_layer_of_dichotomy (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h54 :

    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧
      ((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧
          ((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) < Kc ∧
          QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉ Kc ∧
          (∃ hsN : QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
                ⟨t, h.t_mem_centralizer_J₀ d⟩ ∈ normalizer (Kc : Set _),
            Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥ ∧
          center Kc = ⊥ ∧
          Nonempty (Kc ≃* (((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) : Subgroup _))))) :
    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧ center Kc = ⊥ ∧
      (∀ C : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
          CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
        CFSG.IsComponent C → C = Kc ∨ C = Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom) ∧
      CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) =
        normalClosure (((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
            Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) :
              Set (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ∧
      (∀ a ∈ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        ∀ e ∈ CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
          a * e = e * a) ∧
      (CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) =
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      QuotientGroup.mk' (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥)) := by
  obtain ⟨Kc, hKc, hKb, hcase⟩ := h54
  have hKH : d.leviJ₀.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    leviJ₀_map_le_centralizer_J₀ d
  have hKperf : ⁅(d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        (d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))⁆ =
      (d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) := by
    have hKG : ⁅d.leviJ₀.map L.subtype, d.leviJ₀.map L.subtype⁆ = d.leviJ₀.map L.subtype :=
      Subgroup.isPerfect_iff.1 (isQuasisimple_leviJ₀_map d).1
    apply Subgroup.map_injective (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G)).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_eq_left.2 hKH, hKG]
  have hKO : ∀ a ∈ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      ∀ k ∈ (d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)), a * k = k * a :=
    fun a ha k hk => Subtype.ext (h.oddCore_commute_leviJ₀ d ⟨a, ha, rfl⟩ hk)
  have hs : (⟨t, h.t_mem_centralizer_J₀ d⟩ :
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) * ⟨t, h.t_mem_centralizer_J₀ d⟩ =
        1 := Subtype.ext h.t_mul_t
  have hsK : ∀ k ∈ (d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        k * ⟨t, h.t_mem_centralizer_J₀ d⟩ = ⟨t, h.t_mem_centralizer_J₀ d⟩ * k :=
    fun k hk => Subtype.ext (mem_centralizer_iff.1 h.htL _ (map_subtype_le _ hk))
  have hZ : center Kc = ⊥ := by
    rcases hcase with ⟨-, -, -, -, hZ, -⟩ | ⟨-, -, hZ, -⟩ <;> exact hZ
  have hcomp := fun C hC => h.isComponent_eq_of_le_sup d hKc hKb (C' := C) hC
  have hKab : ∃ a ∈ (d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      ∃ b ∈ (d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      a * b * a⁻¹ * b⁻¹ ∉ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) :
        Set G)) := by
    have h2 : d.x₂ 1 ∈ d.leviJ₀ := d.U₂_le_leviJ₀ (d.x₂_mem_U₂ 1)
    have h5 : d.x₅ 1 ∈ d.leviJ₀ := d.U₅_le_leviJ₀ (d.x₅_mem_U₅ 1)
    set a : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
      ⟨(d.x₂ 1 : G), hKH ⟨_, h2, rfl⟩⟩ with ha
    set b : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
      ⟨(d.x₅ 1 : G), hKH ⟨_, h5, rfl⟩⟩ with hb
    refine ⟨a, ⟨_, h2, rfl⟩, b, ⟨_, h5, rfl⟩, ?_⟩
    have e : ((a * b * a⁻¹ * b⁻¹ : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
        G) = ((d.x₆ 1 : L) : G) := by
      show (d.x₂ 1 : G) * d.x₅ 1 * (d.x₂ 1 : G)⁻¹ * (d.x₅ 1 : G)⁻¹ = d.x₆ 1
      rw [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, ← commutatorElement_def, d.comm₂₅, mul_one]
    refine not_mem_oddCore_of_mul_self_D4 (Subtype.ext ?_) (fun h1 => ?_)
    · rw [Subgroup.coe_mul, e, ← Subgroup.coe_mul, d.x₆_mul_self, Subgroup.coe_one,
        OneMemClass.coe_one]
    · have := congrArg Subtype.val h1
      rw [e, OneMemClass.coe_one] at this
      have h6 : d.x₆ 1 = 1 := Subtype.ext this
      exact one_ne_zero (d.x₆_injective (h6.trans d.x₆_zero.symm))
  obtain ⟨hEN, hEO, hEmap⟩ := layer_eq_normalClosure_D4 hKperf hKO hs hsK hKc hZ hcomp hKb hKab
  refine ⟨Kc, hKc, hZ, hcomp, hEN, hEO, hEmap, ?_, ?_⟩
  · rcases hcase with ⟨heq, -, htK, -, -, -⟩ | ⟨hne, hcomm, -, -⟩
    · rw [heq, sup_idem]
      exact htK
    · intro ht
      apply hne
      refine map_conj_eq_self_D4 ?_
      have hle : Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≤ normalizer (Kc : Set _) :=
        sup_le le_normalizer ((le_centralizer_iff.1
          (commutator_eq_bot_iff_le_centralizer.1 hcomm)).trans
            (Subgroup.centralizer_le_normalizer _))
      exact hle ht
  · rcases hcase with ⟨heq, -, -, -, -, hlie⟩ | ⟨hne, hcomm, -, -⟩
    · exact Or.inl ⟨heq, hlie⟩
    · exact Or.inr ⟨hne, hcomm⟩

end Setup

section Two

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamada_5_4_layer_two
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) :
    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧ center Kc = ⊥ ∧
      (∀ C : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
          CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
        CFSG.IsComponent C → C = Kc ∨ C = Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom) ∧
      CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) =
        normalClosure (((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
            Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) :
              Set (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ∧
      (∀ a ∈ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        ∀ e ∈ CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
          a * e = e * a) ∧
      (CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) =
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      QuotientGroup.mk' (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥)) :=
  h.yamada_5_4_layer_of_dichotomy d (h.yamada_5_4_two d hf)

theorem layerHyp_two
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) : h.LayerHyp d :=
  h.yamada_5_4_layer_two d hf

end Setup

end Two

end CFSG.LocalAnalysis.EvenBN.TrialityD4
