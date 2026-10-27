module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem y7a_comm_range {V W : Subgroup G} {t : G}
    (hWab : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) (hW : ∀ w ∈ W, ∀ v ∈ V, v * w = w * v)
    (hVW : ∀ v ∈ V, ⁅v, t⁆ ∈ W) :
    ∃ R : Subgroup G, R ≤ W ∧ (∀ r : G, r ∈ R ↔ ∃ v ∈ V, ⁅v, t⁆ = r) ∧
      Nat.card ↥V = Nat.card ↥(V ⊓ centralizer ({t} : Set G)) * Nat.card ↥R := by
  let φ : ↥V →* ↥W :=
    MonoidHom.mk' (fun v => ⟨⁅(v : G), t⁆, hVW v v.2⟩) (by
      intro v v'
      apply Subtype.ext
      show ⁅(v : G) * (v' : G), t⁆ = ⁅(v : G), t⁆ * ⁅(v' : G), t⁆
      have hc : ⁅(v' : G), t⁆ ∈ W := hVW v' v'.2
      have hconj : (v : G) * ⁅(v' : G), t⁆ * (v : G)⁻¹ = ⁅(v' : G), t⁆ := by
        rw [hW _ hc _ v.2]; group
      calc ⁅(v : G) * (v' : G), t⁆
          = (v : G) * ⁅(v' : G), t⁆ * (v : G)⁻¹ * ⁅(v : G), t⁆ :=
            commutatorElement_mul_left_eq_conj_mul _ _ _
        _ = ⁅(v' : G), t⁆ * ⁅(v : G), t⁆ := by rw [hconj]
        _ = ⁅(v : G), t⁆ * ⁅(v' : G), t⁆ := hWab _ hc _ (hVW v v.2))
  have hker : φ.ker = (V ⊓ centralizer ({t} : Set G)).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨v.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h)
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hker_card : Nat.card ↥φ.ker = Nat.card ↥(V ⊓ centralizer ({t} : Set G)) := by
    rw [hker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : V ⊓ centralizer ({t} : Set G) ≤ V)).toEquiv
  have hrange_card : Nat.card ↥φ.range = Nat.card ↥(φ.range.map W.subtype) :=
    Nat.card_congr (Subgroup.equivMapOfInjective φ.range W.subtype W.subtype_injective).toEquiv
  have hVcard : Nat.card ↥V = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h
    exact h.trans (mul_comm _ _)
  refine ⟨φ.range.map W.subtype, ?_, ?_, ?_⟩
  · rintro r ⟨w, -, hwr⟩
    rw [← hwr]
    exact w.2
  · intro r
    constructor
    · intro hr
      rw [Subgroup.mem_map] at hr
      obtain ⟨w, hw, hwr⟩ := hr
      rw [MonoidHom.mem_range] at hw
      obtain ⟨v, hv⟩ := hw
      exact ⟨(v : G), v.2, by rw [← hwr, ← hv]; rfl⟩
    · rintro ⟨v, hv, hvr⟩
      rw [Subgroup.mem_map]
      refine ⟨φ ⟨v, hv⟩, ?_, ?_⟩
      · rw [MonoidHom.mem_range]; exact ⟨⟨v, hv⟩, rfl⟩
      · exact hvr
  · rw [hVcard, hker_card, hrange_card]

theorem y7a_sup_elems {E V : Subgroup G} (hc : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e) :
    ∀ x ∈ E ⊔ V, ∃ e ∈ E, ∃ v ∈ V, x = e * v :=
  fun _ hx => CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hc hx

theorem y7a_isElemAbelian_sup {E V : Subgroup G} (hE : IsElemAbelian 2 E)
    (hV : IsElemAbelian 2 V) (hc : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e) :
    IsElemAbelian 2 (E ⊔ V) := by
  have commE : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    intro e he e' he'
    haveI := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨e, he⟩ : E) ⟨e', he'⟩)
  have commV : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v := by
    intro v hv v' hv'
    haveI := hV.1
    exact congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : V) ⟨v', hv'⟩)
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    obtain ⟨e, he, v, hv, hx⟩ := y7a_sup_elems hc (x : G) x.2
    obtain ⟨e', he', v', hv', hy⟩ := y7a_sup_elems hc (y : G) y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hx, hy]
    have h1 : Commute e e' := commE e he e' he'
    have h2 : Commute e v' := hc e he v' hv'
    have h3 : Commute v e' := (hc e' he' v hv).symm
    have h4 : Commute v v' := commV v hv v' hv'
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  · intro x hx
    obtain ⟨e, he, v, hv, rfl⟩ := y7a_sup_elems hc x hx
    have hcomm : Commute e v := hc e he v hv
    rw [hcomm.mul_pow 2, hE.2 e he, hV.2 v hv, one_mul]

theorem y7a_card_sup_mul_inf {E V : Subgroup G} (hc : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e) :
    Nat.card ↥(E ⊔ V) * Nat.card ↥(E ⊓ V) = Nat.card ↥E * Nat.card ↥V :=
  CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hc

end CFSG.OddStandard.HigherRank.YamadaG23
