module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSubDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSubAbs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A] {z : A} {p : ℕ} {X J : Subgroup A}

theorem absHyp_of_subHyp (h : SubHyp z p X J) :
    SubAbs.AbsHyp (⟨z, z_mem_secY z X J⟩ : ↥(secY z X J)) p (X.subgroupOf (secY z X J))
      (J.subgroupOf (secY z X J)) := by
  have hXY : X ≤ secY z X J := X_le_secY z X J
  have hJY : J ≤ secY z X J := J_le_secY z X J
  have hmapX : (X.subgroupOf (secY z X J)).map (secY z X J).subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hXY
  have hmapJ : (J.subgroupOf (secY z X J)).map (secY z X J).subtype = J :=
    Subgroup.map_subgroupOf_eq_of_le hJY
  have hmapZ : (zpowers (⟨z, z_mem_secY z X J⟩ : ↥(secY z X J))).map (secY z X J).subtype =
      zpowers z := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hnormY : secY z X J ≤ normalizer (J : Set A) :=
    sup_le (sup_le le_normalizer h.XJ) (zpowers_le.mpr h.zJ)
  refine ⟨?_, Subtype.ext h.z2, ?_, ?_, ?_, ?_⟩
  · refine ⟨h.A4.prime, h.A4.odd, mem_top _, le_top, ?_, ?_, ?_, ?_⟩
    · exact h.A4.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXY).symm
    · intro hbot
      apply h.A4.ne_bot
      rw [← hmapX, hbot, Subgroup.map_bot]
    · intro c _ hc
      have hcz : (c : A) ∈ centralizer ({z} : Set A) := by
        rw [mem_centralizer_singleton_iff] at hc ⊢
        exact congrArg Subtype.val hc
      have hnorm := h.A4.inv (c : A) (mem_top _) hcz
      rw [mem_normalizer_iff] at hnorm ⊢
      intro y
      exact hnorm (y : A)
    · apply Subgroup.map_injective (secY z X J).subtype_injective
      rw [Subgroup.map_commutator, hmapX, hmapZ, h.A4.comm]
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mpr hnormY
  · exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJY).symm h.comp.1
  · apply Subgroup.map_injective (secY z X J).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, hmapJ, hmapX, hmapZ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    rfl
  · intro hbot
    apply h.JX
    have := congrArg (Subgroup.map (secY z X J).subtype) hbot
    rwa [Subgroup.map_commutator, hmapJ, hmapX, Subgroup.map_bot] at this

theorem secB_Sig4A (h : SubHyp z p X J) :
    Sig4A (secZ z X J) (⊤ : Subgroup (secB z X J)) p (secX z X J) :=
  SubAbs.sig4A_quotient (absHyp_of_subHyp h)

theorem secB_pCore (h : SubHyp z p X J) : pCore p (secB z X J) = ⊥ := by
  have : Fact p.Prime := ⟨h.A4.prime⟩
  exact SubAbs.pCore_quotient_eq_bot (G := ↥(secY z X J)) h.A4.odd

theorem secB_layer (h : SubHyp z p X J) : layer (secB z X J) = secJ z X J :=
  SubAbs.layer_quotient (absHyp_of_subHyp h)

theorem secB_Hyp42 (h : SubHyp z p X J) : Hyp42 (secZ z X J) (secX z X J) :=
  SubAbs.hyp42_quotient (absHyp_of_subHyp h)

theorem secB_X_ker (h : SubHyp z p X J) {x : A} (hx : x ∈ X) :
    (QuotientGroup.mk (⟨x, X_le_secY z X J hx⟩ : ↥(secY z X J)) : secB z X J) = 1 ↔
      x ∈ centralizer (J : Set A) := by
  have hh := absHyp_of_subHyp h
  refine (SubAbs.mk_eq_one_iff_of_mem hh (x := ⟨x, X_le_secY z X J hx⟩) hx).trans ?_
  constructor
  · intro hc j hj
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨j, J_le_secY z X J hj⟩ hj)
  · intro hc
    rw [mem_centralizer_iff]
    intro j hj
    exact Subtype.ext (mem_centralizer_iff.mp hc (j : A) hj)

theorem secJ_equiv (h : SubHyp z p X J) :
    Nonempty (↥(secJ z X J) ≃* (↥J ⧸ pPrimeCore 2 ↥J)) := by
  obtain ⟨e⟩ := SubAbs.equiv_map_J (absHyp_of_subHyp h)
  let eJ : ↥(J.subgroupOf (secY z X J)) ≃* ↥J := Subgroup.subgroupOfEquivOfLe (J_le_secY z X J)
  exact ⟨e.trans (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ))⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
