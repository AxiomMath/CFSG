module

public import CFSG.GH74.Generic.BProg.B3.S1Lemma282Bal
public import CFSG.GH74.Generic.BProg.B3.ObsPump

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalDefs

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev J0 (a : G) (J : Subgroup G) : Type :=
  ↥(PumpCalc.bar a J) ⧸ center ↥(PumpCalc.bar a J)

abbrev NJ (a : G) (J : Subgroup G) : Subgroup G :=
  normalizer (J : Set G) ⊓ centralizer ({a} : Set G)

variable {a : G} {J : Subgroup G}

@[expose] noncomputable def toBarNorm (hJa : J ≤ centralizer ({a} : Set G)) :
    ↥(NJ a J) →* ↥(normalizer ((PumpCalc.bar a J :
      Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set (barQ ↥(centralizer ({a} : Set G))))) :=
  ((barMk ↥(centralizer ({a} : Set G))).comp
      (Subgroup.inclusion (inf_le_right : NJ a J ≤ centralizer ({a} : Set G)))).codRestrict _
    (fun e => ObsPump.bar_mem_normalizer hJa e.2.2 e.2.1)

@[expose] noncomputable def rho (hJa : J ≤ centralizer ({a} : Set G)) : ↥(NJ a J) →* MulAut (J0 a J) :=
  (rhoL (PumpCalc.bar a J)).comp (toBarNorm hJa)

@[expose] noncomputable def barJ (hJa : J ≤ centralizer ({a} : Set G)) : ↥J →* ↥(PumpCalc.bar a J) :=
  ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion hJa)).codRestrict _
    (fun j => ⟨⟨(j : G), hJa j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩)

@[expose] noncomputable def Pi0 (hJa : J ≤ centralizer ({a} : Set G)) : ↥J →* J0 a J :=
  (QuotientGroup.mk' (center ↥(PumpCalc.bar a J))).comp (barJ hJa)

theorem barJ_surjective (hJa : J ≤ centralizer ({a} : Set G)) : Function.Surjective (barJ hJa) := by
  rintro ⟨_, ⟨c, hc, rfl⟩⟩
  exact ⟨⟨(c : G), Subgroup.mem_subgroupOf.1 hc⟩, Subtype.ext rfl⟩

theorem Pi0_surjective (hJa : J ≤ centralizer ({a} : Set G)) : Function.Surjective (Pi0 hJa) :=
  (QuotientGroup.mk'_surjective _).comp (barJ_surjective hJa)

theorem mem_normalizer_conj {e : G} (he : e ∈ normalizer (J : Set G)) (j : ↥J) :
    e * (j : G) * e⁻¹ ∈ J :=
  (mem_normalizer_iff.1 he j).1 j.2

theorem rho_Pi0 (hJa : J ≤ centralizer ({a} : Set G)) (e : ↥(NJ a J)) (j : ↥J) :
    rho hJa e (Pi0 hJa j) = Pi0 hJa ⟨(e : G) * j * (e : G)⁻¹, mem_normalizer_conj e.2.1 j⟩ := rfl

theorem rho_of_mem (hJa : J ≤ centralizer ({a} : Set G)) (e : ↥(NJ a J)) (he : (e : G) ∈ J) :
    rho hJa e = MulAut.conj (Pi0 hJa ⟨(e : G), he⟩) := by
  have h := S1Lemma282Bal.rhoL_eq_conj (L := PumpCalc.bar a J) (toBarNorm hJa e)
    ⟨⟨(e : G), hJa he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  exact h

variable [Finite G] in
theorem rho_eq_one_iff (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) (e : ↥(NJ a J)) :
    rho hJ.1 e = 1 ↔ (e : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have hc : IsComponent (PumpCalc.bar a J) := PumpCalc.isComponent_bar hJ
  have hY : (e : G) ∈ centralizer ({a} : Set G) := e.2.2
  show rhoL (PumpCalc.bar a J) (toBarNorm hJ.1 e) = 1 ↔ _
  rw [ObsPump.rhoL_eq_one_iff hc]
  constructor
  · intro h
    exact ObsPump.mem_cSec_of_bar_comm hJ hY h
  · intro h x hx
    exact Obs.piBar_commute_of_mem_centralizerSection hJ (z := ⟨(e : G), hY⟩) h x hx

end S1FinalDefs

end CFSG.GH74.Generic.BProg.B3
