module

public import CFSG.GH74.GLS.NT44.QuotientOmega
import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem exists_centerQuotient_sylow_omega1_four
    {X : Type} [Group X] [Finite X] {L V : Subgroup X}
    (Sbar : Sylow 2 X) (hLn : L.Normal) (hVL : V ≤ L)
    (hVElem : CFSG.IsElementaryAbelian 2 ↥V) (hV4 : Nat.card ↥V = 4)
    (hfaith : ∀ v ∈ V, v ≠ 1 → ¬ ∀ l ∈ L, v * l = l * v)
    (hind : CFSG.Goldschmidt.InducesOmega1 V L (Sbar : Subgroup X)) :
    ∃ P : Sylow 2 ↥L,
      (P : Subgroup ↥L) = (Sbar : Subgroup X).subgroupOf L ∧
      let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let τ : ↥L →* (↥L ⧸ Subgroup.center ↥L) :=
        QuotientGroup.mk' (Subgroup.center ↥L)
      let Q : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
        P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
      CFSG.Goldschmidt.Omega1 (Q : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
          (V.subgroupOf L).map τ ∧
        Nat.card ↥(CFSG.Goldschmidt.Omega1
          (Q : Subgroup (↥L ⧸ Subgroup.center ↥L))) = 4 ∧
        CFSG.IsElementaryAbelian 2 ↥(CFSG.Goldschmidt.Omega1
          (Q : Subgroup (↥L ⧸ Subgroup.center ↥L))) ∧
        IsMulCommutative ↥(CFSG.Goldschmidt.Omega1
          (Q : Subgroup (↥L ⧸ Subgroup.center ↥L))) := by
  classical
  let _ : L.Normal := hLn
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq L Sbar
  refine ⟨P, hP, ?_⟩
  let τ : ↥L →* (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.mk' (Subgroup.center ↥L)
  let Q : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  change CFSG.Goldschmidt.Omega1 (Q : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
      (V.subgroupOf L).map τ ∧
    Nat.card ↥(CFSG.Goldschmidt.Omega1
      (Q : Subgroup (↥L ⧸ Subgroup.center ↥L))) = 4 ∧
    CFSG.IsElementaryAbelian 2 ↥(CFSG.Goldschmidt.Omega1
      (Q : Subgroup (↥L ⧸ Subgroup.center ↥L))) ∧
    IsMulCommutative ↥(CFSG.Goldschmidt.Omega1
      (Q : Subgroup (↥L ⧸ Subgroup.center ↥L)))
  have hQcoe : (Q : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
      (P : Subgroup ↥L).map τ := by
    simpa only [Q, τ] using
      (Sylow.coe_mapSurjective
        (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) P)
  have hOmega :
      CFSG.Goldschmidt.Omega1 (Q : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
        (V.subgroupOf L).map τ := by
    rw [hQcoe, hP]
    simpa only [τ] using
      CFSG.GH74.GLS.NT44.omega1_centerQuotient_eq_map_of_inducesOmega1 hVL hind
  let κ : ↥(V.subgroupOf L) →* (↥L ⧸ Subgroup.center ↥L) :=
    τ.comp (V.subgroupOf L).subtype
  have hκ : Function.Injective κ := by
    apply (injective_iff_map_eq_one κ).2
    intro v hv
    change (QuotientGroup.mk (v : ↥L) : ↥L ⧸ Subgroup.center ↥L) = 1 at hv
    have hz : (v : ↥L) ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff (v : ↥L)).mp hv
    have hv1 : ((v : ↥L) : X) = 1 := by
      by_contra hvne
      apply hfaith ((v : ↥L) : X) (Subgroup.mem_subgroupOf.mp v.property) hvne
      intro l hl
      exact (congrArg (fun z : ↥L => (z : X))
        ((Subgroup.mem_center_iff.mp hz) ⟨l, hl⟩)).symm
    exact Subtype.ext (Subtype.ext hv1)
  have himage :
      (⊤ : Subgroup ↥(V.subgroupOf L)).map κ = (V.subgroupOf L).map τ := by
    change (⊤ : Subgroup ↥(V.subgroupOf L)).map
      (τ.comp (V.subgroupOf L).subtype) = (V.subgroupOf L).map τ
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  have hVsub4 : Nat.card ↥(V.subgroupOf L) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv).trans hV4
  have hImage4 : Nat.card ↥((V.subgroupOf L).map τ) = 4 := by
    rw [← himage, Subgroup.card_map_of_injective hκ, Subgroup.card_top]
    exact hVsub4
  let _ : CFSG.IsElementaryAbelian 2 ↥V := hVElem
  let _ : CFSG.IsElementaryAbelian 2 ↥(V.subgroupOf L) :=
    CFSG.IsElementaryAbelian.subgroupOf hVL
  have hImageElem : CFSG.IsElementaryAbelian 2 ↥((V.subgroupOf L).map τ) :=
    CFSG.IsElementaryAbelian.map τ
  refine ⟨hOmega, ?_, ?_, ?_⟩
  · rw [hOmega]
    exact hImage4
  · rw [hOmega]
    exact hImageElem
  · rw [hOmega]
    exact hImageElem.toIsMulCommutative

end CFSG.GH74.GLS.NT44

end
