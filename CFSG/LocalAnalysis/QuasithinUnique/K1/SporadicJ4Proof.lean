module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicSelfCentral
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Blueprint.NativeSporadic

theorem selfCentralizingFusionData_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SelfCentralizingFusionData Y) : SelfCentralizingFusionData X := by
  obtain ⟨H, E, hEH, hidx, hnorm, hE2, hmin, hcent, x, hx, g, hx2, hgH, hgE⟩ := h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨H.comap e.toMonoidHom, E.comap e.toMonoidHom, Subgroup.comap_mono hEH, ?_, ?_, ?_, ?_,
    ?_, e.symm x, ?_, e.symm g, ?_, ?_, ?_⟩
  · rwa [Subgroup.index_comap_of_surjective H hsurj]
  · intro h hh y hy
    have := hnorm (e h) hh (e y) hy
    simpa using this
  · exact hE2.comap_of_injective e.toMonoidHom hinj
  · intro D hDE hD
    have hD' : ∀ h ∈ H, ∀ d ∈ D.map e.toMonoidHom, h * d * h⁻¹ ∈ D.map e.toMonoidHom := by
      rintro h hh _ ⟨d, hd, rfl⟩
      refine ⟨e.symm h * d * (e.symm h)⁻¹, hD (e.symm h) ?_ d hd, ?_⟩
      · show e (e.symm h) ∈ H
        simpa using hh
      · simp
    rcases hmin (D.map e.toMonoidHom) (by
      rintro _ ⟨d, hd, rfl⟩
      exact hDE hd) hD' with h0 | h0
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective D hinj).1 h0
    · right
      rw [← Subgroup.comap_map_eq_self_of_injective hinj D, h0]
  · intro h hh hc
    show e h ∈ E
    refine hcent (e h) hh fun y hy => ?_
    have := hc (e.symm y) (by show e (e.symm y) ∈ E; simpa using hy)
    have := congrArg e this
    simpa using this
  · show e (e.symm x) ∈ E
    simpa using hx
  · rw [← map_mul, hx2, map_one]
  · show e (e.symm g * e.symm x * (e.symm g)⁻¹) ∈ H
    simpa using hgH
  · intro hmem
    apply hgE
    have : e (e.symm g * e.symm x * (e.symm g)⁻¹) ∈ E := hmem
    simpa using this

theorem selfCentralizingFusionData_J4
    : SelfCentralizingFusionData (Carrier .J4) :=
  selfCentralizingFusionData_of_mulEquiv (X := Carrier .J4) (Y := CFSG.Sporadic.J4.J)
    (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
    (CFSG.Sporadic.J4.QT.selfCentralizingFusion_J CFSG.Sporadic.J4.j4Facts)

end CFSG.QuasithinUnique.K1
