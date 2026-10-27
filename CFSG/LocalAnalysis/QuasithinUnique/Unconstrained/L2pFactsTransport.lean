module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.QuasithinUnique

variable {X Y : Type} [Group X] [Group Y]

theorem isSylowTwoOf_top_map [Finite X] [Finite Y] (e : X ≃* Y) {P : Subgroup X}
    (hP : IsSylowTwoOf P ⊤) : IsSylowTwoOf (P.map e.toMonoidHom) ⊤ := by
  refine isSylowTwoOf_of_card_eq le_top (hP.isPGroup.map e.toMonoidHom) ?_
  rw [Subgroup.card_map_of_injective e.injective, hP.card_eq]
  simp only [twoPart, Subgroup.card_top, Nat.card_congr e.toEquiv]

theorem l2pData_of_mulEquiv [Finite X] (e : X ≃* Y) (h : L2pData Y) : L2pData X := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have := h.simple
  refine
    { simple := e.isSimpleGroup
      nonabelian := ?_
      single_class := ?_
      cent_two := ?_
      inner_three := ?_
      a4 := ?_
      nonab := ?_
      aut_two := ?_ }
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
    simpa using congrArg e hc
  · intro i j hi hj
    obtain ⟨k, hk⟩ := h.single_class (e i) (e j) (by rwa [MulEquiv.orderOf_eq])
      (by rwa [MulEquiv.orderOf_eq])
    refine ⟨e.symm k, e.injective ?_⟩
    simpa using hk
  · intro i hi g
    have hi' : orderOf (e i) = 2 := by rwa [MulEquiv.orderOf_eq]
    have hg : e (g : X) ∈ Subgroup.centralizer ({e i} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp g.2
      simpa using congrArg e this
    obtain ⟨n, hn⟩ := h.cent_two (e i) hi' ⟨e g, hg⟩
    refine ⟨n, Subtype.ext (e.injective ?_)⟩
    simpa using congrArg Subtype.val hn
  · rintro α ⟨n, hn⟩
    obtain ⟨k, hk⟩ := h.inner_three (MulAut.congr e α)
      ⟨n, by rw [MulEquiv.orderOf_eq]; exact hn⟩
    refine ⟨e.symm k, fun x => e.injective ?_⟩
    simpa [MulAut.congr_apply] using hk (e x)
  · obtain ⟨V, hV0, hV2, hV3, hVc⟩ := h.a4
    have hrange : V ≤ e.toMonoidHom.range := fun v _ => ⟨e.symm v, by simp⟩
    have hN : Subgroup.normalizer ((V.comap e.toMonoidHom : Subgroup X) : Set X) =
        (Subgroup.normalizer (V : Set Y)).comap e.toMonoidHom :=
      (Subgroup.comap_normalizer_eq_of_le_range hrange).symm
    refine ⟨V.comap e.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro hbot
      apply hV0
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      have h1 : e.symm v ∈ V.comap e.toMonoidHom := by simpa using hv
      rw [hbot, Subgroup.mem_bot] at h1
      simpa using congrArg e h1
    · intro g
      obtain ⟨n, hn⟩ := hV2 ⟨e (g : X), g.2⟩
      have h1 : (e (g : X)) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have h2 : e ((g : X) ^ 2 ^ n) = e 1 := by rw [map_pow, map_one]; exact h1
      exact ⟨n, Subtype.ext (e.injective h2)⟩
    · have hc : (Subgroup.normalizer (V : Set Y)).comap e.toMonoidHom =
          (Subgroup.normalizer (V : Set Y)).map e.symm.toMonoidHom :=
        Subgroup.comap_equiv_eq_map_symm e _
      rw [hN, hc, Subgroup.card_map_of_injective e.symm.injective]
      exact hV3
    · intro x hx hcen hx3
      rw [hN] at hx hcen
      have hex : e x ∈ Subgroup.normalizer (V : Set Y) := hx
      have h1 : e x = 1 := by
        refine hVc (e x) hex (fun y hy => ?_) (by rw [← map_pow, hx3, map_one])
        have hy' : e.symm y ∈ (Subgroup.normalizer (V : Set Y)).comap e.toMonoidHom := by
          simpa using hy
        have := hcen (e.symm y) hy'
        simpa using congrArg e this
      exact e.injective (by simpa using h1)
  · intro P hP
    obtain ⟨y, hy, hy2⟩ := h.nonab (P.map e.toMonoidHom) (isSylowTwoOf_top_map e hP)
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨z, hz, fun hz2 => hy2 ?_⟩
    simp [← map_pow, hz2]
  · intro P hP α hα x
    have key := h.aut_two (P.map e.toMonoidHom) (isSylowTwoOf_top_map e hP) (MulAut.congr e α)
      (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        simp [MulAut.congr_apply, hα z hz]) (e x)
    apply e.injective
    simpa [MulAut.congr_apply] using key

end CFSG.QuasithinUnique.Unc25K1
