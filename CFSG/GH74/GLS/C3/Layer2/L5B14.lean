module

public import CFSG.GH74.GLS.C3.Layer2.L5B13

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem sameInvolutionFusionPattern_of_hom {G Gs : Type} [Group G] [Group Gs] [Finite G]
    [Finite Gs] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (φ : ↥S →* Gs)
    (hinj : Function.Injective φ) (hsyl : IsSylowOf 2 φ.range ⊤)
    (hφ : ∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 →
      (IsConj (u : G) (v : G) ↔ IsConj (φ u) (φ v))) :
    SameInvolutionFusionPattern G Gs := by
  obtain ⟨Q, hQ⟩ := L4.PartB6.exists_sylow_eq_of_isSylowOf_top hS
  obtain ⟨Q', hQ'⟩ := L4.PartB6.exists_sylow_eq_of_isSylowOf_top hsyl
  let e : ↥(Q : Subgroup G) ≃* ↥(Q' : Subgroup Gs) :=
    (MulEquiv.subgroupCongr hQ).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hQ'.symm))
  refine ⟨Q, Q', e, fun u v hu hv => ?_⟩
  exact hφ (MulEquiv.subgroupCongr hQ u) (MulEquiv.subgroupCongr hQ v)
    (by rw [MulEquiv.orderOf_eq]; exact hu) (by rw [MulEquiv.orderOf_eq]; exact hv)

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Pattern

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem case47_pattern_of_invol
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hc : Case47 h c) (haa : a * a = 1) :
    SameInvolutionFusionPattern G (alternatingGroup (Fin 9)) := by
  have hTS : T ≤ S := h.T_lt_S.le
  have haR : a * a ∈ c.lift Rm := by rw [haa]; exact one_mem _
  obtain ⟨ψ, hinj, hS0, hsurj, hψT, hψnT⟩ := exists_psi hc haR
  have hcls : ∀ u : ↥S, orderOf u = 2 →
      (IsConj (u : G) x ∧ numMoved (ψ u) = 4) ∨
        (IsConj (u : G) (L4.vElt x a) ∧ numMoved (ψ u) = 8) := by
    intro u hu
    obtain ⟨u, huS⟩ := u
    have hu2 : (⟨u, huS⟩ : ↥S) * ⟨u, huS⟩ = 1 := by
      have := pow_orderOf_eq_one (⟨u, huS⟩ : ↥S)
      rwa [hu, pow_two] at this
    have huu : u * u = 1 := congrArg Subtype.val hu2
    have hu1 : u ≠ 1 := by
      intro e
      have : (⟨u, huS⟩ : ↥S) = 1 := Subtype.ext e
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)
    have hψu2 : ψ ⟨u, huS⟩ * ψ ⟨u, huS⟩ = 1 := by rw [← map_mul, hu2, map_one]
    have hψu1 : ψ ⟨u, huS⟩ ≠ 1 := by
      intro e
      exact hu1 (congrArg Subtype.val (hinj (e.trans (map_one ψ).symm)))
    by_cases huT : u ∈ T
    · have hm5 : c.rco u ∈ T5 := c.rco_mem_T5 huT
      have hm2 : c.rco u * c.rco u = 1 := by rw [← c.rco_T_mul huT huT, huu, Coord5.rco_one]
      have hm1 : c.rco u ≠ 1 := by
        intro e
        exact hu1 (c.rco_T_inj huT T.one_mem (by rw [e, Coord5.rco_one]))
      have hnm : numMoved (ψ ⟨u, huS⟩) = nmE (c.rco u) := by
        rw [hψT u huT]; rfl
      have h8 := nm_id (c.rco u) hm5 hm2 hm1
      by_cases hmix : Mixm (c.rco u)
      · right
        refine ⟨isConj_v_of_Mixm hc huT hmix, ?_⟩
        rw [hnm]
        exact h8.2 hmix
      · left
        have hn8 : nmE (c.rco u) ≠ 8 := fun e => hmix (h8.1 e)
        have hn : numMoved (ψ ⟨u, huS⟩) = 4 := by
          rcases S0_invol_nm (hS0 ⟨u, huS⟩) hψu2 hψu1 with h4 | h8'
          · exact h4
          · exact absurd (hnm ▸ h8') hn8
        refine ⟨?_, hn⟩
        by_cases huR : u ∈ c.lift Rm
        · exact isConj_x_of_R_nonmixed hc huR hu1 hmix
        · exact Mg1 hsimple hnab hc haa huT huR huu
    · right
      refine ⟨Mg2 hsimple hnab hc haa huS huT huu, ?_⟩
      exact S0_invol_nT_nm8 (hS0 ⟨u, huS⟩) hψu2 hψu1 (hψnT u huS huT)
  let Φ : ↥S →* alternatingGroup (Fin 9) :=
    ψ.codRestrict (alternatingGroup (Fin 9)) (fun s => S0_le_alt (hS0 s))
  have hΦinj : Function.Injective Φ := fun s s' hss =>
    hinj (congrArg (fun z : alternatingGroup (Fin 9) => (z : Perm (Fin 9))) hss)
  have hΦrange : Φ.range = S0A := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact hS0 s
    · intro hz
      obtain ⟨s, hs⟩ := hsurj (z : Perm (Fin 9)) (mem_S0A.1 hz)
      exact ⟨s, Subtype.ext hs⟩
  refine sameInvolutionFusionPattern_of_hom h.sylowS Φ hΦinj (by rw [hΦrange]; exact isSylowOf_S0A)
    (fun u w hu hw => ?_)
  have hΦu : orderOf (Φ u) = 2 := by rw [orderOf_injective Φ hΦinj]; exact hu
  have hΦw : orderOf (Φ w) = 2 := by rw [orderOf_injective Φ hΦinj]; exact hw
  have hcu := hcls u hu
  have hcw := hcls w hw
  have hnm : numMoved ((Φ u : alternatingGroup (Fin 9)) : Perm (Fin 9)) = numMoved (ψ u) := rfl
  have hnm' : numMoved ((Φ w : alternatingGroup (Fin 9)) : Perm (Fin 9)) = numMoved (ψ w) := rfl
  constructor
  · intro hconj
    apply isConj_alternating_of_numMoved_eq 9 _ _ hΦu hΦw
    rw [hnm, hnm']
    rcases hcu with ⟨hux, hun⟩ | ⟨huv, hun⟩ <;> rcases hcw with ⟨hwx, hwn⟩ | ⟨hwv, hwn⟩
    · rw [hun, hwn]
    · exfalso
      exact x_not_conj_v hc (hux.symm.trans (hconj.trans hwv))
    · exfalso
      exact x_not_conj_v hc (hwx.symm.trans (hconj.symm.trans huv))
    · rw [hun, hwn]
  · intro hconj
    have h1 := numMoved_eq_of_isConj_alternating 9 hconj
    rw [hnm, hnm'] at h1
    rcases hcu with ⟨hux, hun⟩ | ⟨huv, hun⟩ <;> rcases hcw with ⟨hwx, hwn⟩ | ⟨hwv, hwn⟩
    · exact hux.trans hwx.symm
    · exfalso
      rw [hun, hwn] at h1
      exact absurd h1 (by norm_num)
    · exfalso
      rw [hun, hwn] at h1
      exact absurd h1 (by norm_num)
    · exact huv.trans hwv.symm

theorem case47_pattern
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hc : Case47 h c) : SameInvolutionFusionPattern G (alternatingGroup (Fin 9)) := by
  have haR : a * a ∈ c.lift Rm := by
    by_contra hnot
    exact caseII_false hsimple hnab hc hnot
  obtain ⟨p, hp, hpa⟩ := exists_invol_aT hc haR
  have h' : IsAConfig 5 x K T Q S (p * a) := IsAConfig.of_mul h hp.1
  exact case47_pattern_of_invol hsimple hnab (Case47.ofEq hc h') hpa

end Pattern

end CFSG.GH74.GLS.C3.Layer2.L5
