module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmBasic
import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBModule2
public import CFSG.LocalAnalysis.SignalizerFunctor.LinearInvariantActions
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.AGLEmbedding CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon (Q8 Q8_nondegenerate polar_Q8)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace)
open CFSG.SignalizerFunctor.Helpers
open QuadraticMap (polar)

private noncomputable def lin (g : GL ι8 (ZMod 2)) : V8 ≃ₗ[ZMod 2] V8 :=
  toLinEquiv ι8 (ZMod 2) g

private theorem lin_mul (a b : GL ι8 (ZMod 2)) : lin (a * b) = lin a * lin b :=
  map_mul (toLinEquiv ι8 (ZMod 2)) a b

private theorem lin_one : lin (1 : GL ι8 (ZMod 2)) = 1 :=
  map_one (toLinEquiv ι8 (ZMod 2))

private theorem lin_add (g : GL ι8 (ZMod 2)) (x y : V8) : lin g (x + y) = lin g x + lin g y :=
  map_add (lin g) x y

private theorem lin_smul (g : GL ι8 (ZMod 2)) (a : ZMod 2) (x : V8) :
    lin g (a • x) = a • lin g x :=
  map_smul (lin g) a x

private theorem lin_sub (g : GL ι8 (ZMod 2)) (x y : V8) : lin g (x - y) = lin g x - lin g y :=
  map_sub (lin g) x y

private theorem lin_zero (g : GL ι8 (ZMod 2)) : lin g 0 = 0 :=
  map_zero (lin g)

private theorem lin_mul_apply (a b : GL ι8 (ZMod 2)) (v : V8) :
    lin (a * b) v = lin a (lin b v) := by
  rw [lin_mul, LinearEquiv.mul_apply]

private theorem isometry_mem (g : ↥Om8) :
    lin (g : GL ι8 (ZMod 2)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q8 := by
  have h := (CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon.mem_Om8_iff_omegaGroup
    (g : CFSG.LocalAnalysis.GLTheoremA.HSubT.SpGL)).mp g.2
  exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp h).1

private theorem map_Q_of_mem (g : ↥Om8) (v : V8) :
    Q8 (lin (g : GL ι8 (ZMod 2)) v) = Q8 v :=
  CFSG.ClassicalGroups.Orthogonal.map_of_mem (isometry_mem g) v

private theorem map_polar_of_mem (g : ↥Om8) (x y : V8) :
    polar Q8 (lin (g : GL ι8 (ZMod 2)) x) (lin (g : GL ι8 (ZMod 2)) y) = polar Q8 x y :=
  CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (isometry_mem g) x y

private theorem even_finrank_commSpace (g : ↥Om8) :
    Even (Module.finrank (ZMod 2) ↥(commSpace (lin (g : GL ι8 (ZMod 2))))) := by
  have h := (CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon.mem_Om8_iff_omegaGroup
    (g : CFSG.LocalAnalysis.GLTheoremA.HSubT.SpGL)).mp g.2
  exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp h).2

private theorem lin_injective : Function.Injective (lin : GL ι8 (ZMod 2) → V8 ≃ₗ[ZMod 2] V8) :=
  (toLinEquiv ι8 (ZMod 2)).injective

private theorem lin_eq_one_iff {u : ↥Om8} : lin (u : GL ι8 (ZMod 2)) = 1 ↔ u = 1 := by
  constructor
  · intro h
    exact Subtype.ext (lin_injective (h.trans lin_one.symm))
  · intro h
    rw [h]
    exact lin_one

private noncomputable def omW (U₀ : Subgroup ↥Om8) : Submodule (ZMod 2) V8 :=
  Submodule.span (ZMod 2) {w : V8 | ∃ u ∈ U₀, ∃ v : V8, w = lin (u : GL ι8 (ZMod 2)) v - v}

private noncomputable def omC (U₀ : Subgroup ↥Om8) : Submodule (ZMod 2) V8 where
  carrier := {v : V8 | ∀ u ∈ U₀, lin (u : GL ι8 (ZMod 2)) v = v}
  add_mem' := by
    intro x y hx hy u hu
    rw [lin_add, hx u hu, hy u hu]
  zero_mem' := by
    intro u _
    exact lin_zero _
  smul_mem' := by
    intro a x hx u hu
    rw [lin_smul, hx u hu]

private noncomputable def omR (U₀ : Subgroup ↥Om8) : Submodule (ZMod 2) V8 :=
  omW U₀ ⊓ omC U₀

private theorem mem_omC {U₀ : Subgroup ↥Om8} {v : V8} :
    v ∈ omC U₀ ↔ ∀ u ∈ U₀, lin (u : GL ι8 (ZMod 2)) v = v := Iff.rfl

private theorem mem_omR {U₀ : Subgroup ↥Om8} {v : V8} :
    v ∈ omR U₀ ↔ v ∈ omW U₀ ∧ v ∈ omC U₀ := Submodule.mem_inf

private theorem gen_mem_omW {U₀ : Subgroup ↥Om8} {u : ↥Om8} (hu : u ∈ U₀) (v : V8) :
    lin (u : GL ι8 (ZMod 2)) v - v ∈ omW U₀ :=
  Submodule.subset_span ⟨u, hu, v, rfl⟩

private theorem omW_polar_omC (U₀ : Subgroup ↥Om8) {w : V8} (hw : w ∈ omW U₀)
    {c : V8} (hc : c ∈ omC U₀) : polar Q8 w c = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro x ⟨u, hu, v, rfl⟩
    have hc' : lin (u : GL ι8 (ZMod 2)) c = c := (mem_omC.mp hc) u hu
    calc polar Q8 (lin (u : GL ι8 (ZMod 2)) v - v) c
        = polar Q8 (lin (u : GL ι8 (ZMod 2)) v) c - polar Q8 v c := by
          rw [QuadraticMap.polar_sub_left]
      _ = polar Q8 (lin (u : GL ι8 (ZMod 2)) v) (lin (u : GL ι8 (ZMod 2)) c)
            - polar Q8 v c := by rw [hc']
      _ = polar Q8 v c - polar Q8 v c := by rw [map_polar_of_mem u]
      _ = 0 := sub_self _
  · exact QuadraticMap.polar_zero_left Q8 c
  · intro x y _ _ hx hy
    rw [QuadraticMap.polar_add_left, hx, hy, add_zero]
  · intro a x _ hx
    rw [QuadraticMap.polar_smul_left, hx, smul_zero]

private theorem omR_polar (U₀ : Subgroup ↥Om8) {x y : V8} (hx : x ∈ omR U₀)
    (hy : y ∈ omR U₀) : polar Q8 x y = 0 :=
  omW_polar_omC U₀ (mem_omR.mp hx).1 (mem_omR.mp hy).2

private noncomputable def omR0 (U₀ : Subgroup ↥Om8) : Submodule (ZMod 2) V8 where
  carrier := {x : V8 | x ∈ omR U₀ ∧ Q8 x = 0}
  add_mem' := by
    rintro x y ⟨hxR, hxQ⟩ ⟨hyR, hyQ⟩
    refine ⟨(omR U₀).add_mem hxR hyR, ?_⟩
    rw [QuadraticMap.map_add Q8 x y, hxQ, hyQ, omR_polar U₀ hxR hyR, add_zero, zero_add]
  zero_mem' := ⟨(omR U₀).zero_mem, QuadraticMap.map_zero Q8⟩
  smul_mem' := by
    rintro a x ⟨hxR, hxQ⟩
    refine ⟨(omR U₀).smul_mem a hxR, ?_⟩
    rw [QuadraticMap.map_smul, hxQ, smul_zero]

private theorem mem_omR0 {U₀ : Subgroup ↥Om8} {x : V8} :
    x ∈ omR0 U₀ ↔ x ∈ omR U₀ ∧ Q8 x = 0 := Iff.rfl

private theorem omW_ne_bot (U₀ : Subgroup ↥Om8) (hU₀ : U₀ ≠ ⊥) : omW U₀ ≠ ⊥ := by
  intro hbot
  apply hU₀
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  by_contra h1
  have hne : lin (u : GL ι8 (ZMod 2)) ≠ 1 := fun h => h1 ((lin_eq_one_iff (u := u)).mp h)
  obtain ⟨v, hv⟩ : ∃ v : V8, lin (u : GL ι8 (ZMod 2)) v ≠ v := by
    by_contra h
    push Not at h
    exact hne (LinearEquiv.ext h)
  have hmem : lin (u : GL ι8 (ZMod 2)) v - v ∈ omW U₀ := gen_mem_omW hu v
  rw [hbot] at hmem
  have hzero : lin (u : GL ι8 (ZMod 2)) v - v = 0 := by simpa using hmem
  exact hv (sub_eq_zero.mp hzero)

private noncomputable def omAct (U₀ : Subgroup ↥Om8) : U₀ →* (V8 ≃ₗ[ZMod 2] V8) :=
  (toLinEquiv ι8 (ZMod 2)).toMonoidHom.comp (Om8.subtype.comp U₀.subtype)

private theorem omAct_apply (U₀ : Subgroup ↥Om8) (u : U₀) (v : V8) :
    omAct U₀ u v = lin ((u : ↥Om8) : GL ι8 (ZMod 2)) v := rfl

private theorem map_mem_omC {U₀ E : Subgroup ↥Om8}
    (hE : E ≤ Subgroup.normalizer (U₀ : Set ↥Om8)) {e : ↥Om8} (he : e ∈ E)
    {c : V8} (hc : c ∈ omC U₀) : lin (e : GL ι8 (ZMod 2)) c ∈ omC U₀ := by
  intro u hu
  have hconj : ((e : ↥Om8)⁻¹ * u * e) ∈ U₀ := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem (hE he)) u).mp hu
    simpa using h
  have hfix : lin ((((e : ↥Om8)⁻¹ * u * e) : ↥Om8) : GL ι8 (ZMod 2)) c = c :=
    (mem_omC.mp hc) ((e : ↥Om8)⁻¹ * u * e) hconj
  have hcoe : (u : ↥Om8) * e = e * ((e : ↥Om8)⁻¹ * u * e) := by group
  have h1 : (u : GL ι8 (ZMod 2)) * (e : GL ι8 (ZMod 2))
      = (((e * ((e : ↥Om8)⁻¹ * u * e)) : ↥Om8) : GL ι8 (ZMod 2)) := by
    conv_lhs => rw [← Subgroup.coe_mul]
    exact congrArg Subtype.val hcoe
  calc lin (u : GL ι8 (ZMod 2)) (lin (e : GL ι8 (ZMod 2)) c)
      = lin ((u : GL ι8 (ZMod 2)) * (e : GL ι8 (ZMod 2))) c := (lin_mul_apply _ _ _).symm
    _ = lin (((e * ((e : ↥Om8)⁻¹ * u * e)) : ↥Om8) : GL ι8 (ZMod 2)) c := by rw [h1]
    _ = lin ((e : GL ι8 (ZMod 2)) * ((((e : ↥Om8)⁻¹ * u * e) : ↥Om8) : GL ι8 (ZMod 2))) c := by
        conv_lhs => rw [Subgroup.coe_mul]
    _ = lin (e : GL ι8 (ZMod 2)) (lin ((((e : ↥Om8)⁻¹ * u * e) : ↥Om8) : GL ι8 (ZMod 2)) c) :=
        lin_mul_apply _ _ _
    _ = lin (e : GL ι8 (ZMod 2)) c := by rw [hfix]

private theorem map_mem_omW_of_normalizes {U₀ E : Subgroup ↥Om8}
    (hE : E ≤ Subgroup.normalizer (U₀ : Set ↥Om8)) {e : ↥Om8} (he : e ∈ E)
    {x : V8} (hx : x ∈ omW U₀) : lin (e : GL ι8 (ZMod 2)) x ∈ omW U₀ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro x ⟨u, hu, v, rfl⟩
    have hconj : ((e : ↥Om8) * u * (e : ↥Om8)⁻¹) ∈ U₀ :=
      (Subgroup.mem_normalizer_iff.mp (hE he) u).mp hu
    have hcoe : (e : ↥Om8) * u = (e * u * e⁻¹) * e := by group
    have h1 : lin (e : GL ι8 (ZMod 2)) (lin (u : GL ι8 (ZMod 2)) v)
        = lin (((e * u * e⁻¹) : ↥Om8) : GL ι8 (ZMod 2))
            (lin (e : GL ι8 (ZMod 2)) v) := by
      have h2 : (e : GL ι8 (ZMod 2)) * (u : GL ι8 (ZMod 2))
          = (((e * u * e⁻¹) : ↥Om8) : GL ι8 (ZMod 2)) * (e : GL ι8 (ZMod 2)) := by
        conv_lhs => rw [← Subgroup.coe_mul]
        conv_rhs => rw [← Subgroup.coe_mul]
        exact congrArg Subtype.val hcoe
      rw [← lin_mul_apply (e : GL ι8 (ZMod 2)) (u : GL ι8 (ZMod 2)) v, h2, lin_mul_apply]
    rw [lin_sub, h1]
    exact gen_mem_omW hconj (lin (e : GL ι8 (ZMod 2)) v)
  · rw [lin_zero]
    exact (omW U₀).zero_mem
  · intro x y _ _ hx hy
    rw [lin_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [lin_smul]
    exact Submodule.smul_mem _ _ hx

private theorem lin_mem_omW {U₀ : Subgroup ↥Om8} {u : ↥Om8} (hu : u ∈ U₀) {v : V8}
    (hv : v ∈ omW U₀) : lin (u : GL ι8 (ZMod 2)) v ∈ omW U₀ :=
  map_mem_omW_of_normalizes (U₀ := U₀) (E := U₀) Subgroup.le_normalizer hu hv

private noncomputable def omWRep (U₀ : Subgroup ↥Om8) :
    U₀ →* (↥(omW U₀) ≃ₗ[ZMod 2] ↥(omW U₀)) :=
  invariantLinearRestriction (omAct U₀) (omW U₀)
    (fun u _ hx => lin_mem_omW (U₀ := U₀) u.2 hx)

private theorem omWRep_apply (U₀ : Subgroup ↥Om8) (u : U₀) (v : ↥(omW U₀)) :
    ((omWRep U₀ u) v : V8) = lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (v : V8) := by
  have h := invariant_linear_restriction_apply (omAct U₀) (omW U₀)
    (fun u _ hx => lin_mem_omW (U₀ := U₀) u.2 hx) u v
  exact h.trans (omAct_apply U₀ u (v : V8))

private theorem omR_ne_bot (U₀ : Subgroup ↥Om8) (hU₀ : U₀ ≠ ⊥) (hU₀2 : IsPGroup 2 ↥U₀) :
    omR U₀ ≠ ⊥ := by
  classical
  have hW : omW U₀ ≠ ⊥ := omW_ne_bot U₀ hU₀
  haveI : Nontrivial ↥(omW U₀) := Submodule.nontrivial_iff_ne_bot.mpr hW
  let act : MulAction U₀ ↥(omW U₀) :=
    { smul := fun u x => (omWRep U₀ u) x
      one_smul := fun x => by
        change (omWRep U₀ 1) x = x
        rw [map_one]
        rfl
      mul_smul := fun u v x => by
        change (omWRep U₀ (u * v)) x = (omWRep U₀ u) ((omWRep U₀ v) x)
        rw [map_mul]
        rfl }
  letI := act
  obtain ⟨w, hw0, hwfix⟩ := CFSG.Quasithin.H13.L827X.LBModule2.ch827_exists_fixed_ne_zero
    (W := ↥(omW U₀)) U₀ hU₀2 (fun u => by
      change (omWRep U₀ u) (0 : ↥(omW U₀)) = 0
      exact map_zero _)
  have hfixall : ∀ u : U₀, lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) = (w : V8) := by
    intro u
    have h := hwfix u
    change (omWRep U₀ u) w = w at h
    have h2 : ((omWRep U₀ u) w : V8) = (w : V8) := congrArg Subtype.val h
    rwa [omWRep_apply] at h2
  have hw0' : (w : V8) ≠ 0 := fun h => hw0 (Subtype.ext h)
  intro hbot
  have hmem : (w : V8) ∈ omR U₀ :=
    mem_omR.mpr ⟨w.2, mem_omC.mpr fun u hu => hfixall ⟨u, hu⟩⟩
  rw [hbot] at hmem
  exact hw0' (by simpa using hmem)

private theorem omR_eq_span (U₀ : Subgroup ↥Om8) (hRne : omR U₀ ≠ ⊥)
    (hR0 : ∀ x ∈ omR U₀, Q8 x = 0 → x = 0) :
    ∃ r : V8, r ≠ 0 ∧ omR U₀ = Submodule.span (ZMod 2) {r} ∧ Q8 r = 1 := by
  have hns : ∀ x ∈ omR U₀, x ≠ 0 → Q8 x = 1 := fun x hx hx0 =>
    Fin.eq_one_of_ne_zero (Q8 x) fun h => hx0 (hR0 x hx h)
  obtain ⟨r, hrR, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := omR U₀) hRne
  have hQr : Q8 r = 1 := hns r hrR hr0
  refine ⟨r, hr0, ?_, hQr⟩
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    · by_cases hxr : x = r
      · rw [hxr]
        exact Submodule.subset_span (Set.mem_singleton r)
      · exfalso
        have hxQ : Q8 x = 1 := hns x hx hx0
        have hsumR : x + r ∈ omR U₀ := (omR U₀).add_mem hx hrR
        have hsumQ : Q8 (x + r) = 0 := by
          rw [QuadraticMap.map_add Q8 x r, hxQ, hQr, omR_polar U₀ hx hrR, add_zero]
          exact CharTwo.add_self_eq_zero 1
        have hsum0 : x + r = 0 := hR0 _ hsumR hsumQ
        apply hxr
        have hxneg : x = -r := eq_neg_of_add_eq_zero_right (by rw [add_comm]; exact hsum0)
        rw [hxneg, neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide) r]
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hrR

private theorem omR0_ne_bot (U₀ : Subgroup ↥Om8) (hU₀ : U₀ ≠ ⊥) (hU₀2 : IsPGroup 2 ↥U₀) :
    omR0 U₀ ≠ ⊥ := by
  classical
  have hRne : omR U₀ ≠ ⊥ := omR_ne_bot U₀ hU₀ hU₀2
  intro hR0bot
  have hR0 : ∀ x ∈ omR U₀, Q8 x = 0 → x = 0 := by
    intro x hx hxQ
    have hmem : x ∈ omR0 U₀ := mem_omR0.mpr ⟨hx, hxQ⟩
    rw [hR0bot] at hmem
    simpa using hmem
  obtain ⟨r, hr0, hRspan, hQr⟩ := omR_eq_span U₀ hRne hR0
  by_cases hWR : omW U₀ = omR U₀
  ·
    apply hU₀
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hcomm : commSpace (lin (u : GL ι8 (ZMod 2))) ≤ omR U₀ := by
      rw [← hWR]
      intro x hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      exact gen_mem_omW hu v
    have heven := even_finrank_commSpace u
    have hle : Module.finrank (ZMod 2) ↥(commSpace (lin (u : GL ι8 (ZMod 2)))) ≤ 1 := by
      have h1 := Submodule.finrank_mono hcomm
      rwa [hRspan, finrank_span_singleton hr0] at h1
    obtain ⟨k, hk⟩ := heven
    have hzero : Module.finrank (ZMod 2) ↥(commSpace (lin (u : GL ι8 (ZMod 2)))) = 0 := by
      omega
    have hbot : commSpace (lin (u : GL ι8 (ZMod 2))) = ⊥ :=
      Submodule.finrank_eq_zero.mp hzero
    have hlin : lin (u : GL ι8 (ZMod 2)) = 1 := by
      ext v
      have hv : lin (u : GL ι8 (ZMod 2)) v - v ∈ commSpace (lin (u : GL ι8 (ZMod 2))) :=
        sub_mem_commSpace _ v
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
      rw [hv]
      rfl
    exact (lin_eq_one_iff (u := u)).mp hlin
  ·
    let R' : Submodule (ZMod 2) ↥(omW U₀) := Submodule.comap (omW U₀).subtype (omC U₀)
    have hR'mem : ∀ x : ↥(omW U₀), x ∈ R' ↔ (x : V8) ∈ omC U₀ := fun x => Submodule.mem_comap
    have hR'top : R' ≠ ⊤ := by
      intro htop
      apply hWR
      rw [omR]
      refine le_antisymm ?_ inf_le_left
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥(omW U₀)) ∈ R' := by rw [htop]; exact Submodule.mem_top
      exact ⟨hx, (hR'mem _).mp hx'⟩
    have hR'inv : ∀ u : U₀, ∀ x ∈ R', (omWRep U₀ u) x ∈ R' := by
      intro u x hx
      rw [hR'mem] at hx ⊢
      rw [omWRep_apply]
      exact map_mem_omC (U₀ := U₀) (E := U₀) Subgroup.le_normalizer u.2 hx
    let ρQ := invariantLinearQuotient (omWRep U₀) R' hR'inv
    let qact : MulAction U₀ (↥(omW U₀) ⧸ R') :=
      { smul := fun u q => ρQ u q
        one_smul := fun q => by
          change (ρQ 1) q = q
          rw [map_one]
          rfl
        mul_smul := fun u v q => by
          change (ρQ (u * v)) q = (ρQ u) ((ρQ v) q)
          rw [map_mul]
          rfl }
    letI := qact
    haveI : Finite (↥(omW U₀) ⧸ R') :=
      Finite.of_surjective (Submodule.mkQ R') (Submodule.mkQ_surjective R')
    haveI : Nontrivial (↥(omW U₀) ⧸ R') := Submodule.Quotient.nontrivial_iff.mpr hR'top
    obtain ⟨q, hq0, hqfix⟩ := CFSG.Quasithin.H13.L827X.LBModule2.ch827_exists_fixed_ne_zero
      (W := ↥(omW U₀) ⧸ R') U₀ hU₀2 (fun u => by
        change (ρQ u) (0 : ↥(omW U₀) ⧸ R') = 0
        exact map_zero _)
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective R' q
    have hwR' : w ∉ R' := by
      intro hw
      apply hq0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hw
    have hfixmod : ∀ u : U₀, (omWRep U₀ u) w - w ∈ R' := by
      intro u
      have h := hqfix u
      change (ρQ u) (Submodule.mkQ R' w) = Submodule.mkQ R' w at h
      rw [invariant_linear_quotient_apply] at h
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
      exact h
    have hfixall : ∀ u : U₀, lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) = (w : V8) := by
      intro u
      have hcW : lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8) ∈ omW U₀ :=
        (omW U₀).sub_mem (lin_mem_omW u.2 w.2) w.2
      have hcC : lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8) ∈ omC U₀ := by
        have h1 := (hR'mem _).mp (hfixmod u)
        have h2 : (((omWRep U₀ u) w - w : ↥(omW U₀)) : V8)
            = lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8) := by
          rw [Submodule.coe_sub, omWRep_apply]
        rwa [h2] at h1
      have hcR : lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8) ∈ omR U₀ :=
        mem_omR.mpr ⟨hcW, hcC⟩
      have hQc : Q8 (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8)) = 0 := by
        have hQy : Q8 (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8)) = Q8 (w : V8) :=
          map_Q_of_mem (u : ↥Om8) (w : V8)
        have hpol : polar Q8 (w : V8)
            (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8)) = 0 :=
          omW_polar_omC U₀ w.2 hcC
        have h1 : Q8 (w : V8)
            + Q8 (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8))
            = Q8 (w : V8) := by
          have h2 := QuadraticMap.map_add Q8 (w : V8)
            (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8))
          rw [hpol, add_zero] at h2
          rw [← h2,
            show (w : V8) + (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8))
              = lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) from by abel,
            hQy]
        have h3 : Q8 (w : V8)
            + Q8 (lin ((u : ↥Om8) : GL ι8 (ZMod 2)) (w : V8) - (w : V8))
            = Q8 (w : V8) + 0 := by rw [add_zero]; exact h1
        exact add_left_cancel h3
      exact sub_eq_zero.mp (hR0 _ hcR hQc)
    apply hwR'
    rw [hR'mem]
    intro u hu
    exact hfixall ⟨u, hu⟩

theorem omTSFact_holds : OmTSFact := by
  intro E U₀ hU₀2 hU₀ hE
  refine ⟨omR0 U₀, omR0_ne_bot U₀ hU₀ hU₀2, ?_, ?_⟩
  · intro x hx
    exact (mem_omR0.mp hx).2
  · intro e he x hx
    obtain ⟨hxR, hxQ⟩ := mem_omR0.mp hx
    refine mem_omR0.mpr ⟨⟨?_, ?_⟩, ?_⟩
    · exact map_mem_omW_of_normalizes (U₀ := U₀) (E := E) hE he (mem_omR.mp hxR).1
    · exact map_mem_omC (U₀ := U₀) (E := E) hE he (mem_omR.mp hxR).2
    · exact (map_Q_of_mem e x).trans hxQ

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
