module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem isElemAb2_map_mulEquiv {H : Type} [Group H] (f : H ≃* H) {U : Subgroup H} {k : ℕ}
    (h : IsElemAb2 U k) : IsElemAb2 (U.map f.toMonoidHom) k := by
  haveI : IsMulCommutative U := h.1.1
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h.1.2 u hu, map_one]
  · rw [Nat.card_congr (U.equivMapOfInjective f.toMonoidHom f.injective).toEquiv.symm, h.2]

private lemma map_mulEquiv_symm_map {H : Type} [Group H] (c : MulAut H) (U : Subgroup H) :
    (U.map c.symm.toMonoidHom).map c.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact MulEquiv.apply_symm_apply c x
  rw [h, Subgroup.map_id]

private lemma map_mulEquiv_map_symm {H : Type} [Group H] (c : MulAut H) (U : Subgroup H) :
    (U.map c.toMonoidHom).map c.symm.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id H := by
    ext x
    exact MulEquiv.symm_apply_apply c x
  rw [h, Subgroup.map_id]

private lemma map_mulEquiv_injective {H : Type} [Group H] (c : MulAut H) :
    Function.Injective (fun U : Subgroup H => U.map c.toMonoidHom) := by
  intro U W h
  have h' := congrArg (fun X : Subgroup H => X.map c.symm.toMonoidHom) h
  rwa [map_mulEquiv_map_symm, map_mulEquiv_map_symm] at h'

private lemma normal_subgroupOf_map_mulEquiv {H : Type} [Group H] (c : MulAut H)
    {P K : Subgroup H} (hKP : K ≤ P) (h : (K.subgroupOf P).Normal) :
    ((K.map c.toMonoidHom).subgroupOf (P.map c.toMonoidHom)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (f := c.toMonoidHom) hKP)]
  intro v p hv hp
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
  refine Subgroup.mem_map.mpr ⟨p' * v' * p'⁻¹,
    (Subgroup.normal_subgroupOf_iff hKP).mp h v' p' hv' hp', ?_⟩
  simp only [map_mul, map_inv]

theorem ff_exists_outer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6) :
    ∃ ξ : ProjSim Q, ¬ SimInGStar ξ := by
  have h6 : 0 < Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  obtain ⟨σ, hσ⟩ := (exists_isSimilitude_neg_one_iff hQ).mpr (by rw [hdim]; decide)
  let γ : simGroup Q := ⟨σ, ⟨-1, hσ⟩⟩
  refine ⟨QuotientGroup.mk γ, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  rw [projOrthToProjSim_toProj] at hy
  have hmem : (orthToSim Q t)⁻¹ * γ ∈ piSim Q := QuotientGroup.eq.mp hy
  have hsub : γ ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q) := by
    rcases mem_piSim_iff.mp hmem with h | h
    · rw [← inv_mul_eq_one.mp h]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using t.2)
    · rw [eq_mul_of_inv_mul_eq h]
      exact Subgroup.mem_subgroupOf.mpr (by
        simp only [Subgroup.coe_mul, coe_orthToSim]
        exact mul_mem t.2 (piOrth Q).2)
  exact (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)
    ((aux_mem_subgroupOf_iff hQ h6 (show IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) (-1) from hσ)).mp
      hsub)

theorem ff_star_exists_second (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1) :
    ∃ U : Subgroup ↥(omegaProj hQ), U ≤ ffP1 hQ fr ∧ IsElemAb2 U 4 ∧ U ≠ ffB1 hQ fr ∧
      ∃ y : ProjSim Q, U = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
  haveI : Finite (↥(omegaProj hQ)) := Nat.finite_of_card_ne_zero
    (by rw [ff_natCard_omegaProj_six_minus hQ hdim hsgn]; norm_num)
  obtain ⟨ξ, hξ⟩ := ff_exists_outer hQ hdim
  let α : MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ h2 ξ
  let U₁ : Subgroup ↥(omegaProj hQ) := (ffB1 hQ fr).map α.toMonoidHom
  have hU₁e : IsElemAb2 U₁ 4 := isElemAb2_map_mulEquiv α (ffB1_elemAb2 hQ hdim hsgn fr)
  have hU₁p : IsPGroup 2 U₁ := IsPGroup.of_card (p := 2) (n := 4) hU₁e.2
  obtain ⟨P', hP'syl, hU₁P'⟩ := exists_isSylow2Of_ge hU₁p (le_top : U₁ ≤ ⊤)
  obtain ⟨a, -, hconj⟩ := IsSylow2Of.exists_conj_mem (ffP1_sylow hQ hdim hsgn fr) hP'syl
  let U : Subgroup ↥(omegaProj hQ) := U₁.map (MulAut.conj a⁻¹).toMonoidHom
  have hUle : U ≤ ffP1 hQ fr := by
    intro u hu
    obtain ⟨u₁, hu₁, rfl⟩ := Subgroup.mem_map.mp hu
    have h1 := (hconj u₁).mp (hU₁P' hu₁)
    have hc : (MulAut.conj a⁻¹).toMonoidHom u₁ = a⁻¹ * u₁ * a := by
      change MulAut.conj a⁻¹ u₁ = a⁻¹ * u₁ * a
      rw [MulAut.conj_apply]
      group
    rwa [hc]
  have hUe : IsElemAb2 U 4 := isElemAb2_map_mulEquiv (MulAut.conj a⁻¹) hU₁e
  let y : ProjSim Q := projOrthToProjSim Q (↑(a⁻¹) : ProjOrth Q) * ξ
  have hUy : U = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
    have hcomp : ((MulAut.conj a⁻¹).toMonoidHom.comp α.toMonoidHom) =
        (ffSimOmegaAct hQ h2 y).toMonoidHom := by
      have hy : ffSimOmegaAct hQ h2 y = MulAut.conj a⁻¹ * α := by
        rw [show y = projOrthToProjSim Q (↑(a⁻¹) : ProjOrth Q) * ξ from rfl, map_mul,
          ffSimOmegaAct_projOrthToProjSim, MulAut.conjNormal_val]
      rw [hy]
      ext x
      rfl
    dsimp only [U, U₁]
    rw [Subgroup.map_map, hcomp]
  have hUne : U ≠ ffB1 hQ fr := by
    intro hUeq
    have hmapEq : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffB1 hQ fr := by
      rw [← hUy, hUeq]
    have hyG : SimInGStar y := ff_star_normalizes_simInGStar hQ h2 fr hmapEq
    refine hξ ?_
    have hxi : ξ = projOrthToProjSim Q (↑a : ProjOrth Q) * y := by
      rw [show y = projOrthToProjSim Q (↑(a⁻¹) : ProjOrth Q) * ξ from rfl]
      rw [← mul_assoc, ← map_mul]
      simp
    rw [hxi]
    obtain ⟨y', hy'⟩ := hyG
    exact ⟨(↑a : ProjOrth Q) * y', by rw [map_mul, hy']⟩
  exact ⟨U, hUle, hUe, hUne, y, hUy⟩

theorem ff_star_sylow_E16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1)
    {P : Subgroup ↥(omegaProj hQ)} (hP : IsSylow2Of P (⊤ : Subgroup ↥(omegaProj hQ))) :
    ∃ B₁ B₂ : Subgroup ↥(omegaProj hQ), B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧ IsNormalE16In P B₂ ∧
      (∀ B : Subgroup ↥(omegaProj hQ), B ≤ P → IsElemAb2 B 4 → B = B₁ ∨ B = B₂) ∧
      (∃ y : ProjSim Q, B₁ = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom) ∧
      (∃ y : ProjSim Q, B₂ = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom) := by
  haveI : Finite (↥(omegaProj hQ)) := Nat.finite_of_card_ne_zero
    (by rw [ff_natCard_omegaProj_six_minus hQ hdim hsgn]; norm_num)
  obtain ⟨U₂, hU₂le, hU₂e, hU₂ne, y₂, hU₂y⟩ := ff_star_exists_second hQ hdim hsgn h2 fr
  obtain ⟨a, -, hconj⟩ := IsSylow2Of.exists_conj_mem (ffP1_sylow hQ hdim hsgn fr) hP
  let c : MulAut ↥(omegaProj hQ) := MulAut.conj a
  have hP_eq : P = (ffP1 hQ fr).map c.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨a⁻¹ * x * a, (hconj x).mp hx, ?_⟩
      have hcx : c.toMonoidHom (a⁻¹ * x * a) = x := by
        change MulAut.conj a (a⁻¹ * x * a) = x
        rw [MulAut.conj_apply]
        group
      exact hcx
    · rintro ⟨v, hv, rfl⟩
      refine (hconj (c.toMonoidHom v)).mpr ?_
      have hcv : c.toMonoidHom v = a * v * a⁻¹ := by
        change MulAut.conj a v = a * v * a⁻¹
        rw [MulAut.conj_apply]
      rw [hcv]
      have hv' : a⁻¹ * (a * v * a⁻¹) * a = v := by group
      rw [hv']
      exact hv
  have hU₂norm : (U₂.subgroupOf (ffP1 hQ fr)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hU₂le]
    intro v p hv hp
    have hWle : U₂.map (MulAut.conj p).toMonoidHom ≤ ffP1 hQ fr := by
      rintro w ⟨u, hu, rfl⟩
      have hm : p * u * p⁻¹ ∈ ffP1 hQ fr :=
        (ffP1 hQ fr).mul_mem ((ffP1 hQ fr).mul_mem hp (hU₂le hu))
          ((ffP1 hQ fr).inv_mem hp)
      have hc : (MulAut.conj p).toMonoidHom u = p * u * p⁻¹ := by
        change MulAut.conj p u = p * u * p⁻¹
        rw [MulAut.conj_apply]
      rwa [hc]
    have hconjU : U₂.map (MulAut.conj p).toMonoidHom = U₂ := by
      by_cases hB : U₂.map (MulAut.conj p).toMonoidHom = ffB1 hQ fr
      · exfalso
        have hsub : U₂ ≤ ffB1 hQ fr := by
          intro u hu
          have hmem : (MulAut.conj p) u ∈ ffB1 hQ fr := by
            rw [← hB]
            exact Subgroup.mem_map_of_mem (MulAut.conj p).toMonoidHom hu
          have h2' := (Subgroup.normal_subgroupOf_iff (ffB1_le_ffP1 hQ fr)).mp
            (ffB1_normalE16 hQ hdim hsgn fr).2.2 ((MulAut.conj p) u) p⁻¹ hmem
            ((ffP1 hQ fr).inv_mem hp)
          rw [MulAut.conj_apply] at h2'
          simp only [inv_inv] at h2'
          have heq : p⁻¹ * (p * u * p⁻¹) * p = u := by group
          rwa [heq] at h2'
        have hcard : Nat.card ↥(ffB1 hQ fr) ≤ Nat.card ↥U₂ := by
          rw [ffB1_card hQ hdim hsgn fr, hU₂e.2]
          norm_num
        exact hU₂ne (Subgroup.eq_of_le_of_card_ge hsub hcard)
      · exact (ffP1_E16_unique hQ hdim hsgn fr hU₂le hU₂e hWle
          (isElemAb2_map_mulEquiv (MulAut.conj p) hU₂e) hU₂ne hB).symm
    have hmem : (MulAut.conj p) v ∈ U₂ := by
      have hmem' : (MulAut.conj p) v ∈ U₂.map (MulAut.conj p).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj p).toMonoidHom hv
      rwa [hconjU] at hmem'
    have hc : (MulAut.conj p) v = p * v * p⁻¹ := by
      rw [MulAut.conj_apply]
    simpa only [hc] using hmem
  let B₁ : Subgroup ↥(omegaProj hQ) := (ffB1 hQ fr).map c.toMonoidHom
  let B₂ : Subgroup ↥(omegaProj hQ) := U₂.map c.toMonoidHom
  have hB₁le : B₁ ≤ P := by
    rw [hP_eq]
    exact Subgroup.map_mono (ffB1_le_ffP1 hQ fr)
  have hB₂le : B₂ ≤ P := by
    rw [hP_eq]
    exact Subgroup.map_mono hU₂le
  have hB₁e : IsElemAb2 B₁ 4 := isElemAb2_map_mulEquiv c (ffB1_elemAb2 hQ hdim hsgn fr)
  have hB₂e : IsElemAb2 B₂ 4 := isElemAb2_map_mulEquiv c hU₂e
  have hB₁norm : (B₁.subgroupOf P).Normal := by
    rw [hP_eq]
    exact normal_subgroupOf_map_mulEquiv c (ffB1_le_ffP1 hQ fr)
      (ffB1_normalE16 hQ hdim hsgn fr).2.2
  have hB₂norm : (B₂.subgroupOf P).Normal := by
    rw [hP_eq]
    exact normal_subgroupOf_map_mulEquiv c hU₂le hU₂norm
  have hBne : B₁ ≠ B₂ := by
    intro h
    apply hU₂ne
    exact (map_mulEquiv_injective c (by dsimp only [B₁, B₂] at h; exact h)).symm
  have hclass : ∀ B : Subgroup ↥(omegaProj hQ), B ≤ P → IsElemAb2 B 4 →
      B = B₁ ∨ B = B₂ := by
    intro B hBP hBe
    let B' : Subgroup ↥(omegaProj hQ) := B.map c.symm.toMonoidHom
    have hB'le : B' ≤ ffP1 hQ fr := by
      intro x hx
      obtain ⟨b, hb, hb_eq⟩ := Subgroup.mem_map.mp hx
      have hbP : b ∈ P := hBP hb
      rw [hP_eq] at hbP
      obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hbP
      have hpb : c.symm.toMonoidHom b = p := by
        rw [← hp_eq]
        exact MulEquiv.symm_apply_apply c p
      rw [← hb_eq, hpb]
      exact hp
    have hB'e : IsElemAb2 B' 4 := isElemAb2_map_mulEquiv c.symm hBe
    by_cases hB' : B' = ffB1 hQ fr
    · left
      have h1 : B'.map c.toMonoidHom = B := by
        dsimp only [B']
        exact map_mulEquiv_symm_map c B
      rw [← h1, hB']
    · right
      have h1 : B'.map c.toMonoidHom = B := by
        dsimp only [B']
        exact map_mulEquiv_symm_map c B
      have h2 : B' = U₂ := ffP1_E16_unique hQ hdim hsgn fr hB'le hB'e hU₂le hU₂e hB' hU₂ne
      rw [← h1, h2]
  have hc : c = ffSimOmegaAct hQ h2 (projOrthToProjSim Q (↑a : ProjOrth Q)) := by
    dsimp only [c]
    rw [← MulAut.conjNormal_val, ffSimOmegaAct_projOrthToProjSim]
  have hB₁conj : ∃ y : ProjSim Q,
      B₁ = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
    refine ⟨projOrthToProjSim Q (↑a : ProjOrth Q), ?_⟩
    dsimp only [B₁]
    rw [hc]
  have hB₂conj : ∃ y : ProjSim Q,
      B₂ = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
    refine ⟨projOrthToProjSim Q (↑a : ProjOrth Q) * y₂, ?_⟩
    have hm : ffSimOmegaAct hQ h2 (projOrthToProjSim Q (↑a : ProjOrth Q) * y₂) =
        c * ffSimOmegaAct hQ h2 y₂ := by
      rw [map_mul, ← hc]
    have hcomp : c.toMonoidHom.comp (ffSimOmegaAct hQ h2 y₂).toMonoidHom =
        (ffSimOmegaAct hQ h2 (projOrthToProjSim Q (↑a : ProjOrth Q) * y₂)).toMonoidHom := by
      rw [hm]
      ext x
      rfl
    dsimp only [B₂]
    rw [hU₂y, Subgroup.map_map, hcomp]
  exact ⟨B₁, B₂, hBne, ⟨hB₁le, hB₁e, hB₁norm⟩, ⟨hB₂le, hB₂e, hB₂norm⟩, hclass, hB₁conj,
    hB₂conj⟩

theorem ff_star_E16_conj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1)
    {U : Subgroup ↥(omegaProj hQ)} (hE : IsElemAb2 U 4) :
    ∃ y : ProjSim Q, U = (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
  haveI : Finite (↥(omegaProj hQ)) := Nat.finite_of_card_ne_zero
    (by rw [ff_natCard_omegaProj_six_minus hQ hdim hsgn]; norm_num)
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (p := 2) (n := 4) hE.2
  obtain ⟨P, hPsyl, hUP⟩ := exists_isSylow2Of_ge hU2 (le_top : U ≤ ⊤)
  obtain ⟨B₁, B₂, -, -, -, hclass, hconj₁, hconj₂⟩ :=
    ff_star_sylow_E16 hQ hdim hsgn h2 fr hPsyl
  rcases hclass U hUP hE with h | h
  · obtain ⟨y, hy⟩ := hconj₁
    exact ⟨y, by rw [h, hy]⟩
  · obtain ⟨y, hy⟩ := hconj₂
    exact ⟨y, by rw [h, hy]⟩

end CFSG.OddStandard.SmallF3.Omega
