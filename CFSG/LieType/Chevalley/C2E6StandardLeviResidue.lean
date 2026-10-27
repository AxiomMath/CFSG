module

public import CFSG.LieType.Chevalley.C2E6StandardBetaStar
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open scoped Pointwise

variable {J : Set (Fin 4)}

abbrev radicalOf
    (J : Set (Fin 4)) : Subgroup (nativeParabolic J) :=
  (stdRadical J).subgroupOf (nativeParabolic J)

instance
    (J : Set (Fin 4)) : (radicalOf J).Normal := stdRadical_normal J

@[expose] def leviToQuot
    (hJ : (2 : Fin 4) ∈ J) : stdLevi J →* nativeParabolic J ⧸ radicalOf J :=
  (QuotientGroup.mk' (radicalOf J)).comp (Subgroup.inclusion (stdLevi_le_nativeParabolic hJ))

theorem leviToQuot_apply
    (hJ : (2 : Fin 4) ∈ J) (l : stdLevi J) :
    leviToQuot hJ l = QuotientGroup.mk (Subgroup.inclusion (stdLevi_le_nativeParabolic hJ) l) :=
  rfl

theorem leviToQuot_bijective
    (hJ : (2 : Fin 4) ∈ J) : Function.Bijective (leviToQuot hJ) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro l hl
    rw [leviToQuot_apply, QuotientGroup.eq_one_iff] at hl
    have h1 : (l : ModGL Tag.E6 K) ∈ stdRadical J ⊓ stdLevi J := Subgroup.mem_inf.mpr ⟨hl, l.2⟩
    rw [stdRadical_inf_stdLevi] at h1
    exact Subtype.ext h1
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨q, l⟩, ⟨hq, hl, hpql⟩, -⟩ := existsUnique_stdRadical_mul_stdLevi hJ p.2
    refine ⟨⟨l, hl⟩, ?_⟩
    have hp : p = (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) *
        ⟨l, stdLevi_le_nativeParabolic hJ hl⟩ := Subtype.ext hpql
    rw [hp, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr
      (show (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) ∈ radicalOf J from hq),
      one_mul]
    rfl

@[expose] def leviProj
    (hJ : (2 : Fin 4) ∈ J) : nativeParabolic J →* stdLevi J :=
  (MulEquiv.ofBijective _ (leviToQuot_bijective hJ)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (radicalOf J))

theorem leviToQuot_leviProj
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    leviToQuot hJ (leviProj hJ p) = QuotientGroup.mk p :=
  (MulEquiv.ofBijective _ (leviToQuot_bijective hJ)).apply_symm_apply _

theorem leviProj_mul
    (hJ : (2 : Fin 4) ∈ J) {q l : ModGL Tag.E6 K} (hq : q ∈ stdRadical J)
    (hl : l ∈ stdLevi J) (hql : q * l ∈ nativeParabolic J) :
    leviProj hJ ⟨q * l, hql⟩ = ⟨l, hl⟩ := by
  apply (leviToQuot_bijective hJ).1
  rw [leviToQuot_leviProj, leviToQuot_apply]
  have hp : (⟨q * l, hql⟩ : nativeParabolic J) =
      (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) *
        ⟨l, stdLevi_le_nativeParabolic hJ hl⟩ := rfl
  rw [hp, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr
    (show (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) ∈ radicalOf J from hq),
    one_mul]
  rfl

theorem leviProj_of_mem
    (hJ : (2 : Fin 4) ∈ J) {l : ModGL Tag.E6 K} (hl : l ∈ stdLevi J)
    (hlP : l ∈ nativeParabolic J) : leviProj hJ ⟨l, hlP⟩ = ⟨l, hl⟩ := by
  have h := leviProj_mul hJ (one_mem _) hl (by rw [one_mul]; exact hlP)
  simp only [one_mul] at h
  exact h

theorem mul_inv_leviProj_mem
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    (p : ModGL Tag.E6 K) * ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K)⁻¹ ∈ stdRadical J := by
  set l := leviProj hJ p
  have hlP : (l : ModGL Tag.E6 K) ∈ nativeParabolic J := stdLevi_le_nativeParabolic hJ l.2
  have h1 : leviProj hJ (p * (⟨l, hlP⟩ : nativeParabolic J)⁻¹) = 1 := by
    rw [map_mul, map_inv, leviProj_of_mem hJ l.2 hlP]
    exact mul_inv_cancel l
  have h2 := leviToQuot_leviProj hJ (p * (⟨l, hlP⟩ : nativeParabolic J)⁻¹)
  rw [h1, map_one] at h2
  have h3 : p * (⟨l, hlP⟩ : nativeParabolic J)⁻¹ ∈ radicalOf J :=
    (QuotientGroup.eq_one_iff _).mp h2.symm
  exact h3

theorem leviProj_eq_one_iff
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    leviProj hJ p = 1 ↔ (p : ModGL Tag.E6 K) ∈ stdRadical J := by
  constructor
  · intro h
    have := mul_inv_leviProj_mem hJ p
    rwa [h, OneMemClass.coe_one, inv_one, mul_one] at this
  · intro hp
    have e : p = ⟨(p : ModGL Tag.E6 K) * 1, by rw [mul_one]; exact p.2⟩ :=
      Subtype.ext (mul_one _).symm
    rw [e, leviProj_mul hJ hp (one_mem _)]
    rfl

theorem leviProj_mem_stdLeviBorel
    (hJ : (2 : Fin 4) ∈ J) {b : nativeParabolic J}
    (hb : (b : ModGL Tag.E6 K) ∈ stdBorel) :
    ((leviProj hJ b : stdLevi J) : ModGL Tag.E6 K) ∈ stdLeviBorel J := by
  obtain ⟨⟨q, c⟩, ⟨hq, hc, hbqc⟩, -⟩ := existsUnique_stdRadical_mul_stdBorel J hb
  have e : b = ⟨q * c, hbqc ▸ b.2⟩ := Subtype.ext hbqc
  rw [e, leviProj_mul hJ hq (stdLeviBorel_le_stdLevi hJ hc)]
  exact hc

theorem leviProj_surjective
    (hJ : (2 : Fin 4) ∈ J) : Function.Surjective (leviProj hJ) :=
  fun l => ⟨⟨l, stdLevi_le_nativeParabolic hJ l.2⟩, leviProj_of_mem hJ l.2 _⟩

theorem mem_stdBorel_iff
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    (p : ModGL Tag.E6 K) ∈ stdBorel ↔
      ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) ∈ stdLeviBorel J := by
  refine ⟨leviProj_mem_stdLeviBorel hJ, fun h => ?_⟩
  have := mul_mem (stdRadical_le_stdBorel J (mul_inv_leviProj_mem hJ p))
    (stdLeviBorel_le_stdBorel J h)
  rwa [inv_mul_cancel_right] at this

abbrev ParabolicCosets
    (J : Set (Fin 4)) : Type :=
  nativeParabolic J ⧸ stdBorel.subgroupOf (nativeParabolic J)

abbrev LeviCosets
    (J : Set (Fin 4)) : Type :=
  stdLevi J ⧸ (stdLeviBorel J).subgroupOf (stdLevi J)

@[expose] def residueMap
    (hJ : (2 : Fin 4) ∈ J) : ParabolicCosets J → LeviCosets J :=
  Quotient.lift (fun p => (QuotientGroup.mk (leviProj hJ p) : LeviCosets J)) fun x y hxy => by
    have h : x⁻¹ * y ∈ stdBorel.subgroupOf (nativeParabolic J) :=
      QuotientGroup.leftRel_apply.mp hxy
    refine QuotientGroup.eq.mpr ?_
    rw [← map_inv, ← map_mul]
    exact leviProj_mem_stdLeviBorel hJ h

theorem residueMap_mk
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    residueMap hJ (QuotientGroup.mk p) = QuotientGroup.mk (leviProj hJ p) :=
  rfl

theorem residueMap_mk_mul
    (hJ : (2 : Fin 4) ∈ J) {q l : ModGL Tag.E6 K} (hq : q ∈ stdRadical J)
    (hl : l ∈ stdLevi J) (hql : q * l ∈ nativeParabolic J) :
    residueMap hJ (QuotientGroup.mk ⟨q * l, hql⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
  rw [residueMap_mk, leviProj_mul hJ hq hl hql]

theorem residueMap_bijective
    (hJ : (2 : Fin 4) ∈ J) : Function.Bijective (residueMap hJ) := by
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [residueMap_mk, residueMap_mk, QuotientGroup.eq, ← map_inv, ← map_mul] at hxy
    exact QuotientGroup.eq.mpr ((mem_stdBorel_iff hJ (x⁻¹ * y)).mpr hxy)
  · intro y
    induction y using QuotientGroup.induction_on with | H l => ?_
    exact ⟨QuotientGroup.mk ⟨l, stdLevi_le_nativeParabolic hJ l.2⟩, by
      rw [residueMap_mk, leviProj_of_mem hJ l.2]⟩

theorem residueMap_mk_mul_left
    (hJ : (2 : Fin 4) ∈ J) (p x : nativeParabolic J) :
    residueMap hJ (QuotientGroup.mk (p * x)) =
      QuotientGroup.mk (leviProj hJ p * leviProj hJ x) := by
  rw [residueMap_mk, map_mul]

@[expose] def leviParabolic
    (J I : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  Subgroup.closure ((stdLeviBorel J : Set (ModGL Tag.E6 K)) ∪ nativeRep '' I)

theorem leviParabolic_le_stdLevi
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J) :
    leviParabolic J I ≤ stdLevi J := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | ⟨i, hi, rfl⟩)
  · exact stdLeviBorel_le_stdLevi hJ hx
  · exact nativeRep_mem_stdLevi (hIJ hi)

theorem leviParabolic_le_nativeParabolic
    (J : Set (Fin 4)) (I : Set (Fin 4)) :
    leviParabolic J I ≤ nativeParabolic I := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | ⟨i, hi, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl (stdLeviBorel_le_stdBorel J hx))
  · exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)

theorem mem_nativeParabolic_iff
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J)
    (p : nativeParabolic J) :
    (p : ModGL Tag.E6 K) ∈ nativeParabolic I ↔
      ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I := by
  constructor
  · intro hp
    let S : Subgroup (nativeParabolic J) :=
      (leviParabolic J I).comap ((stdLevi J).subtype.comp (leviProj hJ))
    have hle : nativeParabolic I ≤ S.map (nativeParabolic J).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | ⟨i, hi, rfl⟩)
      · refine ⟨⟨x, stdBorel_le_nativeParabolic J hx⟩, ?_, rfl⟩
        exact Subgroup.subset_closure (Or.inl (leviProj_mem_stdLeviBorel hJ hx))
      · refine ⟨⟨nativeRep i, nativeRep_mem_nativeParabolic (hIJ hi)⟩, ?_, rfl⟩
        change ((leviProj hJ _ : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I
        rw [leviProj_of_mem hJ (nativeRep_mem_stdLevi (hIJ hi))]
        exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
    obtain ⟨p', hp', hpp'⟩ := hle hp
    rw [show p = p' from Subtype.ext hpp'.symm]
    exact hp'
  · intro h
    have := mul_mem ((stdRadical_le_stdBorel J).trans (stdBorel_le_nativeParabolic I)
      (mul_inv_leviProj_mem hJ p)) (leviParabolic_le_nativeParabolic J I h)
    rwa [inv_mul_cancel_right] at this

theorem adjacent_iff
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J)
    (x y : nativeParabolic J) :
    ((x⁻¹ * y : nativeParabolic J) : ModGL Tag.E6 K) ∈ nativeParabolic I ↔
      (((leviProj hJ x)⁻¹ * leviProj hJ y : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I := by
  rw [mem_nativeParabolic_iff hJ hIJ, map_mul, map_inv]

theorem image_residueMap_subresidue
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J) :
    residueMap hJ '' {x | ∃ p : nativeParabolic J, (p : ModGL Tag.E6 K) ∈ nativeParabolic I ∧
        x = QuotientGroup.mk p} =
      {y | ∃ l : stdLevi J, (l : ModGL Tag.E6 K) ∈ leviParabolic J I ∧ y = QuotientGroup.mk l} := by
  ext y
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨leviProj hJ p, (mem_nativeParabolic_iff hJ hIJ p).mp hp, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨QuotientGroup.mk ⟨l, stdLevi_le_nativeParabolic hJ l.2⟩,
      ⟨⟨l, stdLevi_le_nativeParabolic hJ l.2⟩, leviParabolic_le_nativeParabolic J I hl, rfl⟩, ?_⟩
    rw [residueMap_mk, leviProj_of_mem hJ l.2]

theorem stdLevi_eq_closure
    (hJ : (2 : Fin 4) ∈ J) :
    stdLevi J = Subgroup.closure ((stdTorus : Set (ModGL Tag.E6 K)) ∪ stdLeviUnipotent J ∪
      nativeRep '' J) := by
  refine le_antisymm (fun l hl => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hlP := stdLevi_le_nativeParabolic hJ hl
    have h := (mem_nativeParabolic_iff hJ subset_rfl ⟨l, hlP⟩).mp hlP
    rw [leviProj_of_mem hJ hl] at h
    refine (Subgroup.closure_le _).2 ?_ h
    rintro x (hx | ⟨i, hi, rfl⟩)
    · refine (sup_le ?_ ?_ : stdLeviBorel J ≤ _) hx
      · exact fun y hy => Subgroup.subset_closure (Or.inl (Or.inl hy))
      · exact fun y hy => Subgroup.subset_closure (Or.inl (Or.inr hy))
    · exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
  · rintro x ((hx | hx) | ⟨i, hi, rfl⟩)
    · exact stdLeviBorel_le_stdLevi hJ (Subgroup.mem_sup_left hx)
    · exact stdLeviBorel_le_stdLevi hJ (Subgroup.mem_sup_right hx)
    · exact nativeRep_mem_stdLevi hi

theorem leviProj_betaGL
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    ((leviProj hJ ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ : stdLevi J) : ModGL Tag.E6 K) =
      betaGL ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) := by
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hpql⟩, -⟩ := existsUnique_stdRadical_mul_stdLevi hJ p.2
  have hβp : betaGL (p : ModGL Tag.E6 K) = betaGL q * betaGL l := by
    rw [hpql, map_mul]
  have e : (⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ : nativeParabolic J) =
      ⟨betaGL q * betaGL l, hβp ▸ betaGL_mem_nativeParabolic p.2⟩ := Subtype.ext hβp
  have e' : p = ⟨q * l, hpql ▸ p.2⟩ := Subtype.ext hpql
  rw [e, leviProj_mul hJ (betaGL_mem_stdRadical hq) (betaGL_mem_stdLevi hl), e',
    leviProj_mul hJ hq hl]

theorem residueMap_betaGL
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    residueMap hJ (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) =
      QuotientGroup.mk ⟨betaGL ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K),
        betaGL_mem_stdLevi (leviProj hJ p).2⟩ := by
  rw [residueMap_mk]
  congr 1
  exact Subtype.ext (leviProj_betaGL hJ p)

theorem stdRadical_normal_stdBorel
    (J : Set (Fin 4)) :
    ((stdRadical J).subgroupOf stdBorel).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := (stdRadical_normal J).conj_mem ⟨n, stdBorel_le_nativeParabolic J n.2⟩ hn
    ⟨g, stdBorel_le_nativeParabolic J g.2⟩
  exact h

theorem standard_parabolic_Levi_residue_quotients
    (J : Set (Fin 4)) (hJ : (2 : Fin 4) ∈ J) :
    ((stdRadical J).subgroupOf (nativeParabolic J)).Normal ∧
    stdRadical J ≤ nativeParabolic J ∧ stdLevi J ≤ nativeParabolic J ∧
    stdRadical J ⊓ stdLevi J = ⊥ ∧
    (∀ g ∈ nativeParabolic J, ∃! ql : ModGL Tag.E6 K × ModGL Tag.E6 K,
      ql.1 ∈ stdRadical J ∧ ql.2 ∈ stdLevi J ∧ g = ql.1 * ql.2) ∧
    stdRadical J ≤ stdBorel ∧ stdLeviBorel J ≤ stdBorel ∧
    ((stdRadical J).subgroupOf stdBorel).Normal ∧
    (∀ b ∈ stdBorel, ∃! qc : ModGL Tag.E6 K × ModGL Tag.E6 K,
      qc.1 ∈ stdRadical J ∧ qc.2 ∈ stdLeviBorel J ∧ b = qc.1 * qc.2) ∧
    (stdLeviBorel J : Set (ModGL Tag.E6 K)) =
      (stdTorus : Set (ModGL Tag.E6 K)) * (stdLeviUnipotent J : Set (ModGL Tag.E6 K)) ∧
    stdLevi J ⊓ stdBorel = stdLeviBorel J ∧
    stdLevi J = Subgroup.closure ((stdTorus : Set (ModGL Tag.E6 K)) ∪ stdLeviUnipotent J ∪
      nativeRep '' J) ∧
    Function.Surjective (leviProj hJ) ∧
    (∀ p : nativeParabolic J, leviProj hJ p = 1 ↔ (p : ModGL Tag.E6 K) ∈ stdRadical J) ∧
    (∀ q l : ModGL Tag.E6 K, q ∈ stdRadical J → ∀ (hl : l ∈ stdLevi J)
      (hql : q * l ∈ nativeParabolic J),
      leviProj hJ ⟨q * l, hql⟩ = ⟨l, hl⟩ ∧
        residueMap hJ (QuotientGroup.mk ⟨q * l, hql⟩) = QuotientGroup.mk ⟨l, hl⟩) ∧
    Function.Bijective (residueMap hJ) ∧
    (∀ p x : nativeParabolic J, residueMap hJ (QuotientGroup.mk (p * x)) =
      QuotientGroup.mk (leviProj hJ p * leviProj hJ x)) ∧
    (∀ I ⊆ J, ∀ x y : nativeParabolic J,
      ((x⁻¹ * y : nativeParabolic J) : ModGL Tag.E6 K) ∈ nativeParabolic I ↔
        (((leviProj hJ x)⁻¹ * leviProj hJ y : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I) ∧
    (∀ I ⊆ J, residueMap hJ '' {x | ∃ p : nativeParabolic J,
        (p : ModGL Tag.E6 K) ∈ nativeParabolic I ∧ x = QuotientGroup.mk p} =
      {y | ∃ l : stdLevi J, (l : ModGL Tag.E6 K) ∈ leviParabolic J I ∧ y = QuotientGroup.mk l}) ∧
    (stdRadical J).map betaGL = stdRadical J ∧ (stdLevi J).map betaGL = stdLevi J ∧
    (stdLeviBorel J).map betaGL = stdLeviBorel J ∧
    (stdLeviUnipotent J).map betaGL = stdLeviUnipotent J ∧
    stdTorus.map betaGL = stdTorus ∧ stdBorel.map betaGL = stdBorel ∧
    (nativeParabolic J).map betaGL = nativeParabolic J ∧
    (∀ p : nativeParabolic J,
      ((leviProj hJ ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ : stdLevi J) : ModGL Tag.E6 K) =
        betaGL ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) ∧
      residueMap hJ (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) =
        QuotientGroup.mk ⟨betaGL ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K),
          betaGL_mem_stdLevi (leviProj hJ p).2⟩) :=
  ⟨stdRadical_normal J, stdRadical_le_nativeParabolic J, stdLevi_le_nativeParabolic hJ,
    stdRadical_inf_stdLevi J, fun _ hg => existsUnique_stdRadical_mul_stdLevi hJ hg,
    stdRadical_le_stdBorel J, stdLeviBorel_le_stdBorel J, stdRadical_normal_stdBorel J,
    fun _ hb => existsUnique_stdRadical_mul_stdBorel J hb, coe_stdLeviBorel J,
    stdLevi_inf_stdBorel hJ, stdLevi_eq_closure hJ, leviProj_surjective hJ,
    leviProj_eq_one_iff hJ,
    fun _ _ hq hl hql => ⟨leviProj_mul hJ hq hl hql, residueMap_mk_mul hJ hq hl hql⟩,
    residueMap_bijective hJ, residueMap_mk_mul_left hJ, fun _ hIJ => adjacent_iff hJ hIJ,
    fun _ hIJ => image_residueMap_subresidue hJ hIJ, map_betaGL_stdRadical J,
    map_betaGL_stdLevi J, map_betaGL_stdLeviBorel J, map_betaGL_stdLeviUnipotent J,
    map_betaGL_stdTorus, map_betaGL_stdBorel, map_betaGL_nativeParabolic J,
    fun p => ⟨leviProj_betaGL hJ p, residueMap_betaGL hJ p⟩⟩

end CFSG.LieType.Chevalley.C2E6Std
