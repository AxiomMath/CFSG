module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BWeights
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {φ : (Fin 6 → ZMod 2) → G} {A H : Subgroup G}

private theorem card_GL_six :
    Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) = 20158709760 := by
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod 6]
  simp [Fin.prod_univ_succ]

theorem IsPerm6.card_mulAut (h : IsPerm6 φ A H) : Nat.card (MulAut A) = 20158709760 := by
  let f : Multiplicative (Fin 6 → ZMod 2) →* A :=
    { toFun := fun v => ⟨φ v.toAdd, h.mem v.toAdd⟩
      map_one' := Subtype.ext h.map_zero
      map_mul' := fun v w => Subtype.ext (by
        rw [toAdd_mul]
        exact h.map_add v.toAdd w.toAdd) }
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      apply Multiplicative.toAdd.injective
      exact h.injective (Subtype.ext_iff.mp hvw)
    · intro a
      obtain ⟨v, hv⟩ := (h.mem_iff (a : G)).mp a.2
      exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩
  have he : A ≃* Multiplicative (Fin 6 → ZMod 2) := (MulEquiv.ofBijective f hf).symm
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2) he, card_GL_six]

private lemma sec5b6_conjNormal_congr_apply_coe {G : Type*} [Group G] {M A : Subgroup G}
    [(A.subgroupOf M).Normal] (hAM : A ≤ M) (m : ↥M) (a : ↥A) :
    (((MulAut.congr (Subgroup.subgroupOfEquivOfLe hAM))
        (MulAut.conjNormal (H := A.subgroupOf M) m)) a : G) =
      (m : G) * (a : G) * (m : G)⁻¹ := by
  rw [MulAut.congr_apply]
  change ((Subgroup.subgroupOfEquivOfLe hAM)
    (MulAut.conjNormal (H := A.subgroupOf M) m
      ((Subgroup.subgroupOfEquivOfLe hAM).symm a)) : G) = _
  have hcoe : ∀ x : A.subgroupOf M,
      ((Subgroup.subgroupOfEquivOfLe hAM x : ↥A) : G) = ((x : ↥M) : G) := fun x => rfl
  rw [hcoe]
  rw [MulAut.conjNormal_apply]
  rfl

theorem IsPerm6.ncard_conjClass_dvd (h : IsPerm6 φ A H) {x : G} (hx : x ∈ A) :
    (conjClassIn (normalizer (A : Set G)) x).ncard ∣ 20158709760 := by
  classical
  let M : Subgroup G := normalizer (A : Set G)
  haveI hN : (A.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  let ρ : M →* MulAut A :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := A)))).toMonoidHom.comp
      MulAut.conjNormal
  have hρapply : ∀ (m : M) (a : A),
      ((ρ m a : A) : G) = (m : G) * (a : G) * (m : G)⁻¹ := by
    intro m a
    change (((MulAut.congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := A))))
      (MulAut.conjNormal m)) a : G) = _
    exact sec5b6_conjNormal_congr_apply_coe (Subgroup.le_normalizer (H := A)) m a
  let P : Subgroup (MulAut A) := ρ.range
  letI : MulAction P A := MulAction.compHom A P.subtype
  let a : A := ⟨x, hx⟩
  have hclass : (conjClassIn M x).ncard = (MulAction.orbit P a).ncard := by
    have himg : Subtype.val '' (MulAction.orbit P a) = conjClassIn M x := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [MulAction.mem_orbit_iff] at hz
        obtain ⟨p, hp⟩ := hz
        obtain ⟨m, hm⟩ := p.2
        refine ⟨m, m.2, ?_⟩
        have hp' : (p : MulAut A) a = z := hp
        rw [← hp', ← hm, hρapply]
      · rintro ⟨m, hm, rfl⟩
        refine ⟨(⟨ρ ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩⟩ : P) • a, ⟨_, rfl⟩, ?_⟩
        change (((ρ ⟨m, hm⟩) a : A) : G) = m * x * m⁻¹
        simpa using hρapply ⟨m, hm⟩ a
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have h1 : (MulAction.orbit P a).ncard ∣ Nat.card P := by
    rw [← MulAction.index_stabilizer P a]
    exact Subgroup.index_dvd_card (H := MulAction.stabilizer P a)
  have h2 : Nat.card P ∣ 20158709760 := by
    rw [← h.card_mulAut]
    exact Subgroup.card_subgroup_dvd_card P
  rw [hclass]
  exact h1.trans h2

theorem IsPerm6.ncard_conjClass_ne_thirteen (h : IsPerm6 φ A H) {x : G} (hx : x ∈ A) :
    (conjClassIn (normalizer (A : Set G)) x).ncard ≠ 13 := by
  intro h13
  have hdvd := h.ncard_conjClass_dvd hx
  rw [h13] at hdvd
  norm_num at hdvd

theorem IsPerm6.ncard_conjClass_ne_twentytwo (h : IsPerm6 φ A H) {x : G} (hx : x ∈ A) :
    (conjClassIn (normalizer (A : Set G)) x).ncard ≠ 22 := by
  intro h22
  have hdvd := h.ncard_conjClass_dvd hx
  rw [h22] at hdvd
  norm_num at hdvd

end CFSG.OddStandard.SmallF3.Omega
