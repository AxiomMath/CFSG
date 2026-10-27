module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

section Types

variable {A B : Type} [Group A] [Group B]

theorem IsL2Sq.of_mulEquiv (e : A ≃* B) (h : IsL2Sq A) : IsL2Sq B := by
  obtain ⟨p, f, hp, hp2, hf, hl⟩ := h
  exact ⟨p, f, hp, hp2, hf, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hl⟩

theorem IsL3Ge5.of_mulEquiv (e : A ≃* B) (h : IsL3Ge5 A) : IsL3Ge5 B := by
  obtain ⟨p, f, hp, hp2, hq, hl⟩ := h
  exact ⟨p, f, hp, hp2, hq, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hl⟩

theorem IsU3Ge5.of_mulEquiv (e : A ≃* B) (h : IsU3Ge5 A) : IsU3Ge5 B := by
  obtain ⟨p, f, hp, hp2, hq, hl⟩ := h
  exact ⟨p, f, hp, hp2, hq, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hl⟩

theorem IsU33.of_mulEquiv (e : A ≃* B) (h : IsU33 A) : IsU33 B :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h

theorem IsM12.of_mulEquiv (e : A ≃* B) (h : IsM12 A) : IsM12 B := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

theorem IsSp62.of_mulEquiv (e : A ≃* B) (h : IsSp62 A) : IsSp62 B :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h

theorem IsO8p2.of_mulEquiv (e : A ≃* B) (h : IsO8p2 A) : IsO8p2 B :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h

end Types

section Bar

variable {X : Type} [Group X] {M Z : Subgroup X}

theorem subgroupOf_eq_center (hZc : Z ≤ Subgroup.center X)
    (hCZ : Subgroup.centralizer (M : Set X) = Z) : Z.subgroupOf M = Subgroup.center ↥M := by
  ext m
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro hm g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hm) g)
  · intro hm
    rw [← hCZ, Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hm ⟨y, hy⟩)

variable [Z.Normal]

noncomputable abbrev barHom (M Z : Subgroup X) [Z.Normal] : ↥M →* X ⧸ Z :=
  (QuotientGroup.mk' Z).comp M.subtype

theorem barHom_ker : (barHom M Z).ker = Z.subgroupOf M := by
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem barHom_range : (barHom M Z).range = M.map (QuotientGroup.mk' Z) := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

noncomputable def barEquiv (hZc : Z ≤ Subgroup.center X)
    (hCZ : Subgroup.centralizer (M : Set X) = Z) :
    ↥(M.map (QuotientGroup.mk' Z)) ≃* ↥M ⧸ Subgroup.center ↥M :=
  ((MulEquiv.subgroupCongr barHom_range).symm.trans
    (QuotientGroup.quotientKerEquivRange (barHom M Z)).symm).trans
    (QuotientGroup.quotientMulEquivOfEq (barHom_ker.trans (subgroupOf_eq_center hZc hCZ)))

theorem isSimpleGroup_bar (hMq : CFSG.IsQuasisimple ↥M) (hZc : Z ≤ Subgroup.center X)
    (hCZ : Subgroup.centralizer (M : Set X) = Z) :
    IsSimpleGroup ↥(M.map (QuotientGroup.mk' Z)) :=
  have := hMq.2.1
  (barEquiv hZc hCZ).isSimpleGroup

theorem exists_ne_comm_bar (hMq : CFSG.IsQuasisimple ↥M) (hZc : Z ≤ Subgroup.center X)
    (hCZ : Subgroup.centralizer (M : Set X) = Z) :
    ∃ a b : ↥(M.map (QuotientGroup.mk' Z)), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hMq.2.2
  refine ⟨(barEquiv hZc hCZ).symm a, (barEquiv hZc hCZ).symm b, fun h => hab ?_⟩
  simpa using congrArg (barEquiv hZc hCZ) h

theorem centralizer_bar_eq_bot (hMq : CFSG.IsQuasisimple ↥M) (hZc : Z ≤ Subgroup.center X)
    (hCZ : Subgroup.centralizer (M : Set X) = Z) :
    Subgroup.centralizer ((M.map (QuotientGroup.mk' Z) : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) = ⊥ := by
  have := hMq.1
  rw [eq_bot_iff]
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z xb
  let β : ↥M →* X := (MulAut.conj x).toMonoidHom.comp M.subtype
  have hker : (QuotientGroup.mk' Z).ker ≤ Subgroup.center X := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hcomp : (QuotientGroup.mk' Z).comp β = (QuotientGroup.mk' Z).comp M.subtype := by
    ext m
    have h1 := Subgroup.mem_centralizer_iff.mp hxb (QuotientGroup.mk' Z m)
      (Subgroup.mem_map_of_mem _ m.2)
    show QuotientGroup.mk' Z (x * (m : X) * x⁻¹) = QuotientGroup.mk' Z m
    rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
  have hβ := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker hcomp
  have hxC : x ∈ Subgroup.centralizer (M : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h2 := congrArg (fun φ : ↥M →* X => φ ⟨m, hm⟩) hβ
    simp only [β, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at h2
    calc m * x = x * m * x⁻¹ * x := by rw [h2]
      _ = x * m := by group
  rw [hCZ] at hxC
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hxC

end Bar

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
