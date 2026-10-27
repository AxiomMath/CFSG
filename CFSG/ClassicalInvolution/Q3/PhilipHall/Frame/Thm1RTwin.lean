module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.RecogE4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SharedRecog
import CFSG.Models.Blueprint
import CFSG.Models.Transport

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section ConjClass

variable {G : Type} [Group G]

theorem conjInvariant_conjClass (K : Subgroup G) : ConjInvariant (CoreAssembly.conjClass K) := by
  rintro n J ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K⟩

end ConjClass

section Bridge

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)]

theorem eq_bot_of_normal_isPGroup (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    {P : Subgroup Y} (hPn : P.Normal) (hP : IsPGroup 2 P) : P = ⊥ := by
  by_contra hne
  have hle := fstar_le_of_normal hnab hPn hne
  have h2 : IsPGroup 2 ↥(genFittingFStar Y) := hP.to_le hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥(genFittingFStar Y) := IsSimpleGroup.toNontrivial
  have hZ := h2.center_nontrivial
  have hZtop : Subgroup.center ↥(genFittingFStar Y) = ⊤ := by
    rcases (Subgroup.center ↥(genFittingFStar Y)).normal_of_characteristic.eq_bot_or_eq_top with
      h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hZ)
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  have ha : a ∈ Subgroup.center ↥(genFittingFStar Y) := hZtop ▸ Subgroup.mem_top a
  exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem not_tightInO2_of_fstar (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) {t : Y}
    (ht : t ≠ 1) : ¬ TightInO2 t := by
  rintro ⟨P, hPn, hP, htP⟩
  rw [eq_bot_of_normal_isPGroup hnab hPn hP, Subgroup.mem_bot] at htP
  exact ht htP

omit [Finite Y] [IsSimpleGroup (genFittingFStar Y)] in
theorem models_psp_three_two_of_blueprint {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.Blueprint.LieModel G .PSp 3 2 1) : Models.LieModel G' .PSp 3 2 1 :=
  (CFSG.Models.LieModel.of_blueprint (by decide) h).of_mulEquiv e

omit [Finite Y] [IsSimpleGroup (genFittingFStar Y)] in
theorem models_pomegaPlus_four_two_of_blueprint {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') (h : CFSG.Blueprint.LieModel G .POmegaPlus 4 2 1) :
    Models.LieModel G' .POmegaPlus 4 2 1 :=
  (CFSG.Models.LieModel.of_blueprint (by decide) h).of_mulEquiv e

theorem TwinE4.exSpD4 (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) (h : TwinE4 Y) :
    ExSpD4 Y := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  have hker : f.ker = ⊥ := eq_bot_of_normal_isPGroup hnab inferInstance hf2
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  let e : Y ≃* Q := MulEquiv.ofBijective f ⟨hinj, hfs⟩
  have hsimpleQ : IsSimpleGroup Q := by
    rcases hQ with hQ | hQ
    · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q 3 2 1
          hcl
      all_goals exact absurd h0 (by norm_num)
    · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
          Q 4 2 1 hcl).2
      all_goals exact absurd h0 (by norm_num)
  have hsimpleY : IsSimpleGroup Y := by
    have := hsimpleQ
    exact e.isSimpleGroup
  have hnabY : ∃ a b : Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have htop : genFittingFStar Y = ⊤ := @genFittingFStar_eq_top_of_simple Y _ _ hsimpleY hnabY
  let e' : Q ≃* ↥(genFittingFStar Y) :=
    e.symm.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm))
  rcases hQ with hQ | hQ
  · exact Or.inl (models_psp_three_two_of_blueprint e' hQ)
  · exact Or.inr (models_pomegaPlus_four_two_of_blueprint e' hQ)

theorem TwinE4.exLie (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) (h : TwinE4 Y) :
    QuaternionBridge.ExLie Y := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  have hker : f.ker = ⊥ := eq_bot_of_normal_isPGroup hnab inferInstance hf2
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  let e : Y ≃* Q := MulEquiv.ofBijective f ⟨hinj, hfs⟩
  rcases hQ with hQ | hQ
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hQ)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hQ)

end Bridge

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
