module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinGood
public import CFSG.ClassicalInvolution.Q3.TA3SmallDescent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem mem_fstarCenter {z : Y} (hz : z ∈ genFittingFStar Y)
    (hc : ∀ l ∈ genFittingFStar Y, z * l = l * z) : z ∈ fstarCenter Y :=
  ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm, rfl⟩

theorem twinHyp_fstar (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t)
    (hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)) :
    TwinHyp (genFittingFStar Y) R S t := by
  have hNc := fstarCenter_le_center hd hc hE2
  have hN2 := isPGroup_fstarCenter hc
  have htN := not_mem_fstarCenter hc hE2
  have htL : t ∈ genFittingFStar Y := hd.mem_genFittingFStar hc.2.2
  have hCL : ∀ y : Y, (∀ l ∈ genFittingFStar Y, y * l = l * y) → y ∈ genFittingFStar Y :=
    fun y hy => CFSG.Adapters.generalized_fitting_self_centralizing Y
      (Subgroup.mem_centralizer_iff.mpr fun l hl => (hy l hl).symm)
  refine ⟨hd, htL, ?_, hsmall, hCL, fun r hr hrc => ?_, fun z hz hzc g =>
    Subgroup.mem_center_iff.mp (hNc (mem_fstarCenter hz hzc)) g⟩
  · by_contra hcon
    push Not at hcon
    exact htN (mem_fstarCenter htL fun l hl => (hcon l hl).symm)
  · have hrN := mem_fstarCenter (hCL r hrc) hrc
    by_contra hr1
    obtain ⟨n, hn⟩ := hN2 ⟨r, hrN⟩
    have hr2 : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hr2)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
      rcases k with _ | k
      · exact absurd (orderOf_eq_one_iff.mp (by rw [hk, pow_zero])) hr1
      · omega⟩
    have h2 : orderOf (r ^ 2 ^ j) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk, pow_succ,
        Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    exact htN (hd.eq_of_orderOf_eq_two (R.pow_mem hr _) h2 ▸ (fstarCenter Y).pow_mem hrN _)

omit [Finite Y] in
theorem isQuasisimple_fstar (hQ : TightFStarQuasisimple Y) :
    CFSG.IsQuasisimple ↥(genFittingFStar Y) := by
  have := hQ.2
  have hs := QuotientGroup.mk'_surjective (Subgroup.center ↥(genFittingFStar Y))
  have hperf : commutator (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) = ⊤ := by
    rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator,
      ← _root_.commutator_def, hQ.1, Subgroup.map_top_of_surjective _ hs]
  exact ⟨⟨hQ.1⟩, hQ.2, exists_ne_comm_of_commutator_eq_top hperf⟩

theorem isPGroup_center_fstar (hc : TightCls Y R S t) :
    IsPGroup 2 ↥(Subgroup.center ↥(genFittingFStar Y)) := fun z => by
  obtain ⟨n, hn⟩ := isPGroup_fstarCenter hc ⟨((z : ↥(genFittingFStar Y)) : Y), ⟨z, z.2, rfl⟩⟩
  exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩

theorem ghList_of_small {X : Type} [Group X] (h : SmallFamily X ∨ Nobq.ExcludedSmall X) :
    GH74.GHList X := by
  have hc : ∀ {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}, t = .PSL ∨ t = .PSU →
      Assembly.LowTwoRank.StatedClassicalModel X t n p f → LieModel X t n p f := by
    rintro t n p f (rfl | rfl) h <;> exact Or.inl ⟨by decide, h⟩
  have hG := fun (h : GH74.GH74Conclusion X) => GH74.GH74Conclusion.ghList h
  rcases h with (⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hm, h⟩ | ⟨p, f, hp, hp2, hf, hm, h⟩ | ⟨p, f, hp, -, hf, hm, h⟩ |
      ⟨p, f, hp, -, hf, hm, h⟩ | h | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ |
      ⟨p, f, hp, hp2, hf, h⟩ | h) |
      (h | h | h | h | h | h | h | h | h | h | h | h | h | h)
  · exact hG (Or.inl ⟨p, f, hp, hp2, hf, Or.inl h⟩)
  · exact hG (Or.inl ⟨p, f, hp, hp2, hf, Or.inr h⟩)
  · exact hG (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h⟩))
  · exact hG (Or.inr (Or.inr (Or.inl ⟨f, h⟩)))
  · exact hG (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm, h⟩))))
  · exact hG (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm, h⟩)))))
  · exact hG (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hm, h⟩))))))
  · exact hG (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hm, h⟩)))))))
  · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2, Or.inl (hc (Or.inl rfl) h)⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2, Or.inr (Or.inl (hc (Or.inl rfl) h))⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2, Or.inr (Or.inr (Or.inl
      (hc (Or.inr rfl) h)))⟩⟩)
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inl ⟨7, le_rfl, by norm_num, h⟩
  · exact Or.inr (Or.inr ⟨2, 1, Nat.prime_two, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl (hc (Or.inr rfl) h))))⟩)))))⟩)
  · exact hG (GH74.GH74Conclusion.of_eight (Or.inl h))
  · exact hG (GH74.GH74Conclusion.of_eight (Or.inr (Or.inl h)))
  · exact hG (GH74.GH74Conclusion.of_eight (Or.inr (Or.inr (Or.inl h))))
  · exact hG (GH74.GH74Conclusion.of_eight (Or.inr (Or.inr (Or.inr h))))
  · exact hG (GH74.GH74Conclusion.of_nine h)
  · exact hG (GH74.GH74Conclusion.of_M22 h)
  · exact hG (GH74.GH74Conclusion.of_M23 h)
  · exact hG (GH74.GH74Conclusion.of_J1 h)
  · exact hG (GH74.GH74Conclusion.of_J2 h)
  · exact hG (GH74.GH74Conclusion.of_J3 h)
  · exact hG (GH74.GH74Conclusion.of_McL h)
  · exact hG (GH74.GH74Conclusion.of_Ly h)

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
