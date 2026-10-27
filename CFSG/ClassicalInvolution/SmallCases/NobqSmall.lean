module

public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch
public import CFSG.ClassicalInvolution.RankTwo.Reduction
public import CFSG.ClassicalInvolution.SubnormalClosure
import CFSG.Adapters.GeneralizedFitting
import CFSG.Assembly.LowTwoRank
import CFSG.Milestones.LR_rank_two_isomorphism_types

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def ExcludedSmall (F : Type) [Group F] : Prop :=
  Nonempty (F ≃* alternatingGroup (Fin 7)) ∨
    CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2 ∨ LieModel F .PSL 2 2 3 ∨
    LieModel F .PSL 2 2 4 ∨ LieModel F .PSL 3 2 2 ∨ LieModel F .twistedB2 0 2 3 ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (F ≃* alternatingGroup (Fin n))) ∨
    NativeSporadic.IsSporadic F .M22 ∨ NativeSporadic.IsSporadic F .M23 ∨
    NativeSporadic.IsSporadic F .J1 ∨ NativeSporadic.IsSporadic F .J2 ∨
    NativeSporadic.IsSporadic F .J3 ∨ NativeSporadic.IsSporadic F .McL ∨
    NativeSporadic.IsSporadic F .Ly

theorem centralizer_genFittingFStar_eq_bot {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) :
    Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hxF : x ∈ genFittingFStar G := CFSG.Adapters.generalized_fitting_self_centralizing G hx
  have hcen : (⟨x, hxF⟩ : genFittingFStar G) ∈ Subgroup.center (genFittingFStar G) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g.1 g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (genFittingFStar G)) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcen)
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem oddLieType_or_excludedSmall (hGH : GH74SectionalModels) (F : Type) [Group F] [Finite F]
    [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) (hP : TwoSubgroupsFourGenerated F) :
    OddLieType F ∨ NativeSporadic.IsSporadic F .M11 ∨ NativeSporadic.IsSporadic F .M12 ∨
      ExcludedSmall F := by
  by_cases h3 : 3 ≤ twoRank F
  · rcases hGH F hnab h3 hP with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hf, hm, h⟩ |
      ⟨p, f, hp, hf, hm, h⟩ | h | ⟨n, hn1, hn2, he⟩ | h
    · left
      rcases h with h | h
      · exact oddLieType_of_lieModel h hp hp2 (by decide)
      · exact oddLieType_of_lieModel h hp hp2 (by decide)
    · exact Or.inl (oddLieType_of_lieModel h hp hp2 (by decide))
    · exact Or.inl (oddLieType_of_lieModel h Nat.prime_three (by norm_num) (by decide))
    · exact Or.inl (oddLieType_of_lieModel h hp hp2 (by decide))
    · exact Or.inl (oddLieType_of_lieModel h hp hp2 (by decide))
    · exact Or.inl (oddLieType_of_lieModel h hp (ne_two_of_pow_mod_four hf (Or.inl hm))
        (by decide))
    · exact Or.inl (oddLieType_of_lieModel h hp (ne_two_of_pow_mod_four hf (Or.inr hm))
        (by decide))
    · exact Or.inr (Or.inr (Or.inr (by unfold ExcludedSmall; tauto)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn1, hn2, he⟩))))))
    · rcases h with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      all_goals exact Or.inr (Or.inr (Or.inr (by unfold ExcludedSmall; tauto)))
  · have h2 : twoRank F ≤ 2 := by omega
    have heven : Even (Nat.card F) := by
      by_contra hodd
      have := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := F) (Nat.not_even_iff_odd.mp hodd)
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
    have h2' : twoRank F = 2 := le_antisymm h2 (two_le_twoRank F hnab heven)
    rcases CFSG.Milestones.lr_rank_two_isomorphism_types F hnab h2' with
      ⟨p, f, hp, hp2, -, h⟩ | ⟨p, f, hp, hp2, -, h⟩ | ⟨p, f, hp, hp2, -, h⟩ | h | h | h
    · exact Or.inl ⟨.PSL, 2, p, f, hp, hp2, h.1, Or.inl ⟨by decide, h⟩⟩
    · exact Or.inl ⟨.PSL, 3, p, f, hp, hp2, h.1, Or.inl ⟨by decide, h⟩⟩
    · exact Or.inl ⟨.PSU, 3, p, f, hp, hp2, h.1, Or.inl ⟨by decide, h⟩⟩
    · exact Or.inr (Or.inr (Or.inr (by unfold ExcludedSmall; tauto)))
    · exact Or.inr (Or.inr (Or.inr (by unfold ExcludedSmall; tauto)))
    · exact Or.inr (Or.inl (isSporadic_m11_of_nonempty_mulEquiv_statedM11 h))

theorem normalOddByQuaternionSmall_of_noDatum (hGH : GH74SectionalModels)
    (hex : ∀ (F : Type) [Group F], ExcludedSmall F → NoDatum F) :
    NormalOddByQuaternionUnder fun {G} _ _ _ => TwoSubgroupsFourGenerated (genFittingFStar G) := by
  intro G _ _ _ hnab R S hS t ht hto hRC hRn _ hP
  obtain ⟨r, hr, ⟨eS⟩⟩ := hS
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  rcases oddLieType_or_excludedSmall hGH (genFittingFStar G) hnab hP with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (hex _ h G (genFittingFStar G) ⟨MulEquiv.refl _⟩
      (centralizer_genFittingFStar_eq_bot hnab) R S r hr ⟨eS⟩ t ht hto hRC hRn).elim

structure SmallNoDatum : Prop where
  a7 : NoDatum (alternatingGroup (Fin 7))
  psu34 : ∀ (F : Type) [Group F], CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2 →
    NoDatum F
  psl28 : ∀ (F : Type) [Group F], LieModel F .PSL 2 2 3 → NoDatum F
  psl216 : ∀ (F : Type) [Group F], LieModel F .PSL 2 2 4 → NoDatum F
  psl34 : ∀ (F : Type) [Group F], LieModel F .PSL 3 2 2 → NoDatum F
  sz8 : ∀ (F : Type) [Group F], LieModel F .twistedB2 0 2 3 → NoDatum F
  alt : ∀ n : ℕ, 8 ≤ n → n ≤ 11 → NoDatum (alternatingGroup (Fin n))
  m22 : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .M22 → NoDatum F
  m23 : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .M23 → NoDatum F
  j1 : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .J1 → NoDatum F
  j2 : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .J2 → NoDatum F
  j3 : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .J3 → NoDatum F
  mcl : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .McL → NoDatum F
  ly : ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .Ly → NoDatum F

theorem SmallNoDatum.noDatum (h : SmallNoDatum) (F : Type) [Group F] (hF : ExcludedSmall F) :
    NoDatum F := by
  rcases hF with ⟨⟨e⟩⟩ | hF | hF | hF | hF | hF | ⟨n, hn1, hn2, ⟨e⟩⟩ | hF | hF | hF | hF | hF |
    hF | hF
  · exact NoDatum.of_mulEquiv e h.a7
  · exact h.psu34 F hF
  · exact h.psl28 F hF
  · exact h.psl216 F hF
  · exact h.psl34 F hF
  · exact h.sz8 F hF
  · exact NoDatum.of_mulEquiv e (h.alt n hn1 hn2)
  · exact h.m22 F hF
  · exact h.m23 F hF
  · exact h.j1 F hF
  · exact h.j2 F hF
  · exact h.j3 F hF
  · exact h.mcl F hF
  · exact h.ly F hF

theorem normalOddByQuaternionSmall_of_gh74 (hGH : GH74SectionalModels) (h : SmallNoDatum) :
    NormalOddByQuaternionUnder fun {G} _ _ _ => TwoSubgroupsFourGenerated (genFittingFStar G) :=
  normalOddByQuaternionSmall_of_noDatum hGH fun F _ hF => h.noDatum F hF

end CFSG.ClassicalInvolution.Nobq
