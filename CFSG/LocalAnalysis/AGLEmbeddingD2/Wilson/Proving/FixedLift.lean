module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem exists_fixed_lift_of_pow_three {G Q : Type*} [Group G] [Finite G] [Group Q]
    (f : G →* Q) (hker : Nat.Coprime 3 (Nat.card f.ker)) (σ : MulAut G) (hσ : σ ^ 3 = 1)
    {y : G} (hy : ∀ g : G, f g = f y → f (σ g) = f y) :
    ∃ g : G, f g = f y ∧ σ g = g := by
  classical
  let F := {g : G // f g = f y}
  have hcard : Nat.card F = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun g => ⟨y⁻¹ * g.1, by simp [MonoidHom.mem_ker, g.2]⟩
        invFun := fun k => ⟨y * k.1, by
          have hk : f k.1 = 1 := k.2
          simp [map_mul, hk]⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have hnd : ¬ 3 ∣ Nat.card F := by
    rw [hcard]
    intro h
    have := Nat.Coprime.eq_one_of_dvd hker h
    exact absurd this (by norm_num)
  have hinj : Function.Injective (fun g : F => (⟨σ g.1, hy g.1 g.2⟩ : F)) := by
    intro a b hab
    exact Subtype.ext (σ.injective (congrArg Subtype.val hab))
  let τ : Equiv.Perm F := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ3 : ∀ g : G, σ (σ (σ g)) = g := by
    intro g
    have h := congrArg (fun φ : MulAut G => φ g) hσ
    simpa [pow_succ, MulAut.mul_apply] using h
  have hτ3 : τ ^ 3 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    simp [τ, Equiv.Perm.coe_pow, Function.iterate_succ, hσ3]
  have hdvd : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
  have hpg : IsPGroup 3 (Subgroup.zpowers τ) := by
    rw [IsPGroup.iff_card]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact ⟨0, by rw [Nat.card_zpowers, h1]; simp⟩
    · exact ⟨1, by rw [Nat.card_zpowers, h3]; simp⟩
  obtain ⟨z, hz⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card F hnd
  have hτz : τ z = z := hz ⟨τ, Subgroup.mem_zpowers τ⟩
  exact ⟨z.1, z.2, congrArg Subtype.val hτz⟩

theorem nonempty_quotient_aschbacherSolvableCore_equiv_range {K Q : Type*} [Group K] [Finite K]
    [Group Q] (f : K →* Q) (hs : Group.IsSolvable f.ker) (h3 : Nat.Coprime 3 (Nat.card f.ker))
    (hθ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 f.range = ⊥) :
    Nonempty (K ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K ≃* f.range) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hndker : ¬ 3 ∣ Nat.card f.ker := fun h => by
    have := Nat.Coprime.eq_one_of_dvd h3 h
    exact absurd this (by norm_num)
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨hsolvT, hchar, hcompl, hmaxK, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := K) hp
  obtain ⟨-, -, -, hmaxR, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := f.range) hp
  have := hchar
  have := hsolvT
  have ha : f.ker ≤ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K :=
    hmaxK f.ker (MonoidHom.normal_ker f) hs hndker
  have hb : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K ≤ f.ker := by
    let T := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K
    let M : Subgroup f.range := T.map f.rangeRestrict
    have hMn : M.Normal :=
      Subgroup.Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective
    let φ : T →* M :=
      (f.rangeRestrict.comp T.subtype).codRestrict M (fun t => Subgroup.mem_map_of_mem _ t.2)
    have hφ : Function.Surjective φ := by
      intro m
      obtain ⟨t, ht, hm⟩ := Subgroup.mem_map.mp m.2
      exact ⟨⟨t, ht⟩, Subtype.ext hm⟩
    have hMs : Group.IsSolvable M := Group.isSolvable_of_surjective hφ
    have hM3 : ¬ 3 ∣ Nat.card M := fun h =>
      hcompl (dvd_trans h (Subgroup.card_dvd_of_surjective hφ))
    have hM : M = ⊥ := by
      have hle := hmaxR M hMn hMs hM3
      rw [hθ] at hle
      exact le_bot_iff.mp hle
    intro t ht
    have hmem : f.rangeRestrict t ∈ M := Subgroup.mem_map_of_mem _ ht
    rw [hM, Subgroup.mem_bot] at hmem
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hmem
  have hθeq : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K = f.ker := le_antisymm hb ha
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθeq).trans (QuotientGroup.quotientKerEquivRange f)⟩

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
