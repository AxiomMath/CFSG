module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSec

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V] [Finite V]

instance instIsF2SpaceSec [IsF2Space V] (M₀ M₁ : Subgroup V) : IsF2Space (Sec M₁ M₀) :=
  ⟨sec_sq_eq_one IsF2Space.sq_eq_one M₀ M₁⟩

instance instIsF2SpaceSubgroup [IsF2Space V] (M : Subgroup V) : IsF2Space ↥M :=
  ⟨fun v => Subtype.ext (by simpa using IsF2Space.sq_eq_one (v : V))⟩

private theorem aeval_comm_of_linear {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] (f : Module.End (ZMod 2) A)
    (g : Module.End (ZMod 2) B) (ι : A →ₗ[ZMod 2] B) (hι : ∀ x, ι (f x) = g (ι x))
    (p : Polynomial (ZMod 2)) (x : A) :
    ι (Polynomial.aeval f p x) = Polynomial.aeval g p (ι x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply, map_smul]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    have hsplit : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (ZMod 2)) =
        Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    rw [hsplit, map_mul (Polynomial.aeval f), map_mul (Polynomial.aeval g), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih (f x), hι x]

theorem polyAct_map {A B : Type} [CommGroup A] [CommGroup B] [IsF2Space A] [IsF2Space B]
    (f : A →* B) {θA : MulAut A} {θB : MulAut B} (hf : ∀ x, f (θA x) = θB (f x))
    (p : Polynomial (ZMod 2)) (x : A) : f (polyAct θA p x) = polyAct θB p (f x) := by
  have hι : ∀ y : Additive A,
      AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f) (linOf θA y) =
        linOf θB (AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f) y) := by
    intro y
    show Additive.ofMul (f (θA (Additive.toMul y))) = Additive.ofMul (θB (f (Additive.toMul y)))
    rw [hf]
  have key := aeval_comm_of_linear (linOf θA) (linOf θB)
    (AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f)) hι p (Additive.ofMul x)
  exact congrArg (fun z : Additive B => Additive.toMul z) key

theorem exists_prod_of_mem_iSup {S : Type} [CommGroup S] {ι : Type} [Fintype ι]
    (W : ι → Subgroup S) {s : S} (hs : s ∈ ⨆ i, W i) :
    ∃ f : ι → S, (∀ i, f i ∈ W i) ∧ ∏ i, f i = s := by
  classical
  refine Subgroup.iSup_induction W
    (C := fun s : S => ∃ f : ι → S, (∀ i, f i ∈ W i) ∧ ∏ i, f i = s) hs ?_ ?_ ?_
  · intro j s hsj
    refine ⟨fun i => if i = j then s else 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h
        simpa using hsj
      · simp [h]
    · simp [Finset.prod_ite_eq']
  · exact ⟨fun _ => 1, fun i => (W i).one_mem, by simp⟩
  · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun i => f i * g i, fun i => (W i).mul_mem (hf i) (hg i), Finset.prod_mul_distrib⟩

theorem prod_act_eq_component {S : Type} [CommGroup S] [Finite S] {ι : Type} [Fintype ι]
    [DecidableEq ι] (W : ι → Subgroup S) (hind : iSupIndep W) {G : Type} [Group G] [Fintype G]
    (hGodd : Odd (Fintype.card G)) (ρ : G →* MulAut S) (j : ι) (hsq : ∀ s : S, s ^ 2 = 1)
    (hstab : ∀ i, ∀ g, ∀ s ∈ W i, ρ g s ∈ W i) (htriv : ∀ g, ∀ s ∈ W j, ρ g s = s)
    (hfix : ∀ s, (∀ g, ρ g s = s) → s ∈ W j) (f : ι → S) (hf : ∀ i, f i ∈ W i) :
    ∏ g : G, ρ g (∏ i, f i) = f j := by
  simp only [map_prod]
  rw [Finset.prod_comm, Finset.prod_eq_single j]
  ·
    have hfj : ∀ g : G, ρ g (f j) = f j := fun g => htriv g (f j) (hf j)
    simp only [hfj, Finset.prod_const, Finset.card_univ]
    obtain ⟨k, hk⟩ := hGodd
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  ·
    intro i _ hij
    have hbW : (∏ g : G, ρ g (f i)) ∈ W i :=
      Subgroup.prod_mem (W i) (fun g _ => hstab i g (f i) (hf i))
    have hbfix : ∀ h : G, ρ h (∏ g : G, ρ g (f i)) = ∏ g : G, ρ g (f i) := by
      intro h
      rw [map_prod]
      refine Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
      show ρ h (ρ g (f i)) = ρ (h * g) (f i)
      rw [map_mul, MulAut.mul_apply]
    have hbj : (∏ g : G, ρ g (f i)) ∈ W j := hfix _ hbfix
    have hdisj : Disjoint (W i) (W j) := hind.pairwiseDisjoint hij
    exact Subgroup.disjoint_def.mp hdisj hbW hbj
  · intro h
    exact absurd (Finset.mem_univ j) h

end CFSG.LocalAnalysis.RankThreeUC
