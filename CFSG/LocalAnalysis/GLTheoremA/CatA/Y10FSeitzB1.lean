module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitz
public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem hasLabel_isQuasisimple {X : Type} [Group X] {S : GLALabel → Prop} (h : HasLabel X S) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨hcomm, -, -, R, _, I, F, θ, hs, -, -⟩ := CFSG.StandardType.Canonical.largeEvenMarking_exists h
  exact ⟨hcomm, (MulEquiv.isSimpleGroup_congr θ).2 hs⟩

theorem le_center_of_normal_isPGroup_two {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    {T : Subgroup K} (hT2 : IsPGroup 2 T) (hTn : T.Normal) : T ≤ Subgroup.center K := by
  obtain ⟨hperf, hsimple⟩ := hK
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hsimple
  haveI : Group.IsPerfect K := ⟨hperf⟩
  have hnorm : (T.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map hTn _ (QuotientGroup.mk'_surjective _)
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · intro t ht
    have : QuotientGroup.mk' (Subgroup.center K) t ∈ (⊥ : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [← h]; exact Subgroup.mem_map_of_mem _ ht
    exact (QuotientGroup.eq_one_iff _).1 this
  · exfalso
    have hall : ∀ y : K ⧸ Subgroup.center K, ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
      intro y
      have hy : y ∈ T.map (QuotientGroup.mk' (Subgroup.center K)) := by rw [h]; trivial
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
      refine ⟨n, ?_⟩
      rw [← map_pow]
      have : t ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      rw [this, map_one]
    haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
        (QuotientGroup.mk'_surjective _)
    have hpg : IsPGroup 2 (K ⧸ Subgroup.center K) := fun y => hall y
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Group.IsPerfect.not_isNilpotent (K ⧸ Subgroup.center K) hpg.isNilpotent

theorem seitz_core (h : SeitzGen) {K : Type} [Group K] [Finite K] (hK : HasLabel K (fun _ => True))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y : Type} [Group Y] (ρ : Y →* MulAut K)
    {E : Subgroup Y} (hE : IsElemAbelian q E) (hcard : Nat.card (E.map ρ) ≤ q ^ 3) {T : Subgroup K}
    (hT2 : IsPGroup 2 T)
    (hTinv : ∀ e ∈ E, ∀ t ∈ T, ρ e t ∈ T)
    (hnorm : ∀ F : Subgroup Y, F ≤ E → F.relIndex E ≤ q →
      centFixAct ρ F ≤ Subgroup.normalizer (T : Set K)) : T ≤ Subgroup.center K := by
  by_contra hTc
  have hgen := seitzGen_action h hK hq hq2 ρ hE hcard ⟨T, hT2, hTc, hTinv⟩
  have hN : Subgroup.normalizer (T : Set K) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le fun F hF => hnorm F hF.1 hF.2
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (T : Set K) := by rw [hN]; trivial
    exact (Subgroup.mem_normalizer_iff.1 hg t).1 ht
  exact hTc (le_center_of_normal_isPGroup_two (hasLabel_isQuasisimple hK) hT2 hTn)

theorem exists_fixed_lift {Kg Y : Type} [Group Kg] [Finite Kg] [Group Y] (N : Subgroup Kg) [N.Normal]
    (ρ₀ : Y →* MulAut Kg) (hρ : ∀ y, N.map (ρ₀ y).toMonoidHom = N) {q : ℕ} [Fact q.Prime]
    {F : Subgroup Y} (hF : IsPGroup q ↥F) (hN : ¬ q ∣ Nat.card N) (x : Kg ⧸ N)
    (hx : ∀ f ∈ F, quotAutHom N ρ₀ hρ f x = x) :
    ∃ k : Kg, (QuotientGroup.mk k : Kg ⧸ N) = x ∧ ∀ f ∈ F, ρ₀ f k = k := by
  classical
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective x
  let S : Type := {k : Kg // (QuotientGroup.mk k : Kg ⧸ N) = QuotientGroup.mk k₀}
  have hmem : ∀ (f : F) (k : S), (QuotientGroup.mk (ρ₀ f k.1) : Kg ⧸ N) = QuotientGroup.mk k₀ := by
    intro f k
    calc (QuotientGroup.mk (ρ₀ f k.1) : Kg ⧸ N)
        = quotAutHom N ρ₀ hρ f (QuotientGroup.mk k.1) := (quotAutHom_mk N ρ₀ hρ f k.1).symm
      _ = quotAutHom N ρ₀ hρ f (QuotientGroup.mk k₀) := by rw [k.2]
      _ = QuotientGroup.mk k₀ := hx f f.2
  letI act : MulAction F S :=
    { smul := fun f k => ⟨ρ₀ f k.1, hmem f k⟩
      one_smul := fun k => Subtype.ext (by
        show (ρ₀ ((1 : F) : Y)) k.1 = k.1
        simp)
      mul_smul := fun f g k => Subtype.ext (by
        show (ρ₀ ((f * g : F) : Y)) k.1 = (ρ₀ (f : Y)) ((ρ₀ (g : Y)) k.1)
        simp) }
  have hcardS : Nat.card S = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun k => ⟨k₀⁻¹ * k.1, by simpa using (QuotientGroup.eq.1 k.2.symm)⟩
        invFun := fun n => ⟨k₀ * n.1, by
          rw [QuotientGroup.eq]; simpa using N.inv_mem n.2⟩
        left_inv := fun k => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hSp : ¬ q ∣ Nat.card S := by rw [hcardS]; exact hN
  obtain ⟨k, hk⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card S hSp
  refine ⟨k.1, k.2, fun f hf => ?_⟩
  have := hk ⟨f, hf⟩
  exact congrArg Subtype.val this

end CFSG.LocalAnalysis.GLTheoremA.Y10F
