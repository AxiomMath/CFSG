module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoSc
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.Steinberg

noncomputable abbrev twE6F0 (L : Type)
    [Field L] (Fr : L →+* L) : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
  twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) Fr

section BaseChange


theorem baseChangeGL_twE6F0 {k k' : Type} [Field k] [Field k'] (ι : k →+* k') {φ : k →+* k}
    {Fr : k' →+* k'} (h : ι.comp φ = Fr.comp ι) (g : ModGL Tag.E6 k) :
    baseChangeGL ι (twE6F0 k φ g) = twE6F0 k' Fr (baseChangeGL ι g) := by
  change baseChangeGL ι (canonicalRep (coxeterSystem TwistTag.E6.tag) k twE6W0 *
      twistHom TwistTag.E6 k φ g * (canonicalRep (coxeterSystem TwistTag.E6.tag) k twE6W0)⁻¹) =
    canonicalRep (coxeterSystem TwistTag.E6.tag) k' twE6W0 *
      twistHom TwistTag.E6 k' Fr (baseChangeGL ι g) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) k' twE6W0)⁻¹
  rw [map_mul, map_mul, map_inv, baseChangeGL_canonicalRep,
    twistHom_baseChangeGL (t := TwistTag.E6) ι h g]

end BaseChange

section Word


theorem isReduced_e6W0FourWord : (coxeterSystem Tag.E6).IsReduced e6W0FourWord :=
  isReduced_of_reducedCheck (by decide +kernel)

end Word

section Sc


variable {k : Type} [Field k]

theorem e6Isogeny_twE6NSc_eq [Finite k] :
    ((e6Isogeny k (twE6NSc k) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) k twE6W0 :=
  e6Isogeny_nWord_eq_canonicalRep isReduced_e6W0FourWord

theorem e6Isogeny_twistSc_eq [Finite k] (θ : k →+* k) (g : e6Data_valid.minGroup k) :
    ((e6Isogeny k (twistSc θ g) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      twE6F0 k θ ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) := by
  change ((e6Isogeny k (twE6NSc k * TwistedE6.sigma k θ g * (twE6NSc k)⁻¹) :
      adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
  rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    e6Isogeny_twE6NSc_eq, e6Isogeny_sigma θ g]
  rfl

theorem twistSc_center (θ : k →+* k) (q : ℕ) (hθ : ∀ c, θ c = c ^ q) (hq : q % 3 = 2)
    {z : e6Data_valid.minGroup k} (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    twistSc θ z = z := by
  change twE6NSc k * TwistedE6.sigma k θ z * (twE6NSc k)⁻¹ = z
  rw [twl_sigma_center θ q hθ hq hz, Subgroup.mem_center_iff.1 hz (twE6NSc k),
    mul_inv_cancel_right]

theorem twistSc_minTorus_of_pow_three_q (θ : k →+* k) (q : ℕ) (hθ : ∀ c, θ c = c ^ q)
    (hq : q % 3 = 2) (u : Fin Tag.E6.rank → kˣ) (hu : ∀ l, u l ^ 3 = 1) :
    twistSc θ (minTorus e6Data_valid k u) = minTorus e6Data_valid k u := by
  rw [twistSc_minTorus]
  congr 1
  funext l
  have e1 : Units.map θ.toMonoidHom (u l) = u l ^ q := Units.ext (by simp [hθ])
  obtain ⟨t, ht⟩ : ∃ t : ℕ, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  rw [e1, ht, pow_add, pow_mul, hu l, one_pow, one_mul]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ]
  exact hu l

end Sc

section LangTw


variable {L : Type} [Field L] [IsAlgClosed L] (p : ℕ) [Fact p.Prime] [CharP L p]

theorem familyGroup_unit_eq_toralRootGroup (a : Fin Tag.E6.rank → Lˣ) :
    familyGroup (K := L) (fun _ : Unit => a) = toralRootGroup Tag.E6 L a := by
  have h : familyKernel (fun _ : Unit => a) = rootCharKernel a := by
    ext α
    simp [familyKernel, rootCharKernel]
  rw [familyGroup, toralRootGroup, h]

theorem toralRootGroup_lang_twq (f : ℕ) (hf : 1 ≤ f) (a : Fin Tag.E6.rank → Lˣ) :
    ∀ c ∈ toralRootGroup Tag.E6 L a, ∃ z ∈ toralRootGroup Tag.E6 L a,
      z⁻¹ * twE6F0 L (iterateFrobenius L p f) z = c := by
  have hFrs : Function.Surjective (iterateFrobenius L p f) := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : p.Prime).pos f)
    exact ⟨x, by rw [iterateFrobenius_def, hx]⟩
  have himg : (fun α => twE6W0 • permLattice TwistTag.E6.perm α) ''
      familyKernel (fun _ : Unit => a) = familyKernel (fun _ : Unit => a) := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
      refine ⟨?_, fun i => ?_⟩
      · dsimp only
        rw [twE6W0_smul_permLattice]
        exact IsRoot.neg hα
      · dsimp only
        rw [twE6W0_smul_permLattice]
        exact (rootChar_neg_vec_E6Four (τ := Tag.E6) a α).trans
          (by have h : rootChar a α = 1 := hαa i; rw [h, inv_one])
    · rintro ⟨hβ, hβa⟩
      refine ⟨-β, ⟨IsRoot.neg hβ, fun i => ?_⟩, ?_⟩
      · exact (rootChar_neg_vec_E6Four (τ := Tag.E6) a β).trans
          (by have h : rootChar a β = 1 := hβa i; rw [h, inv_one])
      · simp only
        rw [twE6W0_smul_permLattice, neg_neg]
  have hF : ∀ g : ModGL Tag.E6 L, frobTwistGL Tag.E6 L p f
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0 * diagramMap TwistTag.E6 L) g =
        twE6F0 L (iterateFrobenius L p f) g := fun g => rfl
  have hst : ∀ g ∈ familyGroup (K := L) (fun _ : Unit => a),
      frobTwistGL Tag.E6 L p f (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0 *
        diagramMap TwistTag.E6 L) g ∈ familyGroup (K := L) (fun _ : Unit => a) := by
    intro g hg
    rw [hF]
    exact twFrob_mem_familyGroup TwistTag.E6 hFrs twE6W0 (fun _ : Unit => a) himg hg
  intro c hc
  rw [← familyGroup_unit_eq_toralRootGroup] at hc ⊢
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo p (fun _ : Unit => a) f hf _ hst c hc
  exact ⟨z, hz, hzc⟩

end LangTw

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
