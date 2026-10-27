module

public import CFSG.HardMathSupport.Dickson.Bal207.FCBridge
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerCompSU3

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Image

variable {X : Type} [Group X]

@[expose] noncomputable def imageIn (J S : Subgroup X) :
    Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
  (S.subgroupOf (Subgroup.normalizer (J : Set X))).map (actHom J)

theorem mem_imageIn {J S : Subgroup X} {e : MulAut (↥J ⧸ Subgroup.center ↥J)} :
    e ∈ imageIn J S ↔ ∃ (s : X) (hs : s ∈ Subgroup.normalizer (J : Set X)), s ∈ S ∧
      actHom J ⟨s, hs⟩ = e := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, n.2, Subgroup.mem_subgroupOf.1 hn, rfl⟩
  · rintro ⟨s, hs, hsS, rfl⟩
    exact ⟨⟨s, hs⟩, Subgroup.mem_subgroupOf.2 hsS, rfl⟩

theorem not_three_dvd_card_imageIn {J S : Subgroup X} (hSN : S ≤ Subgroup.normalizer (J : Set X))
    (hS3 : Nat.Coprime 3 (Nat.card S)) : ¬ 3 ∣ Nat.card (imageIn J S) := by
  intro h3
  have h1 : Nat.card (imageIn J S) ∣ Nat.card (S.subgroupOf (Subgroup.normalizer (J : Set X))) :=
    Subgroup.card_map_dvd _ _
  have h2 : Nat.card (S.subgroupOf (Subgroup.normalizer (J : Set X))) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hS3 (h2 ▸ h3.trans h1)

theorem autImage_le_normalizer_imageIn {B J S : Subgroup X}
    (hBS : B ⊓ Subgroup.normalizer (J : Set X) ≤ Subgroup.normalizer (S : Set X)) :
    autImage B J ≤ Subgroup.normalizer (imageIn J S : Set (MulAut (↥J ⧸ Subgroup.center ↥J))) := by
  have hstable : ∀ e ∈ autImage B J, ∀ y ∈ imageIn J S, e * y * e⁻¹ ∈ imageIn J S := by
    intro e he y hy
    obtain ⟨x, hxN, hxB, rfl⟩ := mem_autImage.1 he
    obtain ⟨s, hsN, hsS, rfl⟩ := mem_imageIn.1 hy
    have hxS : x ∈ Subgroup.normalizer (S : Set X) := hBS ⟨hxB, hxN⟩
    have hconj : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hxS _).1 hsS
    have hconjN : x * s * x⁻¹ ∈ Subgroup.normalizer (J : Set X) :=
      (Subgroup.normalizer (J : Set X)).mul_mem
        ((Subgroup.normalizer (J : Set X)).mul_mem hxN hsN)
        ((Subgroup.normalizer (J : Set X)).inv_mem hxN)
    refine mem_imageIn.2 ⟨x * s * x⁻¹, hconjN, hconj, ?_⟩
    rw [show (⟨x * s * x⁻¹, hconjN⟩ : Subgroup.normalizer (J : Set X)) =
      ⟨x, hxN⟩ * ⟨s, hsN⟩ * ⟨x, hxN⟩⁻¹ from rfl]
    simp only [map_mul, map_inv]
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hstable e he y hy, fun hy => ?_⟩
  have := hstable e⁻¹ ((autImage B J).inv_mem he) _ hy
  simpa [mul_assoc] using this

theorem centralizes_of_imageIn_eq_bot {J S : Subgroup X} (hperf : ⁅J, J⁆ = J)
    (hSN : S ≤ Subgroup.normalizer (J : Set X)) (h : imageIn J S = ⊥) :
    S ≤ Subgroup.centralizer (J : Set X) := by
  intro s hs
  refine KSF4SU3.mem_centralizer_of_actHom_eq_one hperf (hSN hs) ?_
  have hmem : actHom J ⟨s, hSN hs⟩ ∈ imageIn J S :=
    mem_imageIn.2 ⟨s, hSN hs, hs, rfl⟩
  rw [h] at hmem
  exact Subgroup.mem_bot.1 hmem

end Image

@[expose] def SU38Toral {X : Type} [Group X] (B J : Subgroup X) : Prop :=
  CFSG.Open.IsQuasisimple ↥J ∧
    ∃ (ℓ f : ℕ) (F : Type) (_ : Field F) (h : UnitaryFieldData ℓ f F), ℓ = 2 ∧ (f = 1 ∨ f = 3) ∧
      ℓ ^ f ≠ 2 ∧
      ∃ e : (↥J ⧸ Subgroup.center ↥J) ≃* primeFormP h (FirstClaim.oneGram F 3),
        ∃ D : Subgroup (GL (Fin 3) F), FirstClaim.IsOmegaOneTorus D ∧
          ∀ A : primeFormUnitary h (FirstClaim.oneGram F 3), (A : GL (Fin 3) F) ∈ D →
            ∃ (b : X) (hb : b ∈ Subgroup.normalizer (J : Set X)), b ∈ B ∧
              MulAut.congr e (actHom J ⟨b, hb⟩) = primeFormConjHom h _ A

theorem isStronglyLocallyOneBalanced_of_toral {X : Type} [Group X] [Finite X] {B J : Subgroup X}
    (a : X) (h : SU38Toral B J) : IsStronglyLocallyOneBalanced 3 B a J := by
  obtain ⟨hJ, ℓ, f, F, _, hud, hℓ, hf, hne, e, D, hD, hBD⟩ := h
  exact FirstClaim.isStronglyLocallyOneBalanced_of_omegaOne (n := 3) hJ hud hℓ hf le_rfl
    (fun hh => hne hh.2) e hD hBD

theorem isU3EightIndexTwo_of_isSU38Idx {d : TauCeti.LieTypeIndex} (h : IsSU38Idx d) :
    KSF4SU3.IsU3EightIndexTwo d := by
  cases d with
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := h
    exact ⟨q, hq, rfl⟩
  | _ => exact False.elim h

theorem isLieQuot_isU3EightIndexTwo {X : Type} [Group X] {J : Subgroup X} (h : IsSU38Comp J) :
    IsLieQuot ↥J KSF4SU3.IsU3EightIndexTwo := by
  obtain ⟨d, hd, e⟩ := h
  exact ⟨d, isU3EightIndexTwo_of_isSU38Idx hd, e⟩

section K0

set_option linter.unusedSectionVars false

theorem isStronglyLocallyOneBalanced_of_rankThree_or_toral {X : Type} [Group X] [Finite X]
    {B J : Subgroup X} (a : X) (hperf : ⁅J, J⁆ = J) (hJ : IsSU38Comp J)
    (h : KSF4SU3.AutImageRankThree B J ∨ SU38Toral B J) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  rcases h with h | h
  · exact KSF4SU3.isStronglyLocallyOneBalanced_of_autImageRankThree hperf
      (isLieQuot_isU3EightIndexTwo hJ) h
  · exact isStronglyLocallyOneBalanced_of_toral a h

end K0

end CFSG.HardMathSupport.Dickson.Bal207

end
