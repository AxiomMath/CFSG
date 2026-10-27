module

public import CFSG.ClassicalInvolution.Q3.Q3WTree
public import CFSG.ClassicalInvolution.WeakCT.Spin
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT3_simplyLaced_of_equiv [Finite F] (e : F3 ≃+* F) {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F3 W (U i) (U j)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  obtain ⟨ρ, hρ, hψ⟩ := exists_frame_of_tree3 hT hroot hcomm hpair
  let φ₂ : SL(2, F) →* SL(2, F3) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F3) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F3), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  refine weakCT_of_frame hCT hL hD k₀ hgen hcomm (ρ := fun k => (ρ k).comp φ₂)
    (fun k => ⟨(hρ k).1.comp hφ₂inj, ?_⟩) (fun i j hij => ?_)
  · rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  · obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
    refine ⟨ψ.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 1 A)

theorem weakCT3_of_chevalleyExtras_of_equiv [Finite F] (e : F3 ≃+* F)
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    (hasymm : ∀ i j, adj i j → ¬ adj j i)
    (hadj : ∀ i j, adj i j → D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hnadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → D.cartan i j = 0 ∧ D.cartan j i = 0)
    (hnb : ∀ i j, adj i j → ∃ k, k ≠ i ∧ k ≠ j ∧
      ((adj j k ∨ adj k j) ∧ ¬ adj i k ∧ ¬ adj k i ∨
        (adj i k ∨ adj k i) ∧ ¬ adj j k ∧ ¬ adj k j))
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F3 W (U i) (U j)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE hdiv hC hasymm hadj hnadj hnb hind hsq
  exact weakCT3_simplyLaced_of_equiv e hCT hL hD hT hroot hgen hcomm hpair

end Recognition

theorem weakCT3_spinPlus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    (hn3 : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, edgeD n i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (Spin.quadPlus n F))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaPlus n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Spin.plusDatum n F hn3).rootGroup k).map Ψ = U k := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hF' : Nat.card F = 3 ^ 1 := by rw [hF]; norm_num
  obtain ⟨e⟩ : Nonempty (F ≃+* F3) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite F3
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
      simp)⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum n F hn3).isFiniteType
    (Dv := (Spin.plusDatum n F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin n) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := F) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  have hroot : ∃ c : Fin n, edgeD n ⟨0, by omega⟩ c ∨ edgeD n c ⟨0, by omega⟩ :=
    ⟨⟨1, by omega⟩, Or.inl (Or.inl ⟨rfl, by change 1 + 1 < n; omega⟩)⟩
  exact weakCT3_simplyLaced_of_equiv e.symm
    (CurtisTits.curtisTitsConclusion_spinPlus hadm hF' hn3)
    (leviConePresented_spinPlus F hn3) hD (rootedTree_edgeD hn4) hroot hgen hcomm
    (fun i j h => (hpair i j h).imp fun W hW =>
      LinearBlockStandardPair.of_ringEquiv e hW)

end CFSG.ClassicalInvolution.Q3.Q3W
