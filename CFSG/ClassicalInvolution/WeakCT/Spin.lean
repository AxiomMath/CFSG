module

public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.Timmesfeld.RankTwo.LeviData

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

section Tree

@[expose] def parentD (n : ℕ) (k : Fin n) : Fin n :=
  if k.val + 1 = n then ⟨n - 3, by have := k.2; omega⟩ else ⟨k.val - 1, by have := k.2; omega⟩

@[expose] def depthD (n : ℕ) (k : Fin n) : ℕ := if k.val + 1 = n then n - 2 else k.val

theorem val_parentD {n : ℕ} (k : Fin n) :
    (parentD n k).val = if k.val + 1 = n then n - 3 else k.val - 1 := by
  unfold parentD
  split_ifs <;> rfl

theorem rootedTree_edgeD {n : ℕ} (hn : 4 ≤ n) :
    RootedTree (edgeD n) (parentD n) (depthD n) ⟨0, by omega⟩ := by
  have hk0 : ∀ k : Fin n, k ≠ ⟨0, by omega⟩ → k.val ≠ 0 := fun k hk h => hk (Fin.ext h)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 := hk0 k hk
    have h2 := k.2
    have h3 := val_parentD k
    unfold depthD
    split_ifs at h3 ⊢ <;> omega
  · have h1 := hk0 k hk
    have h2 := k.2
    have h3 := val_parentD k
    unfold edgeD
    split_ifs at h3 <;> omega
  · unfold edgeD at hij hji
    omega
  · left
    unfold edgeD at hij
    have h3 := val_parentD j
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · split_ifs at h3 <;> omega

end Tree

section Torus

variable {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)

theorem weylElement_spinPlus (k : Fin n) :
    Steinberg.weylElement (Steinberg.SpinPlus.x n F hn) k 1 = Spin.weylD F hn k := by
  rw [Spin.weylD_eq]
  simp [Steinberg.weylElement, Steinberg.SpinPlus.x_single, Steinberg.SpinPlus.x_neg_single,
    Spin.rankOneD_upperSL2, Spin.rankOneD_lowerSL2]

end Torus

theorem weakCT_spinPlus {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hn3 : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, edgeD n i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (Spin.quadPlus n F))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaPlus n p f ∧
      ∀ k, (CurtisTits.rankOne (Spin.plusDatum n F hn3).rootGroup k).map Ψ = U k := by
  have hn4 : 4 ≤ n := hadm.2.2
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
  exact weakCT_simplyLaced (CurtisTits.curtisTitsConclusion_spinPlus hadm hF hn3)
    (leviConePresented_spinPlus F hn3) hD hq (rootedTree_edgeD hn4) hroot hgen hcomm hpair

end CFSG.ClassicalInvolution.WeakCT
