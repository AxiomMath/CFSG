module

public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic
public import CFSG.LieType.Steinberg.Extras
public import CFSG.LieType.Steinberg.Classical.OrthogonalRoots
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Unipotent

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinPlus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem QuadraticMap

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

@[expose] def plusIdx (m : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl m
  | false => .inr m

@[expose] def plusWt : Fin n ⊕ Fin n → Fin n → ℤ :=
  Sum.elim (fun m => Pi.single m 1) (fun m => Pi.single m (-1))

theorem plusWt_plusIdx (m : Fin n) (r : Bool) :
    plusWt (plusIdx m r) = Pi.single m (boolSign r) := by
  cases r <;> rfl

theorem isCoordFrame_plusFrame : IsCoordFrame (plusFrame n K hn) plusIdx where
  vec_eq m r := by cases r <;> rfl
  polar_eq v m r := by
    cases r
    · rw [plusFrame_vec, plusVec_false, polar_quadPlus_single_inr]
      rfl
    · rw [plusFrame_vec, plusVec_true, polar_quadPlus_single_inl]
      rfl

theorem exists_toStdD_eq_two_smul (hn2 : 2 ≤ n) (a : Fin n) :
    ∃ v, toStdD n v = (2 : ℤ) • Pi.single a 1 := by
  obtain ⟨b, hb⟩ : ∃ b : Fin n, a ≠ b := by
    by_cases ha : a.val = 0
    · exact ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by simp [ha])⟩
    · exact ⟨⟨0, by omega⟩, Fin.ne_of_val_ne (by simpa using ha)⟩
  obtain ⟨γ, -, hγ⟩ := exists_mem_rootsD_toStdD_eq n hb (Or.inl rfl) (Or.inl rfl)
  obtain ⟨δ, -, hδ⟩ := exists_mem_rootsD_toStdD_eq n hb (Or.inl rfl) (Or.inr rfl)
  refine ⟨γ + δ, ?_⟩
  rw [toStdD_add, hγ, hδ, two_smul]
  have h : (Pi.single b (1 : ℤ) + Pi.single b (-1) : Fin n → ℤ) = 0 := by
    rw [← Pi.single_add, add_neg_cancel, Pi.single_zero]
  calc (Pi.single a 1 + Pi.single b 1 + (Pi.single a 1 + Pi.single b (-1)) : Fin n → ℤ)
      = Pi.single a 1 + Pi.single a 1 + (Pi.single b 1 + Pi.single b (-1)) := by abel
    _ = _ := by rw [h, add_zero]

theorem prodInjective (f : (Fin n → ℤ) →+ ℤ) (L : List (Fin n → ℤ)) (hL : L.Nodup)
    (hpos : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanD n) ∅ ∧ 0 < f γ)
    (hsort : L.Pairwise fun γ δ => f γ ≤ f δ) :
    ProdInjectiveFor (plusRootGroup n K hn) L := by
  intro g g' hg hg' hgg
  obtain ⟨μ, hμ⟩ := exists_levelFun (Orthogonal.toStdDHom n) Orthogonal.toStdDHom_injective 2
    (exists_toStdD_eq_two_smul (by omega)) f
  have hcoef : ∀ e : (Fin n → ℤ) → spinGroup (quadPlus n K),
      (∀ γ ∈ L, e γ ∈ plusRootGroup n K hn γ) →
        ∃ c : (Fin n → ℤ) → K, ∀ γ ∈ L, x n K hn γ (c γ) = e γ := by
    intro e he
    have : ∀ γ, ∃ c : K, γ ∈ L → x n K hn γ c = e γ := by
      intro γ
      by_cases hγ : γ ∈ L
      · obtain ⟨c, hc⟩ := ((isParametrization hn) γ (hpos γ hγ).1).1 (e γ) |>.mp (he γ hγ)
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hγ⟩
    choose c hc using this
    exact ⟨c, fun γ hγ => hc γ hγ⟩
  obtain ⟨c, hc⟩ := hcoef g hg
  obtain ⟨d, hd⟩ := hcoef g' hg'
  have hprod : ∀ (e : (Fin n → ℤ) → spinGroup (quadPlus n K)) (c' : (Fin n → ℤ) → K),
      (∀ γ ∈ L, x n K hn γ (c' γ) = e γ) →
        (L.map e).prod = (L.map fun γ => rootElt (plusFrame n K hn) (toStdD n γ) (c' γ)).prod :=
    fun e c' he => congrArg List.prod (List.map_congr_left fun γ hγ => (he γ hγ).symm)
  have hlev : ∀ γ, μ (toStdD n γ) = 2 * f γ := fun γ => hμ γ
  have hcd := eq_of_prod_rootElt_eq (isCoordFrame_plusFrame (K := K) hn) plusWt plusWt_plusIdx μ
    (toStdD n) L hL (fun γ hγ => (isLong_toStdD_iff (by omega)).mpr (hpos γ hγ).1)
    (fun γ _ δ _ h => toStdD_injective n h)
    (fun γ hγ => by
      rw [hlev]
      have := (hpos γ hγ).2
      omega)
    (hsort.imp fun {γ δ} h => by
      rw [hlev, hlev]
      omega)
    c d ((hprod g c hc).symm.trans (hgg.trans (hprod g' d hd)))
  intro γ hγ
  rw [← hc γ hγ, ← hd γ hγ, hcd γ hγ]

end CFSG.LieType.Steinberg.SpinPlus
