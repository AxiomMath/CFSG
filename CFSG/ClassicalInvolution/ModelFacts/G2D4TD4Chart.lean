module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Tori
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Weyl

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Nhat

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def nB : twistedGroup σ := nHat σ (ng 1) * nHat σ (ng 0)

theorem twistedIncl_nB : twistedIncl σ (nB σ) =
    weylElt d4 K (nd 0) 1 * weylElt d4 K (nd 1) 1 * weylElt d4 K (nd 3) 1 *
      weylElt d4 K (nd 2) 1 := by
  rw [nB, map_mul]
  show ((nHatE K (ng 1) : adjointGroup d4 K) : ModGL d4 K) *
    ((nHatE K (ng 0) : adjointGroup d4 K) : ModGL d4 K) = _
  rw [nHatE_zero, nHatE_one]
  rfl

theorem tdNhat_eq_wordProd : tdNhat = (coxeterSystem d4).wordProd [nd 0, nd 1, nd 3, nd 2] := by
  simp only [tdNhat, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_assoc]

theorem isReduced_tdNhat : (coxeterSystem d4).IsReduced [nd 0, nd 1, nd 3, nd 2] :=
  isReduced_of_reducedCheck (by decide +kernel)

theorem canonicalRep_tdNhat : canonicalRep (coxeterSystem d4) K tdNhat = twistedIncl σ (nB σ) := by
  rw [tdNhat_eq_wordProd, canonicalRep_wordProd isReduced_tdNhat, twistedIncl_nB]
  simp [mul_assoc]

end Nhat

section Weyl

variable {K : Type} [Field K]

theorem rootChar_aShortTD4 (v : Fin d4.rank → ℤ) :
    rootChar (aShortTD4 K) v = (-1 : Kˣ) ^ v (nd 2) := by
  rw [rootChar_four, show aShortTD4 K (nd 0) = 1 from rfl, show aShortTD4 K (nd 1) = 1 from rfl,
    show aShortTD4 K (nd 2) = -1 from rfl, show aShortTD4 K (nd 3) = 1 from rfl, one_zpow,
    one_zpow, one_zpow, one_mul, one_mul, mul_one]

theorem rootChar_aLongTD4 (v : Fin d4.rank → ℤ) :
    rootChar (aLongTD4 K) v = (-1 : Kˣ) ^ (v (nd 0) + v (nd 1) + v (nd 3)) := by
  rw [rootChar_four, show aLongTD4 K (nd 0) = -1 from rfl, show aLongTD4 K (nd 1) = -1 from rfl,
    show aLongTD4 K (nd 2) = 1 from rfl, show aLongTD4 K (nd 3) = -1 from rfl, one_zpow,
    mul_one, zpow_add, zpow_add]

theorem tdNhat_inv_smul_zero :
    tdNhat⁻¹ • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = vd4 (-1) 0 (-1) 0 := by
  rw [tdNhat_inv]
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem tdNhat_inv_smul_one :
    tdNhat⁻¹ • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = vd4 0 (-1) (-1) 0 := by
  rw [tdNhat_inv]
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem tdNhat_inv_smul_two :
    tdNhat⁻¹ • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = vd4 1 1 2 1 := by
  rw [tdNhat_inv]
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem tdNhat_inv_smul_three :
    tdNhat⁻¹ • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = vd4 0 0 (-1) (-1) := by
  rw [tdNhat_inv]
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem weylTuple_tdNhat_aShort : weylTuple tdNhat (aShortTD4 K) = aLongTD4 K := by
  funext i
  match i with
  | ⟨0, _⟩ =>
    show rootChar (aShortTD4 K) (tdNhat⁻¹ • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) = _
    rw [tdNhat_inv_smul_zero, rootChar_aShortTD4]
    show (-1 : Kˣ) ^ (-1 : ℤ) = -1
    simp
  | ⟨1, _⟩ =>
    show rootChar (aShortTD4 K) (tdNhat⁻¹ • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ)) = _
    rw [tdNhat_inv_smul_one, rootChar_aShortTD4]
    show (-1 : Kˣ) ^ (-1 : ℤ) = -1
    simp
  | ⟨2, _⟩ =>
    show rootChar (aShortTD4 K) (tdNhat⁻¹ • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) = _
    rw [tdNhat_inv_smul_two, rootChar_aShortTD4]
    show (-1 : Kˣ) ^ (2 : ℤ) = 1
    simp
  | ⟨3, _⟩ =>
    show rootChar (aShortTD4 K) (tdNhat⁻¹ • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ)) = _
    rw [tdNhat_inv_smul_three, rootChar_aShortTD4]
    show (-1 : Kˣ) ^ (-1 : ℤ) = -1
    simp

theorem weylTwist_tdNhat : weylTwist TwistTag.D4 tdNhat = tdNhat := by
  rw [tdNhat_eq_wordProd, weylTwist_wordProd]
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul]
  revert k
  decide +kernel

theorem tdNhat_smul_zero :
    tdNhat • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = vd4 0 1 1 1 := by
  simp only [tdNhat, mul_smul, simple_smul]
  decide +kernel

end Weyl

section ChartB

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

variable (σ) in
@[expose] def slB : SL(2, K) →* twistedGroup σ :=
  (MulAut.conj (nB σ)).toMonoidHom.comp (slShort σ hσ)

theorem slB_apply (C : SL(2, K)) : slB σ hσ C = nB σ * slShort σ hσ C * (nB σ)⁻¹ := rfl

theorem slB_injective : Function.Injective (slB σ hσ) :=
  (MulAut.conj (nB σ)).injective.comp (slShort_injective hσ)

theorem twistedIncl_slB (C : SL(2, K)) : twistedIncl σ (slB σ hσ C) =
    canonicalRep (coxeterSystem d4) K tdNhat * twistedIncl σ (slShort σ hσ C) *
      (canonicalRep (coxeterSystem d4) K tdNhat)⁻¹ := by
  rw [slB_apply, map_mul, map_mul, map_inv, canonicalRep_tdNhat σ]

include hσ in
theorem slB_neg_one : slB σ hσ (-1) = slLong σ hσ (-1) := by
  apply twistedIncl_injective σ
  rw [twistedIncl_slB, twistedIncl_slShort_neg_one hσ, twistedIncl_slLong_neg_one hσ,
    canonicalRep_conj_rootDiagUnit, weylTuple_tdNhat_aShort]

include hσ in
theorem twistedIncl_slLong_mem_rootSpan (A : SL(2, fixedField σ)) :
    twistedIncl σ (slLong σ hσ A) ∈ rootSpan d4 K
      ({Pi.single (nd 2) 1, -Pi.single (nd 2) 1} : Set (Fin d4.rank → ℤ)) := by
  have h1 : twistedIncl σ (slLong σ hσ A) ∈ nodeGroupTD4 σ (Pi.single (nd 2) 1) := by
    rw [← map_rankOne_long, ModelFacts.rankOne_long_eq_range hσ]
    exact Subgroup.mem_map_of_mem _ ⟨A, rfl⟩
  have h2 := nodeGroupTD4_le_rootSpan σ (Pi.single (nd 2) 1) h1
  rwa [td4Orb_single_two, td4Orb_neg_single_two, Set.singleton_union] at h2

theorem isRoot_gamma3 : IsRoot d4 (vd4 0 1 1 1) := by
  have h := IsRoot.smul (isRoot_single d4 (nd 0)) tdNhat
  rwa [tdNhat_smul_zero] at h

include hσ in
theorem twistedIncl_slB_mem_rootSpan (B : SL(2, K)) :
    twistedIncl σ (slB σ hσ B) ∈ rootSpan d4 K (td4Orb (vd4 0 1 1 1) ∪ td4Orb (-vd4 0 1 1 1)) := by
  have h1 : twistedIncl σ (slShort σ hσ B) ∈ nodeGroupTD4 σ (Pi.single (nd 0) 1) := by
    rw [← map_rankOne_short, ModelFacts.rankOne_short_eq_range hσ]
    exact Subgroup.mem_map_of_mem _ ⟨B, rfl⟩
  have h2 := nodeGroupTD4_le_rootSpan σ (Pi.single (nd 0) 1) h1
  have hS : ∀ α ∈ td4Orb (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) ∪
      td4Orb (-Pi.single (nd 0) 1), IsRoot d4 α := fun α hα =>
    hα.elim (fun h => isRoot_of_mem_td4Orb (isRoot_single d4 (nd 0)) h)
      (fun h => isRoot_of_mem_td4Orb (IsRoot.neg (isRoot_single d4 (nd 0))) h)
  have h3 := (canonical_weyl_root_transport d4 K).1 tdNhat _ hS
  have h4 : twistedIncl σ (slB σ hσ B) ∈
      (rootSpan d4 K (td4Orb (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) ∪
        td4Orb (-Pi.single (nd 0) 1))).map
        (MulAut.conj (canonicalRep (coxeterSystem d4) K tdNhat)).toMonoidHom := by
    rw [twistedIncl_slB]
    exact ⟨_, h2, by simp [MulAut.conj_apply]⟩
  rw [h3, Set.image_union, image_td4Orb weylTwist_tdNhat, image_td4Orb weylTwist_tdNhat,
    tdNhat_smul_zero, smul_neg, tdNhat_smul_zero] at h4
  exact h4

theorem long_orth_list : ∀ δ ∈ ([vd4 0 1 1 1, rho (vd4 0 1 1 1), rho (rho (vd4 0 1 1 1)),
    -vd4 0 1 1 1, -rho (vd4 0 1 1 1), -rho (rho (vd4 0 1 1 1))] : List (Fin d4.rank → ℤ)),
    ∀ γ ∈ ([Pi.single (nd 2) 1, -Pi.single (nd 2) 1] : List (Fin d4.rank → ℤ)),
      γ ≠ δ ∧ γ ≠ -δ ∧ γ + δ ∉ rootFinset d4 := by decide +kernel

theorem long_orth_gamma3 :
    ∀ γ ∈ ({Pi.single (nd 2) 1, -Pi.single (nd 2) 1} : Set (Fin d4.rank → ℤ)),
      ∀ δ ∈ td4Orb (vd4 0 1 1 1) ∪ td4Orb (-vd4 0 1 1 1),
        γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
  intro γ hγ δ hδ
  have hγ' : γ ∈ ([Pi.single (nd 2) 1, -Pi.single (nd 2) 1] : List (Fin d4.rank → ℤ)) := by
    simpa using hγ
  have hδ' : δ ∈ ([vd4 0 1 1 1, rho (vd4 0 1 1 1), rho (rho (vd4 0 1 1 1)),
      -vd4 0 1 1 1, -rho (vd4 0 1 1 1), -rho (rho (vd4 0 1 1 1))] :
      List (Fin d4.rank → ℤ)) := by
    simp only [td4Orb, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, rho_neg] at hδ
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  obtain ⟨h1, h2, h3⟩ := long_orth_list δ hδ' γ hγ'
  exact ⟨h1, h2, fun h => h3 (mem_rootFinset.2 h)⟩

include hσ in
theorem slLong_comm_slB (A : SL(2, fixedField σ)) (B : SL(2, K)) :
    slLong σ hσ A * slB σ hσ B = slB σ hσ B * slLong σ hσ A := by
  apply twistedIncl_injective σ
  rw [map_mul, map_mul]
  refine commute_rootSpan_td4 (S := ({Pi.single (nd 2) 1, -Pi.single (nd 2) 1} :
      Set (Fin d4.rank → ℤ))) (T := td4Orb (vd4 0 1 1 1) ∪ td4Orb (-vd4 0 1 1 1)) ?_ ?_
    long_orth_gamma3 (twistedIncl_slLong_mem_rootSpan hσ A) (twistedIncl_slB_mem_rootSpan hσ B)
  · intro γ hγ
    rcases hγ with rfl | hγ
    · exact isRoot_single d4 (nd 2)
    · rw [Set.mem_singleton_iff] at hγ
      subst hγ
      exact IsRoot.neg (isRoot_single d4 (nd 2))
  · intro δ hδ
    rcases hδ with h | h
    · exact isRoot_of_mem_td4Orb isRoot_gamma3 h
    · exact isRoot_of_mem_td4Orb (IsRoot.neg isRoot_gamma3) h

include hσ in
theorem torus_conj_slB {x : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hx : twistedIncl σ x = rootDiagUnit d4 b) :
    ∃ s : Kˣ, s = b (nd 1) * b (nd 2) * b (nd 3) ∧
      ∀ C : SL(2, K), x * slB σ hσ C * x⁻¹ = slB σ hσ (glConjSL (diagGL s) C) := by
  set x' : twistedGroup σ := (nB σ)⁻¹ * x * nB σ with hx'
  have hx'ι : twistedIncl σ x' = rootDiagUnit d4 (weylTuple tdNhat⁻¹ b) := by
    rw [hx', map_mul, map_mul, map_inv, ← canonicalRep_tdNhat σ, hx]
    have h := canonicalRep_conj_rootDiagUnit (K := K) tdNhat (weylTuple tdNhat⁻¹ b)
    rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one] at h
    rw [← h]
    group
  obtain ⟨s, hs, hconj⟩ := torus_conj_slShort hσ hx'ι
  have hc0 : (weylTuple tdNhat⁻¹ b) (nd 0) = b (nd 1) * b (nd 2) * b (nd 3) := by
    show rootChar b (tdNhat⁻¹⁻¹ • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) = _
    rw [inv_inv, tdNhat_smul_zero, rootChar_four]
    show b (nd 0) ^ (0 : ℤ) * b (nd 1) ^ (1 : ℤ) * b (nd 2) ^ (1 : ℤ) * b (nd 3) ^ (1 : ℤ) = _
    simp
  refine ⟨s, Units.ext (by rw [hs, hc0]), fun C => ?_⟩
  have hxe : x = nB σ * x' * (nB σ)⁻¹ := by rw [hx']; group
  rw [slB_apply, slB_apply, hxe]
  calc nB σ * x' * (nB σ)⁻¹ * (nB σ * slShort σ hσ C * (nB σ)⁻¹) * (nB σ * x' * (nB σ)⁻¹)⁻¹
      = nB σ * (x' * slShort σ hσ C * x'⁻¹) * (nB σ)⁻¹ := by group
    _ = _ := by rw [hconj C]

end ChartB

end CFSG.ClassicalInvolution.G2D4Models
