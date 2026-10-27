module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualSph
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualLin
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualAsmData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

section Pure

theorem exists_omega_of_card_four {F : Type} [Field F] [Finite F] (h4 : Nat.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact h4
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro ω _
      by_cases h0 : ω = 0
      · simp [h0]
      · simp [hcon ω h0]
    have hle : Fintype.card F ≤ 2 := by
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    omega
  refine ⟨ω, ?_⟩
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hcard] at this
  have hprod : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd (sub_eq_zero.1 h) hω1
  · exact h

theorem sum_ite_eq_countP {α : Type} {k : Type} [Field k] (l : List α) (p : α → Bool) :
    (l.map fun a => if p a = true then (1 : k) else 0).sum = (l.countP p : k) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a = true
    · simp [h, add_comm]
    · simp [h]

theorem ite_mul_ite_bool {k : Type} [Field k] (a b : Bool) :
    (if a = true then (1 : k) else 0) * (if b = true then (1 : k) else 0) =
      if (a && b) = true then (1 : k) else 0 := by
  cases a <;> cases b <;> simp

theorem natCast_eq_mod_two {k : Type} [Field k] [CharP k 2] (n : ℕ) :
    (n : k) = ((n % 2 : ℕ) : k) := by
  have h2 : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [Nat.cast_add, Nat.cast_mul, h2, zero_mul, add_zero]

@[expose] def entryMat (k : Type) [Field k] : Matrix (Fin ptsW.length) (Fin ptsW.length) k :=
  Matrix.of fun i j => if entry (ptsW.get i).2 (ptsW.get j).2 = true then 1 else 0

end Pure

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))


theorem wordIdx_eq_iff (l l' : List (Fin TwistTag.E6.foldedTag.rank)) (a b : Fin e6Data.d) :
    wordIdx l a = wordIdx l' b ↔ wordIdxN l (a : ℕ) = wordIdxN l' (b : ℕ) := by
  rw [Fin.ext_iff, wordIdx_val l a, wordIdx_val l' b]

@[expose] def ptG (ω : K) (hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ twN0)
    (x : List (Fin 4) × (ℕ × ℕ) × Bool) : ↥(TwistedE6.fixedGroup K σ) :=
  nWord hf hK σ hσ x.1 * hatY hf hK σ hσ twN0 ⟨ptCoef ω x.2.2, hmem _⟩

theorem twChi27_pt_eq_zero_iff (hσ2 : ∀ c, σ c = c ^ 2) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ twN0)
    {x y : List (Fin 4) × (ℕ × ℕ) × Bool} (hx : x ∈ ptsW) (hy : y ∈ ptsW) :
    twChi27 σ (nWord hf hK σ hσ w0word * (ptG hf hK σ hσ ω hmem x)⁻¹ *
        ptG hf hK σ hσ ω hmem y) = 0 ↔ ¬ (entry x.2 y.2 = true) := by
  unfold ptG
  rw [twChi27_entry hf hK σ hσ w0word wordIdx_w0word_lw x.1 y.1 ⟨ptCoef ω x.2.2, hmem _⟩
    ⟨ptCoef ω y.2.2, hmem _⟩]
  obtain ⟨-, -, hx26, hx25⟩ := ptsW_idx hx
  obtain ⟨hy0, hy1, -, -⟩ := ptsW_idx hy
  obtain ⟨-, hxn'⟩ := ptsW_ne hx
  obtain ⟨hyn, -⟩ := ptsW_ne hy
  have hrev := ptsW_rev hx hy
  have eA : (wordIdx x.1 lwIdx = wordIdx y.1 ⟨0, by decide⟩) ↔
      y.2.1.1 = piIdx.getD x.2.1.1 0 := by
    rw [wordIdx_eq_iff x.1 y.1 lwIdx ⟨0, by decide⟩, lwIdx_val]
    show wordIdxN x.1 26 = wordIdxN y.1 0 ↔ _
    rw [hx26, hy0]
    exact eq_comm
  have eB : (wordIdx x.1 lwIdx = wordIdx y.1 idx1) ↔
      y.2.1.2 = piIdx.getD x.2.1.1 0 := by
    rw [wordIdx_eq_iff x.1 y.1 lwIdx idx1, lwIdx_val, idx1_val, hx26, hy1]
    exact eq_comm
  have eC : (wordIdx x.1 lw1Idx = wordIdx y.1 ⟨0, by decide⟩) ↔
      y.2.1.1 = piIdx.getD x.2.1.2 0 := by
    rw [wordIdx_eq_iff x.1 y.1 lw1Idx ⟨0, by decide⟩, lw1Idx_val]
    show wordIdxN x.1 25 = wordIdxN y.1 0 ↔ _
    rw [hx25, hy0]
    exact eq_comm
  have eD : (wordIdx x.1 lw1Idx = wordIdx y.1 idx1) ↔
      y.2.1.2 = piIdx.getD x.2.1.2 0 := by
    rw [wordIdx_eq_iff x.1 y.1 lw1Idx idx1, lw1Idx_val, idx1_val, hx25, hy1]
    exact eq_comm
  dsimp only
  simp only [eA, eB, eC, eD, hσ2]
  exact ptCoef_value_eq_zero_iff hω (y.2.1.1 = piIdx.getD x.2.1.1 0)
    (y.2.1.2 = piIdx.getD x.2.1.1 0) (y.2.1.1 = piIdx.getD x.2.1.2 0)
    (y.2.1.2 = piIdx.getD x.2.1.2 0)
    (fun h => hyn (h.1.trans h.2.symm)) (fun h => hyn (h.1.trans h.2.symm))
    (fun h => hxn' (h.1.symm.trans h.2)) (fun h => hxn' (h.1.symm.trans h.2)) hrev x.2.2 y.2.2

theorem entryMat_mul_self (k : Type) [Field k] [CharP k 2] : entryMat k * entryMat k = 1 := by
  ext i r
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hmem : ∀ j : Fin ptsW.length, (ptsW.get j).2 ∈ pts := fun j => by
    rw [← ptsW_map]
    exact List.mem_map_of_mem (List.get_mem ptsW j)
  set F : List (Fin 4) × (ℕ × ℕ) × Bool → k := fun s =>
    if (entry (ptsW.get i).2 s.2 && entry s.2 (ptsW.get r).2) = true then (1 : k) else 0 with hF
  have h1 : ∀ q : Fin ptsW.length, entryMat k i q * entryMat k q r = F (ptsW.get q) := by
    intro q
    simp only [entryMat, Matrix.of_apply, hF]
    exact ite_mul_ite_bool _ _
  have h2 : ∑ q, entryMat k i q * entryMat k q r = (ptsW.map F).sum :=
    (Finset.sum_congr rfl fun q _ => h1 q).trans (Fin.sum_univ_fun_getElem ptsW F)
  have h3 : ptsW.map F = pts.map (fun t : (ℕ × ℕ) × Bool =>
      if (entry (ptsW.get i).2 t && entry t (ptsW.get r).2) = true then (1 : k) else 0) := by
    rw [← ptsW_map, List.map_map]
    rfl
  rw [h2, h3, sum_ite_eq_countP pts (fun t => entry (ptsW.get i).2 t && entry t (ptsW.get r).2),
    natCast_eq_mod_two]
  have hc := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 entry_sq_eq_one
    (ptsW.get i).2 (hmem i)) (ptsW.get r).2 (hmem r))
  rw [hc]
  by_cases hir : i = r
  · subst hir
    simp
  · have hne : (ptsW.get i).2 ≠ (ptsW.get r).2 := fun h =>
      hir (Fin.ext (ptsW_getElem_snd_inj i.2 r.2 h))
    rw [if_neg hne, if_neg hir]
    simp

theorem twF1Residual_holds : TwF1Residual hf K hK σ hσ := by
  unfold TwF1Residual
  intro hf1 k _ _ _ _ m ρ y χ J hρ _ ht hJ hχ
  subst hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card K = 4 := by rw [hK, hf1]; norm_num
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c, hf1]; norm_num
  obtain ⟨ω, hω⟩ := exists_omega_of_card_four hK4
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ twN0 := fun c => by
    rw [mem_orbitField, orbit_card_twN0, pow_two]
    exact sigma_sigma_eq hK σ hσ c
  obtain ⟨fm, hfm, hfy⟩ := (twistedE6CoverData hf hK σ hσ).datum.exists_form hρ ht.1 ht.2.1
  have hentry : ∀ i j : Fin ptsW.length,
      fm (ρ (nWord hf hK σ hσ w0word * (ptG hf hK σ hσ ω hmem (ptsW.get i))⁻¹)
        (ρ (ptG hf hK σ hσ ω hmem (ptsW.get j)) y)) = entryMat k i j := by
    intro i j
    have hz := twChi27_pt_eq_zero_iff hf hK σ hσ hσ2 hω hmem (List.get_mem ptsW i)
      (List.get_mem ptsW j)
    rw [← Module.End.mul_apply, ← map_mul,
      form_eq_ite_twChi27 hf hK σ hσ hρ ht hχ hfm hfy]
    by_cases hE : entry (ptsW.get i).2 (ptsW.get j).2 = true
    · have hne : ¬ twChi27 σ (nWord hf hK σ hσ w0word * (ptG hf hK σ hσ ω hmem (ptsW.get i))⁻¹ *
          ptG hf hK σ hσ ω hmem (ptsW.get j)) = 0 := fun h0 => hz.1 h0 hE
      rw [if_neg hne]
      simp only [entryMat, Matrix.of_apply, if_pos hE]
    · have h0 := hz.2 hE
      rw [if_pos h0]
      simp only [entryMat, Matrix.of_apply, if_neg hE]
  have hU : IsUnit (Matrix.of fun i j : Fin ptsW.length =>
      ((fm : (Fin m → k) →ₗ[k] k) ∘ₗ
        ρ (nWord hf hK σ hσ w0word * (ptG hf hK σ hσ ω hmem (ptsW.get i))⁻¹))
        (ρ (ptG hf hK σ hσ ω hmem (ptsW.get j)) y)) := by
    have hEq : (Matrix.of fun i j : Fin ptsW.length =>
        ((fm : (Fin m → k) →ₗ[k] k) ∘ₗ
          ρ (nWord hf hK σ hσ w0word * (ptG hf hK σ hσ ω hmem (ptsW.get i))⁻¹))
          (ρ (ptG hf hK σ hσ ω hmem (ptsW.get j)) y)) = entryMat k := by
      ext i j
      exact hentry i j
    rw [hEq]
    exact ⟨⟨entryMat k, entryMat k, entryMat_mul_self k, entryMat_mul_self k⟩, rfl⟩
  have hli := linearIndependent_of_pairing
    (fun j : Fin ptsW.length => ρ (ptG hf hK σ hσ ω hmem (ptsW.get j)) y)
    (fun i : Fin ptsW.length => (fm : (Fin m → k) →ₗ[k] k) ∘ₗ
      ρ (nWord hf hK σ hσ w0word * (ptG hf hK σ hσ ω hmem (ptsW.get i))⁻¹)) hU
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fin_fun, Fintype.card_fin, ptsW_length] at hcard
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
