module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Vec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n : ℕ}

theorem exists_pair_eq_indF_add (hn : 5 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ (α : Finset (Fin n)) (_ : α.card = 4) (α' : Finset (Fin n)) (_ : α'.card = 4),
      Pi.single i 1 + Pi.single j 1 = indF α + indF α' := by
  classical
  have hc : 3 ≤ (Finset.univ \ {i, j} : Finset (Fin n)).card := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin, Finset.card_pair hij]
    omega
  obtain ⟨T, hTs, hT⟩ := Finset.exists_subset_card_eq hc
  have hiT : i ∉ T := fun h => by
    have := hTs h
    simp at this
  have hjT : j ∉ T := fun h => by
    have := hTs h
    simp at this
  refine ⟨insert i T, by rw [Finset.card_insert_of_notMem hiT, hT], insert j T,
    by rw [Finset.card_insert_of_notMem hjT, hT], funext fun x => ?_⟩
  simp only [Pi.add_apply, Pi.single_apply, indF, Finset.mem_insert]
  by_cases hxi : x = i
  · subst hxi
    simp [hij, hiT]
  · by_cases hxj : x = j
    · subst hxj
      simp [Ne.symm hij, hjT]
    · by_cases hxT : x ∈ T
      · simp [hxi, hxj, hxT]
        decide
      · simp [hxi, hxj, hxT]

theorem fix_vec_of_fix_zBar_gen (hn : 5 ≤ n) {β₁ : MulAut ↥(GBar n)}
    (hβ₁ : ∀ (α : Finset (Fin n)) (h : α.card = 4),
      ((β₁ (zBarG α h) : ↥(GBar n)) : AEQ n) = zBar α h)
    {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0) (g : ↥(GBar n)) (hg : (g : AEQ n) = mkQ n (ofVec v)) :
    ((β₁ g : ↥(GBar n)) : AEQ n) = g := by
  classical
  let P : (Fin n → ZMod 2) → Prop := fun w => ∑ i, w i = 0 ∧
    ∀ g : ↥(GBar n), (g : AEQ n) = mkQ n (ofVec w) → ((β₁ g : ↥(GBar n)) : AEQ n) = g
  have hP0 : P 0 := by
    refine ⟨by simp, fun g hg => ?_⟩
    obtain rfl : g = 1 := Subtype.ext (by rw [hg]; exact map_one (mkQ n))
    rw [map_one]
  have hPadd : ∀ w₁ w₂, P w₁ → P w₂ → P (w₁ + w₂) := by
    intro w₁ w₂ h₁ h₂
    refine ⟨by simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, h₁.1, h₂.1, add_zero],
      fun g hg => ?_⟩
    let g₁ : ↥(GBar n) := ⟨mkQ n (ofVec w₁), ofVec_mem_GBar h₁.1⟩
    let g₂ : ↥(GBar n) := ⟨mkQ n (ofVec w₂), ofVec_mem_GBar h₂.1⟩
    obtain rfl : g = g₁ * g₂ := Subtype.ext (by rw [hg, ofVec_add, map_mul]; rfl)
    rw [map_mul, Subgroup.coe_mul, h₁.2 g₁ rfl, h₂.2 g₂ rfl]
    rfl
  have hP4 : ∀ (α : Finset (Fin n)) (h : α.card = 4), P (indF α) := by
    intro α h
    refine ⟨?_, fun g hg => ?_⟩
    · have h1 : ∑ i, indF α i = ((α.card : ℕ) : ZMod 2) := by
        simp only [indF]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h1, h]
      decide
    · obtain rfl : g = zBarG α h := Subtype.ext (by
        rw [hg]
        show _ = zBar α h
        rw [zBar, zOf_emb_eq])
      exact hβ₁ α h
  have hPpair : ∀ i j : Fin n, P (Pi.single i 1 + Pi.single j 1) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h0 : (Pi.single i 1 + Pi.single i 1 : Fin n → ZMod 2) = 0 :=
        funext fun x => zmod_two_add_self _
      rw [h0]
      exact hP0
    · obtain ⟨α, h, α', h', he⟩ := exists_pair_eq_indF_add hn hij
      rw [he]
      exact hPadd _ _ (hP4 α h) (hP4 α' h')
  set i₀ : Fin n := ⟨0, by omega⟩
  have hdec : v = ∑ i, v i • (Pi.single i 1 + Pi.single i₀ 1 : Fin n → ZMod 2) := by
    rw [Finset.sum_congr rfl fun i _ => smul_add (v i) _ _, Finset.sum_add_distrib,
      ← Finset.sum_smul, hv, zero_smul, add_zero]
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hterm : ∀ i, P (v i • (Pi.single i 1 + Pi.single i₀ 1 : Fin n → ZMod 2)) := by
    intro i
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 (v i) with h | h
    · rw [h, zero_smul]
      exact hP0
    · rw [h, one_smul]
      exact hPpair i i₀
  have hPv : P v := by
    rw [hdec]
    exact Finset.sum_induction _ P hPadd hP0 fun i _ => hterm i
  exact hPv.2 g hg

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
