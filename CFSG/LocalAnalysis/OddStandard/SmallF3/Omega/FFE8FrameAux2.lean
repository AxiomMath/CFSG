module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8FrameAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFFE8Frame_main (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {E : Subgroup (OGroup Q)} {t ν : OGroup Q} (h : FFE8VData hQ E t ν)
    (hsignall : ∀ {c : FFE8Idx → ZMod 3} (fr : PFrame Q FFE8Idx c),
      (∀ i, c i = 1 ∨ c i = -1) → ∀ K : Finset FFE8Idx,
        fr.signChange K ∈ omegaGroup hQ ↔
          Even K.card ∧ Even (K.filter fun i => c i = -1).card)
    (hfixE : ∀ e ∈ E, ∀ v ∈ fixSp t, (e : V ≃ₗ[ZMod 3] V) v = v)
    (hlines : ∃ (a b : V) (f : Fin 4 → V) (e₁ e₂ : OGroup Q), e₁ ∈ E ∧ e₂ ∈ E ∧
      a ∈ fixSp t ∧ b ∈ fixSp t ∧ Q a = 1 ∧ Q b = -1 ∧ QuadraticMap.polar Q a b = 0 ∧
      (∀ v ∈ fixSp t, ∃ x y : ZMod 3, v = x • a + y • b) ∧
      (∀ k, f k ∈ commSp t ∧ Q (f k) ≠ 0) ∧
      (∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0) ∧
      LinearIndependent (ZMod 3) f ∧ Submodule.span (ZMod 3) (Set.range f) = commSp t ∧
      (∀ k, (e₁ : V ≃ₗ[ZMod 3] V) (f k) = ![1, -1, 1, -1] k • f k) ∧
      (∀ k, (e₂ : V ≃ₗ[ZMod 3] V) (f k) = ![1, 1, -1, -1] k • f k) ∧
      (∀ e ∈ E, ∀ k, ∃ c : ZMod 3, (e : V ≃ₗ[ZMod 3] V) (f k) = c • f k)) :
    ∃ (ε : ZMod 3) (_ : ε = 1 ∨ ε = -1) (fr : PFrame Q FFE8Idx (ffE8Norm ε)),
      E = ffE8Group fr ∧ t = fr.signChange (ffE8Hat Finset.univ) := by
  obtain ⟨a, b, f, e₁, e₂, he₁, he₂, ha, hb, hQa, hQb, hab, hfix, hf, hff, -, hspan, hs₁, hs₂,
    hsc⟩ := hlines
  have ht : t * t = 1 := h.t_sq
  obtain ⟨B, hBa, hBb, hBf, hBo⟩ :=
    ffOutFFE8Frame_basis hdim ht ha hb hab hfix (fun k => (hf k).1) hff hspan
  have hz : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  have hfixB : ∀ e ∈ E, ∀ m : Fin 2,
      (e : V ≃ₗ[ZMod 3] V) (B (Sum.inl m)) = B (Sum.inl m) := by
    intro e he m
    fin_cases m
    · simpa [hBa] using hfixE e he a ha
    · simpa [hBb] using hfixE e he b hb
  let c0 : FFE8Idx → ZMod 3 := Sum.elim ![1, -1] fun k => Q (f k)
  have hnorm0 : ∀ i, Q (B i) = c0 i := by
    rintro (m | k)
    · fin_cases m
      · simp [c0, hBa, hQa]
      · simp [c0, hBb, hQb]
    · simp [c0, hBf]
  let fr0 : PFrame Q FFE8Idx c0 := ⟨B, hnorm0, hBo⟩
  have hc0 : ∀ i, c0 i = 1 ∨ c0 i = -1 := by
    rintro (m | k)
    · fin_cases m <;> simp [c0]
    · exact hz _ (hf k).2
  have hsign0 := hsignall fr0 hc0
  have hpair1 : Q (f 1) = Q (f 3) := by
    refine ffOutFFE8Frame_pair_norm hQ fr0 hc0 hsign0 (h.le_omega he₁) (i := 1) (j := 3)
      (by decide) (hfixB e₁ he₁) ?_
    intro k
    show (e₁ : V ≃ₗ[ZMod 3] V) (B (Sum.inr k)) = _ • B (Sum.inr k)
    rw [hBf, hs₁ k]
    fin_cases k <;> simp
  have hpair2 : Q (f 2) = Q (f 3) := by
    refine ffOutFFE8Frame_pair_norm hQ fr0 hc0 hsign0 (h.le_omega he₂) (i := 2) (j := 3)
      (by decide) (hfixB e₂ he₂) ?_
    intro k
    show (e₂ : V ≃ₗ[ZMod 3] V) (B (Sum.inr k)) = _ • B (Sum.inr k)
    rw [hBf, hs₂ k]
    fin_cases k <;> simp
  have hte₂ : t * e₂ ∈ E := E.mul_mem h.t_mem he₂
  have hpair3 : Q (f 0) = Q (f 1) := by
    refine ffOutFFE8Frame_pair_norm hQ fr0 hc0 hsign0 (h.le_omega hte₂) (i := 0) (j := 1)
      (by decide) (hfixB _ hte₂) ?_
    intro k
    show (t : V ≃ₗ[ZMod 3] V) ((e₂ : V ≃ₗ[ZMod 3] V) (B (Sum.inr k))) = _ • B (Sum.inr k)
    have htk : (t : V ≃ₗ[ZMod 3] V) (f k) = -f k := (mem_commSp_iff ht).mp (hf k).1
    rw [hBf, hs₂ k, map_zsmul, htk]
    fin_cases k <;> simp
  have hnorm : ∀ k, Q (f k) = Q (f 0) := by
    intro k
    fin_cases k
    · rfl
    · exact hpair3.symm
    · exact hpair2.trans (hpair1.symm.trans hpair3.symm)
    · exact hpair1.symm.trans hpair3.symm
  have hε : Q (f 0) = 1 ∨ Q (f 0) = -1 := hz _ (hf 0).2
  have hnormε : ∀ i, Q (B i) = ffE8Norm (Q (f 0)) i := by
    rintro (m | k)
    · fin_cases m
      · simp [ffE8Norm, hBa, hQa]
      · simp [ffE8Norm, hBb, hQb]
    · simp [ffE8Norm, hBf, hnorm k]
  let fr : PFrame Q FFE8Idx (ffE8Norm (Q (f 0))) := ⟨B, hnormε, hBo⟩
  have hcε : ∀ i, ffE8Norm (Q (f 0)) i = 1 ∨ ffE8Norm (Q (f 0)) i = -1 := by
    rintro (m | k)
    · fin_cases m <;> simp [ffE8Norm]
    · exact hε
  have hsignε := hsignall fr hcε
  refine ⟨Q (f 0), hε, fr, ?_, ?_⟩
  · have hle : E ≤ ffE8Group fr := by
      intro e he
      refine ffOutFFE8Frame_mem_group hQ hε fr hsignε (h.le_omega he) ?_ (hfixB e he) ?_
      · rw [← pow_two]
        exact h.elemAb.1.2 e he
      · intro k
        obtain ⟨c, hc⟩ := hsc e he k
        exact ⟨c, by simpa [fr, hBf] using hc⟩
    haveI : Finite (ffE8Group fr) :=
      Nat.finite_of_card_ne_zero (by rw [ffE8Group_card fr]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [ffE8Group_card fr, h.elemAb.2]; norm_num)
  · refine ffOutFFE8Frame_t_eq fr ht (fun m => ?_) (fun k => ?_)
    · fin_cases m
      · exact hBa ▸ ha
      · exact hBb ▸ hb
    · exact hBf k ▸ (hf k).1

end CFSG.OddStandard.SmallF3.Omega
