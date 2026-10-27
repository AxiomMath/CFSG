module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Copies

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule


section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem canonMin_conj_xm (w : WeylGroup Tag.E6) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (c : K) :
    canonMin K w * e6Data_valid.xm K γ c * (canonMin K w)⁻¹ = e6Data_valid.xm K (w • γ) c := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  have hcm : canonMin K ((coxeterSystem Tag.E6).wordProd ω) = CurtisE6.nProd K ω :=
    canonMin_wordProd hω
  rw [hcm, wordProd_smul_foldr]
  exact (CurtisE6.nProd_conj_xm hγ c ω).2

theorem orbit_cases : ∀ a : Fin TwistTag.E6.foldedTag.rank,
    ((TwistTag.E6.orbit a).card = 1 ∧ TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a}) ∨
    ((TwistTag.E6.orbit a).card = 2 ∧
      TwistTag.E6.orbit a =
        {TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)} ∧
      TwistTag.E6.orbitMin a ≠ TwistTag.E6.perm (TwistTag.E6.orbitMin a)) := by
  decide

variable (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)

theorem conj_orbit_prod (w : WeylGroup Tag.E6)
    (γ : Fin TwistTag.E6.tag.rank → Fin Tag.E6.rank → ℤ) (hγ : ∀ i, IsRoot Tag.E6 (γ i))
    (hγinj : Function.Injective γ)
    (hcomm : ∀ i ∈ TwistTag.E6.orbit a, ∀ j ∈ TwistTag.E6.orbit a, i ≠ j → ∀ c d : K,
      Commute (e6Data_valid.xm K (γ i) c) (e6Data_valid.xm K (γ j) d))
    (hw : ∀ i ∈ TwistTag.E6.orbit a, ∃ j ∈ TwistTag.E6.orbit a, w • γ i = γ j)
    (c : orbitField TwistTag.E6 K σ a) :
    ∃ c' : orbitField TwistTag.E6 K σ a,
      canonMin K w * ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        e6Data_valid.xm K (γ ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)))
          ((σ ^ k) (c : K))).prod * (canonMin K w)⁻¹ =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        e6Data_valid.xm K (γ ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)))
          ((σ ^ k) (c' : K))).prod := by
  have hmem : TwistTag.E6.orbitMin a ∈ TwistTag.E6.orbit a := TwistTag.E6.orbitMin_mem a
  have hcard := orbit_cases a
  generalize TwistTag.E6.orbitMin a = m at hmem hcard ⊢
  rcases hcard with ⟨h1, h1'⟩ | ⟨h2, h2', hne⟩
  · refine ⟨c, ?_⟩
    obtain ⟨j, hj, hjw⟩ := hw m hmem
    rw [h1'] at hj
    have hjm : j = m := Finset.mem_singleton.1 hj
    rw [hjm] at hjw
    have hr : List.range 1 = [0] := rfl
    rw [h1, hr]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
      Equiv.Perm.coe_one, id_eq, RingHom.one_def, RingHom.id_apply]
    rw [canonMin_conj_xm w (hγ m), hjw]
  · have hmem' : TwistTag.E6.perm m ∈ TwistTag.E6.orbit a := by
      rw [h2']; simp
    have hσσ : ∀ d : orbitField TwistTag.E6 K σ a, σ (σ (d : K)) = d := by
      intro d
      have := mem_orbitField.1 d.2
      rw [h2, pow_two] at this
      exact this
    have hr : List.range 2 = [0, 1] := rfl
    obtain ⟨j0, hj0, e0⟩ := hw m hmem
    obtain ⟨j1, hj1, e1⟩ := hw (TwistTag.E6.perm m) hmem'
    have hj0' := hj0
    have hj1' := hj1
    rw [h2'] at hj0' hj1'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj0' hj1'
    rw [h2, hr]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
      pow_one, Equiv.Perm.coe_one, id_eq, RingHom.one_def, RingHom.id_apply]
    have hsplit : ∀ (x y : ↥(e6Data_valid.minGroup K)),
        canonMin K w * (x * y) * (canonMin K w)⁻¹ =
          (canonMin K w * x * (canonMin K w)⁻¹) * (canonMin K w * y * (canonMin K w)⁻¹) := by
      intro x y; group
    rcases hj0' with h0 | h0 <;> rcases hj1' with h1 | h1 <;> rw [h0] at e0 <;> rw [h1] at e1
    · exact absurd (hγinj (smul_left_cancel w (e0.trans e1.symm))) hne
    · refine ⟨c, ?_⟩
      rw [hsplit, canonMin_conj_xm w (hγ _), canonMin_conj_xm w (hγ _), e0, e1]
    · have hσc : σ (c : K) ∈ orbitField TwistTag.E6 K σ a := by
        refine mem_orbitField.2 ?_
        rw [h2, pow_two]
        show σ (σ (σ (c : K))) = σ (c : K)
        rw [hσσ c]
      refine ⟨⟨σ c, hσc⟩, ?_⟩
      rw [hsplit, canonMin_conj_xm w (hγ _), canonMin_conj_xm w (hγ _), e0, e1]
      show _ * _ = _ * e6Data_valid.xm K (γ (TwistTag.E6.perm m)) (σ (σ (c : K)))
      rw [hσσ c]
      exact ((hcomm _ hmem' _ hmem hne.symm _ _)).eq
    · exact absurd (hγinj (smul_left_cancel w (e0.trans e1.symm))) hne

theorem single_injective {n : ℕ} : Function.Injective (fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [Ne.symm hij] at this

theorem neg_single_injective {n : ℕ} :
    Function.Injective (fun i : Fin n => (-Pi.single i 1 : Fin n → ℤ)) := by
  intro i j h
  exact single_injective (neg_injective h)

end Conj

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twCopiesNormalize_holds : TwCopiesNormalize hf K hK σ hσ := by
  intro a w hw
  have hw' : ∀ i ∈ TwistTag.E6.orbit a, ∃ j ∈ TwistTag.E6.orbit a,
      (w : WeylGroup TwistTag.E6.tag) • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1 := hw
  have hw'' : ∀ i ∈ TwistTag.E6.orbit a, ∃ j ∈ TwistTag.E6.orbit a,
      (w : WeylGroup TwistTag.E6.tag) • (-Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        -Pi.single j 1 := by
    intro i hi
    obtain ⟨j, hj, h⟩ := hw' i hi
    exact ⟨j, hj, by rw [smul_neg, h]⟩
  set nG := (twistedE6CoverData hf hK σ hσ).nhatW w with hnG
  have hle : Subgroup.map (MulAut.conj nG).toMonoidHom (Rhat hf hK σ hσ a).range ≤
      (Rhat hf hK σ hσ a).range := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    refine mem_of_upper_lower (Rhat hf hK σ hσ a).range
      ((MulAut.conj nG).toMonoidHom.comp (Rhat hf hK σ hσ a)) ?_ ?_ g
    · intro c
      obtain ⟨c', hc'⟩ := conj_orbit_prod σ a (w : WeylGroup TwistTag.E6.tag) (fun i => Pi.single i 1)
        (fun i => isRoot_single Tag.E6 i) single_injective
        (fun i hi j hj hij c d => by
          have := commute_slMin (K := K) hi hj hij (uSL c) (uSL d)
          have e1 : e6Data_valid.xm K (Pi.single i 1) c = slMin K i (uSL c) :=
            (slMin_upper i c).symm
          have e2 : e6Data_valid.xm K (Pi.single j 1) d = slMin K j (uSL d) :=
            (slMin_upper j d).symm
          rw [e1, e2]
          exact this) hw' c
      refine ⟨uSL c', Subtype.ext ?_⟩
      show minOrbitHom σ a (uSL c') = canonMin K (w : WeylGroup TwistTag.E6.tag) * minOrbitHom σ a (uSL c) *
        (canonMin K (w : WeylGroup TwistTag.E6.tag))⁻¹
      rw [minOrbitHom_uSL, minOrbitHom_uSL]
      exact hc'.symm
    · intro c
      obtain ⟨c', hc'⟩ := conj_orbit_prod σ a (w : WeylGroup TwistTag.E6.tag) (fun i => -Pi.single i 1)
        (fun i => isRoot_neg_single Tag.E6 i) neg_single_injective
        (fun i hi j hj hij c d => by
          have := commute_slMin (K := K) hi hj hij (vSL c) (vSL d)
          have e1 : e6Data_valid.xm K (-Pi.single i 1) c = slMin K i (vSL c) :=
            (slMin_lower i c).symm
          have e2 : e6Data_valid.xm K (-Pi.single j 1) d = slMin K j (vSL d) :=
            (slMin_lower j d).symm
          rw [e1, e2]
          exact this) hw'' c
      refine ⟨vSL c', Subtype.ext ?_⟩
      show minOrbitHom σ a (vSL c') = canonMin K (w : WeylGroup TwistTag.E6.tag) * minOrbitHom σ a (vSL c) *
        (canonMin K (w : WeylGroup TwistTag.E6.tag))⁻¹
      rw [minOrbitHom_vSL, minOrbitHom_vSL]
      exact hc'.symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj nG).injective]

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
