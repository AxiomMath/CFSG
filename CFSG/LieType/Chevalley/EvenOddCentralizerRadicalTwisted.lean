module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadical

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

theorem isPGroup_negUnipotent
    [Finite K] [CharP K 2] (τ : Tag) :
    IsPGroup 2 (negUnipotent τ K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element τ
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  refine IsPGroup.of_card (n := (n : ℕ) * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) ?_
  rw [card_negUnipotent hmax, Nat.card_eq_fintype_card, hcard, ← pow_mul]

theorem map_twistHom_oppRadical
    (t : TwistTag) (σ : K →+* K)
    (hσ : Function.Surjective σ) (J : Set (Fin t.foldedTag.rank)) :
    (oppRadical t.tag K (t.orbitUnion J)).map (twistHom t K σ) =
      oppRadical t.tag K (t.orbitUnion J) := by
  have hneg : ∀ (π : Equiv.Perm (Fin t.tag.rank)) (α : Fin t.tag.rank → ℤ),
      permLattice π (-α) = -permLattice π α := fun _ _ => rfl
  refine map_twistHom_rootSpan_of_stable hσ (fun _ h => isRoot_of_mem_oppRadicalRoots h)
    (fun α h => ?_) fun α h => ?_
  · show -(permLattice t.perm α) ∈ parabolicRadicalRoots t.tag (t.orbitUnion J)
    rw [← hneg]
    exact permLattice_mem_parabolicRadicalRoots h
  · show -(permLattice t.perm.symm α) ∈ parabolicRadicalRoots t.tag (t.orbitUnion J)
    rw [← hneg]
    exact permLattice_symm_mem_parabolicRadicalRoots h

theorem eq_bot_of_normal_centralizer_twistedE6
    [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) {S : Subgroup (ModGL TwistTag.E6.tag K)}
    (hSG : S ≤ graphFixedRootGroup .E6 K σ.toRingHom) (hodd : Odd (Nat.card S))
    {N : Subgroup (ModGL TwistTag.E6.tag K)}
    (hNC : N ≤ graphFixedRootGroup .E6 K σ.toRingHom ⊓
      Subgroup.centralizer (S : Set (ModGL TwistTag.E6.tag K)))
    (hNn : (N.subgroupOf (graphFixedRootGroup .E6 K σ.toRingHom ⊓
      Subgroup.centralizer (S : Set (ModGL TwistTag.E6.tag K)))).Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  by_contra hN
  have := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  set C₀ := graphFixedRootGroup .E6 K σ.toRingHom with hC₀
  have hCN := (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).1 hNn
  obtain ⟨R, hRC, hCR, hSR, hR2, hR⟩ :=
    exists_invariant_isPGroup (le_normalizer_inf_centralizer hSG) hNC hCN hN2 hN
  obtain ⟨g, hg, J, hP, hQ⟩ :=
    exists_optimal_radical_fixed .E6 σ hσ (hRC.trans inf_le_left) hR2 hR
  set A := TwistTag.E6.orbitUnion J with hA
  have hS₁P : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ graphFixedParabolic .E6 K σ.toRingHom J := by
    rintro _ ⟨s, hs, rfl⟩
    have := hP s (hSG hs) (hSR hs)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -, hdec, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors .E6 K σ J
  have hPQ₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
  have hQ₀A : graphFixedParabolicRadical .E6 K σ.toRingHom J ≤
      parabolicRadical TwistTag.E6.tag K A :=
    inf_le_left
  have hL₀A : graphFixedParabolicLevi .E6 K σ.toRingHom J ≤ parabolicLevi TwistTag.E6.tag K A :=
    inf_le_left
  have hQ₀L₀ : graphFixedParabolicRadical .E6 K σ.toRingHom J ⊓
      graphFixedParabolicLevi .E6 K σ.toRingHom J = ⊥ :=
    eq_bot_iff.2 fun x hx => by
      rw [← parabolicRadical_inf_parabolicLevi (K := K) A]
      exact Subgroup.mem_inf.2 ⟨hQ₀A (Subgroup.mem_inf.1 hx).1, hL₀A (Subgroup.mem_inf.1 hx).2⟩
  have hQ₀2 : IsPGroup 2 (graphFixedParabolicRadical .E6 K σ.toRingHom J) :=
    (isPGroup_posUnipotent 2 TwistTag.E6.tag).to_le
      (hQ₀A.trans (parabolicRadical_le_posUnipotent A))
  have hS₁odd : ¬ 2 ∣ Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd)
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement hQ₀2 hQ₀P hPQ₀ hQ₀L₀
    (fun x hx => by
      obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdec x hx
      exact ⟨qm.1, hq, qm.2, hm, hx.symm⟩) hS₁P hS₁odd
  have hyP : y ∈ graphFixedParabolic .E6 K σ.toRingHom J := hQ₀P hyQ
  have hyC : y ∈ C₀ := graphFixedParabolicRadical_le_graphFixedRootGroup .E6 K σ.toRingHom J hyQ
  set h := y * g⁻¹ with hh
  have hhC : h ∈ C₀ := mul_mem hyC (inv_mem hg)
  have hSh : S.map (MulAut.conj h).toMonoidHom ≤ graphFixedParabolicLevi .E6 K σ.toRingHom J := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : (MulAut.conj y).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom s) ∈
        graphFixedParabolicLevi .E6 K σ.toRingHom J :=
      hyM (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs))
    have e : (MulAut.conj h).toMonoidHom s =
        (MulAut.conj y).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom s) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hh]
      group
    rw [e]
    exact h1
  obtain ⟨⟨u, huR⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR
  have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
  have hu₂ : h * u * h⁻¹ ∈ graphFixedParabolicRadical .E6 K σ.toRingHom J := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hPQ₀ hyP) _).1 (hQ u huR)
    rw [show h * u * h⁻¹ = y * (g⁻¹ * u * g) * y⁻¹ by rw [hh]; group]
    exact h1
  have hu₂1 : h * u * h⁻¹ ≠ 1 := fun h' => hu1' (by
    rw [show u = h⁻¹ * (h * u * h⁻¹) * h by group, h', mul_one, inv_mul_cancel])
  have hu₂fix : ∀ s ∈ S.map (MulAut.conj h).toMonoidHom,
      s * (h * u * h⁻¹) * s⁻¹ = h * u * h⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    have hsu : s * u = u * s :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hRC huR)).2 s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * s * h⁻¹ * (h * u * h⁻¹) * (h * s * h⁻¹)⁻¹ = h * (s * u) * s⁻¹ * h⁻¹ := by group
      _ = h * u * h⁻¹ := by rw [hsu]; group
  have hodd' : Odd (Nat.card (S.map (MulAut.conj h).toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj h).injective]
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical hτ (hSh.trans hL₀A) hodd'
    (hQ₀A hu₂) hu₂1 hu₂fix
  set S' := S.map (MulAut.conj h).toMonoidHom with hS'
  set X := oppRadical TwistTag.E6.tag K A ⊓
    Subgroup.centralizer (S' : Set (ModGL TwistTag.E6.tag K)) with hX
  have hS'Γ : ∀ s ∈ S', twistHom .E6 K σ.toRingHom s = s := by
    intro s hs
    have hsC : s ∈ C₀ := by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      exact mul_mem (mul_mem hhC (hSG hs₀)) (inv_mem hhC)
    exact ((mem_twistedFixedGroup_iff_twistHom .E6 K σ.toRingHom).1
      (graphFixedRootGroup_le .E6 K σ.toRingHom hsC)).2
  have hFQ := map_twistHom_oppRadical TwistTag.E6 σ.toRingHom σ.surjective J
  have hσ' : σ.toRingHom ^ TwistTag.E6.order = 1 := by
    show σ.toRingHom ^ 2 = 1
    rw [pow_two]
    refine RingHom.ext fun c => ?_
    have h2 : σ * σ = 1 := by rw [← pow_two]; exact hσ
    exact congrArg (fun τ : K ≃+* K => τ c) h2
  obtain ⟨w, hwX, hw1, hwF⟩ := exists_fixed_ne_one (X := X)
    ((isPGroup_negUnipotent TwistTag.E6.tag).to_le
      (inf_le_left.trans (oppRadical_le_negUnipotent A)))
    (fun h0 => hv1 (by
      have : v ∈ X := Subgroup.mem_inf.2 ⟨hvQ, Subgroup.mem_centralizer_iff.2 fun s hs =>
        mul_inv_eq_iff_eq_mul.1 (hvfix s hs)⟩
      rw [h0] at this
      exact Subgroup.mem_bot.1 this))
    (twistHom .E6 K σ.toRingHom)
    (fun x hx => Subgroup.mem_inf.2 ⟨by
        rw [← hFQ]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1,
      Subgroup.mem_centralizer_iff.2 fun s hs => by
        have hxs := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 s hs
        rw [← hS'Γ s hs, ← map_mul, ← map_mul, hxs]⟩)
    (fun x _ => twistHom_iterate_order_of_pow_eq_one σ.toRingHom hσ' x)
  have hwG : w ∈ adjointGroup TwistTag.E6.tag K :=
    rootSpan_le_adjointGroup K _ (Subgroup.mem_inf.1 hwX).1
  have hwC : w ∈ C₀ := graphFixedNegUnipotent_le_graphFixedRootGroup .E6 K σ.toRingHom
    (Subgroup.mem_inf.2 ⟨oppRadical_le_negUnipotent A (Subgroup.mem_inf.1 hwX).1,
      (mem_twistedFixedGroup_iff_twistHom .E6 K σ.toRingHom).2 ⟨hwG, hwF⟩⟩)
  have hw'C : h⁻¹ * w * h ∈ C₀ ⊓ Subgroup.centralizer (S : Set (ModGL TwistTag.E6.tag K)) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hhC) hwC) hhC,
      Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hwX).2 _
      (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    calc s * (h⁻¹ * w * h) = h⁻¹ * ((h * s * h⁻¹) * w) * h := by group
      _ = h⁻¹ * (w * (h * s * h⁻¹)) * h := by rw [h1]
      _ = h⁻¹ * w * h * s := by group
  have hwP' := hP _ (Subgroup.mem_inf.1 hw'C).1 (hCR hw'C)
  have hwP : w ∈ graphFixedParabolic .E6 K σ.toRingHom J := by
    have e : w = y * (g⁻¹ * (h⁻¹ * w * h) * g) * y⁻¹ := by rw [hh]; group
    rw [e]
    exact mul_mem (mul_mem hyP hwP') (inv_mem hyP)
  have hwPA : w ∈ parabolicSubgroup TwistTag.E6.tag K A := by
    obtain ⟨qm, ⟨hq, hm, hwqm⟩, -⟩ := hdec w hwP
    rw [hwqm]
    exact mul_mem ((parabolic_root_radical_Levi_factors TwistTag.E6.tag K A).1 (hQ₀A hq))
      (parabolicLevi_le_parabolicSubgroup A (hL₀A hm))
  have h0 := Subgroup.mem_inf.2 ⟨hwPA, (Subgroup.mem_inf.1 hwX).1⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hw1 (Subgroup.mem_bot.1 h0)

end CFSG.LieType.Chevalley.EvenOddRadical
