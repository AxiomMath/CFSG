module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalKempf
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalGroup
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLift

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem le_normalizer_inf_centralizer {G : Type*} [Group G] {S X : Subgroup G} (hSX : S ≤ X) :
    S ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun s hs c hc => by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (hSX hs) (Subgroup.mem_inf.1 hc).1)
      (inv_mem (hSX hs)), Subgroup.mem_centralizer_iff.2 fun s' hs' => ?_⟩
    have ht : s⁻¹ * s' * s ∈ S := mul_mem (mul_mem (inv_mem hs) hs') hs
    have hct := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 _ ht
    calc s' * (s * c * s⁻¹) = s * ((s⁻¹ * s' * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * s' * s)) * s⁻¹ := by rw [hct]
      _ = s * c * s⁻¹ * s' := by group

theorem eq_bot_of_normal_centralizer
    [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {S : Subgroup (ModGL τ K)}
    (hSG : S ≤ adjointGroup τ K) (hodd : Odd (Nat.card S)) {N : Subgroup (ModGL τ K)}
    (hNC : N ≤ adjointGroup τ K ⊓ Subgroup.centralizer (S : Set (ModGL τ K)))
    (hNn : (N.subgroupOf (adjointGroup τ K ⊓ Subgroup.centralizer (S : Set (ModGL τ K)))).Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  by_contra hN
  have := finite_modGL (τ := τ) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN := (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).1 hNn
  obtain ⟨R, hRC, hCR, hSR, hR2, hR⟩ :=
    exists_invariant_isPGroup (le_normalizer_inf_centralizer hSG) hNC hCN hN2 hN
  obtain ⟨g, hg, J, hP, hQ⟩ := exists_optimal_radical_ordinary (hRC.trans inf_le_left) hR2 hR
  have hS₁P : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ parabolicSubgroup τ K J := by
    rintro _ ⟨s, hs, rfl⟩
    have := hP s (hSG hs) (hSR hs)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  obtain ⟨hQP, -, -, -, hQM, -, hdec, -⟩ := parabolic_root_radical_Levi_factors τ K J
  have hQ2 : IsPGroup 2 (parabolicRadical τ K J) :=
    (isPGroup_posUnipotent 2 τ).to_le (parabolicRadical_le_posUnipotent J)
  have hS₁odd : ¬ 2 ∣ Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd)
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement hQ2 hQP
    (parabolicSubgroup_le_normalizer_parabolicRadical J) hQM
    (fun x hx => by
      obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdec x hx
      exact ⟨qm.1, hq, qm.2, hm, hx.symm⟩) hS₁P hS₁odd
  have hyP : y ∈ parabolicSubgroup τ K J := hQP hyQ
  set h := y * g⁻¹ with hh
  have hSh : S.map (MulAut.conj h).toMonoidHom ≤ parabolicLevi τ K J := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : (MulAut.conj y).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom s) ∈
        parabolicLevi τ K J :=
      hyM (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs))
    have e : (MulAut.conj h).toMonoidHom s =
        (MulAut.conj y).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom s) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hh]
      group
    rw [e]
    exact h1
  obtain ⟨⟨u, huR⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR
  have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
  have hu₂ : h * u * h⁻¹ ∈ parabolicRadical τ K J := by
    have h1 := (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical J hyP) _).1 (hQ u huR)
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
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical hτ hSh hodd' hu₂ hu₂1 hu₂fix
  have hvG : v ∈ adjointGroup τ K := rootSpan_le_adjointGroup K _ hvQ
  have hhG : h ∈ adjointGroup τ K :=
    mul_mem (parabolicSubgroup_le_adjointGroup τ K J hyP) (inv_mem hg)
  have hv'C : h⁻¹ * v * h ∈ adjointGroup τ K ⊓ Subgroup.centralizer (S : Set (ModGL τ K)) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hhG) hvG) hhG,
      Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have h1 := hvfix _ (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    calc s * (h⁻¹ * v * h) = h⁻¹ * (h * s * h⁻¹ * v * (h * s * h⁻¹)⁻¹) * h * s := by group
      _ = h⁻¹ * v * h * s := by rw [h1]
  have hvP' := hP _ (Subgroup.mem_inf.1 hv'C).1 (hCR hv'C)
  have hvP : v ∈ parabolicSubgroup τ K J := by
    have e : v = y * (g⁻¹ * (h⁻¹ * v * h) * g) * y⁻¹ := by rw [hh]; group
    rw [e]
    exact mul_mem (mul_mem hyP hvP') (inv_mem hyP)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)

end CFSG.LieType.Chevalley.EvenOddRadical
