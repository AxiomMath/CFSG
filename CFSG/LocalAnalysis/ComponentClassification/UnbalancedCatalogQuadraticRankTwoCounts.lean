module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin Module Submodule

section SquareRoot

variable {K : Type*} [Field K]

theorem eq_of_sq_eq_sq_charTwo [CharP K 2] {a b : K} (h : a ^ 2 = b ^ 2) : a = b := by
  have h' : (a - b) ^ 2 = 0 := by
    linear_combination h + (b ^ 2 - a * b) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h')

theorem exists_sq_eq_charTwo [Finite K] [CharP K 2] (a : K) : ∃ s : K, s ^ 2 = a := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' a
  exact ⟨s, by rw [hs, pow_two]⟩

end SquareRoot

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_ne_zero_add_one [Finite V] {p : V → Prop} (h0 : p 0) :
    Nat.card {v : V // p v ∧ v ≠ 0} + 1 = Nat.card {v : V // p v} := by
  classical
  let _ := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  rw [show (Finset.univ.filter fun x : V => p x ∧ x ≠ 0) = (Finset.univ.filter p).erase 0 by
    ext x
    simp [and_comm]]
  exact Finset.card_erase_add_one (by simpa using h0)

theorem card_singular_mul_card [Finite K] [CharP K 2] (Q : QuadraticForm K V)
    {S : Submodule K V} {u : V} (huS : u ∈ S) (hu : Q u = 1) (hSu : ∀ x ∈ S, polar Q x u = 0) :
    Nat.card {x : V // x ∈ S ∧ Q x = 0} * Nat.card K = Nat.card S := by
  choose rt hsq using fun a : K => exists_sq_eq_charTwo a
  have hsq' : ∀ a, rt (a ^ 2) = a := fun a => eq_of_sq_eq_sq_charTwo (hsq _)
  have hQ : ∀ x ∈ S, ∀ a : K, Q (x + a • u) = Q x + a ^ 2 := fun x hx a => by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu, polar_smul_right_eq, hSu x hx]
    ring
  have h2 : ∀ (a : K) (w : V), w + a • u + a • u = w := fun a w => by
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun p => ⟨p.1.1 + p.2 • u, S.add_mem p.1.2.1 (S.smul_mem _ huS)⟩
      invFun := fun x => (⟨x.1 + rt (Q x.1) • u, S.add_mem x.2 (S.smul_mem _ huS), ?_⟩,
        rt (Q x.1))
      left_inv := fun p => ?_
      right_inv := fun x => ?_ }
  · rw [hQ x.1 x.2, hsq]
    exact CharTwo.add_self_eq_zero _
  · obtain ⟨⟨z, hzS, hz⟩, a⟩ := p
    have hza : Q (z + a • u) = a ^ 2 := by rw [hQ z hzS, hz, zero_add]
    refine Prod.ext (Subtype.ext ?_) ?_
    · change z + a • u + rt (Q (z + a • u)) • u = z
      rw [hza, hsq', h2]
    · change rt (Q (z + a • u)) = a
      rw [hza, hsq']
  · exact Subtype.ext (h2 _ _)

theorem map_mem_singularSubspaces {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {k : ℕ} {M : Submodule K V}
    (hM : M ∈ singularSubspaces Q k) : M.map (g : V →ₗ[K] V) ∈ singularSubspaces Q k := by
  refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hM.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearEquiv.coe_coe, map_of_mem hg]
  exact hM.2 x hx

theorem map_inv_map (g : V ≃ₗ[K] V) (M : Submodule K V) :
    (M.map (g : V →ₗ[K] V)).map ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) = M := by
  rw [← map_mul_linearEquiv, inv_mul_cancel]
  exact Submodule.map_id M

theorem le_orthogonal_of_singular [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {M : Submodule K V} (hM : ∀ x ∈ M, Q x = 0) :
    M ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) M ∧
      finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q) M) =
        finrank K V - finrank K M :=
  ⟨fun x hx => LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
      change polarBilin Q y x = 0
      rw [polarBilin_apply_apply]
      exact polar_eq_zero_of_singular hM hy hx,
    LinearMap.BilinForm.finrank_orthogonal hQ M⟩

theorem mem_of_forall_polar_eq_zero [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {M : Submodule K V} (hM : ∀ x ∈ M, Q x = 0)
    (hd : 2 * finrank K M = finrank K V) {x : V} (hx : ∀ m ∈ M, polar Q m x = 0) : x ∈ M := by
  obtain ⟨hle, hdim⟩ := le_orthogonal_of_singular hQ hM
  have heq : M = LinearMap.BilinForm.orthogonal (polarBilin Q) M :=
    eq_of_le_of_finrank_eq hle (by rw [hdim]; omega)
  rw [heq]
  exact LinearMap.BilinForm.mem_orthogonal_iff.2 fun m hm => by
    change polarBilin Q m x = 0
    rw [polarBilin_apply_apply]
    exact hx m hm

theorem two_mul_finrank_le_of_singular [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {M : Submodule K V} (hM : ∀ x ∈ M, Q x = 0) :
    2 * finrank K M ≤ finrank K V := by
  obtain ⟨hle, hdim⟩ := le_orthogonal_of_singular hQ hM
  have := Submodule.finrank_mono hle
  have := Submodule.finrank_le M
  omega

theorem card_lines_le_mul [Finite K] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {M : Submodule K V} (hM : ∀ x ∈ M, Q x = 0) :
    (Nat.card K - 1) * Nat.card {L // L ∈ singularSubspaces Q 1 ∧ L ≤ M} =
      Nat.card K ^ finrank K M - 1 := by
  have : Finite V := Module.finite_of_finite K
  have h := card_singular_vectors Q M
  have hL : Nat.card (singularLinesIn Q M) = Nat.card {L // L ∈ singularSubspaces Q 1 ∧ L ≤ M} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun L => ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h2, h3⟩, h1⟩,
      fun ⟨⟨h2, h3⟩, h1⟩ => ⟨h1, h2, h3⟩⟩)
  rw [← hL, ← h]
  have hv : Nat.card {v : V | v ∈ M ∧ v ≠ 0 ∧ Q v = 0} = Nat.card {x : V // x ∈ M ∧ x ∉ (⊥ :
      Submodule K V)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      simp only [Set.mem_ofPred_eq, mem_bot]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hM v h.1⟩⟩)
  rw [hv, card_mem_not_mem bot_le, finrank_bot, pow_zero]

end General

section Split

variable {r : ℕ} {K : Type*} [Field K]

theorem card_containing_eq_flag (hr : 1 ≤ r) {L : Submodule K (Fin r ⊕ Fin r → K)}
    (hL : L ∈ singularSubspaces (quadPlus r K) 1) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus r K) r ∧ L ≤ M} =
      Nat.card {M // M ∈ singularSubspaces (quadPlus r K) r ∧ flag r K 1 ≤ M} := by
  obtain ⟨g, hg, hgL⟩ := exists_isometry_map_eq hr hL
  refine (Nat.card_congr ((Submodule.orderIsoMapComap g).toEquiv.subtypeEquiv fun M => ?_)).symm
  simp only [RelIso.coe_fn_toEquiv, Submodule.orderIsoMapComap_apply]
  constructor
  · rintro ⟨hM, hF⟩
    refine ⟨map_mem_singularSubspaces hg hM, ?_⟩
    rw [← hgL]
    exact Submodule.map_mono hF
  · rintro ⟨hM, hF⟩
    refine ⟨?_, ?_⟩
    · have h := map_mem_singularSubspaces (inv_mem hg) hM
      rwa [map_inv_map] at h
    · rw [← hgL] at hF
      exact (Submodule.map_le_map_iff_of_injective g.injective _ _).1 hF

theorem card_containing_mul [Finite K] (hr : 1 ≤ r) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus r K) r ∧ flag r K 1 ≤ M} *
        Nat.card (singularSubspaces (quadPlus r K) 1) * (Nat.card K - 1) =
      Nat.card (singularSubspaces (quadPlus r K) r) * (Nat.card K ^ r - 1) := by
  classical
  set 𝓛 := singularSubspaces (quadPlus r K) 1
  set 𝓜 := singularSubspaces (quadPlus r K) r
  let _ := Fintype.ofFinite 𝓛
  let _ := Fintype.ofFinite 𝓜
  let I := {p : 𝓛 × 𝓜 // (p.1 : Submodule K (Fin r ⊕ Fin r → K)) ≤ p.2}
  let fst : I → 𝓛 := fun p => p.1.1
  let snd : I → 𝓜 := fun p => p.1.2
  have hfst : ∀ L : 𝓛, Nat.card {p // fst p = L} =
      Nat.card {M // M ∈ 𝓜 ∧ flag r K 1 ≤ M} := by
    intro L
    rw [← card_containing_eq_flag hr L.2]
    exact Nat.card_congr
      { toFun := fun p => ⟨p.1.1.2, p.1.1.2.2, by
          have h := p.1.2
          have e : p.1.1.1 = L := p.2
          rw [e] at h
          exact h⟩
        invFun := fun M => ⟨⟨(L, ⟨M.1, M.2.1⟩), M.2.2⟩, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨⟨L', M'⟩, h⟩, rfl⟩ := p
          rfl
        right_inv := fun M => rfl }
  have hsnd : ∀ M : 𝓜, (Nat.card K - 1) * Nat.card {p // snd p = M} =
      Nat.card K ^ r - 1 := by
    intro M
    have h := card_lines_le_mul (Q := quadPlus r K) M.2.2
    rw [M.2.1] at h
    rw [← h]
    congr 1
    exact Nat.card_congr
      { toFun := fun p => ⟨p.1.1.1, p.1.1.1.2, by
          have h := p.1.2
          have e : p.1.1.2 = M := p.2
          rw [e] at h
          exact h⟩
        invFun := fun L => ⟨⟨(⟨L.1, L.2.1⟩, M), L.2.2⟩, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨⟨L', M'⟩, h⟩, rfl⟩ := p
          rfl
        right_inv := fun L => rfl }
  have h1 := Nat.card_congr (Equiv.sigmaFiberEquiv fst)
  have h2 := Nat.card_congr (Equiv.sigmaFiberEquiv snd)
  rw [Nat.card_sigma, Finset.sum_congr rfl fun L _ => hfst L, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at h1
  rw [Nat.card_sigma] at h2
  have h3 : (Nat.card K - 1) * Nat.card I = Nat.card 𝓜 * (Nat.card K ^ r - 1) := by
    rw [← h2, Finset.mul_sum, Finset.sum_congr rfl fun M _ => hsnd M, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [← h3, ← h1]
  ring

theorem mem_singularSubspaces_iff_maximal {M : Submodule K (Fin r ⊕ Fin r → K)} :
    M ∈ singularSubspaces (quadPlus r K) r ↔ (∀ x ∈ M, quadPlus r K x = 0) ∧
      ∀ M', M ≤ M' → (∀ x ∈ M', quadPlus r K x = 0) → M' = M := by
  have hQ := nondegenerate_polarBilin_quadPlus r K
  constructor
  · rintro ⟨hd, hs⟩
    refine ⟨hs, fun M' hMM' hM' => ?_⟩
    have h := two_mul_finrank_le_of_singular hQ hM'
    rw [finrank_split] at h
    exact (eq_of_le_of_finrank_le hMM' (by omega)).symm
  · rintro ⟨hs, hmax⟩
    exact ⟨(orthogonal_geometry_split_Witt_flags hQ finrank_split
      ⟨flag r K r, finrank_flag le_rfl, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩).2 M hs
      hmax, hs⟩

end Split

section RankTwo

variable {K : Type*} [Field K] [CharP K 2] {u v : Fin 4 ⊕ Fin 4 → K}

theorem eichler_rankTwo_apply (hu : quadPlus 4 K u = 1) (hv : quadPlus 4 K v = 1)
    (hB : polar (quadPlus 4 K) u v = 0) (x : Fin 4 ⊕ Fin 4 → K) :
    eichler (quadPlus 4 K) (u + v) u x =
      x + polar (quadPlus 4 K) x u • u + polar (quadPlus 4 K) x v • v := by
  have hr : quadPlus 4 K (u + v) = 0 := by
    rw [QuadraticMap.map_add (quadPlus 4 K), hu, hv, hB, add_zero]
    exact CharTwo.add_self_eq_zero 1
  have hru : polar (quadPlus 4 K) (u + v) u = 0 := by
    rw [polar_add_left, polar_self_charTwo, polar_comm, hB, add_zero]
  rw [eichler_apply hr hru, polar_add_right, hu]
  set a := polar (quadPlus 4 K) x u
  set b := polar (quadPlus 4 K) x v
  calc x + (a + b) • u - (a + 1 * (a + b)) • (u + v)
      = x + a • u + b • v - (2 : K) • (a • u + (a + b) • v) := by module
    _ = x + a • u + b • v := by rw [CharTwo.two_eq_zero, zero_smul, sub_zero]

theorem quadPlus_smul_add_smul (hu : quadPlus 4 K u = 1) (hv : quadPlus 4 K v = 1)
    (hB : polar (quadPlus 4 K) u v = 0) (a b : K) :
    quadPlus 4 K (a • u + b • v) = (a + b) ^ 2 := by
  rw [QuadraticMap.map_add (quadPlus 4 K), map_smul_eq_sq, map_smul_eq_sq, hu, hv,
    polar_smul_left_eq, polar_smul_right_eq, hB]
  linear_combination (-(a * b)) * (CharTwo.two_eq_zero : (2 : K) = 0)

end RankTwo

theorem even_split_eight_rank_two_elementary_fixed_counts {K : Type*} [Field K] [Finite K]
    [CharP K 2] {u v : Fin 4 ⊕ Fin 4 → K} (huv : LinearIndependent K ![u, v])
    (hu : quadPlus 4 K u = 1) (hv : quadPlus 4 K v = 1) (hB : polar (quadPlus 4 K) u v = 0) :
    quadPlus 4 K (u + v) = 0 ∧ polar (quadPlus 4 K) (u + v) u = 0 ∧
    ((eichler (quadPlus 4 K) (u + v) u : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      orthElementaryMap (quadPlus 4 K) (u + v) u ∧
    eichler (quadPlus 4 K) (u + v) u ∈ orthElementaryGroup (quadPlus 4 K) ∧
    eichler (quadPlus 4 K) (u + v) u * eichler (quadPlus 4 K) (u + v) u = 1 ∧
    eichler (quadPlus 4 K) (u + v) u ≠ 1 ∧
    (∀ x, eichler (quadPlus 4 K) (u + v) u x =
      x + polar (quadPlus 4 K) x u • u + polar (quadPlus 4 K) x v • v) ∧
    Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
      L.map ((eichler (quadPlus 4 K) (u + v) u : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
        (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
      (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) + Nat.card K ^ 4 ∧
    Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
      M.map ((eichler (quadPlus 4 K) (u + v) u : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
        (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
      2 * (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) ∧
    ∀ M : Submodule K (Fin 4 ⊕ Fin 4 → K), M ∈ singularSubspaces (quadPlus 4 K) 4 ↔
      (∀ x ∈ M, quadPlus 4 K x = 0) ∧
        ∀ M', M ≤ M' → (∀ x ∈ M', quadPlus 4 K x = 0) → M' = M := by
  set Q := quadPlus 4 K with hQdef
  set g := eichler Q (u + v) u with hgdef
  have hQ : (polarBilin Q).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 K
  have hr : Q (u + v) = 0 := by
    rw [QuadraticMap.map_add Q, hu, hv, hB, add_zero]
    exact CharTwo.add_self_eq_zero 1
  have hru : polar Q (u + v) u = 0 := by
    rw [polar_add_left, polar_self_charTwo, polar_comm, hB, add_zero]
  have hg : ∀ x, g x = x + polar Q x u • u + polar Q x v • v := eichler_rankTwo_apply hu hv hB
  have huu : polar Q u u = 0 := polar_self_charTwo Q u
  have hvv : polar Q v v = 0 := polar_self_charTwo Q v
  have hvu : polar Q v u = 0 := by rw [polar_comm, hB]
  have hfix : ∀ x, g x = x ↔ polar Q x u = 0 ∧ polar Q x v = 0 := by
    intro x
    rw [hg, add_assoc, add_eq_left]
    exact ⟨fun h => LinearIndependent.pair_iff.1 huv _ _ h, fun ⟨h1, h2⟩ => by
      rw [h1, h2]
      simp⟩
  have hgg : g * g = 1 := by
    refine LinearEquiv.ext fun x => ?_
    change g (g x) = x
    rw [hg (g x), hg x]
    simp only [polar_add_left, polar_smul_left_eq, huu, hvu, hB, hvv, mul_zero, add_zero]
    calc x + polar Q x u • u + polar Q x v • v + polar Q x u • u + polar Q x v • v
        = x + (polar Q x u + polar Q x u) • u + (polar Q x v + polar Q x v) • v := by module
      _ = x := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_smul,
          zero_smul, add_zero, add_zero]
  have hg1 : g ≠ 1 := by
    intro h
    have hu0 : u ≠ 0 := LinearIndependent.ne_zero 0 huv
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu0
    have h1 := (hfix y).1 (by rw [h]; rfl)
    exact hy (by rw [polar_comm]; exact h1.1)
  set S := LinearMap.BilinForm.orthogonal (polarBilin Q) (span K {u, v}) with hS
  have hmemS : ∀ x, x ∈ S ↔ polar Q x u = 0 ∧ polar Q x v = 0 := by
    intro x
    rw [hS, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := h u (subset_span (by simp))
        change polarBilin Q u x = 0 at this
        rwa [polarBilin_apply_apply, polar_comm] at this
      · have := h v (subset_span (by simp))
        change polarBilin Q v x = 0 at this
        rwa [polarBilin_apply_apply, polar_comm] at this
    · rintro ⟨h1, h2⟩ n hn
      change polarBilin Q n x = 0
      rw [polarBilin_apply_apply]
      obtain ⟨a, b, rfl⟩ := mem_span_pair.1 hn
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q u x,
        polar_comm Q v x, h1, h2, mul_zero, mul_zero, add_zero]
  have hSdim : finrank K S = 6 := by
    have h := LinearMap.BilinForm.finrank_orthogonal hQ (span K {u, v})
    have h2 : finrank K (span K {u, v}) = 2 := by
      have := finrank_span_eq_card huv
      rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
    rw [← hS, h2, finrank_split] at h
    exact h
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hZ : Nat.card {x // x ∈ S ∧ Q x = 0} = Nat.card K ^ 5 := by
    have h := card_singular_mul_card Q (S := S) ((hmemS u).2 ⟨huu, hB⟩) hu
      fun x hx => ((hmemS x).1 hx).1
    rw [Module.natCard_eq_pow_finrank (K := K) (V := S), hSdim, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have hlines : ∀ L : Submodule K (Fin 4 ⊕ Fin 4 → K), L ∈ singularSubspaces Q 1 →
      (L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L ↔ L ≤ S) := by
    intro L hL
    constructor
    · intro hgL
      obtain ⟨x, hxL, hx0⟩ := exists_ne_zero_of_one_le_finrank (T := L) (by rw [hL.1])
      have hspan := span_singleton_eq_of_mem hL.1 hxL hx0
      have hgx : g x ∈ L := by
        rw [← hgL]
        exact Submodule.mem_map_of_mem hxL
      rw [← hspan] at hgx
      obtain ⟨c, hc⟩ := mem_span_singleton.1 hgx
      have hc1 : c = 1 := by
        have h1 : g (g x) = x := by rw [← LinearEquiv.mul_apply, hgg]; rfl
        rw [← hc, map_smul, ← hc, smul_smul] at h1
        have h2 : (c * c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
        have h3 : c * c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hx0)
        exact eq_of_sq_eq_sq_charTwo (by rw [pow_two, h3, one_pow])
      rw [hc1, one_smul] at hc
      rw [← hspan, span_singleton_le_iff_mem, hmemS]
      exact (hfix x).1 hc.symm
    · intro hLS
      refine le_antisymm ?_ fun x hx => ⟨x, hx, (hfix x).2 ((hmemS x).1 (hLS hx))⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, (hfix x).2 ((hmemS x).1 (hLS hx))]
      exact hx
  have hcard1 : Nat.card {L // L ∈ singularSubspaces Q 1 ∧
      L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
      (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) + Nat.card K ^ 4 := by
    have h := card_singular_vectors Q S
    have hL : Nat.card (singularLinesIn Q S) = Nat.card {L // L ∈ singularSubspaces Q 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun L => ⟨fun ⟨h1, h2, h3⟩ =>
        ⟨⟨h2, h3⟩, (hlines L ⟨h2, h3⟩).2 h1⟩,
        fun ⟨⟨h2, h3⟩, h1⟩ => ⟨(hlines L ⟨h2, h3⟩).1 h1, h2, h3⟩⟩)
    have hv0 : Nat.card {v : Fin 4 ⊕ Fin 4 → K | v ∈ S ∧ v ≠ 0 ∧ Q v = 0} + 1 =
        Nat.card K ^ 5 := by
      rw [← hZ, ← card_ne_zero_add_one (p := fun x => x ∈ S ∧ Q x = 0) ⟨zero_mem _, map_zero Q⟩]
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        simp only [Set.mem_ofPred_eq]
        tauto)
    rw [← hL]
    have hq : Nat.card K - 1 + 1 = Nat.card K := by omega
    set q := Nat.card K
    set N := Nat.card (singularLinesIn Q S)
    have key : (q - 1) * N + 1 = (q - 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) + 1 := by
      rw [← h, hv0]
      obtain ⟨p, hp⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      rw [hp]
      simp only [Nat.add_sub_cancel]
      ring
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q - 1) (Nat.add_right_cancel key)
    rw [this]
    ring
  have hmax : ∀ M ∈ singularSubspaces Q 4,
      (M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M ↔ u + v ∈ M) := by
    intro M hM
    constructor
    · intro hgM
      by_contra hrM
      have hN : ∀ m ∈ M, polar Q m u = 0 := by
        intro m hm
        have hgm : g m ∈ M := by
          rw [← hgM]
          exact Submodule.mem_map_of_mem hm
        have hNm : polar Q m u • u + polar Q m v • v ∈ M := by
          have := M.sub_mem hgm hm
          rwa [hg, add_assoc, add_sub_cancel_left] at this
        have hab : polar Q m u = polar Q m v := by
          have h := hM.2 _ hNm
          rw [quadPlus_smul_add_smul hu hv hB] at h
          have h' := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h
          rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
          exact h'
        by_contra hm0
        apply hrM
        rw [← hab, ← smul_add] at hNm
        have := M.smul_mem (polar Q m u)⁻¹ hNm
        rwa [smul_smul, inv_mul_cancel₀ hm0, one_smul] at this
      have huM : u ∈ M := mem_of_forall_polar_eq_zero hQ hM.2
        (by rw [hM.1, finrank_split]) hN
      have := hM.2 u huM
      rw [hu] at this
      exact one_ne_zero this
    · intro hrM
      have hle : M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ≤ M := by
        rintro _ ⟨m, hm, rfl⟩
        have hmr : polar Q m (u + v) = 0 := polar_eq_zero_of_singular hM.2 hm hrM
        rw [polar_add_right] at hmr
        have hab : polar Q m v = polar Q m u := by
          rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
          exact hmr
        rw [LinearEquiv.coe_coe, hg, hab, add_assoc, ← smul_add]
        exact M.add_mem hm (M.smul_mem _ hrM)
      exact eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g M)
  have hr0 : u + v ≠ 0 := by
    intro h
    have := LinearIndependent.pair_iff.1 huv 1 1 (by rw [one_smul, one_smul, h])
    exact one_ne_zero this.1
  have hline : span K {u + v} ∈ singularSubspaces Q 1 :=
    ⟨finrank_span_singleton hr0, fun x hx => by
      obtain ⟨c, rfl⟩ := mem_span_singleton.1 hx
      rw [map_smul_eq_sq, hr, mul_zero]⟩
  have hcard4 : Nat.card {M // M ∈ singularSubspaces Q 4 ∧
      M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
      2 * (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) := by
    have h1 : Nat.card {M // M ∈ singularSubspaces Q 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        Nat.card {M // M ∈ singularSubspaces Q 4 ∧ span K {u + v} ≤ M} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun M => by
        rw [span_singleton_le_iff_mem]
        exact ⟨fun ⟨hM, h⟩ => ⟨hM, (hmax M hM).1 h⟩, fun ⟨hM, h⟩ => ⟨hM, (hmax M hM).2 h⟩⟩)
    rw [h1, card_containing_eq_flag (by norm_num) hline]
    have hinc := card_containing_mul (K := K) (r := 4) (by norm_num)
    have hL : (Nat.card (singularSubspaces (quadPlus 4 K) 1) : ℚ) =
        ((Nat.card K : ℚ) ^ 4 - 1) * ((Nat.card K : ℚ) ^ 3 + 1) / ((Nat.card K : ℚ) - 1) := by
      rw [card_singularSubspaces (K := K) (r := 4) (k := 1) (by norm_num),
        prod_Icc_one_eq_prod_range]
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      norm_num
    have hM : (Nat.card (singularSubspaces (quadPlus 4 K) 4) : ℚ) =
        2 * (((Nat.card K : ℚ) + 1) * ((Nat.card K : ℚ) ^ 2 + 1) *
          ((Nat.card K : ℚ) ^ 3 + 1)) := by
      rw [card_singularSubspaces_top (K := K) (r := 4) (by norm_num),
        prod_Icc_one_eq_prod_range]
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      norm_num
    set N := Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ flag 4 K 1 ≤ M}
    set q := Nat.card K
    have hq : (1 : ℚ) < q := by exact_mod_cast hq1
    have hq1' : (q : ℚ) - 1 ≠ 0 := by linarith
    have hinc' := congrArg (Nat.cast : ℕ → ℚ) hinc
    push_cast [Nat.cast_sub hq1.le, Nat.cast_sub (Nat.one_le_pow 4 q (by omega))] at hinc'
    rw [hL, hM, mul_assoc (N : ℚ), div_mul_cancel₀ _ hq1'] at hinc'
    have hfac : ((q : ℚ) ^ 4 - 1) * ((q : ℚ) ^ 3 + 1) ≠ 0 := by
      have h4 : (1 : ℚ) < (q : ℚ) ^ 4 := one_lt_pow₀ hq (by norm_num)
      have h3 : (0 : ℚ) < (q : ℚ) ^ 3 := by positivity
      exact mul_ne_zero (by linarith) (by linarith)
    have key : (N : ℚ) = 2 * ((q : ℚ) ^ 3 + (q : ℚ) ^ 2 + q + 1) := by
      apply mul_right_cancel₀ hfac
      linear_combination hinc'
    exact_mod_cast key
  exact ⟨hr, hru, LinearMap.ext fun x => by
      rw [LinearEquiv.coe_coe, eichler_apply hr hru]
      rfl,
    eichler_mem_elementaryGroup Q _ _, hgg, hg1, hg, hcard1, hcard4,
    fun M => mem_singularSubspaces_iff_maximal⟩

end CFSG.ComponentClassification.UnbalancedCatalog
