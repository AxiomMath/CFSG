module

public import CFSG.LargeExtraspecial.DWFldOrthGeom
public import CFSG.LargeExtraspecial.DWFldLinear
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.LargeExtraspecial.DW

open Matrix QuadraticMap Module CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section Dickson

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem commutator_le_omegaGroup (hQ : Q.polarBilin.Nondegenerate) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      omegaGroup Q hQ := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  set g' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨g, hg⟩
  set h' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨h, hh⟩
  have hker : g' * h' * g'⁻¹ * h'⁻¹ ∈ (dicksonHom Q hQ).ker := by
    rw [MonoidHom.mem_ker, ← commutatorElement_def, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at hker
  rw [commutatorElement_def]
  exact hker

theorem not_line_of_mem_commutator (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (ht1 : t ≠ 1) (w₀ : V) : ¬ ∀ y, t y - y ∈ K ∙ w₀ := by
  intro h
  have heven := (commutator_le_omegaGroup hQ ht).2
  have hle : commSpace t ≤ K ∙ w₀ := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.1 hx
    exact h v
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_le_card (R := K) ({w₀} : Set V)
  have h3 := one_le_finrank_commSpace ht1
  rw [Set.toFinset_singleton, Finset.card_singleton] at h2
  have : finrank K (commSpace t) = 1 := by omega
  rw [this] at heven
  exact Nat.not_even_one heven

theorem exists_singular_of_pairs {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (htt : t * t = 1) (ht1 : t ≠ 1) (P P' : HypPair Q) (hPP' : P.Orth P')
    (hmove : t P.e - P.e ≠ 0 ∨ t P.f - P.f ≠ 0) :
    ∃ u, Q u = 0 ∧ Q (t u - u) = 0 ∧ t u - u ≠ 0 := by
  have hsq : ∀ a : K, ∃ r, r * r = a := exists_sq_eq_of_charTwo
  have hO := (commutator_le_omegaGroup hQ).trans (omegaGroup_le Q hQ) ht
  rcases hmove with h | h
  · rcases exists_singular_or_line hsq hQ hO htt P.Q_e P.Q_f P.polar_ef P'.Q_e P'.Q_f
      P'.polar_ef (by rw [polar_comm]; exact hPP'.ee) (by rw [polar_comm]; exact hPP'.ef)
      (by rw [polar_comm]; exact hPP'.fe) (by rw [polar_comm]; exact hPP'.ff) h with h' | ⟨w₀, hw₀⟩
    · exact h'
    · exact absurd hw₀ (not_line_of_mem_commutator hQ ht ht1 w₀)
  · rcases exists_singular_or_line hsq hQ hO htt P.Q_f P.Q_e P.polar_fe P'.Q_e P'.Q_f
      P'.polar_ef (by rw [polar_comm]; exact hPP'.fe) (by rw [polar_comm]; exact hPP'.ff)
      (by rw [polar_comm]; exact hPP'.ee) (by rw [polar_comm]; exact hPP'.ef) h with h' | ⟨w₀, hw₀⟩
    · exact h'
    · exact absurd hw₀ (not_line_of_mem_commutator hQ ht ht1 w₀)

end Dickson

section Generic

variable {X : Type} [Group X] {D : Set X} {K : Type} [Field K] [CharP K 2]
  {σ : Type} [Fintype σ] [DecidableEq σ] {Q : QuadraticForm K (σ → K)} {Q₀ : (σ → K) → K}

omit [CharP K 2] in
theorem eq_one_of_mulVec_eq {M : Matrix σ σ K} (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  simpa [one_apply, Pi.single_apply, eq_comm] using this

theorem false_of_statedProj_statedOmega [Finite X] (hQ₀ : ⇑Q = Q₀)
    (hQ : Q.polarBilin.Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hpair : ∀ t : (σ → K) ≃ₗ[K] (σ → K),
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
        t * t = 1 → t ≠ 1 → ∃ u, Q u = 0 ∧ Q (t u - u) = 0 ∧ t u - u ≠ 0)
    (e : X ≃* StatedProj (StatedOmega Q₀)) (hD : IsTransClass34 D) : False := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨B, hBD, ⟨l, hl⟩, hB1⟩ := hD.exists_lift e
  set M : Matrix σ σ K := ((B : GL σ K) : Matrix σ σ K) with hMdef
  have hcomm : ∀ g : GL σ K, g ∈ StatedOmega Q₀ ↔ toLinEquiv σ K g ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    intro g
    rw [statedOmega_eq_comap hQ₀]
    rfl
  have hcO : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    (commutator_le_omegaGroup hQ).trans (omegaGroup_le Q hQ)
  have hσ : Nonempty σ := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hB1 0 (Subsingleton.elim _ _)
  have hl1 : l = 1 := by
    obtain ⟨v, hv⟩ := exists_map_ne_zero hQ
    have hO2 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (hcO ((hcomm _).1 (B * B).2)) v
    rw [toLinEquiv_apply, hl, smul_mulVec, one_mulVec, QuadraticMap.map_smul, smul_eq_mul] at hO2
    have hll : l * l = 1 := by
      have : (l * l - 1) * Q v = 0 := by linear_combination hO2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)
    have h' : (l - 1) ^ 2 = 0 := by linear_combination hll + (1 - l) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h')
  have hMM : M * M = 1 := by
    have : (((B * B : StatedOmega Q₀) : GL σ K) : Matrix σ σ K) = M * M := by simp [hMdef]
    rw [← this, hl, hl1, one_smul]
  have hM1 : M ≠ 1 := fun h => hB1 1 (by rw [h, one_smul])
  set t := toLinEquiv σ K (B : GL σ K) with htdef
  have htv : ∀ v, t v = M *ᵥ v := fun v => by rw [htdef, toLinEquiv_apply]
  have ht : t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := (hcomm _).1 B.2
  have htt : t * t = 1 := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, htv, htv, mulVec_mulVec, hMM, one_mulVec, LinearEquiv.coe_one,
      id_eq]
  have ht1 : t ≠ 1 := fun h => hM1 (eq_one_of_mulVec_eq fun v => by
    rw [← htv, h, LinearEquiv.coe_one, id_eq])
  obtain ⟨u, hu, hQNu, hNu⟩ := hpair t ht htt ht1
  obtain ⟨z, hzu, hhu, hhw⟩ := exists_eichler_plane hQ (hcO ht) htt hu hQNu hNu s
  have hEz : eichler Q u z ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := hE ▸ eichler_mem_elementaryGroup Q u z
  let C : StatedOmega Q₀ := ⟨(toLinEquiv σ K).symm (eichler Q u z), (hcomm _).2 (by simpa)⟩
  have hCv : ∀ v, ((C : GL σ K) : Matrix σ σ K) *ᵥ v = eichler Q u z v := by
    intro v
    rw [← toLinEquiv_apply]
    simp [C]
  have hCi : (((C⁻¹ : StatedOmega Q₀) : GL σ K) : Matrix σ σ K) *
      ((C : GL σ K) : Matrix σ σ K) = 1 := by
    simp
  have hBw : M *ᵥ (t u - u) = t u - u := by
    have := commSpace_le_fixSpace htt (sub_mem_commSpace t u)
    rw [mem_fixSpace] at this
    rw [← htv, this]
  have hBu : M *ᵥ u = u + (t u - u) := by rw [← htv]; abel
  have hind := independent_of_pair hNu hBw hBu
  refine hD.false_of_statedProj e hBD (C := C) fun k hk1 hk4 hmem => ?_
  obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hmem
  exact conj_pow_ne_smul_one hCi hind hs0 hs1 hBw hBu (by rw [hCv, hhw]) (by rw [hCv, hhu])
    hk1 hk4 c (by simpa [mul_assoc] using hc)

end Generic

section Models

variable {X : Type} [Group X] {D : Set X} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem eq_one_of_fix_single {ι : Type} [Fintype ι] [DecidableEq ι]
    {t : (ι → K) ≃ₗ[K] (ι → K)} (h : ∀ k, t (Pi.single k 1) = Pi.single k 1) : t = 1 := by
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun K ι).ext fun k => ?_
  rw [Pi.basisFun_apply, LinearEquiv.coe_coe, h]
  rfl

theorem exists_singular_quadPlus (hn : 2 ≤ n) {t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (ht : t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ u, quadPlus n K u = 0 ∧ quadPlus n K (t u - u) = 0 ∧ t u - u ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, t (plusPair K i).e - (plusPair K i).e ≠ 0 ∨
      t (plusPair K i).f - (plusPair K i).f ≠ 0 := by
    by_contra! h
    apply ht1
    apply eq_one_of_fix_single
    rintro (k | k)
    · exact sub_eq_zero.1 (h k).1
    · exact sub_eq_zero.1 (h k).2
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  obtain ⟨j, hij⟩ := exists_ne i
  exact exists_singular_of_pairs (nondegenerate_polarBilin_quadPlus n K) ht htt ht1 _ _
    (plusPair_orth hij.symm) hi

theorem exists_singular_quadMinus (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)}
    (ht : t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆) (htt : t * t = 1)
    (ht1 : t ≠ 1) :
    ∃ u, quadMinus n K b c u = 0 ∧ quadMinus n K b c (t u - u) = 0 ∧ t u - u ≠ 0 := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  by_cases hmove : ∃ i : Fin (n - 1), t (minusPair K b c i).e - (minusPair K b c i).e ≠ 0 ∨
      t (minusPair K b c i).f - (minusPair K b c i).f ≠ 0
  · obtain ⟨i, hi⟩ := hmove
    have : Nontrivial (Fin (n - 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
    obtain ⟨j, hij⟩ := exists_ne i
    exact exists_singular_of_pairs hQ ht htt ht1 _ _ (minusPair_orth hij.symm) hi
  push Not at hmove
  exfalso
  have hO := (commutator_le_omegaGroup hQ).trans (omegaGroup_le _ hQ) ht
  have hn' : 0 < n - 1 := by omega
  have htail : ∀ y, t y - y ∈ tailSpace (minusFamily K b c hn') (n - 1) := by
    intro y
    rw [mem_tailSpace]
    intro i hi
    rw [minusFamily_of_lt hn' hi]
    obtain ⟨h1, h2⟩ := hmove ⟨i, hi⟩
    refine ⟨?_, ?_⟩
    · rw [← polar_sub_eq_polar_sub hO htt, h1, polar_zero_left]
    · rw [← polar_sub_eq_polar_sub hO htt, h2, polar_zero_left]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, t y₀ - y₀ ≠ 0 := by
    by_contra! h
    exact ht1 (LinearEquiv.ext fun y => by
      rw [LinearEquiv.coe_one, id_eq]
      exact sub_eq_zero.1 (h y))
  apply not_line_of_mem_commutator hQ ht ht1 (t y₀ - y₀)
  intro y
  obtain ⟨a, ha⟩ := exists_eq_smul_of_mem_tailSpace_minusFamily (CharP.cast_eq_zero K 2) hirr hn'
    (htail y₀) hy₀ (htail y)
    (polar_commSpace_eq_zero hO htt (sub_mem_commSpace t y₀) (sub_mem_commSpace t y))
  rw [ha, Submodule.mem_span_singleton]
  exact ⟨a, rfl⟩

omit [Finite K] [CharP K 2] in
theorem false_of_lieModel_POmegaPlus [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : LieModel X .POmegaPlus n 2 f) (hD : IsTransClass34 D) : False := by
  rcases h with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hcl
    have := charP_two_of_card_eq hK
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_card hK hf
    exact false_of_statedProj_statedOmega (coe_quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
      (commutator_orthogonalGroup_quadPlus (by omega)) hs0 hs1
      (fun t ht htt ht1 => exists_singular_quadPlus (by omega) ht htt ht1) e hD
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

omit [Finite K] [CharP K 2] in
theorem false_of_lieModel_POmegaMinus [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : LieModel X .POmegaMinus n 2 f) (hD : IsTransClass34 D) : False := by
  rcases h with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hcl
    have := charP_two_of_card_eq hK
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_card hK hf
    exact false_of_statedProj_statedOmega (coe_quadMinus n K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (commutator_orthogonalGroup_quadMinus hn hirr) hs0 hs1
      (fun t ht htt ht1 => exists_singular_quadMinus hn hirr ht htt ht1) e hD
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end Models

end CFSG.LargeExtraspecial.DW
