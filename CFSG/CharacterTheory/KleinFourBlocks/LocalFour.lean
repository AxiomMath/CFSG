module

public import CFSG.CharacterTheory.Semidihedral.Principal.TwoLinearLocalBlocks

public section

open scoped BigOperators Classical

namespace CFSG.KleinFourBlocks

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.TwoLinearLocal
  CFSG.TwoRankLowerBound.Helpers

theorem exists_linear_character_closure_pair {C : Type*} [Group C] {t s : C}
    (hts : t * s = s * t) (ht2 : t * t = 1) (hs2 : s * s = 1) (ht1 : t ≠ 1) (hs1 : s ≠ 1)
    (hst : s ≠ t) (hts1 : t * s ≠ 1) (α β : ℂˣ) (hα : α * α = 1) (hβ : β * β = 1) :
    ∃ lam : ↥(Subgroup.closure ({t, s} : Set C)) →* ℂˣ,
      (∀ h : t ∈ Subgroup.closure ({t, s} : Set C), lam ⟨t, h⟩ = α) ∧
      ∀ h : s ∈ Subgroup.closure ({t, s} : Set C), lam ⟨s, h⟩ = β := by
  classical
  have hts' : s * t = t * s := hts.symm
  have e1 : t * (t * s) = s := by rw [← mul_assoc, ht2, one_mul]
  have e2 : t * s * t = s := by rw [mul_assoc, ← hts, ← mul_assoc, ht2, one_mul]
  have e3 : s * (t * s) = t := by rw [← mul_assoc, ← hts, mul_assoc, hs2, mul_one]
  have e4 : t * s * s = t := by rw [mul_assoc, hs2, mul_one]
  have e5 : t * s * (t * s) = 1 := by rw [mul_assoc, e3, ht2]
  have hts_t : t * s ≠ t := fun h => hs1 (by simpa using h)
  have hts_s : t * s ≠ s := fun h => ht1 (by simpa using h)
  have k1 : α * (α * β) = β := by rw [← mul_assoc, hα, one_mul]
  have k3 : β * (α * β) = α := by rw [mul_left_comm, hβ, mul_one]
  have k4 : α * β * α = β := by rw [mul_right_comm, hα, one_mul]
  have k5 : α * β * β = α := by rw [mul_assoc, hβ, mul_one]
  have k6 : α * β * (α * β) = 1 := by rw [mul_mul_mul_comm, hα, hβ, mul_one]
  let f : C → ℂˣ := fun c => if c = 1 then 1 else if c = t then α else if c = s then β else α * β
  have hf : ∀ a b : C, a ∈ Subgroup.closure ({t, s} : Set C) →
      b ∈ Subgroup.closure ({t, s} : Set C) → f (a * b) = f a * f b := by
    intro a b ha hb
    rcases mem_closure_pair hts ht2 hs2 ha with h1 | h1 | h1 | h1 <;>
      rcases mem_closure_pair hts ht2 hs2 hb with h2 | h2 | h2 | h2 <;>
      rw [h1, h2] <;>
      simp [f, ht2, hs2, hts', e1, e2, e3, e4, e5, ht1, hs1, hts1, hst, hts_t, hts_s,
        hα, hβ, k1, k3, k4, k5, k6]
    exact mul_comm _ _
  refine ⟨MonoidHom.mk' (fun v => f v) (fun a b => hf a b a.2 b.2), ?_, ?_⟩
  · intro h
    simp [f, ht1]
  · intro h
    simp [f, hs1, hst]

theorem central_involution_defect_zero_local_blocks_four_characters_and_section_line
    {C : Type} [Group C] [Fintype C] (basis : FiniteIrreducibleCharacterBasis C)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (t s : C) (htcent : ∀ g : C, g * t = t * g) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hst : s ≠ t) (hgroup : IsPGroup 2 (Subgroup.zpowers s))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers s : Set C)))
    (R : Subgroup C) (hRD : R ≤ Subgroup.centralizer (Subgroup.zpowers s : Set C))
    (hDVR : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C),
      ∃ v ∈ Subgroup.closure ({t, s} : Set C), ∃ r ∈ R, x = v * r)
    (hVR : Subgroup.closure ({t, s} : Set C) ⊓ R = ⊥)
    (y : C) (hyV : y ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set C) : Set C))
    (hys : y * s * y⁻¹ = t * s) (w : ℕ) (hw : 0 < w)
    (n₀ n₁ : localBasis.index)
    (hN1 : ∀ n, n = n₀ ∨ n = n₁ →
      ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C)) (v : C),
        v ∈ Subgroup.closure ({t, s} : Set C) → (x : C) = v * (x' : C) → (x' : C) ∈ R →
          (localBasis.representation n).character x = (localBasis.representation n).character x')
    (hN2 : ∀ n, n = n₀ ∨ n = n₁ → (localBasis.representation n).character 1 = w)
    (hN3 : ∀ n, n = n₀ ∨ n = n₁ →
      ∀ x : Subgroup.centralizer (Subgroup.zpowers s : Set C), (x : C) ∈ R →
        2 ∣ orderOf (x : C) → (localBasis.representation n).character x = 0)
    (hN4 : ∀ x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C),
      (x' : C) = y⁻¹ * x * y →
        (localBasis.representation n₁).character x = (localBasis.representation n₀).character x')
    (hN5 : n₀ ≠ n₁)
    (hN6b : ∀ n, n = n₀ ∨ n = n₁ →
      ∀ lam : ↥(Subgroup.closure ({t, s} : Set C)) →* ℂˣ,
        ∃ ψ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) n,
          ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C))
            (v : ↥(Subgroup.closure ({t, s} : Set C))),
            (x : C) = (v : C) * (x' : C) → (x' : C) ∈ R →
              (localBasis.representation ψ).character x =
                (localBasis.representation n).character x' * (lam v : ℂ))
    (hN6c : ∀ n, n = n₀ ∨ n = n₁ →
      ∀ f : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
        f ∈ coefficientCharacterSpace localBasis
            (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ↔
          ∃ F : ↥(Subgroup.closure ({t, s} : Set C)) → ℂ,
            ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C))
              (v : ↥(Subgroup.closure ({t, s} : Set C))),
              (x : C) = (v : C) * (x' : C) → (x' : C) ∈ R →
                f x = (localBasis.representation n).character x' * F v)
    (label : basis.index)
    (hD : coefficientBlockDefect basis ideal 2 label (Subgroup.closure ({t, s} : Set C)))
    (hfiber : brauerFiberBlocks basis ideal 2 s hgroup localBasis label =
      {coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀,
        coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁}) :
    ∃ (θ : Fin 4 → basis.index) (f : ℕ),
      Function.Injective θ ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ.image θ ∧
      0 < f ∧ (∀ i, Module.finrank ℂ (basis.representation (θ i)).vector = f) ∧
      (basis.representation (θ 0)).character t = f ∧
      (basis.representation (θ 1)).character t = f ∧
      (basis.representation (θ 2)).character t = -(f : ℂ) ∧
      (basis.representation (θ 3)).character t = -(f : ℂ) ∧
      (basis.representation (θ 0)).character s = 2 * (w : ℂ) ∧
      (basis.representation (θ 1)).character s = -(2 * (w : ℂ)) ∧
      (basis.representation (θ 2)).character s = 0 ∧
      (basis.representation (θ 3)).character s = 0 ∧
      (∀ x : C, Odd (orderOf x) → ∀ i i',
        (basis.representation (θ i)).character x = (basis.representation (θ i')).character x) ∧
      (∀ x : C, 4 ∣ orderOf x → ∀ i, (basis.representation (θ i)).character x = 0) ∧
      (∀ x, x ∉ translatedOddSection t →
        ((basis.representation (θ 0)).character + (basis.representation (θ 1)).character -
          (basis.representation (θ 2)).character - (basis.representation (θ 3)).character) x =
            0) ∧
      BlocksInnerProduct ((basis.representation (θ 0)).character +
          (basis.representation (θ 1)).character - (basis.representation (θ 2)).character -
            (basis.representation (θ 3)).character)
        ((basis.representation (θ 0)).character + (basis.representation (θ 1)).character -
          (basis.representation (θ 2)).character - (basis.representation (θ 3)).character) = 4 ∧
      ((basis.representation (θ 0)).character + (basis.representation (θ 1)).character -
          (basis.representation (θ 2)).character - (basis.representation (θ 3)).character) t =
        4 * f ∧
      coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (translatedOddSection t) =
        Submodule.span ℂ {(basis.representation (θ 0)).character +
          (basis.representation (θ 1)).character - (basis.representation (θ 2)).character -
            (basis.representation (θ 3)).character} ∧
      Module.finrank ℂ ↥(coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (translatedOddSection t)) = 1 ∧
      Module.finrank ℂ ↥(coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported {x : C | Odd (orderOf x)}) = 1 := by
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hts : t * s = s * t := (htcent s).symm
  have hVmem : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v = 1 ∨ v = t ∨ v = s ∨ v = t * s :=
    fun v hv => mem_closure_pair hts ht2 hs2 hv
  have hV2 : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v * v = 1 := by
    intro v hv
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ht2
    · exact hs2
    · rw [mul_assoc, ← mul_assoc s, ← hts, mul_assoc, hs2, mul_one, ht2]
  have hsD : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), s * x = x * s := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx s (Subgroup.mem_zpowers s))
  have hVcomm : ∀ v ∈ Subgroup.closure ({t, s} : Set C),
      ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), v * x = x * v := by
    intro v hv x hx
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact (htcent x).symm
    · exact hsD x hx
    · rw [mul_assoc, hsD x hx, ← mul_assoc, ← htcent x, mul_assoc]
  have hys' : y⁻¹ * (t * s) * y = s := by rw [← hys]; group
  have hoddR : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), Odd (orderOf x) →
      x ∈ R := by
    intro x hx hodd
    obtain ⟨v, hv, r, hr, rfl⟩ := hDVR x hx
    have hcomm : Commute v r := hVcomm v hv r (hRD hr)
    obtain ⟨k, hk⟩ := hodd
    have h1 : (v * r) ^ orderOf (v * r) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow, hk] at h1
    have hvk : v ^ (2 * k + 1) = v := by
      rw [pow_succ, pow_mul, pow_two, hV2 v hv, one_pow, one_mul]
    rw [hvk] at h1
    have hvR : v ∈ R := by
      have hv' : v = (r ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [hv']
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hr _)
    have hv1 : v = 1 := by
      have hmem : v ∈ Subgroup.closure ({t, s} : Set C) ⊓ R := ⟨hv, hvR⟩
      rw [hVR, Subgroup.mem_bot] at hmem
      exact hmem
    rw [hv1, one_mul]
    exact hr
  have hyD : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C),
      y⁻¹ * x * y ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcs : s * (y⁻¹ * x * y) = y⁻¹ * x * y * s := by
      have hx1 : x * (t * s) = (t * s) * x := by
        rw [← mul_assoc, htcent x, mul_assoc, ← hsD x hx, ← mul_assoc]
      calc s * (y⁻¹ * x * y) = y⁻¹ * (t * s) * y * (y⁻¹ * x * y) := by rw [hys']
        _ = y⁻¹ * ((t * s) * x) * y := by group
        _ = y⁻¹ * (x * (t * s)) * y := by rw [hx1]
        _ = y⁻¹ * x * y * (y⁻¹ * (t * s) * y) := by group
        _ = y⁻¹ * x * y * s := by rw [hys']
    exact (Commute.zpow_left hcs k).eq
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  have hts1 : t * s ≠ 1 := by
    intro h
    apply hst
    have : s = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_left ht2]
  have hVset : (Subgroup.closure ({t, s} : Set C) : Set C) =
      ((({1, t, s, t * s} : Finset C)) : Set C) := by
    ext v
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · exact hVmem v
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hV4 : Nat.card (Subgroup.closure ({t, s} : Set C)) = 4 := by
    have h : Nat.card (Subgroup.closure ({t, s} : Set C)) =
        Nat.card ((({1, t, s, t * s} : Finset C)) : Set C) := Nat.card_congr (Set.equivOfEq hVset)
    rw [h, Nat.card_eq_card_toFinset, Finset.toFinset_coe]
    have hne1 : (1 : C) ∉ ({t, s, t * s} : Finset C) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ht1, Ne.symm hs1, Ne.symm hts1⟩
    have hnet : t ∉ ({s, t * s} : Finset C) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨Ne.symm hst, fun h => hs1 ?_⟩
      calc s = t⁻¹ * (t * s) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]
    have hnes : s ∉ ({t * s} : Finset C) := by
      simp only [Finset.mem_singleton]
      intro h
      apply ht1
      calc t = t * s * s⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel]
    rw [Finset.card_insert_of_notMem hne1, Finset.card_insert_of_notMem hnet,
      Finset.card_insert_of_notMem hnes, Finset.card_singleton]
  have hVD : ∀ v ∈ Subgroup.closure ({t, s} : Set C),
      v ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : s * v = v * s := by
      rcases hVmem v hv with rfl | rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · exact hts.symm
      · rfl
      · rw [← mul_assoc, ← hts]
    exact (Commute.zpow_left hc k).eq
  have htV : t ∈ Subgroup.closure ({t, s} : Set C) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hsV : s ∈ Subgroup.closure ({t, s} : Set C) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hloc : ∀ n : localBasis.index, (n = n₀ ∨ n = n₁) →
      ∃ a : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
        a ∈ coefficientVirtualLattice localBasis
            (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ∧
        coefficientCharacterSpace localBasis
            (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ⊓
          sectionSupported (involutionLocalSection s) = Submodule.span ℂ {a} ∧
        BlocksInnerProduct a a = 4 ∧
        ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
          a (⟨s, element_mem_centralizer_zpowers s⟩ * r) =
            4 * (localBasis.representation n).character r := by
    intro n hn
    have h1 := hN1 n hn
    have h2 := hN2 n hn
    have h3 := hN3 n hn
    have h6b := hN6b n hn
    have h6c := hN6c n hn
    obtain ⟨αs, hαs⟩ : ∃ αs : Fin 4 → ℂˣ, αs = ![1, -1, 1, -1] := ⟨_, rfl⟩
    obtain ⟨βs, hβs⟩ : ∃ βs : Fin 4 → ℂˣ, βs = ![1, 1, -1, -1] := ⟨_, rfl⟩
    obtain ⟨bz, hbz⟩ : ∃ bz : Fin 4 → ℤ, bz = ![1, 1, -1, -1] := ⟨_, rfl⟩
    choose lam hlamt hlams using fun i : Fin 4 =>
      exists_linear_character_closure_pair hts ht2 hs2 ht1 hs1 hst hts1 (αs i) (βs i)
        (by rw [hαs]; fin_cases i <;> simp) (by rw [hβs]; fin_cases i <;> simp)
    have hsumlam : ∀ v : ↥(Subgroup.closure ({t, s} : Set C)),
        ∑ i : Fin 4, (bz i : ℂ) * (lam i v : ℂ) = if (v : C) = s then 4 else 0 := by
      intro v
      rcases hVmem v v.2 with h | h | h | h
      · have hv : v = 1 := Subtype.ext h
        rw [hv, ite_eq_right (by rw [Subgroup.coe_one]; exact Ne.symm hs1)]
        simp [Fin.sum_univ_four, hbz]
      · have hv : v = ⟨t, htV⟩ := Subtype.ext h
        rw [hv, ite_eq_right (by exact hst.symm)]
        simp only [hlamt _ htV, Fin.sum_univ_four, hαs, hbz]
        simp
      · have hv : v = ⟨s, hsV⟩ := Subtype.ext h
        rw [hv, ite_eq_left rfl]
        simp only [hlams _ hsV, Fin.sum_univ_four, hβs, hbz]
        simp
        norm_num
      · have hv : v = ⟨t, htV⟩ * ⟨s, hsV⟩ := Subtype.ext (by rw [h]; rfl)
        rw [hv, ite_eq_right (by
          change t * s ≠ s
          intro h'
          exact ht1 (by simpa using h'))]
        simp only [map_mul, Units.val_mul, hlamt _ htV, hlams _ hsV, Fin.sum_univ_four, hαs, hβs,
          hbz]
        simp
    choose ψ hψB hψval using fun i : Fin 4 => h6b (lam i)
    obtain ⟨a, ha⟩ : ∃ a : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
        a = fun x => ∑ i : Fin 4, (bz i : ℂ) * (localBasis.representation (ψ i)).character x :=
      ⟨_, rfl⟩
    have hform : ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C))
        (v : ↥(Subgroup.closure ({t, s} : Set C))), (x : C) = (v : C) * (x' : C) →
        (x' : C) ∈ R →
        a x = (localBasis.representation n).character x' * (if (v : C) = s then 4 else 0) := by
      intro x x' v hx hx'
      rw [ha]
      dsimp only
      rw [← hsumlam v, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hψval i x x' v hx hx']
      ring
    have hint : a ∈ coefficientVirtualLattice localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) := by
      have hexpand : a = ∑ i : Fin 4, (bz i) • (localBasis.representation (ψ i)).character := by
        funext x
        rw [ha]
        simp only [Finset.sum_apply, Pi.smul_apply]
        simp only [zsmul_eq_mul]
      rw [hexpand]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨ψ i, hψB i, rfl⟩)
    have hψinj : Function.Injective ψ := by
      intro i j hij
      have hvals : ∀ v : ↥(Subgroup.closure ({t, s} : Set C)), (lam i v : ℂ) = lam j v := by
        intro v
        have e1 := hψval i ⟨v, hVD v v.2⟩ 1 v (by simp) (Subgroup.one_mem _)
        have e2 := hψval j ⟨v, hVD v v.2⟩ 1 v (by simp) (Subgroup.one_mem _)
        rw [hij, e2, h2] at e1
        exact (mul_left_cancel₀ hw0 e1).symm
      have hα : (αs i : ℂ) = αs j := by
        rw [← hlamt i htV, ← hlamt j htV]
        exact hvals ⟨t, htV⟩
      have hβ : (βs i : ℂ) = βs j := by
        rw [← hlams i hsV, ← hlams j hsV]
        exact hvals ⟨s, hsV⟩
      rw [hαs] at hα
      rw [hβs] at hβ
      fin_cases i <;> fin_cases j <;>
        first | rfl | (exfalso; norm_num at hα; done) | (exfalso; norm_num at hβ)
    have hvirt : a ∈ BlocksVChar (Subgroup.centralizer (Subgroup.zpowers s : Set C)) := by
      rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
      exact coefficientVirtualLattice_le_virtual localBasis _ hint
    have hpairL : ∀ g : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
        characterPairing a g =
          ∑ i : Fin 4, (bz i : ℂ) * characterPairing (localBasis.representation (ψ i)).character g := by
      intro g
      rw [ha]
      exact KleinFourColumns.pairing_finset_sum_left Finset.univ (fun i => (bz i : ℂ))
        (fun i => (localBasis.representation (ψ i)).character) g
    have hpa : ∀ i : Fin 4, characterPairing a (localBasis.representation (ψ i)).character =
        bz i := by
      intro i
      rw [hpairL]
      simp [KleinFourColumns.pairing_basis, hψinj.eq_iff]
    have hnorm : BlocksInnerProduct a a = 4 := by
      rw [blocksInnerProduct_eq_characterPairing _ hvirt, hpairL]
      have h : ∀ i : Fin 4, (bz i : ℂ) * characterPairing
          (localBasis.representation (ψ i)).character a = (bz i : ℂ) * bz i := fun i => by
        rw [characterPairing_comm, hpa i]
      rw [Finset.sum_congr rfl fun i _ => h i]
      simp [Fin.sum_univ_four, hbz]
      norm_num
    have hmemspan : a ∈ coefficientCharacterSpace localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) :=
      coefficientVirtualLattice_le_complex_space localBasis _ hint
    have hsupp : ∀ x, x ∉ involutionLocalSection s → a x = 0 := by
      intro x hx
      obtain ⟨v, hv, r, hr, hxr⟩ := hDVR x x.2
      rw [hform x ⟨r, hRD hr⟩ ⟨v, hv⟩ hxr hr]
      by_cases hvs : v = s
      · by_cases hodd : Odd (orderOf r)
        · exfalso
          apply hx
          refine ⟨⟨r, hRD hr⟩, Subtype.ext (by rw [hxr, hvs]; rfl), ?_⟩
          rw [← Subgroup.orderOf_coe]
          exact hodd
        · have h2r : 2 ∣ orderOf r := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
          rw [h3 ⟨r, hRD hr⟩ hr h2r, zero_mul]
      · rw [ite_eq_right hvs, mul_zero]
    have hnotQ : ∀ v : ↥(Subgroup.closure ({t, s} : Set C)), (v : C) ≠ s →
        (⟨v, hVD v v.2⟩ : Subgroup.centralizer (Subgroup.zpowers s : Set C)) ∉
          involutionLocalSection s := by
      rintro v hvs ⟨z, hz, hzodd⟩
      apply hvs
      have hzC : (v : C) = s * (z : C) := congrArg Subtype.val hz
      have hzs : (z : C) = s * v := by
        rw [hzC, ← mul_assoc, hs2, one_mul]
      have hzV : (z : C) ∈ Subgroup.closure ({t, s} : Set C) := by
        rw [hzs]
        exact Subgroup.mul_mem _ hsV v.2
      have hz2 : (z : C) * z = 1 := hV2 _ hzV
      have hzo : orderOf (z : C) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
      have hodd' : Odd (orderOf (z : C)) := by
        rw [Subgroup.orderOf_coe]
        exact hzodd
      have hz1 : orderOf (z : C) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hzo with h | h
        · exact h
        · rw [h] at hodd'
          exact absurd hodd' (by decide)
      rw [hzC, orderOf_eq_one_iff.mp hz1, mul_one]
    have hspan : coefficientCharacterSpace localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ⊓
          sectionSupported (involutionLocalSection s) = Submodule.span ℂ {a} := by
      apply le_antisymm
      · intro f hf
        obtain ⟨hfspan, hfsupp⟩ := Submodule.mem_inf.mp hf
        obtain ⟨F, hF⟩ := (h6c f).mp hfspan
        have hFv : ∀ v : ↥(Subgroup.closure ({t, s} : Set C)), (v : C) ≠ s → F v = 0 := by
          intro v hvs
          have e1 := hF ⟨v, hVD v v.2⟩ 1 v (by simp) (Subgroup.one_mem _)
          rw [hfsupp _ (hnotQ v hvs), h2] at e1
          exact (mul_eq_zero.mp e1.symm).resolve_left hw0
        rw [Submodule.mem_span_singleton]
        refine ⟨F ⟨s, hsV⟩ / 4, ?_⟩
        funext x
        obtain ⟨v, hv, r, hr, hxr⟩ := hDVR x x.2
        have hf1 := hF x ⟨r, hRD hr⟩ ⟨v, hv⟩ hxr hr
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hform x ⟨r, hRD hr⟩ ⟨v, hv⟩ hxr hr]
        by_cases hvs : v = s
        · have hvv : (⟨v, hv⟩ : ↥(Subgroup.closure ({t, s} : Set C))) = ⟨s, hsV⟩ :=
            Subtype.ext hvs
          rw [hf1, hvv]
          rw [ite_eq_left (show ((⟨s, hsV⟩ : ↥(Subgroup.closure ({t, s} : Set C))) : C) = s from rfl)]
          ring
        · rw [hf1, hFv ⟨v, hv⟩ hvs, ite_eq_right hvs]
          ring
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_inf.mpr ⟨hmemspan, hsupp⟩
    refine ⟨a, hint, hspan, hnorm, fun r hr => ?_⟩
    rw [hform (⟨s, element_mem_centralizer_zpowers s⟩ * r) r ⟨s, hsV⟩ rfl hr, ite_eq_left rfl]
    ring
  obtain ⟨a₀, hint₀, hspan₀, hnorm₀, hval₀⟩ := hloc n₀ (Or.inl rfl)
  obtain ⟨a₁, hint₁, hspan₁, hnorm₁, hval₁⟩ := hloc n₁ (Or.inr rfl)
  have hcharR : (∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
      (localBasis.representation n₀).character r = (localBasis.representation n₁).character r) →
      n₀ = n₁ := by
    intro h
    apply localBasis.distinct
    funext x
    obtain ⟨v, hv, r, hr, hxr⟩ := hDVR x x.2
    have e0 := hN1 n₀ (Or.inl rfl) x ⟨r, hRD hr⟩ v hv hxr hr
    have e1 := hN1 n₁ (Or.inr rfl) x ⟨r, hRD hr⟩ v hv hxr hr
    change (localBasis.representation n₀).character x = (localBasis.representation n₁).character x
    rw [e0, e1]
    exact h _ hr
  have hβne : coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀ ≠
      coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁ := by
    intro h
    have hmem : (localBasis.representation n₀).character ∈ coefficientCharacterSpace localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁) := by
      rw [← h]
      exact Submodule.subset_span ⟨n₀, coefficientBlock_self_mem _ _ n₀, rfl⟩
    obtain ⟨F, hF⟩ := (hN6c n₁ (Or.inr rfl) _).mp hmem
    have hF1 : F 1 = 1 := by
      have e := hF 1 1 1 (by simp) (Subgroup.one_mem _)
      rw [hN2 n₀ (Or.inl rfl), hN2 n₁ (Or.inr rfl)] at e
      apply mul_left_cancel₀ hw0
      rw [mul_one]
      exact e.symm
    apply hN5
    apply hcharR
    intro r hr
    have e := hF r r 1 (by simp) hr
    rw [hF1, mul_one] at e
    exact e
  obtain ⟨e₀, he₀R, he₀odd, he₀⟩ : ∃ e : Subgroup.centralizer (Subgroup.zpowers s : Set C),
      (e : C) ∈ R ∧ Odd (orderOf (e : C)) ∧
        (localBasis.representation n₀).character e ≠ (localBasis.representation n₁).character e := by
    by_contra hall
    push Not at hall
    apply hN5
    apply hcharR
    intro r hr
    by_cases hodd : Odd (orderOf (r : C))
    · exact hall r hr hodd
    · have h2r : 2 ∣ orderOf (r : C) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
      rw [hN3 n₀ (Or.inl rfl) r hr h2r, hN3 n₁ (Or.inr rfl) r hr h2r]
  obtain ⟨-, horth, eX, heX, heXsymm, hisoX⟩ :=
    brauer_fiber_involution_section_induction_decomposition basis ideal s hs hgroup localBasis
      label
  have hβ₀T : coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀ ∈
      brauerFiberBlocks basis ideal 2 s hgroup localBasis label := by
    rw [hfiber]
    exact Finset.mem_insert_self _ _
  have hβ₁T : coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁ ∈
      brauerFiberBlocks basis ideal 2 s hgroup localBasis label := by
    rw [hfiber]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have ha₀V : a₀ ∈ coefficientCharacterSpace localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀) ⊓
        sectionSupported (involutionLocalSection s) := by
    rw [hspan₀]
    exact Submodule.mem_span_singleton_self _
  have ha₁V : a₁ ∈ coefficientCharacterSpace localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁) ⊓
        sectionSupported (involutionLocalSection s) := by
    rw [hspan₁]
    exact Submodule.mem_span_singleton_self _
  have ha₀M : a₀ ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)) :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hβ₀T ha₀V)
  have ha₁M : a₁ ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)) :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hβ₁T ha₁V)
  have hMspan : ∀ F ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)),
      ∃ c₀ c₁ : ℂ, c₀ • a₀ + c₁ • a₁ = F := by
    intro F hF
    have hle : (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
        coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)) ≤
        Submodule.span ℂ {a₀, a₁} := by
      refine iSup₂_le fun b' hb' => ?_
      rw [hfiber, Finset.mem_insert, Finset.mem_singleton] at hb'
      rcases hb' with rfl | rfl
      · rw [hspan₀]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      · rw [hspan₁]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact Submodule.mem_span_pair.mp (hle hF)
  obtain ⟨Θ₀, hΘ₀⟩ : ∃ Θ : C → ℂ,
      Θ = inducedFunction (Subgroup.centralizer (Subgroup.zpowers s : Set C)) a₀ := ⟨_, rfl⟩
  obtain ⟨Θ₁, hΘ₁⟩ : ∃ Θ : C → ℂ,
      Θ = inducedFunction (Subgroup.centralizer (Subgroup.zpowers s : Set C)) a₁ := ⟨_, rfl⟩
  have hΘ₀e : (eX ⟨a₀, ha₀M⟩ : C → ℂ) = Θ₀ := by rw [heX, hΘ₀]
  have hΘ₁e : (eX ⟨a₁, ha₁M⟩ : C → ℂ) = Θ₁ := by rw [heX, hΘ₁]
  have hΘ₀W : Θ₀ ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion s) := by
    rw [← hΘ₀e]
    exact (eX _).2
  have hΘ₁W : Θ₁ ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion s) := by
    rw [← hΘ₁e]
    exact (eX _).2
  have hΘQ : ∀ x ∈ involutionLocalSection s, Θ₀ x = a₀ x ∧ Θ₁ x = a₁ x := by
    intro x hx
    have h0 := congrFun (congrArg Subtype.val (eX.symm_apply_apply ⟨a₀, ha₀M⟩)) x
    have h1 := congrFun (congrArg Subtype.val (eX.symm_apply_apply ⟨a₁, ha₁M⟩)) x
    rw [heXsymm, hΘ₀e] at h0
    rw [heXsymm, hΘ₁e] at h1
    unfold characterFunctionMask at h0 h1
    rw [ite_eq_left hx] at h0 h1
    exact ⟨h0, h1⟩
  have hΘvirt : Θ₀ ∈ virtualCharacters C ∧ Θ₁ ∈ virtualCharacters C := by
    rw [hΘ₀, hΘ₁]
    exact ⟨inducedFunction_mem_virtualCharacters _
      (coefficientVirtualLattice_le_virtual localBasis _ hint₀),
      inducedFunction_mem_virtualCharacters _
        (coefficientVirtualLattice_le_virtual localBasis _ hint₁)⟩
  have hvchar : ∀ F ∈ virtualCharacters C, F ∈ BlocksVChar C := fun F hF => by
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    exact hF
  have hgram00 : characterPairing Θ₀ Θ₀ = 4 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (hvchar _ hΘvirt.1), ← hΘ₀e, hisoX]
    exact hnorm₀
  have hgram11 : characterPairing Θ₁ Θ₁ = 4 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (hvchar _ hΘvirt.2), ← hΘ₁e, hisoX]
    exact hnorm₁
  have hgram01 : characterPairing Θ₀ Θ₁ = 0 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (hvchar _ hΘvirt.2), ← hΘ₀e, ← hΘ₁e, hisoX]
    exact horth _ hβ₀T _ hβ₁T hβne a₀ ha₀V a₁ ha₁V
  have hXspan : ∀ F ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion s),
      ∃ c₀ c₁ : ℂ, F = c₀ • Θ₀ + c₁ • Θ₁ := by
    intro F hF
    obtain ⟨c₀, c₁, hc⟩ := hMspan _ (eX.symm ⟨F, hF⟩).2
    refine ⟨c₀, c₁, ?_⟩
    have h1 : inducedFunction (Subgroup.centralizer (Subgroup.zpowers s : Set C))
        (eX.symm ⟨F, hF⟩ : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ) = F := by
      have h0 := congrArg Subtype.val (eX.apply_symm_apply ⟨F, hF⟩)
      rw [heX] at h0
      exact h0
    rw [← h1, ← hc, hΘ₀, hΘ₁]
    exact (inducedFunctionComplexLinearMap _).map_add _ _ |>.trans (by
      rw [(inducedFunctionComplexLinearMap _).map_smul,
        (inducedFunctionComplexLinearMap _).map_smul]
      rfl)
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) label with hB
  have hint : ∀ χ : basis.index,
      ∃ n : ℤ, characterPairing Θ₀ (basis.representation χ).character = n :=
    fun χ => characterPairing_virtual_integer _ _ hΘvirt.1 (character_mem_virtualCharacters _)
  choose u hu using hint
  have hΘ₀exp : ∀ x, Θ₀ x = ∑ χ ∈ B, (u χ : ℂ) * (basis.representation χ).character x := by
    intro x
    have h := characterSubsetProjection_identity basis _ Θ₀ (Submodule.mem_inf.mp hΘ₀W).1
    rw [← h, BrauerSecondMain.characterSubsetProjection_apply_sum]
    exact Finset.sum_congr rfl fun χ _ => by rw [hu χ]
  choose σ hσ hσval using fun χ => central_involution_sign basis t htcent ht2 χ
  have hXt : ∀ x, x ∈ involutionSectionUnion s → t * x ∈ involutionSectionUnion s := by
    rintro x ⟨g, q, ⟨z, rfl, hzodd⟩, rfl⟩
    have hz'D : y⁻¹ * (z : C) * y ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) :=
      hyD _ z.2
    have hz'odd : Odd (orderOf (⟨y⁻¹ * (z : C) * y, hz'D⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C))) := by
      rw [← Subgroup.orderOf_coe]
      have h := (MulAut.conj y⁻¹).orderOf_eq (z : C)
      rw [MulAut.conj_apply, inv_inv] at h
      change Odd (orderOf (y⁻¹ * (z : C) * y))
      rw [h, Subgroup.orderOf_coe]
      exact hzodd
    refine ⟨g * y, ⟨s, element_mem_centralizer_zpowers s⟩ * ⟨y⁻¹ * (z : C) * y, hz'D⟩,
      ⟨_, rfl, hz'odd⟩, ?_⟩
    change t * (g * (s * (z : C)) * g⁻¹) = g * y * (s * (y⁻¹ * (z : C) * y)) * (g * y)⁻¹
    have e1 : t * (g * (s * (z : C)) * g⁻¹) = (t * g) * (s * (z : C)) * g⁻¹ := by group
    have e2 : g * y * (s * (y⁻¹ * (z : C) * y)) * (g * y)⁻¹ =
        g * (y * s * y⁻¹) * (z : C) * g⁻¹ := by group
    rw [e1, e2, ← htcent g, hys]
    group
  have hXt' : ∀ x, t * x ∈ involutionSectionUnion s → x ∈ involutionSectionUnion s := by
    intro x hx
    have h := hXt _ hx
    rwa [← mul_assoc, ht2, one_mul] at h
  have hTW : (fun x => Θ₀ (t * x)) ∈ coefficientCharacterSpace basis B ⊓
      sectionSupported (involutionSectionUnion s) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : (fun x => Θ₀ (t * x)) = ∑ χ ∈ B,
          ((u χ : ℂ) * σ χ) • (basis.representation χ).character := by
        funext x
        rw [hΘ₀exp, Finset.sum_apply]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [hσval χ x, Pi.smul_apply, smul_eq_mul]
        ring
      rw [heq]
      exact Submodule.sum_mem _ fun χ hχ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, hχ, rfl⟩)
    · intro x hx
      exact (Submodule.mem_inf.mp hΘ₀W).2 _ (fun h => hx (hXt' x h))
  obtain ⟨c₀, c₁, hc⟩ := hXspan _ hTW
  have hsE : ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
      Odd (orderOf (r : C)) →
      (⟨s, element_mem_centralizer_zpowers s⟩ * r :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) ∈ involutionLocalSection s :=
    fun r _ hodd => ⟨r, rfl, by rw [← Subgroup.orderOf_coe]; exact hodd⟩
  have hΘsE : ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
      Odd (orderOf (r : C)) →
      Θ₀ (s * r) = 4 * (localBasis.representation n₀).character r ∧
        Θ₁ (s * r) = 4 * (localBasis.representation n₁).character r := by
    intro r hr hodd
    obtain ⟨h0, h1⟩ := hΘQ _ (hsE r hr hodd)
    exact ⟨h0.trans (hval₀ r hr), h1.trans (hval₁ r hr)⟩
  have hcν : ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
      Odd (orderOf (r : C)) →
      4 * (localBasis.representation n₁).character r =
        c₀ * (4 * (localBasis.representation n₀).character r) +
          c₁ * (4 * (localBasis.representation n₁).character r) := by
    intro r hr hodd
    have h := congrFun hc (s * r)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [(hΘsE r hr hodd).1, (hΘsE r hr hodd).2] at h
    rw [← h]
    have hconj : Θ₀ (y⁻¹ * (t * (s * r)) * y⁻¹⁻¹) = Θ₀ (t * (s * r)) := by
      rw [hΘ₀]
      exact inducedFunction_conjugate _ _ _ _
    rw [← hconj]
    have hr'D : y⁻¹ * (r : C) * y ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) :=
      hyD _ r.2
    have hr'odd : Odd (orderOf (y⁻¹ * (r : C) * y)) := by
      have h := (MulAut.conj y⁻¹).orderOf_eq (r : C)
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h]
      exact hodd
    have hr'R : y⁻¹ * (r : C) * y ∈ R := hoddR _ hr'D hr'odd
    have heq : y⁻¹ * (t * (s * r)) * y⁻¹⁻¹ = s * ((⟨y⁻¹ * r * y, hr'D⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) : C) := by
      rw [inv_inv]
      calc y⁻¹ * (t * (s * r)) * y = (y⁻¹ * (t * s) * y) * (y⁻¹ * r * y) := by group
        _ = s * (y⁻¹ * r * y) := by rw [hys']
    rw [heq, (hΘsE ⟨_, hr'D⟩ hr'R hr'odd).1, hN4 r ⟨_, hr'D⟩ rfl]
  have hc1 : c₀ + c₁ = 1 := by
    have h := hcν 1 (Subgroup.one_mem _) (by rw [Subgroup.coe_one, orderOf_one]; exact odd_one)
    rw [hN2 n₀ (Or.inl rfl), hN2 n₁ (Or.inr rfl)] at h
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hw0)
    linear_combination -h
  have hc0 : c₀ = 0 := by
    have h := hcν e₀ he₀R he₀odd
    have h' : c₀ * (4 * ((localBasis.representation n₀).character e₀ -
        (localBasis.representation n₁).character e₀)) = 0 := by
      linear_combination -h - 4 * (localBasis.representation n₁).character e₀ * hc1
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd (sub_eq_zero.mp ((mul_eq_zero.mp h'').resolve_left (by norm_num))) he₀
  have hc1' : c₁ = 1 := by rw [hc0, zero_add] at hc1; exact hc1
  have hT : ∀ x, Θ₀ (t * x) = Θ₁ x := by
    intro x
    have h := congrFun hc x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h, hc0, hc1', zero_mul, zero_add, one_mul]
  have hΘ₁exp : ∀ x, Θ₁ x = ∑ χ ∈ B,
      ((u χ : ℂ) * σ χ) * (basis.representation χ).character x := by
    intro x
    rw [← hT x, hΘ₀exp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hσval χ x]
    ring
  have hΘ₀fun : Θ₀ = fun x => ∑ χ ∈ B, (u χ : ℂ) * (basis.representation χ).character x :=
    funext hΘ₀exp
  have hΘ₁fun : Θ₁ = fun x => ∑ χ ∈ B,
      ((u χ : ℂ) * σ χ) * (basis.representation χ).character x :=
    funext hΘ₁exp
  have hpair0 : ∀ ρ, characterPairing (basis.representation ρ).character Θ₀ = u ρ := fun ρ => by
    rw [characterPairing_comm, hu ρ]
  have hpair1 : ∀ ρ ∈ B, characterPairing Θ₁ (basis.representation ρ).character =
      (u ρ : ℂ) * σ ρ := by
    intro ρ hρ
    rw [hΘ₁fun, KleinFourColumns.pairing_finset_sum_left]
    simp only [KleinFourColumns.pairing_basis, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' B ρ, ite_eq_left hρ]
  have hpair1' : ∀ ρ ∈ B, characterPairing (basis.representation ρ).character Θ₁ =
      (u ρ : ℂ) * σ ρ := fun ρ hρ => by rw [characterPairing_comm, hpair1 ρ hρ]
  have hG1 : ∑ χ ∈ B, u χ * u χ = 4 := by
    have h : characterPairing (fun x => ∑ χ ∈ B,
        (u χ : ℂ) * (basis.representation χ).character x) Θ₀ = 4 := by
      rw [← hΘ₀fun]
      exact hgram00
    rw [KleinFourColumns.pairing_finset_sum_left] at h
    simp only [hpair0] at h
    exact_mod_cast h
  have hG2 : ∑ χ ∈ B, u χ * (u χ * σ χ) = 0 := by
    have h : characterPairing (fun x => ∑ χ ∈ B,
        (u χ : ℂ) * (basis.representation χ).character x) Θ₁ = 0 := by
      rw [← hΘ₀fun]
      exact hgram01
    rw [KleinFourColumns.pairing_finset_sum_left] at h
    have h' : ∑ χ ∈ B, (u χ : ℂ) * ((u χ : ℂ) * σ χ) = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun χ hχ => by rw [hpair1' χ hχ]
    exact_mod_cast h'
  have h1X : (1 : C) ∉ involutionSectionUnion s := fun h => by
    have h' := KleinFourColumns.even_orderOf_of_mem_involutionSectionUnion hs 1 h
    rw [orderOf_one] at h'
    exact Nat.not_even_one h'
  have hchar1 : ∀ χ, (basis.representation χ).character 1 =
      (Module.finrank ℂ (basis.representation χ).vector : ℂ) := fun χ => by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have hG3 : ∑ χ ∈ B, u χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
    have h := hΘ₀exp 1
    rw [(Submodule.mem_inf.mp hΘ₀W).2 1 h1X] at h
    simp only [hchar1] at h
    exact_mod_cast h.symm
  have hG4 : ∑ χ ∈ B, u χ * σ χ *
      (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
    have h := hΘ₁exp 1
    rw [(Submodule.mem_inf.mp hΘ₁W).2 1 h1X] at h
    simp only [hchar1] at h
    exact_mod_cast h.symm
  have hdeg : ∀ χ, 0 < Module.finrank ℂ (basis.representation χ).vector := fun χ => by
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [hchar1] at h
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hpair : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ∃ χ₁ χ₂ : basis.index,
      χ₁ ∈ B ∧ χ₂ ∈ B ∧ σ χ₁ = ε ∧ σ χ₂ = ε ∧ u χ₁ = 1 ∧ u χ₂ = -1 ∧
      Module.finrank ℂ (basis.representation χ₁).vector =
        Module.finrank ℂ (basis.representation χ₂).vector ∧
      ∀ χ ∈ B, σ χ = ε → χ ≠ χ₁ → χ ≠ χ₂ → u χ = 0 := by
    intro ε hε
    obtain ⟨w, hw⟩ : ∃ w : basis.index → ℤ,
        w = fun χ => if χ ∈ B ∧ σ χ = ε then u χ else 0 := ⟨_, rfl⟩
    have hwsq : ∀ χ, 2 * w χ ^ 2 =
        if χ ∈ B then u χ * u χ + ε * (u χ * (u χ * σ χ)) else 0 := by
      intro χ
      rw [hw]
      dsimp only
      by_cases hχ : χ ∈ B
      · rcases hσ χ with h | h <;> rcases hε with h' | h' <;> simp [hχ, h, h'] <;> ring
      · simp [hχ]
    have hwdeg : ∀ χ, 2 * (w χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ)) =
        if χ ∈ B then u χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ) +
          ε * (u χ * σ χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ)) else 0 := by
      intro χ
      rw [hw]
      dsimp only
      by_cases hχ : χ ∈ B
      · rcases hσ χ with h | h <;> rcases hε with h' | h' <;> simp [hχ, h, h'] <;> ring
      · simp [hχ]
    have hnorm : ∑ χ, w χ ^ 2 = 2 := by
      have h : ∑ χ, 2 * w χ ^ 2 = 4 := by
        rw [Finset.sum_congr rfl fun χ _ => hwsq χ, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_add_distrib, ← Finset.mul_sum, hG1, hG2]
        ring
      rw [← Finset.mul_sum] at h
      linarith
    have hdsum : ∑ χ, w χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
      have h : ∑ χ, 2 * (w χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ)) = 0 := by
        rw [Finset.sum_congr rfl fun χ _ => hwdeg χ, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_add_distrib, ← Finset.mul_sum, hG3, hG4]
        ring
      rw [← Finset.mul_sum] at h
      linarith
    obtain ⟨χ₁, χ₂, h12, h1, h2, hother⟩ := integer_norm_two_two_coefficients w hnorm
    have hsum2 : w χ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
        w χ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) = 0 := by
      rw [← hdsum, ← Finset.sum_subset (Finset.subset_univ {χ₁, χ₂}) ?_]
      · exact (Finset.sum_pair (f := fun χ => w χ *
          (Module.finrank ℂ (basis.representation χ).vector : ℤ)) h12).symm
      · intro χ _ hχ
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hχ
        rw [hother χ hχ.1 hχ.2, zero_mul]
    have hmem : ∀ χ, w χ ≠ 0 → χ ∈ B ∧ σ χ = ε ∧ w χ = u χ := by
      intro χ hχ
      rw [hw] at hχ ⊢
      dsimp only at hχ ⊢
      split_ifs at hχ ⊢ with hc
      · exact ⟨hc.1, hc.2, rfl⟩
      · exact absurd rfl hχ
    have hzero : ∀ χ ∈ B, σ χ = ε → χ ≠ χ₁ → χ ≠ χ₂ → u χ = 0 := by
      intro χ hχ hσχ hne1 hne2
      have h := hother χ hne1 hne2
      rw [hw] at h
      dsimp only at h
      rwa [ite_eq_left ⟨hχ, hσχ⟩] at h
    have hd1 := hdeg χ₁
    have hd2 := hdeg χ₂
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      rw [h1, h2] at hsum2
      omega
    · obtain ⟨hB1, hσ1, hw1⟩ := hmem χ₁ (by rw [h1]; norm_num)
      obtain ⟨hB2, hσ2, hw2⟩ := hmem χ₂ (by rw [h2]; norm_num)
      refine ⟨χ₁, χ₂, hB1, hB2, hσ1, hσ2, by rw [← hw1, h1], by rw [← hw2, h2], ?_,
        fun χ hχ hσχ hne1 hne2 => hzero χ hχ hσχ hne1 hne2⟩
      rw [h1, h2] at hsum2
      omega
    · obtain ⟨hB1, hσ1, hw1⟩ := hmem χ₁ (by rw [h1]; norm_num)
      obtain ⟨hB2, hσ2, hw2⟩ := hmem χ₂ (by rw [h2]; norm_num)
      refine ⟨χ₂, χ₁, hB2, hB1, hσ2, hσ1, by rw [← hw2, h2], by rw [← hw1, h1], ?_,
        fun χ hχ hσχ hne2 hne1 => hzero χ hχ hσχ hne1 hne2⟩
      rw [h1, h2] at hsum2
      omega
    · exfalso
      rw [h1, h2] at hsum2
      omega
  obtain ⟨θ₀, θ₁, hθ₀B, hθ₁B, hσθ₀, hσθ₁, huθ₀, huθ₁, hdeg01, hzeroP⟩ := hpair 1 (Or.inl rfl)
  obtain ⟨θ₂, θ₃, hθ₂B, hθ₃B, hσθ₂, hσθ₃, huθ₂, huθ₃, hdeg23, hzeroM⟩ := hpair (-1) (Or.inr rfl)
  have hXsec : primeSectionUnion 2 (involutionSectionUnion s) := by
    intro u₁ u₂ v₁ v₂ e₁ e₂ hu₁ hu₂ hv₁ hv₂ hc₁ hc₂ hconj
    rw [mem_involutionSectionUnion_iff hs2 hu₁ hv₁ hc₁,
      mem_involutionSectionUnion_iff hs2 hu₂ hv₂ hc₂]
    exact ⟨fun h => hconj.symm.trans h, fun h => hconj.trans h⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  have hXinv : ∀ x, x ∈ involutionSectionUnion s → x⁻¹ ∈ involutionSectionUnion s := by
    rintro x ⟨g, q, ⟨z, rfl, hzodd⟩, rfl⟩
    refine ⟨g, ⟨s, element_mem_centralizer_zpowers s⟩ * z⁻¹,
      ⟨z⁻¹, rfl, by rw [orderOf_inv]; exact hzodd⟩, ?_⟩
    have hcomm : Commute (z : C) s := (hsD z z.2).symm
    change (g * (s * (z : C)) * g⁻¹)⁻¹ = g * (s * (z : C)⁻¹) * g⁻¹
    calc (g * (s * (z : C)) * g⁻¹)⁻¹ = g * ((z : C)⁻¹ * s⁻¹) * g⁻¹ := by group
      _ = g * (s * (z : C)⁻¹) * g⁻¹ := by rw [hsinv, hcomm.inv_left.eq]
  have hXinv' : ∀ x, x ∉ involutionSectionUnion s → x⁻¹ ∉ involutionSectionUnion s :=
    fun x hx h => hx (by simpa using hXinv _ h)
  have hgram10 : characterPairing Θ₁ Θ₀ = 0 := by rw [characterPairing_comm]; exact hgram01
  have hmaskX : ∀ χ ∈ B, characterFunctionMask (involutionSectionUnion s)
      (basis.representation χ).character =
        ((u χ : ℂ) / 4) • Θ₀ + ((u χ : ℂ) * σ χ / 4) • Θ₁ := by
    intro χ hχ
    have hFW : characterFunctionMask (involutionSectionUnion s)
        (basis.representation χ).character ∈
          coefficientCharacterSpace basis B ⊓ sectionSupported (involutionSectionUnion s) := by
      refine Submodule.mem_inf.mpr ⟨coefficientBlock_section_mask_mem basis ideal 2 label _
        hXsec _ (Submodule.subset_span ⟨χ, hχ, rfl⟩), ?_⟩
      intro x hx
      unfold characterFunctionMask
      rw [ite_eq_right hx]
    obtain ⟨c₀', c₁', hc'⟩ := hXspan _ hFW
    have hmp : ∀ F : C → ℂ, F ∈ sectionSupported (involutionSectionUnion s) →
        characterPairing (characterFunctionMask (involutionSectionUnion s)
          (basis.representation χ).character) F =
            characterPairing (basis.representation χ).character F := by
      intro F hF
      unfold characterPairing characterFunctionMask
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ involutionSectionUnion s
      · rw [ite_eq_left hx]
      · rw [ite_eq_right hx, zero_mul, hF x⁻¹ (hXinv' x hx), mul_zero]
    have h0 := hmp Θ₀ (Submodule.mem_inf.mp hΘ₀W).2
    have h1 := hmp Θ₁ (Submodule.mem_inf.mp hΘ₁W).2
    rw [hc', pairing_add_smul_left, hgram00, hgram10, hpair0 χ] at h0
    rw [hc', pairing_add_smul_left, hgram01, hgram11, hpair1' χ hχ] at h1
    have hc0' : c₀' = (u χ : ℂ) / 4 := by linear_combination h0 / 4
    have hc1' : c₁' = (u χ : ℂ) * σ χ / 4 := by linear_combination h1 / 4
    rw [hc', hc0', hc1']
  have hXval : ∀ χ ∈ B, ∀ x ∈ involutionSectionUnion s, (basis.representation χ).character x =
      (u χ : ℂ) / 4 * Θ₀ x + (u χ : ℂ) * σ χ / 4 * Θ₁ x := by
    intro χ hχ x hx
    have h := congrFun (hmaskX χ hχ) x
    unfold characterFunctionMask at h
    rw [ite_eq_left hx] at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hnotconj1s : ¬ IsConj (1 : C) s := fun h => hs1 (isConj_one_right.mp h)
  have hnotconjts : ¬ IsConj t s := by
    intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply hst
    rw [← hc, htcent c, mul_inv_cancel_right]
  have hpart : ∀ χ ∈ B, ∀ x : C, (basis.representation χ).character x =
      characterFunctionMask {x : C | Odd (orderOf x)} (basis.representation χ).character x +
      characterFunctionMask (translatedOddSection t) (basis.representation χ).character x +
      characterFunctionMask (involutionSectionUnion s) (basis.representation χ).character x := by
    intro χ hχ x
    obtain ⟨a, v, k, -, -, hav, hprod, ha, hv⟩ :=
      finite_prime_primary_factorization x 2 Nat.prime_two
    subst hprod
    have hodd := odd_iff_two_part_eq_one ha hv hav
    have htO := mem_translatedOddSection_iff htcent ht2 ha hv hav
    have hX := mem_involutionSectionUnion_iff hs2 ha hv hav
    unfold characterFunctionMask
    by_cases h1 : a = 1
    · have hO : a * v ∈ {x : C | Odd (orderOf x)} := hodd.mpr h1
      have hT' : a * v ∉ translatedOddSection t := fun h => ht1 ((htO.mp h).symm.trans h1)
      have hX' : a * v ∉ involutionSectionUnion s := fun h => hnotconj1s (h1 ▸ hX.mp h)
      rw [ite_eq_left hO, ite_eq_right hT', ite_eq_right hX', add_zero, add_zero]
    by_cases h2 : a = t
    · have hO : a * v ∉ {x : C | Odd (orderOf x)} := fun h => h1 (hodd.mp h)
      have hT' : a * v ∈ translatedOddSection t := htO.mpr h2
      have hX' : a * v ∉ involutionSectionUnion s := fun h => hnotconjts (h2 ▸ hX.mp h)
      rw [ite_eq_right hO, ite_eq_left hT', ite_eq_right hX', zero_add, add_zero]
    by_cases h3 : IsConj a s
    · have hO : a * v ∉ {x : C | Odd (orderOf x)} := fun h => h1 (hodd.mp h)
      have hT' : a * v ∉ translatedOddSection t := fun h => h2 (htO.mp h)
      have hX' : a * v ∈ involutionSectionUnion s := hX.mpr h3
      rw [ite_eq_right hO, ite_eq_right hT', ite_eq_left hX', zero_add, zero_add]
    have hnot : ¬ subgroupSubconjugate (Subgroup.zpowers a)
        (Subgroup.closure ({t, s} : Set C)) := by
      rintro ⟨c, hc⟩
      have hmem : (MulAut.conj c) a ∈ Subgroup.closure ({t, s} : Set C) :=
        hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers a))
      rw [MulAut.conj_apply] at hmem
      rcases hVmem _ hmem with h | h | h | h
      · apply h1
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group
      · apply h2
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = t := by rw [h, mul_assoc, ← htcent c, ← mul_assoc, inv_mul_cancel, one_mul]
      · exact h3 (isConj_iff.mpr ⟨c, h⟩)
      · apply h3
        refine isConj_iff.mpr ⟨y⁻¹ * c, ?_⟩
        calc y⁻¹ * c * a * (y⁻¹ * c)⁻¹ = y⁻¹ * (c * a * c⁻¹) * y := by group
          _ = s := by rw [h, hys']
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
    have hzero := (block_characters_vanish_outside_defect_primary basis ideal 2 label _ hD
      (a * v) a v rfl hav ⟨j, hj⟩ hv).1 hnot χ hχ
    rw [hzero]
    simp only [ite_self, add_zero]
  have hpairsplit : ∀ χ ∈ B, ∀ ρ : basis.index,
      characterPairing (basis.representation χ).character (basis.representation ρ).character =
        characterPairing (characterFunctionMask {x : C | Odd (orderOf x)}
          (basis.representation χ).character) (basis.representation ρ).character +
        characterPairing (characterFunctionMask (translatedOddSection t)
          (basis.representation χ).character) (basis.representation ρ).character +
        characterPairing (characterFunctionMask (involutionSectionUnion s)
          (basis.representation χ).character) (basis.representation ρ).character := by
    intro χ hχ ρ
    unfold characterPairing
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← add_mul, ← add_mul, ← hpart χ hχ x]
  have htOdd_iff : ∀ z : C, t * z ∈ translatedOddSection t ↔ Odd (orderOf z) := by
    intro z
    constructor
    · rintro ⟨z', hz', hodd⟩
      rw [mul_left_cancel hz']
      exact hodd
    · intro hz
      exact ⟨z, rfl, hz⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hpairT : ∀ χ ρ : basis.index,
      characterPairing (characterFunctionMask (translatedOddSection t)
        (basis.representation χ).character) (basis.representation ρ).character =
        (σ χ * σ ρ : ℂ) * characterPairing (characterFunctionMask {x : C | Odd (orderOf x)}
          (basis.representation χ).character) (basis.representation ρ).character := by
    intro χ ρ
    unfold characterPairing characterFunctionMask
    have h : ∑ x : C, (if x ∈ translatedOddSection t then (basis.representation χ).character x
        else 0) * (basis.representation ρ).character x⁻¹ =
        ∑ z : C, (σ χ * σ ρ : ℂ) * ((if z ∈ {x : C | Odd (orderOf x)} then
          (basis.representation χ).character z else 0) *
            (basis.representation ρ).character z⁻¹) := by
      calc ∑ x : C, (if x ∈ translatedOddSection t then (basis.representation χ).character x
            else 0) * (basis.representation ρ).character x⁻¹
          = ∑ z : C, (if t * z ∈ translatedOddSection t then
              (basis.representation χ).character (t * z) else 0) *
                (basis.representation ρ).character (t * z)⁻¹ :=
            (Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)).symm
        _ = _ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          have hinv : (t * z)⁻¹ = t * z⁻¹ := by rw [mul_inv_rev, htinv, htcent]
          by_cases hz : Odd (orderOf z)
          · rw [ite_eq_left ((htOdd_iff z).mpr hz),
              ite_eq_left (show z ∈ {x : C | Odd (orderOf x)} from hz), hinv, hσval χ z,
              hσval ρ z⁻¹]
            ring
          · rw [ite_eq_right (fun h => hz ((htOdd_iff z).mp h)),
              ite_eq_right (show z ∉ {x : C | Odd (orderOf x)} from hz)]
            ring
    rw [h, ← Finset.mul_sum]
    ring_nf
  have hA : ∀ χ ∈ B, ∀ ρ ∈ B, σ χ = σ ρ →
      oddSectionMatrix basis χ ρ = 2 * (if χ = ρ then 1 else 0) - (u χ : ℂ) * u ρ := by
    intro χ hχ ρ hρ hσχρ
    have h := hpairsplit χ hχ ρ
    rw [hpairT, hmaskX χ hχ, pairing_add_smul_left, hu ρ, hpair1 ρ hρ,
      KleinFourColumns.pairing_basis] at h
    rw [DefectFourOdd.oddSectionMatrix_eq_pairing]
    have hσ2 : (σ χ : ℂ) * σ ρ = 1 := by
      rw [hσχρ]
      rcases hσ ρ with h' | h' <;> rw [h'] <;> norm_num
    set P := characterPairing (characterFunctionMask {x : C | Odd (orderOf x)}
      (basis.representation χ).character) (basis.representation ρ).character with hP
    linear_combination (-2 : ℂ) * h - (2 * P + (u χ : ℂ) * u ρ / 2) * hσ2
  have hcover : ∀ χ ∈ B, χ = θ₀ ∨ χ = θ₁ ∨ χ = θ₂ ∨ χ = θ₃ := by
    intro χ hχ
    by_contra hne
    push Not at hne
    obtain ⟨hn0, hn1, hn2, hn3⟩ := hne
    rcases hσ χ with h | h
    · have hu0 : u χ = 0 := hzeroP χ hχ h hn0 hn1
      have hAχ := hA χ hχ θ₀ hθ₀B (h.trans hσθ₀.symm)
      rw [ite_eq_right hn0, hu0] at hAχ
      have hA00 := hA θ₀ hθ₀B θ₀ hθ₀B rfl
      rw [ite_eq_left rfl, huθ₀] at hA00
      exact oddSectionMatrix_column_ne_zero basis ideal label _ hD hV4 θ₀ hθ₀B 1 odd_one
        (by rw [hA00]; norm_num) χ hχ (by rw [hAχ]; norm_num)
    · have hu0 : u χ = 0 := hzeroM χ hχ h hn2 hn3
      have hAχ := hA χ hχ θ₂ hθ₂B (h.trans hσθ₂.symm)
      rw [ite_eq_right hn2, hu0] at hAχ
      have hA22 := hA θ₂ hθ₂B θ₂ hθ₂B rfl
      rw [ite_eq_left rfl, huθ₂] at hA22
      exact oddSectionMatrix_column_ne_zero basis ideal label _ hD hV4 θ₂ hθ₂B 1 odd_one
        (by rw [hA22]; norm_num) χ hχ (by rw [hAχ]; norm_num)
  have hθ01 : θ₀ ≠ θ₁ := fun h => by rw [h, huθ₁] at huθ₀; norm_num at huθ₀
  have hθ23 : θ₂ ≠ θ₃ := fun h => by rw [h, huθ₃] at huθ₂; norm_num at huθ₂
  have hθ02 : θ₀ ≠ θ₂ := fun h => by rw [h, hσθ₂] at hσθ₀; norm_num at hσθ₀
  have hθ03 : θ₀ ≠ θ₃ := fun h => by rw [h, hσθ₃] at hσθ₀; norm_num at hσθ₀
  have hθ12 : θ₁ ≠ θ₂ := fun h => by rw [h, hσθ₂] at hσθ₁; norm_num at hσθ₁
  have hθ13 : θ₁ ≠ θ₃ := fun h => by rw [h, hσθ₃] at hσθ₁; norm_num at hσθ₁
  have hBeq : B = {θ₀, θ₁, θ₂, θ₃} := by
    ext χ
    constructor
    · intro hχ
      rcases hcover χ hχ with rfl | rfl | rfl | rfl <;> simp
    · intro hχ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
      rcases hχ with rfl | rfl | rfl | rfl <;> assumption
  have hsumB : ∀ g : basis.index → ℂ, ∑ χ ∈ B, g χ = g θ₀ + g θ₁ + g θ₂ + g θ₃ := by
    intro g
    rw [hBeq, Finset.sum_insert (by simp [hθ01, hθ02, hθ03]),
      Finset.sum_insert (by simp [hθ12, hθ13]), Finset.sum_pair hθ23]
    ring
  have htval : ∀ χ, (basis.representation χ).character t =
      (σ χ : ℂ) * (Module.finrank ℂ (basis.representation χ).vector : ℂ) := by
    intro χ
    have h := hσval χ 1
    rw [mul_one, hchar1] at h
    exact h
  have hnotconj1t : ¬ IsConj (1 : C) t := fun h => ht1 (isConj_one_right.mp h)
  have hf02 : Module.finrank ℂ (basis.representation θ₀).vector =
      Module.finrank ℂ (basis.representation θ₂).vector := by
    have h := admissible_character_section_column_orthogonality basis ideal 2 B
      (coefficientBlock_admissible basis _ label) 1 t 1 1 0 1
      (by rw [orderOf_one]; exact one_dvd _) (by rw [ht, pow_one])
      (by rw [orderOf_one]; exact Nat.coprime_one_right 2)
      (by rw [orderOf_one]; exact Nat.coprime_one_right 2) (Commute.one_right 1)
      (Commute.one_right t) hnotconj1t
    simp only [mul_one, htinv] at h
    rw [hsumB, htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃, hchar1, hchar1,
      hchar1, hchar1, ← hdeg01, ← hdeg23] at h
    push_cast at h
    have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) ^ 2 =
        ((Module.finrank ℂ (basis.representation θ₂).vector : ℕ) : ℂ) ^ 2 := by
      linear_combination h / 2
    have h'' : (Module.finrank ℂ (basis.representation θ₀).vector) ^ 2 =
        (Module.finrank ℂ (basis.representation θ₂).vector) ^ 2 := by
      exact_mod_cast h'
    exact Nat.pow_left_injective two_ne_zero h''
  have hsX : s ∈ involutionSectionUnion s := by
    refine ⟨1, ⟨s, element_mem_centralizer_zpowers s⟩,
      ⟨1, (mul_one _).symm, by rw [orderOf_one]; exact odd_one⟩, ?_⟩
    rw [one_mul, inv_one, mul_one]
  have hΘs : Θ₀ s = 4 * w ∧ Θ₁ s = 4 * w := by
    have h := hΘsE 1 (Subgroup.one_mem _) (by rw [Subgroup.coe_one, orderOf_one]; exact odd_one)
    simp only [OneMemClass.coe_one, mul_one] at h
    rw [hN2 n₀ (Or.inl rfl), hN2 n₁ (Or.inr rfl)] at h
    exact h
  have hsval : ∀ χ ∈ B, (basis.representation χ).character s =
      (u χ : ℂ) * (w * (1 + σ χ)) := by
    intro χ hχ
    rw [hXval χ hχ s hsX, hΘs.1, hΘs.2]
    ring
  have hsEX : ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
      Odd (orderOf (r : C)) → s * (r : C) ∈ involutionSectionUnion s := by
    intro r hr hodd
    refine ⟨1, _, hsE r hr hodd, ?_⟩
    rw [one_mul, inv_one, mul_one]
    rfl
  have hsEval : ∀ χ ∈ B, ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
      Odd (orderOf (r : C)) → (basis.representation χ).character (s * r) =
        (u χ : ℂ) * ((localBasis.representation n₀).character r +
          σ χ * (localBasis.representation n₁).character r) := by
    intro χ hχ r hr hodd
    rw [hXval χ hχ _ (hsEX r hr hodd), (hΘsE r hr hodd).1, (hΘsE r hr hodd).2]
    ring
  have hcol : ∀ x : C, Odd (orderOf x) → ∀ (a w : C) (k : ℕ), orderOf a ∣ 2 ^ k →
      ¬ IsConj 1 a → Nat.Coprime 2 (orderOf w) → Commute a w →
      ∑ χ ∈ B, (basis.representation χ).character x *
        (basis.representation χ).character (a * w)⁻¹ = 0 := by
    intro x hx a w k ha hna hw haw
    have h := admissible_character_section_column_orthogonality basis ideal 2 B
      (coefficientBlock_admissible basis _ label) 1 a x w 0 k
      (by rw [orderOf_one]; exact one_dvd _) ha (Nat.coprime_two_left.mpr hx) hw
      (Commute.one_left x) haw hna
    simpa only [one_mul] using h
  have hoddagree : ∀ x : C, Odd (orderOf x) →
      (basis.representation θ₁).character x = (basis.representation θ₀).character x ∧
      (basis.representation θ₂).character x = (basis.representation θ₀).character x ∧
      (basis.representation θ₃).character x = (basis.representation θ₀).character x := by
    intro x hx
    have hse : ∀ r : Subgroup.centralizer (Subgroup.zpowers s : Set C), (r : C) ∈ R →
        Odd (orderOf (r : C)) →
        (basis.representation θ₀).character x * ((localBasis.representation n₀).character r +
          (localBasis.representation n₁).character r) -
        (basis.representation θ₁).character x * ((localBasis.representation n₀).character r +
          (localBasis.representation n₁).character r) +
        (basis.representation θ₂).character x * ((localBasis.representation n₀).character r -
          (localBasis.representation n₁).character r) -
        (basis.representation θ₃).character x * ((localBasis.representation n₀).character r -
          (localBasis.representation n₁).character r) = 0 := by
      intro r hr hodd
      have hcse : Commute s (r : C) := hsD r r.2
      have hinvse : (s * (r : C)⁻¹)⁻¹ = s * r := by
        rw [mul_inv_rev, inv_inv, hsinv]
        exact hcse.eq.symm
      have h := hcol x hx s (r : C)⁻¹ 1 (by rw [hs, pow_one]) hnotconj1s
        (by rw [orderOf_inv]; exact Nat.coprime_two_left.mpr hodd) hcse.inv_right
      rw [hinvse, hsumB, hsEval θ₀ hθ₀B r hr hodd, hsEval θ₁ hθ₁B r hr hodd,
        hsEval θ₂ hθ₂B r hr hodd, hsEval θ₃ hθ₃B r hr hodd,
        huθ₀, huθ₁, huθ₂, huθ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃] at h
      simp only [Int.cast_one, Int.cast_neg] at h
      linear_combination h
    have h1 := hse 1 (Subgroup.one_mem _) (by rw [Subgroup.coe_one, orderOf_one]; exact odd_one)
    rw [hN2 n₀ (Or.inl rfl), hN2 n₁ (Or.inr rfl)] at h1
    have h01 : (basis.representation θ₁).character x = (basis.representation θ₀).character x := by
      have h' : (w : ℂ) * 2 * ((basis.representation θ₁).character x -
          (basis.representation θ₀).character x) = 0 := by
        linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (mul_ne_zero hw0 two_ne_zero))
    have h23 : (basis.representation θ₂).character x = (basis.representation θ₃).character x := by
      have h' : ((basis.representation θ₂).character x - (basis.representation θ₃).character x) *
          ((localBasis.representation n₀).character e₀ -
            (localBasis.representation n₁).character e₀) = 0 := by
        linear_combination hse e₀ he₀R he₀odd + ((localBasis.representation n₀).character e₀ +
          (localBasis.representation n₁).character e₀) * h01
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr he₀))
    have ht' := hcol x hx t 1 1 (by rw [ht, pow_one]) hnotconj1t
      (by rw [orderOf_one]; exact Nat.coprime_one_right 2) (Commute.one_right t)
    rw [mul_one, htinv, hsumB, htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃,
      ← hdeg01, ← hdeg23, ← hf02] at ht'
    push_cast at ht'
    have hf0 : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (hdeg θ₀).ne'
    have h02 : (basis.representation θ₂).character x = (basis.representation θ₀).character x := by
      have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) *
          ((basis.representation θ₂).character x - (basis.representation θ₀).character x) = 0 := by
        linear_combination -ht' / 2 + ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) :
          ℂ) / 2 * h01 + ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) / 2 * h23
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hf0)
    exact ⟨h01, h02, by rw [← h23, h02]⟩
  have hexpV : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v ≠ 1 → orderOf v = 2 := fun v hv hv1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hV2 v hv) hv1
  have hvan4 : ∀ χ ∈ B, ∀ x : C, 4 ∣ orderOf x → (basis.representation χ).character x = 0 :=
    fun χ hχ x hx => block_characters_vanish_of_defect_exponent_prime basis ideal 2 label _ hD
      hexpV x (by norm_num; exact hx) χ hχ
  have hrest : ∀ χ ∈ B, ∀ x : C, ¬ Odd (orderOf x) → x ∉ translatedOddSection t →
      x ∉ involutionSectionUnion s → (basis.representation χ).character x = 0 := by
    intro χ hχ x hodd htx hxX
    rw [hpart χ hχ x]
    unfold characterFunctionMask
    rw [ite_eq_right (show x ∉ {x : C | Odd (orderOf x)} from hodd), ite_eq_right htx,
      ite_eq_right hxX]
    ring
  have hoddX : ∀ x : C, Odd (orderOf x) → x ∉ involutionSectionUnion s := fun x hx hX =>
    Nat.not_even_iff_odd.mpr hx
      (KleinFourColumns.even_orderOf_of_mem_involutionSectionUnion hs x hX)
  have htOddX : ∀ x ∈ translatedOddSection t, x ∉ involutionSectionUnion s := by
    rintro x ⟨z, rfl, hz⟩ hX
    exact hnotconjts ((mem_involutionSectionUnion_iff hs2 (e := 1) (by rw [ht, pow_one])
      (Nat.coprime_two_left.mpr hz) (htcent z).symm).mp hX)
  have h1tOdd : (1 : C) ∉ translatedOddSection t := by
    rintro ⟨z, hz, hodd⟩
    have hzt : z = t := by
      calc z = t⁻¹ * (t * z) := by group
        _ = t := by rw [← hz, mul_one, htinv]
    rw [hzt, ht] at hodd
    exact Nat.not_even_iff_odd.mpr hodd even_two
  have htodd : ¬ Odd (orderOf t) := by
    rw [ht]
    exact Nat.not_odd_iff_even.mpr even_two
  have hαB : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character ∈
        coefficientCharacterSpace basis B :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
      (Submodule.subset_span ⟨θ₀, hθ₀B, rfl⟩) (Submodule.subset_span ⟨θ₁, hθ₁B, rfl⟩))
        (Submodule.subset_span ⟨θ₂, hθ₂B, rfl⟩)) (Submodule.subset_span ⟨θ₃, hθ₃B, rfl⟩)
  have hαsupp : ∀ x, x ∉ translatedOddSection t →
      ((basis.representation θ₀).character + (basis.representation θ₁).character -
        (basis.representation θ₂).character - (basis.representation θ₃).character) x = 0 := by
    intro x hx
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases hodd : Odd (orderOf x)
    · obtain ⟨h1, h2, h3⟩ := hoddagree x hodd
      rw [h1, h2, h3]
      ring
    by_cases hxX : x ∈ involutionSectionUnion s
    · rw [hXval θ₀ hθ₀B x hxX, hXval θ₁ hθ₁B x hxX, hXval θ₂ hθ₂B x hxX, hXval θ₃ hθ₃B x hxX,
        huθ₀, huθ₁, huθ₂, huθ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
      push_cast
      ring
    · rw [hrest θ₀ hθ₀B x hodd hx hxX, hrest θ₁ hθ₁B x hodd hx hxX, hrest θ₂ hθ₂B x hodd hx hxX,
        hrest θ₃ hθ₃B x hodd hx hxX]
      ring
  have hαfun : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character =
      fun x => ∑ χ ∈ B, (σ χ : ℂ) * (basis.representation χ).character x := by
    funext x
    rw [hsumB, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
    simp only [Pi.add_apply, Pi.sub_apply]
    push_cast
    ring
  have hpairα : ∀ ρ ∈ B, characterPairing (fun x => ∑ χ ∈ B,
      (σ χ : ℂ) * (basis.representation χ).character x) (basis.representation ρ).character =
        σ ρ := by
    intro ρ hρ
    rw [KleinFourColumns.pairing_finset_sum_left]
    simp only [KleinFourColumns.pairing_basis, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' B ρ, ite_eq_left hρ]
  have hαvirt : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character ∈
        virtualCharacters C :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
      (character_mem_virtualCharacters _) (character_mem_virtualCharacters _))
        (character_mem_virtualCharacters _)) (character_mem_virtualCharacters _)
  have hαnorm : BlocksInnerProduct ((basis.representation θ₀).character +
      (basis.representation θ₁).character - (basis.representation θ₂).character -
        (basis.representation θ₃).character) ((basis.representation θ₀).character +
      (basis.representation θ₁).character - (basis.representation θ₂).character -
        (basis.representation θ₃).character) = 4 := by
    rw [blocksInnerProduct_eq_characterPairing _ (hvchar _ hαvirt), hαfun,
      KleinFourColumns.pairing_finset_sum_left]
    have h : ∀ χ ∈ B, (σ χ : ℂ) * characterPairing (basis.representation χ).character
        (fun x => ∑ χ ∈ B, (σ χ : ℂ) * (basis.representation χ).character x) =
          (σ χ : ℂ) * σ χ := fun χ hχ => by rw [characterPairing_comm, hpairα χ hχ]
    rw [Finset.sum_congr rfl h, hsumB, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
    norm_num
  have hαt : ((basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character) t =
        4 * (Module.finrank ℂ (basis.representation θ₀).vector : ℂ) := by
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃, ← hdeg01, ← hdeg23,
      ← hf02]
    push_cast
    ring
  have hf0 : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (hdeg θ₀).ne'
  have hα0 : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character ≠ 0 := by
    intro h
    have h' := hαt
    rw [h, Pi.zero_apply] at h'
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hf0 h'.symm
  have hFexp : ∀ F ∈ coefficientCharacterSpace basis B, ∀ x, F x =
      characterPairing F (basis.representation θ₀).character *
        (basis.representation θ₀).character x +
      characterPairing F (basis.representation θ₁).character *
        (basis.representation θ₁).character x +
      characterPairing F (basis.representation θ₂).character *
        (basis.representation θ₂).character x +
      characterPairing F (basis.representation θ₃).character *
        (basis.representation θ₃).character x := by
    intro F hF x
    have h := congrFun (characterSubsetProjection_identity basis _ F hF) x
    rw [BrauerSecondMain.characterSubsetProjection_apply_sum, hsumB] at h
    exact h.symm
  have hFsum : ∀ F ∈ coefficientCharacterSpace basis B, F = fun x => ∑ χ ∈ B,
      characterPairing F (basis.representation χ).character *
        (basis.representation χ).character x := by
    intro F hF
    funext x
    have h := congrFun (characterSubsetProjection_identity basis _ F hF) x
    rw [BrauerSecondMain.characterSubsetProjection_apply_sum] at h
    exact h.symm
  have hcoefX : ∀ F ∈ coefficientCharacterSpace basis B,
      (∀ x ∈ involutionSectionUnion s, F x = 0) →
      characterPairing F (basis.representation θ₁).character =
        characterPairing F (basis.representation θ₀).character ∧
      characterPairing F (basis.representation θ₃).character =
        characterPairing F (basis.representation θ₂).character := by
    intro F hF hFX
    have key : ∀ Θ : C → ℂ, Θ ∈ sectionSupported (involutionSectionUnion s) →
        characterPairing F Θ = 0 := by
      intro Θ hΘ
      unfold characterPairing
      rw [Finset.sum_eq_zero (fun x _ => ?_), mul_zero]
      by_cases hx : x ∈ involutionSectionUnion s
      · rw [hFX x hx, zero_mul]
      · rw [hΘ x⁻¹ (hXinv' x hx), mul_zero]
    have h0 := key Θ₀ (Submodule.mem_inf.mp hΘ₀W).2
    have h1 := key Θ₁ (Submodule.mem_inf.mp hΘ₁W).2
    have hF' := hFsum F hF
    rw [hF', KleinFourColumns.pairing_finset_sum_left, hsumB] at h0 h1
    simp only [hpair0] at h0
    rw [hpair1' θ₀ hθ₀B, hpair1' θ₁ hθ₁B, hpair1' θ₂ hθ₂B, hpair1' θ₃ hθ₃B] at h1
    rw [huθ₀, huθ₁, huθ₂, huθ₃] at h0 h1
    rw [hσθ₀, hσθ₁, hσθ₂, hσθ₃] at h1
    push_cast at h0 h1
    exact ⟨by linear_combination (-(h0 + h1)) / 2, by linear_combination (-(h0 - h1)) / 2⟩
  have hspanα : coefficientCharacterSpace basis B ⊓ sectionSupported (translatedOddSection t) =
      Submodule.span ℂ {(basis.representation θ₀).character +
        (basis.representation θ₁).character - (basis.representation θ₂).character -
          (basis.representation θ₃).character} := by
    apply le_antisymm
    · intro F hF
      obtain ⟨hFB, hFsupp⟩ := Submodule.mem_inf.mp hF
      obtain ⟨h10, h32⟩ := hcoefX F hFB (fun x hx => hFsupp x (fun h => htOddX x h hx))
      have h1 : F 1 = 0 := hFsupp 1 h1tOdd
      rw [hFexp F hFB 1, hchar1, hchar1, hchar1, hchar1, ← hdeg01, ← hdeg23, ← hf02, h10,
        h32] at h1
      have hc2 : characterPairing F (basis.representation θ₂).character =
          -characterPairing F (basis.representation θ₀).character := by
        have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) *
            (characterPairing F (basis.representation θ₂).character +
              characterPairing F (basis.representation θ₀).character) = 0 := by
          linear_combination h1 / 2
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h').resolve_left hf0)
      rw [Submodule.mem_span_singleton]
      refine ⟨characterPairing F (basis.representation θ₀).character, ?_⟩
      funext x
      rw [hFexp F hFB x, h10, h32, hc2]
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.mem_inf.mpr ⟨hαB, hαsupp⟩
  have hωB : (basis.representation θ₀).character + (basis.representation θ₁).character +
      (basis.representation θ₂).character + (basis.representation θ₃).character ∈
        coefficientCharacterSpace basis B :=
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.subset_span ⟨θ₀, hθ₀B, rfl⟩) (Submodule.subset_span ⟨θ₁, hθ₁B, rfl⟩))
        (Submodule.subset_span ⟨θ₂, hθ₂B, rfl⟩)) (Submodule.subset_span ⟨θ₃, hθ₃B, rfl⟩)
  have hωsupp : ∀ x, x ∉ {x : C | Odd (orderOf x)} →
      ((basis.representation θ₀).character + (basis.representation θ₁).character +
        (basis.representation θ₂).character + (basis.representation θ₃).character) x = 0 := by
    intro x hx
    simp only [Pi.add_apply]
    by_cases htx : x ∈ translatedOddSection t
    · obtain ⟨z, rfl, hz⟩ := htx
      rw [hσval θ₀ z, hσval θ₁ z, hσval θ₂ z, hσval θ₃ z, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
      obtain ⟨h1, h2, h3⟩ := hoddagree z hz
      rw [h1, h2, h3]
      push_cast
      ring
    by_cases hxX : x ∈ involutionSectionUnion s
    · rw [hXval θ₀ hθ₀B x hxX, hXval θ₁ hθ₁B x hxX, hXval θ₂ hθ₂B x hxX, hXval θ₃ hθ₃B x hxX,
        huθ₀, huθ₁, huθ₂, huθ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
      push_cast
      ring
    · rw [hrest θ₀ hθ₀B x hx htx hxX, hrest θ₁ hθ₁B x hx htx hxX, hrest θ₂ hθ₂B x hx htx hxX,
        hrest θ₃ hθ₃B x hx htx hxX]
      ring
  have hω0 : (basis.representation θ₀).character + (basis.representation θ₁).character +
      (basis.representation θ₂).character + (basis.representation θ₃).character ≠ 0 := by
    intro h
    have h' := congrFun h 1
    simp only [Pi.add_apply, Pi.zero_apply] at h'
    rw [hchar1, hchar1, hchar1, hchar1, ← hdeg01, ← hdeg23, ← hf02] at h'
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hf0 (by linear_combination h')
  have hspanω : coefficientCharacterSpace basis B ⊓ sectionSupported {x : C | Odd (orderOf x)} =
      Submodule.span ℂ {(basis.representation θ₀).character +
        (basis.representation θ₁).character + (basis.representation θ₂).character +
          (basis.representation θ₃).character} := by
    apply le_antisymm
    · intro F hF
      obtain ⟨hFB, hFsupp⟩ := Submodule.mem_inf.mp hF
      obtain ⟨h10, h32⟩ := hcoefX F hFB (fun x hx => hFsupp x (fun h => hoddX x h hx))
      have ht0 : F t = 0 := hFsupp t htodd
      rw [hFexp F hFB t, htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃,
        ← hdeg01, ← hdeg23, ← hf02, h10, h32] at ht0
      push_cast at ht0
      have hc2 : characterPairing F (basis.representation θ₂).character =
          characterPairing F (basis.representation θ₀).character := by
        have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) *
            (characterPairing F (basis.representation θ₂).character -
              characterPairing F (basis.representation θ₀).character) = 0 := by
          linear_combination -ht0 / 2
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hf0)
      rw [Submodule.mem_span_singleton]
      refine ⟨characterPairing F (basis.representation θ₀).character, ?_⟩
      funext x
      rw [hFexp F hFB x, h10, h32, hc2]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.mem_inf.mpr ⟨hωB, hωsupp⟩
  have hinj : Function.Injective ![θ₀, θ₁, θ₂, θ₃] :=
    vec_four_injective hθ01 hθ02 hθ03 hθ12 hθ13 hθ23
  have himg : B = Finset.univ.image ![θ₀, θ₁, θ₂, θ₃] := by
    rw [hBeq, image_vec_four]
  refine ⟨![θ₀, θ₁, θ₂, θ₃], Module.finrank ℂ (basis.representation θ₀).vector, hinj, himg,
    hdeg θ₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hαsupp, hαnorm, hαt, hspanα, ?_, ?_⟩
  · intro i
    fin_cases i
    · rfl
    · exact hdeg01.symm
    · exact hf02.symm
    · exact hdeg23.symm.trans hf02.symm
  · change (basis.representation θ₀).character t = _
    rw [htval θ₀, hσθ₀]
    push_cast
    ring
  · change (basis.representation θ₁).character t = _
    rw [htval θ₁, hσθ₁, ← hdeg01]
    push_cast
    ring
  · change (basis.representation θ₂).character t = _
    rw [htval θ₂, hσθ₂, ← hf02]
    push_cast
    ring
  · change (basis.representation θ₃).character t = _
    rw [htval θ₃, hσθ₃, ← hdeg23, ← hf02]
    push_cast
    ring
  · change (basis.representation θ₀).character s = _
    rw [hsval θ₀ hθ₀B, huθ₀, hσθ₀]
    push_cast
    ring
  · change (basis.representation θ₁).character s = _
    rw [hsval θ₁ hθ₁B, huθ₁, hσθ₁]
    push_cast
    ring
  · change (basis.representation θ₂).character s = _
    rw [hsval θ₂ hθ₂B, huθ₂, hσθ₂]
    push_cast
    ring
  · change (basis.representation θ₃).character s = _
    rw [hsval θ₃ hθ₃B, huθ₃, hσθ₃]
    push_cast
    ring
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := hoddagree x hx
    have hall : ∀ i, (basis.representation (![θ₀, θ₁, θ₂, θ₃] i)).character x =
        (basis.representation θ₀).character x := by
      intro i
      fin_cases i
      · rfl
      · exact h1
      · exact h2
      · exact h3
    intro i i'
    rw [hall i, hall i']
  · intro x hx i
    have hmem : ![θ₀, θ₁, θ₂, θ₃] i ∈ B := by
      rw [himg]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    exact hvan4 _ hmem x hx
  · rw [hspanα]
    exact finrank_span_singleton hα0
  · rw [hspanω]
    exact finrank_span_singleton hω0

end CFSG.KleinFourBlocks
