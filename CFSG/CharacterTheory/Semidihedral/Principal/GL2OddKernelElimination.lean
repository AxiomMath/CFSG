module

public import CFSG.CharacterTheory.Semidihedral.Principal.OddKernelGL2ScaledOrders
public import CFSG.CharacterTheory.Semidihedral.Principal.QuaternionCosetSixteenBound
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.SixteenCharacters

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers GL2ThreeCharacters

namespace GL2Elimination

theorem orbit_three_fixed {α : Type*} [DecidableEq α] (σ κ : α → α) (x : α)
    (hσ3 : σ (σ (σ x)) = x) (hκ2 : ∀ u, κ (κ u) = u) (hcomm : ∀ u, σ (κ u) = κ (σ u))
    (hfix : κ x ≠ x ∧ κ (σ x) ≠ σ x ∧ κ (σ (σ x)) ≠ σ (σ x))
    (hcard : ({x, σ x, σ (σ x), κ x, κ (σ x), κ (σ (σ x))} : Finset α).card ≤ 5) :
    σ x = x := by
  by_contra hxy
  obtain ⟨f1, f2, f3⟩ := hfix
  have hyz : σ (σ x) ≠ σ x := by
    intro h
    have h' := congrArg σ h
    rw [hσ3, h] at h'
    exact hxy h'.symm
  have hxz : σ (σ x) ≠ x := by
    intro h
    have h' := congrArg σ h
    rw [hσ3] at h'
    exact hxy h'.symm
  have hκinj : ∀ u v, κ u = κ v → u = v := fun u v h => by rw [← hκ2 u, h, hκ2]
  have c1 : κ x ≠ σ x := by
    intro h
    have h2 : κ (σ x) = σ (σ x) := by rw [← hcomm, h]
    apply hxz
    rw [← h2, ← h, hκ2]
  have c2 : κ x ≠ σ (σ x) := by
    intro h
    have h2 : κ (σ x) = x := by rw [← hcomm, h, hσ3]
    apply hyz
    calc σ (σ x) = κ x := h.symm
      _ = κ (κ (σ x)) := by rw [h2]
      _ = σ x := hκ2 _
  have c3 : κ (σ x) ≠ x := fun h => c1 (by
    calc κ x = κ (κ (σ x)) := by rw [h]
      _ = σ x := hκ2 _)
  have c4 : κ (σ x) ≠ σ (σ x) := by
    intro h
    have h2 : κ (σ (σ x)) = x := by rw [← hcomm (σ x), h, hσ3]
    apply c1
    calc κ x = κ (σ (σ (σ x))) := by rw [hσ3]
      _ = σ (κ (σ (σ x))) := (hcomm _).symm
      _ = σ x := by rw [h2]
  have c5 : κ (σ (σ x)) ≠ x := fun h => c2 (by
    calc κ x = κ (κ (σ (σ x))) := by rw [h]
      _ = σ (σ x) := hκ2 _)
  have c6 : κ (σ (σ x)) ≠ σ x := fun h => c4 (by
    calc κ (σ x) = κ (κ (σ (σ x))) := by rw [h]
      _ = σ (σ x) := hκ2 _)
  have d1 : κ x ≠ κ (σ x) := fun h => hxy (hκinj _ _ h).symm
  have d2 : κ x ≠ κ (σ (σ x)) := fun h => hxz (hκinj _ _ h).symm
  have d3 : κ (σ x) ≠ κ (σ (σ x)) := fun h => hyz (hκinj _ _ h).symm
  have hsix : ({x, σ x, σ (σ x), κ x, κ (σ x), κ (σ (σ x))} : Finset α).card = 6 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact d3
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d1, d2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨c2.symm, c4.symm, f3.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hyz.symm, c1.symm, f2.symm, c6.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hxy, hxz.symm, f1.symm, c3.symm, c5.symm⟩
  omega

theorem linear_label_mul {N : Type} [Group N] [Fintype N]
    (basisN : FiniteIrreducibleCharacterBasis N)
    (l : basisN.index) (hl : (basisN.representation l).character 1 = 1) (x y : N) :
    (basisN.representation l).character (x * y) =
      (basisN.representation l).character x * (basisN.representation l).character y := by
  have hdim : Module.finrank ℂ (basisN.representation l).vector = 1 := by
    have h := hl
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact_mod_cast h
  show LinearMap.trace ℂ _ ((basisN.representation l).representation (x * y)) =
    LinearMap.trace ℂ _ ((basisN.representation l).representation x) *
      LinearMap.trace ℂ _ ((basisN.representation l).representation y)
  rw [map_mul, RationalOddCharacter.trace_mul_of_finrank_eq_one hdim]

theorem eq_one_of_real_pow_odd {z : ℂ} {n : ℕ} (hn : Odd n) (hz : z ^ n = 1)
    (hreal : starRingEnd ℂ z = z) : z = 1 := by
  have hzre : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · have := congrArg Complex.im hreal
      simp only [Complex.conj_im] at this
      simp only [Complex.ofReal_im]
      linarith
  have hre : z.re ^ n = 1 := by
    have h := hz
    rw [hzre] at h
    exact_mod_cast h
  have h1 : z.re = 1 := by
    have := hn.strictMono_pow (R := ℝ)
    exact this.injective (by rw [hre, one_pow])
  rw [hzre, h1, Complex.ofReal_one]

theorem centralizes_of_cube_mem {C : Type} [Group C] [Fintype C] (N : Subgroup C) [N.Normal]
    [Fintype N]
    (hNodd : Odd (Nat.card N)) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ C W) (hfaith : ∀ u ∈ N, ρ u = 1 → u = 1)
    (hdim : Module.finrank ℂ W ≤ 5)
    (hreal : ∀ u ∈ N, starRingEnd ℂ (ρ.character u) = ρ.character u)
    (hlin : ∀ θ ∈ CFSG.BlocksIrr N,
      CFSG.BlocksInnerProduct (fun u : N => ρ.character u) θ ≠ 0 → θ 1 = 1)
    (c : C) (hc : c ^ 3 ∈ N) : ∀ n ∈ N, c * n = n * c := by
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := N)
  let θ : basisN.index → N → ℂ := fun l => (basisN.representation l).character
  let τ : N → ℂ := fun u => ρ.character u
  let dataN : FiniteComplexRepresentation N := ⟨W, ρ.comp N.subtype⟩
  choose m hm using characterPairing_basis_natural basisN dataN
  have hm' : ∀ l, characterPairing τ (θ l) = m l := hm
  have hexp : ∀ u, τ u = ∑ l, (m l : ℂ) * θ l u := by
    intro u
    have h := congrFun (character_eq_sum_multiplicity basisN dataN) u
    have h' : τ u = ∑ l, characterPairing τ (θ l) * θ l u := by
      rw [show τ u = dataN.character u from rfl, h]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [h']
    simp only [hm']
  have hlinear : ∀ l, m l ≠ 0 → θ l 1 = 1 := by
    intro l hl
    have hmem := GL2Columns.label_mem_blocksIrr basisN l
    apply hlin (θ l) hmem
    rw [CFSG.blocksInnerProduct_eq_characterPairing τ (AddSubgroup.subset_closure hmem), hm' l]
    exact_mod_cast hl
  have hd : ∀ l, θ l 1 = (Module.finrank ℂ (basisN.representation l).vector : ℂ) := fun l => by
    show (basisN.representation l).representation.character 1 = _
    rw [Representation.char_one]
  have hdpos : ∀ l, 0 < Module.finrank ℂ (basisN.representation l).vector := fun l => by
    have h := irreducible_character_degree_ne_zero (basisN.representation l) (basisN.irreducible l)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hsumdeg : (∑ l, m l * Module.finrank ℂ (basisN.representation l).vector) =
      Module.finrank ℂ W := by
    have h := hexp 1
    have h1 : τ 1 = (Module.finrank ℂ W : ℂ) := by
      show ρ.character ((1 : N) : C) = _
      rw [OneMemClass.coe_one, Representation.char_one]
    rw [h1] at h
    simp only [hd] at h
    exact_mod_cast h.symm
  have hcount : ∀ S : Finset basisN.index, (∀ l ∈ S, m l ≠ 0) → S.card ≤ 5 := by
    intro S hS
    calc S.card = ∑ l ∈ S, 1 := by simp
      _ ≤ ∑ l ∈ S, m l * Module.finrank ℂ (basisN.representation l).vector :=
          Finset.sum_le_sum fun l hl =>
            Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hS l hl) (hdpos l).ne')
      _ ≤ ∑ l, m l * Module.finrank ℂ (basisN.representation l).vector :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = Module.finrank ℂ W := hsumdeg
      _ ≤ 5 := hdim
  have hσex : ∀ l, ∃ l', θ l' = fun u => θ l (MulAut.conjNormal c⁻¹ u) := by
    intro l
    let data' : FiniteComplexRepresentation N := ⟨(basisN.representation l).vector,
      (basisN.representation l).representation.comp
        (MulAut.conjNormal c⁻¹ : MulAut N).toMonoidHom⟩
    have hirr : data'.IsIrreducible :=
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective _ (MulEquiv.surjective _) _
        (basisN.irreducible l)
    obtain ⟨l', hl'⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisN data' hirr
    exact ⟨l', hl'⟩
  choose σ hσ using hσex
  have hκex : ∀ l, ∃ l', θ l' =
      if θ l 1 = 1 then (fun u => starRingEnd ℂ (θ l u)) else θ l := by
    intro l
    by_cases hl : θ l 1 = 1
    · rw [ite_eq_left hl]
      let hom : N →* ℂ :=
        { toFun := fun u => starRingEnd ℂ (θ l u)
          map_one' := by
            show starRingEnd ℂ (θ l 1) = 1
            rw [hl, map_one]
          map_mul' := fun x y => by
            show starRingEnd ℂ (θ l (x * y)) = starRingEnd ℂ (θ l x) * starRingEnd ℂ (θ l y)
            rw [show θ l (x * y) = θ l x * θ l y from linear_label_mul basisN l hl x y, map_mul] }
      let data' : FiniteComplexRepresentation N := ⟨ℂ, scalarHomRepresentation hom⟩
      have hirr : data'.IsIrreducible :=
        CFSG.LyonsUnitaryFour.scalarHomRepresentation_isIrreducible hom
      obtain ⟨l', hl'⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisN data' hirr
      refine ⟨l', ?_⟩
      show (basisN.representation l').character = _
      rw [hl']
      exact scalarHomRepresentation_character hom
    · exact ⟨l, by rw [ite_eq_right hl]⟩
  choose κ hκ using hκex
  have hconj_apply : ∀ u : N, ((MulAut.conjNormal c⁻¹ u : N) : C) = c⁻¹ * u * c := fun u => by
    rw [MulAut.conjNormal_apply, inv_inv]
  have hτconj : ∀ u : N, τ (MulAut.conjNormal c⁻¹ u) = τ u := fun u => by
    show ρ.character ((MulAut.conjNormal c⁻¹ u : N) : C) = ρ.character u
    rw [hconj_apply]
    have h := Representation.char_conj ρ (u : C) c⁻¹
    rwa [inv_inv] at h
  have hmσ : ∀ l, m (σ l) = m l := by
    intro l
    have h : characterPairing τ (θ (σ l)) = characterPairing τ (θ l) := by
      rw [hσ l]
      unfold characterPairing
      congr 1
      exact Fintype.sum_equiv (MulAut.conjNormal c⁻¹).toEquiv _ _ fun u => by
        show τ u * θ l (MulAut.conjNormal c⁻¹ u⁻¹) =
          τ (MulAut.conjNormal c⁻¹ u) * θ l (MulAut.conjNormal c⁻¹ u)⁻¹
        rw [hτconj, _root_.map_inv]
    rw [hm', hm'] at h
    exact_mod_cast h
  have hκlin : ∀ l, θ l 1 = 1 → θ (κ l) = fun u => starRingEnd ℂ (θ l u) := fun l hl => by
    rw [hκ l, ite_eq_left hl]
  have hκnon : ∀ l, θ l 1 ≠ 1 → κ l = l := fun l hl =>
    basisN.distinct (by
      show θ (κ l) = θ l
      rw [hκ l, ite_eq_right hl])
  have hmκ : ∀ l, m (κ l) = m l := by
    intro l
    by_cases hl : θ l 1 = 1
    · have h : characterPairing τ (θ (κ l)) = starRingEnd ℂ (characterPairing τ (θ l)) := by
        rw [hκlin l hl]
        unfold characterPairing
        rw [map_mul, map_inv₀, map_natCast, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [map_mul, hreal u u.2]
      rw [hm', hm', Complex.conj_natCast] at h
      exact_mod_cast h
    · rw [hκnon l hl]
  have hθσ1 : ∀ l, θ (σ l) 1 = θ l 1 := fun l => by
    rw [hσ l]
    simp only [map_one]
  have hσ3 : ∀ l, σ (σ (σ l)) = l := by
    intro l
    apply basisN.distinct
    show θ (σ (σ (σ l))) = θ l
    funext u
    have hw : MulAut.conjNormal c⁻¹ (MulAut.conjNormal c⁻¹ (MulAut.conjNormal c⁻¹ u)) =
        (⟨c ^ 3, hc⟩ : N)⁻¹ * u * (⟨c ^ 3, hc⟩ : N) := by
      apply Subtype.ext
      rw [hconj_apply, hconj_apply, hconj_apply]
      show c⁻¹ * (c⁻¹ * (c⁻¹ * (u : C) * c) * c) * c = (c ^ 3)⁻¹ * (u : C) * c ^ 3
      rw [show (c ^ 3 : C) = c * c * c by rw [pow_succ, pow_succ, pow_one]]
      group
    have e1 : θ (σ (σ (σ l))) u = θ (σ (σ l)) (MulAut.conjNormal c⁻¹ u) := congrFun (hσ _) u
    have e2 : θ (σ (σ l)) (MulAut.conjNormal c⁻¹ u) =
        θ (σ l) (MulAut.conjNormal c⁻¹ (MulAut.conjNormal c⁻¹ u)) := congrFun (hσ _) _
    have e3 : θ (σ l) (MulAut.conjNormal c⁻¹ (MulAut.conjNormal c⁻¹ u)) =
        θ l (MulAut.conjNormal c⁻¹ (MulAut.conjNormal c⁻¹ (MulAut.conjNormal c⁻¹ u))) :=
      congrFun (hσ _) _
    rw [e1, e2, e3, hw]
    have h := Representation.char_conj (basisN.representation l).representation u
      (⟨c ^ 3, hc⟩ : N)⁻¹
    rwa [inv_inv] at h
  have hκ2 : ∀ l, κ (κ l) = l := by
    intro l
    by_cases hl : θ l 1 = 1
    · have hl' : θ (κ l) 1 = 1 := by rw [hκlin l hl]; simp only; rw [hl, map_one]
      apply basisN.distinct
      show θ (κ (κ l)) = θ l
      rw [hκlin _ hl', hκlin l hl]
      funext u
      simp
    · rw [hκnon l hl, hκnon l hl]
  have hcomm : ∀ l, σ (κ l) = κ (σ l) := by
    intro l
    apply basisN.distinct
    show θ (σ (κ l)) = θ (κ (σ l))
    by_cases hl : θ l 1 = 1
    · rw [hκlin _ (by rw [hθσ1]; exact hl), hσ, hκlin l hl, hσ]
    · rw [hκnon l hl, hκnon _ (by rw [hθσ1]; exact hl)]
  have hmulθ : ∀ l, θ l 1 = 1 → ∀ x y : N, θ l (x * y) = θ l x * θ l y :=
    fun l hl x y => linear_label_mul basisN l hl x y
  have hpow : ∀ l, θ l 1 = 1 → ∀ (u : N) (k : ℕ), θ l (u ^ k) = θ l u ^ k := by
    intro l hl u k
    induction k with
    | zero => rw [pow_zero, pow_zero, hl]
    | succ k ih => rw [pow_succ, hmulθ l hl, ih, pow_succ]
  have hfixfree : ∀ l, θ l 1 = 1 → θ l ≠ 1 → κ l ≠ l := by
    intro l hl hne heq
    apply hne
    funext u
    have hreal' : starRingEnd ℂ (θ l u) = θ l u := by
      have h := congrFun (hκlin l hl) u
      rw [heq] at h
      exact h.symm
    have hp : θ l u ^ Nat.card N = 1 := by
      rw [← hpow l hl, pow_card_eq_one', hl]
    exact eq_one_of_real_pow_odd hNodd hp hreal'
  have hσne : ∀ l, θ l ≠ 1 → θ (σ l) ≠ 1 := by
    intro l hne heq
    apply hne
    funext u
    have h := congrFun heq ((MulAut.conjNormal c⁻¹).symm u)
    rw [hσ l] at h
    simpa using h
  have hfixσ : ∀ l, m l ≠ 0 → σ l = l := by
    intro l hml
    by_cases htriv : θ l = 1
    · apply basisN.distinct
      show θ (σ l) = θ l
      rw [hσ l, htriv]
      rfl
    have hl1 := hlinear l hml
    have hl1' : θ (σ l) 1 = 1 := by rw [hθσ1]; exact hl1
    have hl1'' : θ (σ (σ l)) 1 = 1 := by rw [hθσ1]; exact hl1'
    have hne' := hσne l htriv
    have hne'' := hσne _ hne'
    refine orbit_three_fixed σ κ l (hσ3 l) hκ2 hcomm
      ⟨hfixfree l hl1 htriv, hfixfree _ hl1' hne', hfixfree _ hl1'' hne''⟩ ?_
    apply hcount
    intro l' hl'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hml
    · rw [hmσ]; exact hml
    · rw [hmσ, hmσ]; exact hml
    · rw [hmκ]; exact hml
    · rw [hmκ, hmσ]; exact hml
    · rw [hmκ, hmσ, hmσ]; exact hml
  intro n hn
  have hw : c⁻¹ * n * c * n⁻¹ ∈ N :=
    N.mul_mem (by simpa using ‹N.Normal›.conj_mem n hn c⁻¹) (N.inv_mem hn)
  have hθw : ∀ l, (m l : ℂ) * θ l ⟨c⁻¹ * n * c * n⁻¹, hw⟩ = (m l : ℂ) * θ l 1 := by
    intro l
    by_cases hml : m l = 0
    · rw [hml, Nat.cast_zero, zero_mul, zero_mul]
    by_cases htriv : θ l = 1
    · rw [htriv]
      rfl
    have hl1 := hlinear l hml
    have hfix := hfixσ l hml
    have hinv : θ l (MulAut.conjNormal c⁻¹ ⟨n, hn⟩) = θ l ⟨n, hn⟩ := by
      have h := congrFun (hσ l) ⟨n, hn⟩
      rw [hfix] at h
      exact h.symm
    have hsplit : (⟨c⁻¹ * n * c * n⁻¹, hw⟩ : N) =
        MulAut.conjNormal c⁻¹ ⟨n, hn⟩ * (⟨n, hn⟩ : N)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hconj_apply, Subgroup.coe_inv]
    rw [hsplit, hmulθ l hl1, hinv, ← hmulθ l hl1, mul_inv_cancel]
  have hchar : ρ.character (c⁻¹ * n * c * n⁻¹) = ρ.character 1 := by
    have h1 : τ ⟨c⁻¹ * n * c * n⁻¹, hw⟩ = τ 1 := by
      rw [hexp, hexp]
      exact Finset.sum_congr rfl fun l _ => hθw l
    exact h1
  have h1 := hfaith _ hw (GL2ScaledOrders.rep_eq_one_of_character_eq
    ρ _ hchar)
  have h2 : c⁻¹ * n * c = n := by
    calc c⁻¹ * n * c = c⁻¹ * n * c * n⁻¹ * n := by group
      _ = n := by rw [h1, one_mul]
  calc c * n = c * (c⁻¹ * n * c) := by rw [h2]
    _ = n * c := by group

@[expose] def qA : G23 := ⟨!![0, 1; 2, 0], !![0, 2; 1, 0], by decide, by decide⟩

@[expose] def qB : G23 := ⟨!![1, 1; 1, 2], !![2, 2; 2, 1], by decide, by decide⟩

@[expose] def quatFun : QuaternionGroup 2 → G23
  | QuaternionGroup.a i => qA ^ i.val
  | QuaternionGroup.xa i => qB * qA ^ i.val

set_option maxRecDepth 20000 in
theorem quatFun_mul : ∀ g h : QuaternionGroup 2, quatFun (g * h) = quatFun g * quatFun h := by
  decide

set_option maxRecDepth 20000 in
theorem quatFun_injective : ∀ g h : QuaternionGroup 2, quatFun g = quatFun h → g = h := by
  decide

set_option maxRecDepth 20000 in
theorem quatFun_neg_one : ∀ g : QuaternionGroup 2, g ≠ 1 →
    quatFun g = -1 ∨ quatFun g ^ 2 = -1 := by
  decide

set_option maxRecDepth 20000 in
theorem quatFun_det : ∀ g : QuaternionGroup 2,
    Matrix.GeneralLinearGroup.det (quatFun g) = 1 := by
  decide

@[expose] def quatHom : QuaternionGroup 2 →* G23 where
  toFun := quatFun
  map_one' := by decide
  map_mul' := quatFun_mul

theorem quatHom_injective : Function.Injective quatHom := fun g h hgh => quatFun_injective g h hgh

theorem quatHom_a_two : quatHom (QuaternionGroup.a 2) = -1 := by decide

theorem neg_one_mem_zpowers_quatHom (g : QuaternionGroup 2) (hg : g ≠ 1) :
    (-1 : G23) ∈ Subgroup.zpowers (quatHom g) := by
  rcases quatFun_neg_one g hg with h | h
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]; exact h⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨2, by rw [zpow_two, ← pow_two]; exact h⟩

theorem quatHom_mem_K (g : QuaternionGroup 2) : quatHom g ∈ GL2ThreeStructure.K :=
  quatFun_det g

theorem orderOf_V : orderOf GL2ThreeStructure.V = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem card_quatHom_range : Nat.card quatHom.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective quatHom_injective).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

section Kernel

variable {C : Type} [Group C] [Fintype C] (π : C →* G23) (hπ : Function.Surjective π)

omit [Fintype C] in
include hπ in
theorem preimage_K_le_centralizer (habel : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a)
    (hcube : ∀ c : C, c ^ 3 ∈ π.ker → ∀ n ∈ π.ker, c * n = n * c) :
    GL2ThreeStructure.K.comap π ≤ Subgroup.centralizer (π.ker : Set C) := by
  have hNM : π.ker ≤ Subgroup.centralizer (π.ker : Set C) := fun n hn =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => habel h hh n hn
  have hcM : ∀ c : C, c ^ 3 ∈ π.ker → c ∈ Subgroup.centralizer (π.ker : Set C) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => (hcube c hc h hh).symm
  have hKmap : GL2ThreeStructure.K ≤ (Subgroup.centralizer (π.ker : Set C)).map π := by
    rw [← GL2ThreeStructure.unipotents_generate_K, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · obtain ⟨c, hc⟩ := hπ GL2ThreeStructure.U
      refine ⟨c, hcM c ?_, hc⟩
      have h3 := pow_orderOf_eq_one GL2ThreeStructure.U
      rw [GL2ScaledOrders.orderOf_U] at h3
      rw [MonoidHom.mem_ker, map_pow, hc, h3]
    · obtain ⟨c, hc⟩ := hπ GL2ThreeStructure.V
      refine ⟨c, hcM c ?_, hc⟩
      have h3 := pow_orderOf_eq_one GL2ThreeStructure.V
      rw [orderOf_V] at h3
      rw [MonoidHom.mem_ker, map_pow, hc, h3]
  intro x hx
  obtain ⟨m, hm, hmx⟩ := hKmap hx
  have hker : m⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  have h := (Subgroup.centralizer (π.ker : Set C)).mul_mem hm (hNM hker)
  rwa [mul_inv_cancel_left] at h

omit [Fintype C] in
include hπ in
theorem card_eq_card_ker_mul : Nat.card C = Nat.card π.ker * 48 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, card_G23]

include hπ in
theorem exists_quaternion_lift (hN : Odd (Nat.card π.ker)) (s : C) (hs : s * s = 1)
    (hπs : π s = -1) (hscen : ∀ c : C, c * s = s * c) :
    ∃ (S : Subgroup C) (e : QuaternionGroup 2 ≃* S),
      ((e (QuaternionGroup.a 2) : S) : C) = s ∧ S ≤ quatHom.range.comap π ∧
      ∀ x : S, π x ∈ quatHom.range ∧ (x ≠ 1 → (-1 : G23) ∈ Subgroup.zpowers (π x)) := by
  set R := quatHom.range
  set P := R.comap π
  have hRidx : R.index = 6 := by
    have h := R.index_mul_card
    rw [card_quatHom_range, card_G23] at h
    omega
  have hPcard : Nat.card P = 8 * Nat.card π.ker := by
    have h := P.index_mul_card
    rw [Subgroup.index_comap_of_surjective R hπ, hRidx, card_eq_card_ker_mul π hπ] at h
    omega
  obtain ⟨S₀⟩ := Sylow.nonempty (p := 2) (G := P)
  have hS₀card : Nat.card (S₀ : Subgroup P) = 8 := by
    rw [Sylow.card_eq_multiplicity, hPcard]
    have hN0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (by norm_num) hN0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hN)
        (even_iff_two_dvd.mpr h)), add_zero]
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  set S := (S₀ : Subgroup P).map P.subtype
  have hScard : Nat.card S = 8 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hS₀card]
  have hSP : S ≤ P := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  let πS : S →* G23 := π.comp S.subtype
  have hπSinj : Function.Injective πS := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hker : (x : C) ∈ π.ker := hx
    have h1 : orderOf x ∣ 8 := hScard ▸ orderOf_dvd_natCard x
    have h2 : orderOf (x : C) ∣ Nat.card π.ker := π.ker.orderOf_dvd_natCard hker
    rw [Subgroup.orderOf_coe] at h2
    have hodd := hN.of_dvd_nat h2
    have h3 : orderOf x = 1 := by
      have : orderOf x ∣ 2 ^ 3 := by norm_num; exact h1
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
      rcases k with _ | k
      · simpa using hk
      · rw [hk, pow_succ] at hodd
        exact absurd hodd (by simp [Nat.odd_mul])
    exact orderOf_eq_one_iff.mp h3
  have hrange : πS.range = R := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, rfl⟩
      exact hSP x.2
    · rw [card_quatHom_range, ← Nat.card_congr (MonoidHom.ofInjective hπSinj).toEquiv, hScard]
  let e : QuaternionGroup 2 ≃* S := (MonoidHom.ofInjective quatHom_injective).trans
    ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hπSinj).symm)
  have hπe : ∀ g, π (e g) = quatHom g := by
    intro g
    have h := MonoidHom.apply_ofInjective_symm hπSinj
      ((MulEquiv.subgroupCongr hrange.symm) ((MonoidHom.ofInjective quatHom_injective) g))
    exact h
  refine ⟨S, e, ?_, hSP, fun x => ⟨hSP x.2, fun hx => ?_⟩⟩
  · have horder : orderOf (e (QuaternionGroup.a 2)) = 2 := by
      rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a]
      decide
    have hsq : ((e (QuaternionGroup.a 2) : S) : C) * ((e (QuaternionGroup.a 2) : S) : C) = 1 := by
      have h1 := pow_orderOf_eq_one (e (QuaternionGroup.a 2))
      rw [horder, pow_two] at h1
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_mul, Subgroup.coe_one] at h2
    obtain ⟨n, -, hn⟩ := GL2ScaledOrders.exists_conj_of_involutions π hN hsq hs
      (by rw [hπe, quatHom_a_two, hπs])
    rw [hn, hscen n, mul_assoc, mul_inv_cancel, mul_one]
  · obtain ⟨g, rfl⟩ := e.surjective x
    rw [hπe]
    exact neg_one_mem_zpowers_quatHom g fun h => hx (by rw [h, map_one])

end Kernel

end GL2Elimination

theorem small_faithful_principal_character_eliminates_GL2_odd_kernel {G : Type} [Group G]
    [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (t : G) (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1) (χ : G → ℂ)
    (hχ : χ ∈ (fun l => (basis.representation l).character) ''
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal : Set basis.index))
    (hfaith : ∀ g : G, χ g = χ 1 → g = 1) (hrat : ∀ g : G, ∃ q : ℚ, χ g = q) :
    ((χ 1).re < 16 → ((χ 1).re - ‖χ t‖) / 2 ≤ 5 → π.ker = ⊥) ∧
      ((χ 1 = 10 ∧ χ t = 2) ∨ (χ 1 = 12 ∧ χ t = 4) → π.ker = ⊥) := by
  obtain ⟨j, hj, rfl⟩ := hχ
  have hj' := Finset.mem_coe.mp hj
  have key : ((basis.representation j).character 1).re < 16 →
      (((basis.representation j).character 1).re - ‖(basis.representation j).character t‖) / 2 ≤
        5 → π.ker = ⊥ := by
    intro hd hhalf
    let ρC : Representation ℂ (Subgroup.centralizer ({t} : Set G))
        (basis.representation j).vector :=
      (basis.representation j).representation.comp (Subgroup.centralizer ({t} : Set G)).subtype
    obtain ⟨F, hF, -⟩ := GL2PrincipalColumns.principal_section_formula ideal basis principal
      hprincipal π hπ hN orderOf_a0 GL2ScaledOrders.orderOf_U GL2ScaledOrders.orderOf_C
      GL2ScaledOrders.C_not_mem_center j hj'
    have hπt' : π (GL2OddKernel.tC t) = -1 := hπt
    have htC : GL2OddKernel.tC t ∈ Subgroup.center (Subgroup.centralizer ({t} : Set G)) :=
      Subgroup.mem_center_iff.mpr fun x => (GL2OddKernel.tC_comm t x).eq
    have htCord : orderOf (GL2OddKernel.tC t) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact ht
    have hfaithN : ∀ u ∈ π.ker, ρC u = 1 → u = 1 := by
      intro u _ h1
      have hc : (basis.representation j).character (u : G) =
          (basis.representation j).character 1 := by
        show LinearMap.trace ℂ _ (ρC u) =
          LinearMap.trace ℂ _ ((basis.representation j).representation 1)
        rw [h1, _root_.map_one (basis.representation j).representation]
      exact Subtype.ext (hfaith _ hc)
    have hratN : ∀ u ∈ π.ker, ∃ q : ℚ, ρC.character u = q := fun u _ => hrat u
    have hconstN : ∀ u ∈ π.ker, ρC.character (GL2OddKernel.tC t * u) =
        ρC.character (GL2OddKernel.tC t) := by
      intro u hu
      have hu_odd : Odd (orderOf (u : G)) := by
        rw [Subgroup.orderOf_coe]
        exact hN.of_dvd_nat (π.ker.orderOf_dvd_natCard hu)
      have h1 := hF (GL2OddKernel.tC t * u) (GL2Columns.t_mul_mem_section ht u.2 hu_odd)
      have h2 := hF (GL2OddKernel.tC t) (GL2Columns.self_mem_section ht)
      rw [map_mul, MonoidHom.mem_ker.mp hu, mul_one] at h1
      exact h1.trans h2.symm
    obtain ⟨k, r, hk, hdim, ε, hE, -, hEdim, -, hτrat, -, hτfaith, -⟩ :=
      central_involution_coset_constant_half_degree ρC htC htCord π.ker hN hfaithN hratN hconstN
    have hχ1 : (basis.representation j).character 1 =
        (Module.finrank ℂ (basis.representation j).vector : ℂ) := Representation.char_one _
    have hχt : (basis.representation j).character t = k := hk
    have hr5 : r ≤ 5 := by
      rw [hχ1, hχt, hdim] at hhalf
      push_cast at hhalf
      rw [Complex.norm_intCast] at hhalf
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero] at hhalf
      have habs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      have : (r : ℝ) ≤ 5 := by linarith
      exact_mod_cast this
    set ρE := ρC.subrepresentation _ hE with hρE
    clear_value ρE
    have hlin := rational_odd_character_degree_le_five_linear (A := π.ker)
      hN (ρE.comp π.ker.subtype) (fun a => hτrat a a.2) (by rw [hEdim]; exact hr5)
    have hinj : Function.Injective (ρE.comp π.ker.subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      exact Subtype.ext (hτfaith a a.2 ha)
    have habel : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hlin.2 hinj ⟨a, ha⟩ ⟨b, hb⟩)
    have hreal : ∀ u ∈ π.ker, starRingEnd ℂ (ρE.character u) = ρE.character u := by
      intro u hu
      obtain ⟨q, hq⟩ := hτrat u hu
      rw [hq, map_ratCast]
    have hchar_eq : Representation.character (ρE.comp π.ker.subtype) =
        fun u : π.ker => ρE.character u :=
      funext fun u => rfl
    have hlin1 : ∀ θ ∈ CFSG.BlocksIrr π.ker,
        CFSG.BlocksInnerProduct (fun u : π.ker => ρE.character u) θ ≠ 0 → θ 1 = 1 := by
      intro θ hθ hne
      apply hlin.1 θ hθ
      rwa [hchar_eq]
    have hcube : ∀ c, c ^ 3 ∈ π.ker → ∀ n ∈ π.ker, c * n = n * c := fun c hc =>
      GL2Elimination.centralizes_of_cube_mem π.ker hN ρE hτfaith (by rw [hEdim]; exact hr5)
        hreal hlin1 c hc
    have hKcent := GL2Elimination.preimage_K_le_centralizer π hπ habel hcube
    have ht2 : GL2OddKernel.tC t * GL2OddKernel.tC t = 1 := by
      rw [← pow_two, ← htCord, pow_orderOf_eq_one]
    obtain ⟨S, e, he, hSP, hSprops⟩ :=
      GL2Elimination.exists_quaternion_lift π hπ hN (GL2OddKernel.tC t) ht2
        hπt' fun c => (GL2OddKernel.tC_comm t c).eq
    have hNS : π.ker ≤ Subgroup.centralizer (S : Set (Subgroup.centralizer ({t} : Set G))) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsK : s ∈ GL2ThreeStructure.K.comap π := by
        obtain ⟨g, hg⟩ := hSP hs
        show π s ∈ GL2ThreeStructure.K
        rw [← hg]
        exact GL2Elimination.quatHom_mem_K g
      exact (Subgroup.mem_centralizer_iff.mp (hKcent hsK) n hn).symm
    have hconstS : ∀ q ∈ S, q ≠ 1 → ∀ n ∈ π.ker, ρC.character (q * n) = ρC.character q := by
      intro q hq hq1 n hn
      have hneg := (hSprops ⟨q, hq⟩).2 (fun h => hq1 (congrArg Subtype.val h))
      have hqn : π (q * n) = π q := by rw [map_mul, MonoidHom.mem_ker.mp hn, mul_one]
      have h1 := hF (q * n) (GL2OddKernel.mem_section_of_neg_one_mem π ht hN hπt' (q * n)
        (by rw [hqn]; exact hneg))
      have h2 := hF q (GL2OddKernel.mem_section_of_neg_one_mem π ht hN hπt' q hneg)
      rw [hqn] at h1
      exact h1.trans h2.symm
    have hfin : (Module.finrank ℂ (basis.representation j).vector : ℝ) < 16 := by
      rw [hχ1, Complex.natCast_re] at hd
      exact hd
    have hbound : (Module.finrank ℂ (basis.representation j).vector : ℝ) -
        ‖ρC.character (GL2OddKernel.tC t)‖ ≤ 16 := by
      have := norm_nonneg (ρC.character (GL2OddKernel.tC t))
      linarith
    obtain ⟨-, h2⟩ := quaternion_coset_constant_rational_odd_sixteen_bound ρC S e he π.ker hNS hN
      hfaithN hratN hconstS hbound
    by_contra hne
    have h16 := (h2 hne).1
    have := norm_nonneg (ρC.character (GL2OddKernel.tC t))
    linarith
  refine ⟨key, ?_⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp only at h1 h2
  · refine key (by rw [h1]; norm_num) ?_
    rw [h1, h2]
    norm_num
  · refine key (by rw [h1]; norm_num) ?_
    rw [h1, h2]
    norm_num

end CFSG.Semidihedral.Principal
