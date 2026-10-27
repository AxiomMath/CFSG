module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamental
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat elt)
open scoped MatrixGroups

section Generation

variable {K : Type} [Field K] {n : ℕ}

theorem eq_top_of_forall_pair_le (hn : 2 ≤ n) (H' : Subgroup (StatedSp n K))
    (h : ∀ a b : Fin n, a ≠ b → suppGroup (coords a ∪ coords b) ≤ H') : H' = ⊤ := by
  have hlong : ∀ r : Fin n, ∃ b : Fin n, b ≠ r := fun r => by
    by_cases hr : r.val = 0
    · exact ⟨⟨1, by omega⟩, fun hh => by rw [← hh] at hr; simp at hr⟩
    · exact ⟨⟨0, by omega⟩, fun hh => hr (by rw [← hh])⟩
  let H : Subgroup (TauCeti.GLSymplecticFin n K) := H'.comap (equivStatedSp n K).toMonoidHom
  obtain ⟨r, hr0⟩ : ∃ r : Fin n, True := ⟨⟨0, by omega⟩, trivial⟩
  obtain ⟨b, hb⟩ := hlong r
  have hH : H = ⊤ := by
    refine TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long H r ?_ ?_ ?_
    · intro i j hij c _
      have key : equivStatedSp n K (TauCeti.GLSymplecticFin.differenceShortRootUnit hij c) =
          elt (.difference i j hij) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_difference,
          TauCeti.GLSymplecticFin.differenceShortRootHom_apply, toAdd_ofAdd]
      change equivStatedSp n K _ ∈ H'
      rw [key, ← shortBlock_sl2Upper hij c]
      exact h i j hij (shortBlock_range_le_suppGroup hij ⟨_, rfl⟩)
    · intro c
      have key : equivStatedSp n K (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit r c) =
          elt (.positiveLong r) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
          TauCeti.GLSymplecticFin.positiveLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp n K _ ∈ H'
      rw [key, ← longBlock_sl2Upper r c]
      exact h b r hb (longBlock_range_le_suppGroup_right hb ⟨_, rfl⟩)
    · intro c
      have key : equivStatedSp n K (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit r c) =
          elt (.negativeLong r) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
          TauCeti.GLSymplecticFin.negativeLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp n K _ ∈ H'
      rw [key, ← longBlock_sl2Lower r c]
      exact h b r hb (longBlock_range_le_suppGroup_right hb ⟨_, rfl⟩)
  rw [eq_top_iff]
  intro x _
  have : (equivStatedSp n K).symm x ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using this

end Generation

section Center

variable {K : Type} [Field K] {n : ℕ}

theorem eq_one_or_eq_of_mem_center (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)}
    {i : StatedSp n K} (h : IsLongRootSp2 L i) {c : StatedSp n K} (hc : c ∈ L)
    (hcc : ∀ r ∈ L, c * r = r * c) : c = 1 ∨ c = i := by
  obtain ⟨e⟩ := (h.isClassicalSL2 h2).nonempty_mulEquiv
  have hz : e ⟨c, hc⟩ ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨y, rfl⟩ := e.surjective B
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hcc y y.2).symm)
  obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hBB : e ⟨c, hc⟩ * e ⟨c, hc⟩ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrB, ← map_mul, Matrix.SpecialLinearGroup.coe_one]
    have hr2 : r * r = 1 := by simpa [pow_two] using hr
    rw [hr2, map_one]
  have hcc2 : c * c = 1 := by
    have : (⟨c, hc⟩ : L) * ⟨c, hc⟩ = 1 := e.injective (by rw [map_mul, hBB, map_one])
    exact congrArg Subtype.val this
  by_cases h1 : c = 1
  · exact Or.inl h1
  · exact Or.inr (h.eq_of_orderOf_eq_two h2 hc (orderOf_eq_prime (by rwa [sq]) h1))

end Center

section Model

variable {p : ℕ} [Fact p.Prime] {n e : ℕ}

theorem fund_iff_isLongRootSp2 (hadm : StatedLieAdmissible .PSp n p e)
    (h2 : (2 : GaloisField p e) ≠ 0) (R : Subgroup (StatedSp n (GaloisField p e))) :
    R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D ↔
      ∃ i, IsLongRootSp2 R i :=
  (mem_fundamentalSubgroups_PSp_iff hadm R).trans (exists_isLongRootSp2_iff h2 R).symm

variable (p n e) in
@[expose] noncomputable def allowedSubgroup (c₁ c₂ : StatedSp n (GaloisField p e)) :
    Subgroup (StatedSp n (GaloisField p e)) :=
  ⨆ (R : Subgroup (StatedSp n (GaloisField p e)))
    (_ : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D)
    (_ : R ≤ Subgroup.centralizer ({c₁} : Set (StatedSp n (GaloisField p e))) ∨
      R ≤ Subgroup.centralizer ({c₂} : Set (StatedSp n (GaloisField p e))) ∨
      R ≤ Subgroup.centralizer ({c₁ * c₂} : Set (StatedSp n (GaloisField p e)))), R

theorem top_le_iSup_fund_psp (hadm : StatedLieAdmissible .PSp n p e)
    (h2 : (2 : GaloisField p e) ≠ 0) (h4 : 4 ≤ Nat.card (GaloisField p e)) :
    (⊤ : Subgroup (StatedSp n (GaloisField p e))) ≤
      ⨆ (R : Subgroup (StatedSp n (GaloisField p e)))
        (_ : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D), R := by
  have hn : 2 ≤ n := hadm.2.2.1
  set N : Subgroup (StatedSp n (GaloisField p e)) := ⨆ (R : Subgroup (StatedSp n (GaloisField p e)))
    (_ : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D), R with hN
  have hconj : ∀ g : StatedSp n (GaloisField p e), N.map (MulAut.conj g).toMonoidHom ≤ N := by
    intro g
    rw [hN, Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR => ?_
    obtain ⟨i, hi⟩ := (fund_iff_isLongRootSp2 hadm h2 R).1 hR
    have hR' : R.map (MulAut.conj g).toMonoidHom ∈
        fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D :=
      (fund_iff_isLongRootSp2 hadm h2 _).2 ⟨_, hi.conj g⟩
    exact le_iSup₂_of_le _ hR' le_rfl
  have hNn : N.Normal := ⟨fun x hx g => hconj g ⟨x, hx, rfl⟩⟩
  let k₀ : Fin n := ⟨0, by omega⟩
  have hk₀ : longRootSp2 (GaloisField p e) n k₀ ∈
      fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D :=
    (fund_iff_isLongRootSp2 hadm h2 _).2 ⟨_, isLongRootSp2_standard k₀⟩
  have hnc : ¬ N ≤ Subgroup.center (StatedSp n (GaloisField p e)) := by
    intro hle
    refine planeGroup_not_le_center hn (isHyperbolicPlane_stdPlane (K := GaloisField p e) k₀) ?_
    rw [planeGroup_stdPlane]
    exact (le_iSup₂_of_le _ hk₀ le_rfl).trans hle
  have htop := eq_top_of_normal_of_not_le_center (by omega) h4 hNn hnc
  exact htop.ge

theorem map_suppGroup_pair_le (hadm : StatedLieAdmissible .PSp n p e)
    (h2 : (2 : GaloisField p e) ≠ 0) (h4 : 4 ≤ Nat.card (GaloisField p e)) {k₀ k₁ : Fin n}
    (hk : k₀ ≠ k₁) (g : StatedSp n (GaloisField p e)) {a b : Fin n} (hab : a ≠ b) :
    (suppGroup (coords a ∪ coords b)).map (MulAut.conj g).toMonoidHom ≤
      allowedSubgroup p n e (g * longInv (GaloisField p e) n k₀ * g⁻¹)
        (g * longInv (GaloisField p e) n k₁ * g⁻¹) := by
  rw [← pairPlaneSubgroup_eq h4 hab, pairPlaneSubgroup, Subgroup.map_iSup]
  refine iSup_le fun H => ?_
  obtain ⟨hH, hHle⟩ := H.2
  have hfund : (planeGroup (H : Submodule (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e))).map
      (MulAut.conj g).toMonoidHom ∈
        fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D := by
    obtain ⟨i, hi, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hH
    exact (fund_iff_isLongRootSp2 hadm h2 _).2 ⟨_, hi.conj g⟩
  have hsupp := planeGroup_le_suppGroup_pair hab hHle
  refine le_iSup₂_of_le _ hfund ?_
  have hcent : ∀ {x : StatedSp n (GaloisField p e)},
      (∀ y ∈ planeGroup (H : Submodule (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e)),
        Commute x y) →
      (planeGroup (H : Submodule (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e))).map
        (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set _) := by
    intro x hx
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (hx y hy).map (MulAut.conj g).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using this.symm.eq
  have hstd : ∀ k : Fin n, k ≠ a → k ≠ b → ∀ y ∈ planeGroup
      (H : Submodule (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e)),
      Commute (longInv (GaloisField p e) n k) y := by
    intro k hka hkb y hy
    have hy' : y ∈ complGroup (longInv (GaloisField p e) n k) := by
      rw [complGroup_longInv h2]
      exact suppGroup_mono (Set.union_subset (coords_subset_compl hka.symm)
        (coords_subset_compl hkb.symm)) (hsupp hy)
    exact (isLongRootSp2_standard (K := GaloisField p e) (n := n) k).commute_of_mem_complGroup h2
      ((isLongRootSp2_standard (K := GaloisField p e) (n := n) k).isClassicalSL2 h2).mem hy'
  by_cases h0 : k₀ ≠ a ∧ k₀ ≠ b
  · exact le_iSup_of_le (Or.inl (hcent (hstd k₀ h0.1 h0.2))) le_rfl
  by_cases h1 : k₁ ≠ a ∧ k₁ ≠ b
  · exact le_iSup_of_le (Or.inr (Or.inl (hcent (hstd k₁ h1.1 h1.2)))) le_rfl
  · have h0' : a = k₀ ∨ b = k₀ := by
      by_contra hh
      push Not at hh
      exact h0 ⟨hh.1.symm, hh.2.symm⟩
    have h1' : a = k₁ ∨ b = k₁ := by
      by_contra hh
      push Not at hh
      exact h1 ⟨hh.1.symm, hh.2.symm⟩
    have hy : ∀ y ∈ planeGroup
        (H : Submodule (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e)),
        Commute (longInv (GaloisField p e) n k₀ * longInv (GaloisField p e) n k₁) y := by
      intro y hy
      rcases h0' with ha | hb
      · rcases h1' with ha' | hb'
        · exact absurd (ha.symm.trans ha') hk
        · subst ha hb'
          exact commute_longInv_mul_longInv hab (hsupp hy)
      · rcases h1' with ha' | hb'
        · subst hb ha'
          exact commute_longInv_mul_longInv hk
            (suppGroup_mono (le_of_eq (Set.union_comm _ _)) (hsupp hy))
        · exact absurd (hb.symm.trans hb') hk
    refine le_iSup_of_le (Or.inr (Or.inr ?_)) le_rfl
    have := hcent hy
    simpa [mul_assoc] using this

theorem commutingFundamentalGeneration_psp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp n p e) : CommutingFundamentalGeneration p .PSp n e := by
  have hn : 2 ≤ n := hadm.2.2.1
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  obtain ⟨i₁, hi₁⟩ := (fund_iff_isLongRootSp2 hadm h2 R₁).1 hR₁
  obtain ⟨i₂, hi₂⟩ := (fund_iff_isLongRootSp2 hadm h2 R₂).1 hR₂
  suffices hmain : (⊤ : Subgroup (StatedSp n (GaloisField p e))) ≤ allowedSubgroup p n e c₁ c₂ from
    hmain
  have htriv : (c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1) → (⊤ : Subgroup (StatedSp n (GaloisField p e))) ≤
      allowedSubgroup p n e c₁ c₂ := by
    intro h
    refine (top_le_iSup_fund_psp hadm h2 h4).trans (iSup_le fun R => iSup_le fun hR => ?_)
    refine le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le ?_ le_rfl))
    have hcen : ∀ c : StatedSp n (GaloisField p e), c = 1 →
        R ≤ Subgroup.centralizer ({c} : Set (StatedSp n (GaloisField p e))) := by
      rintro c rfl r -
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    rcases h with h | h | h
    · exact Or.inl (hcen _ h)
    · exact Or.inr (Or.inl (hcen _ h))
    · exact Or.inr (Or.inr (hcen _ h))
  rcases eq_one_or_eq_of_mem_center h2 hi₁ hc₁ hz₁ with h1 | h1
  · exact htriv (Or.inl h1)
  rcases eq_one_or_eq_of_mem_center h2 hi₂ hc₂ hz₂ with h1' | h1'
  · exact htriv (Or.inr (Or.inl h1'))
  by_cases hii : i₁ = i₂
  · refine htriv (Or.inr (Or.inr ?_))
    rw [h1, h1', ← hii]
    exact hi₁.mul_self h2
  have hcomm : Commute i₁ i₂ := by
    have hi₁mem : i₁ ∈ R₁ := (hi₁.isClassicalSL2 h2).mem
    rw [h1'] at hx₂₁
    exact (hx₂₁ i₁ hi₁mem).symm
  have horth : ∀ u ∈ minusSpace i₁, ∀ v ∈ minusSpace i₂, form u v = 0 := by
    rcases (hi₁.commute_iff_minusSpace h2 hi₂).1 hcomm with h | h
    · exact absurd (hi₁.eq_of_minusSpace_eq h2 hi₂ h) hii
    · exact h
  obtain ⟨u₁, w₁, huw₁, hP₁⟩ := hi₁.isHyperbolicPlane h2
  obtain ⟨u₂, w₂, huw₂, hP₂⟩ := hi₂.isHyperbolicPlane h2
  have hmem₁ : ∀ x ∈ ({u₁, w₁} : Set (Fin n ⊕ Fin n → GaloisField p e)), x ∈ minusSpace i₁ := by
    intro x hx
    rw [hP₁]
    exact Submodule.subset_span hx
  have hmem₂ : ∀ x ∈ ({u₂, w₂} : Set (Fin n ⊕ Fin n → GaloisField p e)), x ∈ minusSpace i₂ := by
    intro x hx
    rw [hP₂]
    exact Submodule.subset_span hx
  let k₀ : Fin n := ⟨0, by omega⟩
  let k₁ : Fin n := ⟨1, by omega⟩
  have hk : k₀ ≠ k₁ := fun h => by simpa [k₀, k₁] using congrArg Fin.val h
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := exists_sp_apply_eq_two_at hk u₁ w₁ u₂ w₂ huw₁ huw₂
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
  have e₁ : i₁ = g * longInv (GaloisField p e) n k₀ * g⁻¹ :=
    hi₁.eq_of_minusSpace_eq h2 ((isLongRootSp2_standard (K := GaloisField p e) k₀).conj g)
      (by rw [minusSpace_conj_eq h2 g k₀, hg₁, hg₂, hP₁])
  have e₂ : i₂ = g * longInv (GaloisField p e) n k₁ * g⁻¹ :=
    hi₂.eq_of_minusSpace_eq h2 ((isLongRootSp2_standard (K := GaloisField p e) k₁).conj g)
      (by rw [minusSpace_conj_eq h2 g k₁, hg₃, hg₄, hP₂])
  have hc₁e : c₁ = g * longInv (GaloisField p e) n k₀ * g⁻¹ := h1.trans e₁
  have hc₂e : c₂ = g * longInv (GaloisField p e) n k₁ * g⁻¹ := h1'.trans e₂
  rw [hc₁e, hc₂e]
  have hpair : ∀ a b : Fin n, a ≠ b → suppGroup (coords a ∪ coords b) ≤
      (allowedSubgroup p n e (g * longInv (GaloisField p e) n k₀ * g⁻¹)
        (g * longInv (GaloisField p e) n k₁ * g⁻¹)).comap (MulAut.conj g).toMonoidHom :=
    fun a b hab => Subgroup.map_le_iff_le_comap.1 (map_suppGroup_pair_le hadm h2 h4 hk g hab)
  have htop := eq_top_of_forall_pair_le hn _ hpair
  intro x _
  have hx : g⁻¹ * x * g ∈ (allowedSubgroup p n e (g * longInv (GaloisField p e) n k₀ * g⁻¹)
      (g * longInv (GaloisField p e) n k₁ * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
    rw [htop]
    trivial
  simpa [MulAut.conj_apply, mul_assoc] using hx

end Model

end CFSG.ClassicalInvolution.ModelFacts
