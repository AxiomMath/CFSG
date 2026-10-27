module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
public import CFSG.ClassicalInvolution.Asc77.AscR10E1

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n m : ℕ}

section Normal

theorem eq_top_of_normal_of_not_le_center3 [Finite K] (hn : 2 ≤ n) (hK3 : Nat.card K = 3)
    {N : Subgroup (StatedSp n K)} (hN : N.Normal) (hnc : ¬ N ≤ Subgroup.center (StatedSp n K)) :
    N = ⊤ := by
  have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n
    (by omega) (Or.inr (Or.inl ⟨hK3, hn⟩))
  have hperf : Group.IsPerfect (StatedSp n K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n K (Or.inr (Or.inl ⟨hK3, hn⟩))
  set Z := (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) with hZdef
  have hZ : Z ≤ Subgroup.center (StatedSp n K) := scalars_le_center
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · exfalso
    apply hnc
    intro x hx
    have hx' : QuotientGroup.mk' Z x ∈ N.map (QuotientGroup.mk' Z) := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact hZ ((QuotientGroup.eq_one_iff x).1 (by simpa using hx'))
  · have hsup : ∀ g : StatedSp n K, ∃ a ∈ N, ∃ z ∈ Z, g = a * z := by
      intro g
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨a, ha, hag⟩ := this
      refine ⟨a, ha, a⁻¹ * g, QuotientGroup.eq.1 hag, by group⟩
    have hcomm : ∀ a b : StatedSp n K, ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hsup a
      obtain ⟨b₁, hb₁, z₂, hz₂, rfl⟩ := hsup b
      rw [(commutator_mul_central (hZ hz₁)).1, (commutator_mul_central (hZ hz₂)).2]
      have : ⁅a₁, b₁⁆ = a₁ * (b₁ * a₁⁻¹ * b₁⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem ha₁ (hN.conj_mem _ (inv_mem ha₁) _)
    have hcom : commutator (StatedSp n K) = ⊤ := Group.isPerfect_def.1 hperf
    have hle : ⁅(⊤ : Subgroup (StatedSp n K)), ⊤⁆ ≤ N :=
      Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    rw [← commutator_def, hcom] at hle
    exact eq_top_iff.2 hle


end Normal

section PairPlanes

variable {a b : Fin n}

theorem pairPlaneSubgroup_eq3 [Finite K] (hK3 : Nat.card K = 3) (hab : a ≠ b) :
    pairPlaneSubgroup K n a b = suppGroup (coords a ∪ coords b) := by
  refine le_antisymm (pairPlaneSubgroup_le hab) ?_
  have hmem : ∀ g : StatedSp 2 K, pairEmbed K hab g ∈ suppGroup (coords a ∪ coords b) := fun g => by
    rw [← range_pairEmbed hab]
    exact ⟨g, rfl⟩
  have hnorm : ((pairPlaneSubgroup K n a b).comap (pairEmbed K hab)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_pairPlaneSubgroup_le hab (hmem g) ⟨_, hx, rfl⟩
  have hL : ∀ A : SL(2, K), pairEmbed K hab (longBlock K 2 0 A) ∈ pairPlaneSubgroup K n a b :=
    fun A => by
      rw [pairEmbed, spEmbed_longBlock]
      exact longBlock_mem_pairPlaneSubgroup_left A
  have hnc : ¬ (pairPlaneSubgroup K n a b).comap (pairEmbed K hab) ≤
      Subgroup.center (StatedSp 2 K) := by
    intro hle
    have hx : longBlock K 2 0 (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])) ∈
        (pairPlaneSubgroup K n a b).comap (pairEmbed K hab) := hL _
    exact noncomm_longBlock_transv (K := K) (n := 2) 0
      (Subgroup.mem_center_iff.1 (hle hx)
        (longBlock K 2 0 (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])))).symm
  have htop := eq_top_of_normal_of_not_le_center3 (by norm_num) hK3 hnorm hnc
  intro g hg
  rw [← range_pairEmbed hab] at hg
  obtain ⟨y, rfl⟩ := hg
  have : y ∈ (pairPlaneSubgroup K n a b).comap (pairEmbed K hab) := by
    rw [htop]
    trivial
  exact this

end PairPlanes

end CFSG.ClassicalInvolution.Models.SymplecticPairs

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat elt)
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three)
open scoped MatrixGroups

section Model

variable {p : ℕ} [Fact p.Prime] {n e : ℕ}

theorem top_le_iSup_fund_psp3 (hadm : StatedLieAdmissible .PSp n p e)
    (h2 : (2 : GaloisField p e) ≠ 0) (hF3 : Nat.card (GaloisField p e) = 3) :
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
  have htop := eq_top_of_normal_of_not_le_center3 hn hF3 hNn hnc
  exact htop.ge

theorem map_suppGroup_pair_le3 (hadm : StatedLieAdmissible .PSp n p e)
    (h2 : (2 : GaloisField p e) ≠ 0) (hF3 : Nat.card (GaloisField p e) = 3) {k₀ k₁ : Fin n}
    (hk : k₀ ≠ k₁) (g : StatedSp n (GaloisField p e)) {a b : Fin n} (hab : a ≠ b) :
    (suppGroup (coords a ∪ coords b)).map (MulAut.conj g).toMonoidHom ≤
      allowedSubgroup p n e (g * longInv (GaloisField p e) n k₀ * g⁻¹)
        (g * longInv (GaloisField p e) n k₁ * g⁻¹) := by
  rw [← pairPlaneSubgroup_eq3 hF3 hab, pairPlaneSubgroup, Subgroup.map_iSup]
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

theorem commutingFundamentalGeneration3_psp (h3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .PSp n p e) : CommutingFundamentalGeneration p .PSp n e := by
  have hn : 2 ≤ n := hadm.2.2.1
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e (ne_two_of_pow_eq_three h3)
  have hF3 : Nat.card (GaloisField p e) = 3 := by
    rw [GaloisField.card p e he]
    exact h3
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  obtain ⟨i₁, hi₁⟩ := (fund_iff_isLongRootSp2 hadm h2 R₁).1 hR₁
  obtain ⟨i₂, hi₂⟩ := (fund_iff_isLongRootSp2 hadm h2 R₂).1 hR₂
  suffices hmain : (⊤ : Subgroup (StatedSp n (GaloisField p e))) ≤ allowedSubgroup p n e c₁ c₂ from
    hmain
  have htriv : (c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1) → (⊤ : Subgroup (StatedSp n (GaloisField p e))) ≤
      allowedSubgroup p n e c₁ c₂ := by
    intro h
    refine (top_le_iSup_fund_psp3 hadm h2 hF3).trans (iSup_le fun R => iSup_le fun hR => ?_)
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
    fun a b hab => Subgroup.map_le_iff_le_comap.1 (map_suppGroup_pair_le3 hadm h2 hF3 hk g hab)
  have htop := eq_top_of_forall_pair_le hn _ hpair
  intro x _
  have hx : g⁻¹ * x * g ∈ (allowedSubgroup p n e (g * longInv (GaloisField p e) n k₀ * g⁻¹)
      (g * longInv (GaloisField p e) n k₁ * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
    rw [htop]
    trivial
  simpa [MulAut.conj_apply, mul_assoc] using hx

end Model

end CFSG.ClassicalInvolution.ModelFacts
