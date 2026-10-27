module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowRev
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.RankThree.PartOne (linearSubfieldInclusion fixingSubgroup_range_linearSubfieldInclusion)
open scoped commutatorElement

section Rigidity

variable {K : Type*} [Field K] {F : Type*} [Field F]

theorem eq_one_or_eq_map_of_fix_subfield [Finite F] {m : ℕ} (hm : 3 ≤ m) (ι : K →+* F)
    {σ : F ≃+* F} (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (τ : MulAut (SpecialLinearGroup (Fin m) F))
    (hτ : ∀ x : SpecialLinearGroup (Fin m) K,
      τ (SpecialLinearGroup.map ι x) = SpecialLinearGroup.map ι x) :
    (∀ y, τ y = y) ∨ (∀ y, τ y = SpecialLinearGroup.map σ.toRingHom y) := by
  have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := F) hm
  have hk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange]
    rfl
  have hfixτ : LinearFlag.descendAut m F τ ∈ fixingSubgroup (MulAut (LinearFlag.projectiveSL m F))
      ((linearSubfieldInclusion m ι.fieldRange).range : Set (LinearFlag.projectiveSL m F)) := by
    rw [mem_fixingSubgroup_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := exists_proj_map_eq_of_mem_range ι hz
    change LinearFlag.descendAut m F τ _ = _
    rw [LinearFlag.descendAut_proj, hτ]
  rw [fixingSubgroup_range_linearSubfieldInclusion hk hm] at hfixτ
  obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 hfixτ
  have hf2 : LinearFlag.fieldAut m F σ ^ (2 : ℤ) = 1 := by
    rw [_root_.zpow_two, ← map_mul, hσσ, map_one]
  have hker : (LinearFlag.proj m F).ker ≤ center (SpecialLinearGroup (Fin m) F) := by
    intro x hx
    rw [MonoidHom.mem_ker, LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center] at hx
    exact hx
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · have hτb : LinearFlag.descendAut m F τ = 1 := by
      rw [← hk', ← Int.mul_ediv_add_emod k 2, h, add_zero, _root_.zpow_mul, hf2, _root_.one_zpow]
    left
    have heq := eq_of_comp_eq_of_ker_le_center hker (φ := τ.toMonoidHom)
      (ψ := MonoidHom.id _) fun y => by
        change LinearFlag.proj m F (τ y) = LinearFlag.proj m F y
        rw [← LinearFlag.descendAut_proj, hτb]
        rfl
    exact fun y => DFunLike.congr_fun heq y
  · have hτb : LinearFlag.descendAut m F τ = LinearFlag.fieldAut m F σ := by
      rw [← hk', ← Int.mul_ediv_add_emod k 2, h, _root_.zpow_add, _root_.zpow_mul, hf2, _root_.one_zpow,
        one_mul, zpow_one]
    right
    have heq := eq_of_comp_eq_of_ker_le_center hker (φ := τ.toMonoidHom)
      (ψ := SpecialLinearGroup.map σ.toRingHom) fun y => by
        change LinearFlag.proj m F (τ y) = LinearFlag.proj m F (SpecialLinearGroup.map _ y)
        rw [← LinearFlag.descendAut_proj, hτb, LinearFlag.fieldAut_proj]
    exact fun y => DFunLike.congr_fun heq y

theorem eq_one_or_eq_mapBlock_of_fix_subfield [Finite F] {n : ℕ} {M : Finset (Fin n)}
    (hM : 3 ≤ M.card) (ι : K →+* F) {σ : F ≃+* F} (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (τ : MulAut (blockSpecialLinear (K := F) M))
    (hτ : ∀ x : blockSpecialLinear (K := K) M,
      τ ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
        ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩) :
    (∀ y, τ y = y) ∨ (∀ y, τ y = mapBlock σ M y) := by
  set εF := blockSLEquiv (R := F) M M.equivFin with hεF
  set εK := blockSLEquiv (R := K) M M.equivFin with hεK
  set τ' : MulAut (SpecialLinearGroup (Fin M.card) F) := (εF.trans τ).trans εF.symm with hτ'
  have hmap : ∀ x : SpecialLinearGroup (Fin M.card) K, εF (SpecialLinearGroup.map ι x) =
      ⟨SpecialLinearGroup.map ι (εK x), map_ringHom_mem_blockSpecialLinear ι (εK x).2⟩ :=
    fun x => Subtype.ext (blockSLEquiv_map ι M M.equivFin x)
  have hτ'fix : ∀ x : SpecialLinearGroup (Fin M.card) K,
      τ' (SpecialLinearGroup.map ι x) = SpecialLinearGroup.map ι x := by
    intro x
    change εF.symm (τ (εF (SpecialLinearGroup.map ι x))) = _
    rw [hmap, hτ, ← hmap, MulEquiv.symm_apply_apply]
  have hback : ∀ z, τ (εF z) = εF (τ' z) := fun z => by
    change τ (εF z) = εF (εF.symm (τ (εF z)))
    rw [MulEquiv.apply_symm_apply]
  rcases eq_one_or_eq_map_of_fix_subfield hM ι hσσ hfix τ' hτ'fix with h | h
  · left
    intro y
    obtain ⟨z, rfl⟩ := εF.surjective y
    rw [hback, h]
  · right
    intro y
    obtain ⟨z, rfl⟩ := εF.surjective y
    rw [hback, h, hεF, mapBlock_blockSLEquiv]

end Rigidity

theorem card_sdiff_pair_of_disjoint_pair {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    (({a, b} : Finset (Fin n))ᶜ \ {c, d}).card = n - 4 := by
  have hsub : ({c, d} : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n))ᶜ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_compl]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases hx with rfl | rfl
    · exact ⟨hca, hcb⟩
    · exact ⟨hda, hdb⟩
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_compl, Fintype.card_fin, Finset.card_pair hab,
    Finset.card_pair hcd]
  omega

theorem ne_of_disjoint_pair {n : ℕ} {a b c d : Fin n}
    (h : Disjoint ({a, b} : Finset (Fin n)) {c, d}) : c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  rw [Finset.disjoint_left] at h
  refine ⟨fun hca => ?_, fun hcb => ?_, fun hda => ?_, fun hdb => ?_⟩
  · subst hca
    exact h (a := c) (by simp) (by simp)
  · subst hcb
    exact h (a := c) (by simp) (by simp)
  · subst hda
    exact h (a := d) (by simp) (by simp)
  · subst hdb
    exact h (a := d) (by simp) (by simp)

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F]

theorem FieldNeighbourParam.injective_comp_inclusion {e : L ≃* LinearFlag.projectiveSL n K}
    {t : G} {ι : K →+* F} {σ : F ≃+* F} {X : Subgroup G} {N : Finset (Fin n)}
    (P : FieldNeighbourParam e t ι σ X N) {M : Finset (Fin n)} (hMN : M ⊆ N) {j : Fin n}
    (hjN : j ∈ N) (hjM : j ∉ M) (hN : 2 ≤ N.card) :
    Function.Injective (P.Φ.comp (Subgroup.inclusion (blockSpecialLinear_mono (K := F) hMN))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : Subgroup.inclusion (blockSpecialLinear_mono (K := F) hMN) x ∈
      center (blockSpecialLinear (K := F) N) := P.ker_le hx
  have hpat : TPattern N ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    refine pattern_of_commute_transvections hN fun i hi k hk hik => ?_
    have h1 := mem_center_iff.1 hc ⟨SpecialLinearGroup.transvection hik 1,
      transvection_mem_blockSpecialLinear hik hi hk 1⟩
    exact (congrArg (fun z : blockSpecialLinear (K := F) N =>
      (z : SpecialLinearGroup (Fin n) F)) h1).symm
  have hjj : ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = 1 := by
    rw [x.2 j j (Or.inl hjM), Matrix.one_apply_eq]
  apply Subtype.ext
  apply Subtype.ext
  change ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
  ext i k
  by_cases hi : i ∈ N
  · by_cases hik : i = k
    · subst hik
      rw [hpat.2 i hi j hjN, hjj, Matrix.one_apply_eq]
    · rw [(hpat.1 i hi k (Ne.symm hik)).2, Matrix.one_apply_ne hik]
  · exact x.2 i k (Or.inl fun h => hi (hMN h))

end Param

section Pair

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F] [Finite F]

theorem centralizerPerfectCore_le_map_of_order3_pair {e : L ≃* LinearFlag.projectiveSL n K}
    {t : G} {ι : K →+* F} {σ : F ≃+* F} {X : Subgroup G} {N : Finset (Fin n)}
    (P : FieldNeighbourParam e t ι σ X N) {a b : Fin n} (hab : a ≠ b) (haN : a ∈ N) (hbN : b ∈ N)
    {Y : Subgroup G} (hXY : X ≤ Y) (hyY : ((e.symm (order3Elt K hab) : L) : G) ∈ Y) :
    centralizerPerfectCore Y ≤
      ((blockSpecialLinear (K := F) (N \ {a, b})).subgroupOf (blockSpecialLinear N)).map P.Φ := by
  set H := blockSpecialLinear (K := F) N with hH
  set W := centralizerPerfectCore Y with hW
  have hWX : W ≤ P.Φ.range := by
    rw [P.range_eq]
    exact F4Pilot.centralizerPerfectCore_anti hXY
  set Q : Subgroup H := perfectCore (W.comap P.Φ) with hQ
  have hQR : Q.map P.Φ = W := by
    rw [hQ, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq, inf_eq_right.2 hWX,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect (F4Pilot.commutator_centralizerPerfectCore Y)]
  have hQperf : ⁅Q, Q⁆ = Q := CFSG.Quasithin.perfectCore_perfect _
  have hyH : SpecialLinearGroup.transvection hab (1 : F) *
      SpecialLinearGroup.transvection (Ne.symm hab) 1 ∈ H :=
    H.mul_mem (transvection_mem_blockSpecialLinear hab haN hbN 1)
      (transvection_mem_blockSpecialLinear (Ne.symm hab) hbN haN 1)
  let y' : H := ⟨_, hyH⟩
  have hyY' : P.Φ y' ∈ Y := by
    have hxK : SpecialLinearGroup.transvection hab (1 : K) *
        SpecialLinearGroup.transvection (Ne.symm hab) 1 ∈ blockSpecialLinear (K := K) N :=
      (blockSpecialLinear _).mul_mem (transvection_mem_blockSpecialLinear hab haN hbN 1)
        (transvection_mem_blockSpecialLinear (Ne.symm hab) hbN haN 1)
    have h1 := P.N1 ⟨_, hxK⟩
    have hyeq : (⟨Matrix.SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hab (1 : K) *
        SpecialLinearGroup.transvection (Ne.symm hab) 1),
        map_ringHom_mem_blockSpecialLinear ι hxK⟩ : H) = y' := by
      apply Subtype.ext
      change Matrix.SpecialLinearGroup.map ι _ = _
      rw [map_mul, map_transvection_one, map_transvection_one]
    rw [hyeq] at h1
    rw [h1]
    exact hyY
  have hQJ : Q ≤ centralizer ((zpowers y' : Subgroup H) : Set H) := by
    refine le_centralizer_of_commutator_le_center_of_perfect hQperf ?_
    rw [Subgroup.commutator_le]
    intro q hq w hw
    refine P.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hqW : P.Φ q ∈ W := by
      rw [← hQR]
      exact mem_map_of_mem _ hq
    have hwY : P.Φ w ∈ Y := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      rw [map_zpow]
      exact zpow_mem hyY' k
    exact (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hqW)
      (P.Φ w) hwY).symm
  set Q' := Q.map H.subtype with hQ'
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← map_commutator, hQperf]
  have hQ'2 : Q' ≤ blockSpecialLinear (K := F) ({a, b} : Finset (Fin n))ᶜ := by
    have hpat : ∀ A ∈ Q', Order3Pattern a b (A : Matrix (Fin n) (Fin n) F) := by
      rintro _ ⟨q, hq, rfl⟩
      have h1 := mem_centralizer_iff.1 (hQJ hq) y' (mem_zpowers y')
      exact order3Pattern_of_commute hab (congrArg Subtype.val h1).symm
    rw [← hQ'perf, Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_blockSpecialLinear_compl_of_order3 hab hpat hx hy
  have hQ'3 : Q' ≤ blockSpecialLinear (K := F) (N \ {a, b}) := by
    have h := le_inf (map_subtype_le Q) hQ'2
    rwa [blockSpecialLinear_inf, ← Finset.sdiff_eq_inter_compl] at h
  rw [← hQR]
  refine map_mono fun q hq => ?_
  rw [mem_subgroupOf]
  exact hQ'3 (mem_map_of_mem _ hq)

theorem map_eq_centralizerPerfectCore_pair (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (h1 : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    (hM : 3 ≤ (({a, b}ᶜ : Finset (Fin n)) \ {c, d}).card) :
    ((blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d})).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ =
      centralizerPerfectCore (modelToG e (Xr a b) ⊔ modelToG e (Xr c d)) := by
  have hMN : (({a, b}ᶜ : Finset (Fin n)) \ {c, d}) ⊆ ({a, b}ᶜ : Finset (Fin n)) :=
    Finset.sdiff_subset
  have hcdN : ({c, d} : Finset (Fin n)) ⊆ ({a, b}ᶜ : Finset (Fin n)) :=
    Finset.subset_compl_iff_disjoint_right.2 h1.symm
  apply le_antisymm
  · refine F4Pilot.le_centralizerPerfectCore (by
      rw [← map_commutator, commutator_subgroupOf_eq_self (blockSpecialLinear_mono hMN)
        (commutator_blockSpecialLinear_eq_of_three_le hM)]) ?_
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff]
      exact (map_le_range _ _).trans ((P a b hab).range_eq.le.trans
        (F4Pilot.centralizerPerfectCore_le_centralizer _))
    · refine (modelToG_mono e ((hXr c d).trans le_rfl)).trans ?_
      refine (modelToG_blockSL_le_map (P a b hab) hcdN).trans ?_
      exact map_le_centralizer_map_of_disjoint _ Finset.disjoint_sdiff
  · exact centralizerPerfectCore_le_map_of_order3_pair (P a b hab) hcd (hcdN (by simp))
      (hcdN (by simp)) le_sup_left (mem_sup_right (symm_mem_modelToG e (hXy c d hcd)))

omit [Finite G] [Finite F] in
theorem compl_pair_sdiff_comm {a b c d : Fin n} :
    (({a, b}ᶜ : Finset (Fin n)) \ {c, d}) = ({c, d}ᶜ : Finset (Fin n)) \ {a, b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_compl]
  tauto

theorem map_le_map_of_disjoint_roots_of_rigidity (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (h1 : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    (hM : 3 ≤ (({a, b}ᶜ : Finset (Fin n)) \ {c, d}).card) {A : Finset (Fin n)}
    (hAM : A ⊆ ({a, b}ᶜ : Finset (Fin n)) \ {c, d}) :
    ((blockSpecialLinear (K := F) A).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ ≤
    ((blockSpecialLinear (K := F) A).subgroupOf
      (blockSpecialLinear ({c, d}ᶜ : Finset (Fin n)))).map (P c d hcd).Φ := by
  set M : Finset (Fin n) := ({a, b}ᶜ : Finset (Fin n)) \ {c, d} with hMdef
  have hM₂ : M = ({c, d}ᶜ : Finset (Fin n)) \ {a, b} := compl_pair_sdiff_comm
  have hM₁N : M ⊆ ({a, b}ᶜ : Finset (Fin n)) := Finset.sdiff_subset
  have hM₂N : M ⊆ ({c, d}ᶜ : Finset (Fin n)) := hM₂ ▸ Finset.sdiff_subset
  obtain ⟨hca, hcb, hda, hdb⟩ := ne_of_disjoint_pair h1
  have hcN : c ∈ ({a, b}ᶜ : Finset (Fin n)) := by simp [hca, hcb]
  have hcM : c ∉ M := by simp [hMdef]
  have haN : a ∈ ({c, d}ᶜ : Finset (Fin n)) := by simp [Ne.symm hca, Ne.symm hda]
  have haM : a ∉ M := by rw [hM₂]; simp
  have hNc : ∀ x y : Fin n, x ≠ y → 2 ≤ (({x, y}ᶜ : Finset (Fin n))).card := by
    intro x y hxy
    have h2 : (({x, y}ᶜ : Finset (Fin n))).card = n - 2 := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hxy]
    have h3 := Finset.card_le_card hM₁N
    omega
  set ψ₁ := (P a b hab).Φ.comp (Subgroup.inclusion (blockSpecialLinear_mono (K := F) hM₁N))
    with hψ₁
  set ψ₂ := (P c d hcd).Φ.comp (Subgroup.inclusion (blockSpecialLinear_mono (K := F) hM₂N))
    with hψ₂
  have hinj₁ : Function.Injective ψ₁ :=
    (P a b hab).injective_comp_inclusion hM₁N hcN hcM (hNc a b hab)
  have hinj₂ : Function.Injective ψ₂ :=
    (P c d hcd).injective_comp_inclusion hM₂N haN haM (hNc c d hcd)
  have hr₁ : ψ₁.range = centralizerPerfectCore (modelToG e (Xr a b) ⊔ modelToG e (Xr c d)) := by
    rw [hψ₁, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact map_eq_centralizerPerfectCore_pair e hXr hXy P hab hcd h1 hM
  have hr₂ : ψ₂.range = centralizerPerfectCore (modelToG e (Xr a b) ⊔ modelToG e (Xr c d)) := by
    rw [hψ₂, MonoidHom.range_comp, Subgroup.inclusion_range, sup_comm]
    have hM' : 3 ≤ (({c, d}ᶜ : Finset (Fin n)) \ {a, b}).card := hM₂ ▸ hM
    have h := map_eq_centralizerPerfectCore_pair e hXr hXy P hcd hab h1.symm hM'
    rwa [← hM₂] at h
  set τ : MulAut (blockSpecialLinear (K := F) M) :=
    (MonoidHom.ofInjective hinj₁).trans ((MulEquiv.subgroupCongr (hr₁.trans hr₂.symm)).trans
      (MonoidHom.ofInjective hinj₂).symm) with hτ
  have hτψ : ∀ x, ψ₂ (τ x) = ψ₁ x := by
    intro x
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hinj₂).apply_symm_apply
      ((MulEquiv.subgroupCongr (hr₁.trans hr₂.symm)) (MonoidHom.ofInjective hinj₁ x)))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hN1 : ∀ x : blockSpecialLinear (K := K) M,
      ψ₁ ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
        ψ₂ ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ := by
    intro x
    have e₁ := (P a b hab).N1 ⟨x, blockSpecialLinear_mono hM₁N x.2⟩
    have e₂ := (P c d hcd).N1 ⟨x, blockSpecialLinear_mono hM₂N x.2⟩
    exact e₁.trans e₂.symm
  have hfixτ : ∀ x : blockSpecialLinear (K := K) M,
      τ ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
        ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ :=
    fun x => hinj₂ ((hτψ _).trans (hN1 x))
  have hrig := eq_one_or_eq_mapBlock_of_fix_subfield hM ι hσσ hfix τ hfixτ
  have hτA : ∀ x : blockSpecialLinear (K := F) M,
      (x : SpecialLinearGroup (Fin n) F) ∈ blockSpecialLinear (K := F) A →
        ((τ x : blockSpecialLinear (K := F) M) : SpecialLinearGroup (Fin n) F) ∈
          blockSpecialLinear (K := F) A := by
    intro x hx
    rcases hrig with h | h
    · rw [h x]
      exact hx
    · rw [h x, coe_mapBlock_apply]
      exact map_ringHom_mem_blockSpecialLinear σ.toRingHom hx
  rintro _ ⟨y, hy, rfl⟩
  replace hy := mem_subgroupOf.1 hy
  set x : blockSpecialLinear (K := F) M := ⟨y, blockSpecialLinear_mono hAM hy⟩ with hx
  have hyx : y = Subgroup.inclusion (blockSpecialLinear_mono (K := F) hM₁N) x := rfl
  refine ⟨Subgroup.inclusion (blockSpecialLinear_mono (K := F) hM₂N) (τ x),
    mem_subgroupOf.2 (hτA x hy), ?_⟩
  rw [hyx]
  exact hτψ x

theorem map_eq_map_of_disjoint_roots_of_seven_le (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) {A : Finset (Fin n)}
    (h1 : Disjoint ({a, b} : Finset (Fin n)) {c, d}) (h2 : Disjoint A {a, b})
    (h3 : Disjoint A {c, d}) (hn : 7 ≤ n) :
    ((blockSpecialLinear (K := F) A).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ =
    ((blockSpecialLinear (K := F) A).subgroupOf
      (blockSpecialLinear ({c, d}ᶜ : Finset (Fin n)))).map (P c d hcd).Φ := by
  obtain ⟨hca, hcb, hda, hdb⟩ := ne_of_disjoint_pair h1
  have hM : 3 ≤ (({a, b}ᶜ : Finset (Fin n)) \ {c, d}).card := by
    rw [card_sdiff_pair_of_disjoint_pair hab hcd hca hcb hda hdb]
    omega
  have hM' : 3 ≤ (({c, d}ᶜ : Finset (Fin n)) \ {a, b}).card := by
    rw [← compl_pair_sdiff_comm]
    exact hM
  have hAM : A ⊆ ({a, b}ᶜ : Finset (Fin n)) \ {c, d} := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_compl]
    exact ⟨fun h => Finset.disjoint_left.1 h2 hx h, fun h => Finset.disjoint_left.1 h3 hx h⟩
  have hAM' : A ⊆ ({c, d}ᶜ : Finset (Fin n)) \ {a, b} := by
    rw [← compl_pair_sdiff_comm]
    exact hAM
  exact le_antisymm
    (map_le_map_of_disjoint_roots_of_rigidity e hσσ hfix hXr hXy P hab hcd h1 hM hAM)
    (map_le_map_of_disjoint_roots_of_rigidity e hσσ hfix hXr hXy P hcd hab h1.symm hM' hAM')

theorem fieldRevComm_of_seven_le (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    (hn : 7 ≤ n) : FieldRevComm e P := by
  intro a b hab A hA hdis
  have hstep₁ : ∀ (c d : Fin n) (hcd : c ≠ d), Disjoint ({a, b} : Finset (Fin n)) {c, d} →
      Disjoint A ({c, d} : Finset (Fin n)) →
      ((blockSpecialLinear (K := F) A).subgroupOf
        (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ =
      ((blockSpecialLinear (K := F) A).subgroupOf
        (blockSpecialLinear ({c, d}ᶜ : Finset (Fin n)))).map (P c d hcd).Φ :=
    fun c d hcd h1 h3 =>
      map_eq_map_of_disjoint_roots_of_seven_le e hσσ hfix hXr hXy P hab hcd h1 hdis h3 hn
  have hstep : ∀ (c d : Fin n) (hcd : c ≠ d), Disjoint A ({c, d} : Finset (Fin n)) →
      ((blockSpecialLinear (K := F) A).subgroupOf
        (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ =
      ((blockSpecialLinear (K := F) A).subgroupOf
        (blockSpecialLinear ({c, d}ᶜ : Finset (Fin n)))).map (P c d hcd).Φ := by
    intro c d hcd hdis'
    by_cases h1 : Disjoint ({a, b} : Finset (Fin n)) {c, d}
    · exact hstep₁ c d hcd h1 hdis'
    · have hcard : ({a, b} ∪ {c, d} : Finset (Fin n)).card ≤ 3 := by
        have hne := Finset.not_disjoint_iff_nonempty_inter.1 h1
        have h5 := Finset.card_union_add_card_inter ({a, b} : Finset (Fin n)) {c, d}
        have h6 := Finset.card_le_two (a := a) (b := b)
        have h7 := Finset.card_le_two (a := c) (b := d)
        have h8 := hne.card_pos
        omega
      obtain ⟨u, v, huv, huvdis⟩ := exists_root_disjoint
        (S := ({a, b} ∪ {c, d} ∪ A : Finset (Fin n))) (by
          have := Finset.card_union_le ({a, b} ∪ {c, d} : Finset (Fin n)) A
          omega)
      have hu1 : Disjoint ({a, b} : Finset (Fin n)) {u, v} :=
        huvdis.mono_left (Finset.subset_union_left.trans Finset.subset_union_left)
      have hu2 : Disjoint ({c, d} : Finset (Fin n)) {u, v} :=
        huvdis.mono_left (Finset.subset_union_right.trans Finset.subset_union_left)
      have hu3 : Disjoint A ({u, v} : Finset (Fin n)) := huvdis.mono_left Finset.subset_union_right
      rw [hstep₁ u v huv hu1 hu3, map_eq_map_of_disjoint_roots_of_seven_le e hσσ hfix hXr hXy P
        huv hcd hu2.symm hu3 hdis' hn]
  rw [le_centralizer_iff]
  have hmod : modelToG e (blockSL (K := K) Aᶜ) = (blockSpecialLinear (K := K) Aᶜ).map
      (L.subtype.comp (e.symm.toMonoidHom.comp (LinearFlag.proj n K))) := by
    rw [modelToG, blockSL, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hmod, Subgroup.map_le_iff_le_comap, blockSpecialLinear_eq_closure, closure_le]
  rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
  obtain ⟨u, v, huv, huvdis⟩ := exists_root_disjoint (S := (A ∪ {i, j} : Finset (Fin n)))
    (by
      have h1 := Finset.card_union_le A ({i, j} : Finset (Fin n))
      have h2 := Finset.card_le_two (a := i) (b := j)
      omega)
  have hAuv : Disjoint A ({u, v} : Finset (Fin n)) := huvdis.mono_left Finset.subset_union_left
  have hijuv : ({i, j} : Finset (Fin n)) ⊆ ({u, v}ᶜ : Finset (Fin n)) :=
    Finset.subset_compl_iff_disjoint_right.2 (huvdis.mono_left Finset.subset_union_right)
  have hijA : Disjoint ({i, j} : Finset (Fin n)) A := by
    rw [Finset.disjoint_left]
    intro x hx hxA
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_compl.1 hi hxA
    · rw [Finset.mem_singleton.1 hx] at hxA
      exact Finset.mem_compl.1 hj hxA
  rw [SetLike.mem_coe, Subgroup.mem_comap, hstep u v huv hAuv]
  refine map_le_centralizer_map_of_disjoint (P u v huv).Φ hijA
    (modelToG_blockSL_le_map (P u v huv) hijuv ?_)
  exact symm_mem_modelToG e (proj_mem_blockSL
    (transvection_mem_blockSpecialLinear hij (by simp) (by simp) c))

end Pair

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldRow_compl_of_seven_le (hset : SeitzSetting G L) {m f : ℕ} (hm : 6 ≤ m)
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Xr : Fin (m + 1) → Fin (m + 1) → Subgroup (LinearFlag.projectiveSL (m + 1) K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin (m + 1)) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin (m + 1), a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin (m + 1)))) :
    False :=
  false_of_fieldRow_compl hset (by omega) hKc hf e ht hKt ι hσ1 hσσ hfix hXr P
    (fieldRevComm_of_seven_le e hσσ hfix hXr hXy P (by omega))

end FieldRow

end CFSG.SeitzReduction.LinearPilot
