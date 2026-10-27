module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4FourSL2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open
open scoped MatrixGroups

namespace E6CartanRankFourAux

open CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth (c3 u1 c3_pow_three c3_ne_one c3_pow_commute_u1)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (orderThreeHom pow_three_eq_one_of_multiplicative_zmod)

section Group

variable {F : Type} [Field F] {S : Type} [Group S]

theorem exists_elemAbelian_three_pow {k : ℕ} (ψ : Fin k → SL(2, F) →* S)
    (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧
      ∀ N : Subgroup S, (∀ i, ψ i c3 ∈ N) → E ≤ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : ∀ i, ψ i c3 ^ 3 = 1 := fun i => by rw [← map_pow, c3_pow_three, map_one]
  have hy1 : ∀ i, ψ i c3 ≠ 1 := fun i h => c3_ne_one (hψ i (h.trans (map_one (ψ i)).symm))
  let ϕ : ∀ _ : Fin k, Multiplicative (ZMod 3) →* S := fun i => orderThreeHom (ψ i c3) (hy3 i)
  have hϕ : ∀ i s, ϕ i s = ψ i c3 ^ (Multiplicative.toAdd s).val := fun i s => rfl
  have hϕψ : ∀ i s, ϕ i s = ψ i (c3 ^ (Multiplicative.toAdd s).val) := fun i s => by
    rw [hϕ, map_pow]
  have hcomm : Pairwise fun i j : Fin k => ∀ (a b : Multiplicative (ZMod 3)),
      Commute (ϕ i a) (ϕ j b) := fun i j hij a b => by
    rw [hϕψ, hϕψ]
    exact hc i j hij _ _
  have hϕinj : ∀ i, Function.Injective (ϕ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro s hs
    have h : ψ i c3 ^ (Multiplicative.toAdd s).val = 1 := hs
    have hord : orderOf (ψ i c3) = 3 := orderOf_eq_prime (hy3 i) (hy1 i)
    have h3 : 3 ∣ (Multiplicative.toAdd s).val := by
      have := orderOf_dvd_of_pow_eq_one h
      rwa [hord] at this
    have hlt := ZMod.val_lt (Multiplicative.toAdd s)
    have h0 : (Multiplicative.toAdd s).val = 0 := by omega
    exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h0)
  have hcen : ∀ i j, i ≠ j → (ϕ j).range ≤ Subgroup.centralizer ((ψ i).range : Set S) := by
    rintro i j hij _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    rw [hϕψ]
    exact (hc i j hij A _).eq
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    obtain ⟨hgi, hgj⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨s, rfl⟩ := hgi
    have hgc : ϕ i s ∈ Subgroup.centralizer ((ψ i).range : Set S) :=
      (iSup₂_le fun j hj => hcen i j (Ne.symm hj)) hgj
    have h3 : 3 ∣ (Multiplicative.toAdd s).val :=
      TwE6FourRankAux.exponent_eq_of_commute_u1 (hψ i) (y := ϕ i s)
        (fun B => (Subgroup.mem_centralizer_iff.1 hgc (ψ i B) ⟨B, rfl⟩).symm) (hϕ i s).symm
    obtain ⟨m, hm⟩ := h3
    rw [Subgroup.mem_bot, hϕ, hm, pow_mul, hy3 i, one_pow]
  set Φ := MonoidHom.noncommPiCoprod ϕ hcomm with hΦdef
  have hΦ : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ hind hϕinj
  refine ⟨Φ.range, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨t, ht⟩ := b.2
    change (a : S) * b = b * a
    rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨s, rfl⟩
    have hs3 : s ^ 3 = 1 := funext fun i => pow_three_eq_one_of_multiplicative_zmod (s i)
    rw [← map_pow, hs3, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_pi]
    simp [TwE6FourRankAux.card_multiplicative_zmod_three]
  · intro N hN
    rw [hΦdef, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    rw [hϕ]
    exact Subgroup.pow_mem N (hN i) _

theorem inner_of_elemAbelian (hZ : ∀ a : S, (∀ x : S, a * x = x * a) → a = 1) {k : ℕ}
    {E U : Subgroup S} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ k) (hU0 : U ≠ ⊥)
    (hU2 : IsPGroup 2 ↥U) (hEN : E ≤ Subgroup.normalizer (U : Set S)) :
    ∃ A : Subgroup (MulAut S), IsElemAbelian 3 A ∧ Nat.card A = 3 ^ k ∧
      A ≤ (MulAut.conj : S →* MulAut S).range ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ A, ∀ u ∈ U, φ u ∈ U := by
  haveI : IsMulCommutative E := hE.1
  let κ : E →* MulAut S := (MulAut.conj : S →* MulAut S).comp E.subtype
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    apply hZ (a : S)
    intro x
    have hx := congrArg (fun φ : MulAut S => φ x) ha
    simp only [κ, MonoidHom.comp_apply, MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul).1 hx
  have hκcard : Nat.card κ.range = 3 ^ k := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv).symm
  have hκel : IsElemAbelian 3 κ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      show (x : MulAut S) * (y : MulAut S) = (y : MulAut S) * (x : MulAut S)
      rw [← ha, ← hb]
      change κ a * κ b = κ b * κ a
      rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm a b]
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
      have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (a : S) a.2)
      rw [← ha, ← map_pow, h3, map_one]
  refine ⟨κ.range, hκel, hκcard, ?_, U, hU0, hU2, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨(a : S), rfl⟩
  · rintro φ hφ u hu
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hφ
    show MulAut.conj (a : S) u ∈ U
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hEN a.2) u).1 hu

end Group

section Lie

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley
open scoped commutatorElement


variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def levelGen (τ : Tag) (K : Type) [Field K] (J : Finset (Fin τ.rank))
    (β : Fin τ.rank → ℤ) : Set (ModGL τ K) :=
  {g | ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ (∀ j, j ∉ J → γ j = β j) ∧ ∃ c : K, pinnedX τ K γ c = g}

@[expose] noncomputable def levelGroup (τ : Tag) (K : Type) [Field K] (J : Finset (Fin τ.rank))
    (β : Fin τ.rank → ℤ) : Subgroup (ModGL τ K) :=
  Subgroup.closure (levelGen τ K J β)

theorem pinnedX_mem_levelGroup {J : Finset (Fin τ.rank)} {β γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγJ : ∀ j, j ∉ J → γ j = β j) (c : K) : pinnedX τ K γ c ∈ levelGroup τ K J β :=
  Subgroup.subset_closure ⟨γ, hγ, hγJ, c, rfl⟩

theorem conj_mem_levelGroup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {J : Finset (Fin τ.rank)} {β : Fin τ.rank → ℤ} {j₀ : Fin τ.rank} (hj₀ : j₀ ∉ J)
    (hβ : 0 < β j₀) {δ γ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hδJ : ∀ j, j ∉ J → δ j = 0)
    (hγ : IsRoot τ γ) (hγJ : ∀ j, j ∉ J → γ j = β j) (t c : K) :
    pinnedX τ K δ t * pinnedX τ K γ c * (pinnedX τ K δ t)⁻¹ ∈ levelGroup τ K J β := by
  have h0 : δ j₀ = 0 := hδJ j₀ hj₀
  have hγ0 : γ j₀ = β j₀ := hγJ j₀ hj₀
  have hne : δ ≠ γ := fun h => by
    rw [h, hγ0] at h0
    omega
  have hne' : δ ≠ -γ := fun h => by
    have := congrFun h j₀
    simp only [Pi.neg_apply] at this
    omega
  obtain ⟨hform, hcomm⟩ := simply_laced_root_commutator_unit τ hτ hδ hγ hne hne'
  by_cases hs : IsRoot τ (δ + γ)
  · obtain ⟨-, hf⟩ := hform hs
    have h1 := hf K t c
    rw [commutatorElement_def] at h1
    have h2 : pinnedX τ K δ t * pinnedX τ K γ c * (pinnedX τ K δ t)⁻¹ =
        pinnedX τ K (δ + γ) ((commConst τ δ γ (1, 1) : K) * t * c) * pinnedX τ K γ c := by
      rw [← h1]
      group
    rw [h2]
    refine mul_mem (pinnedX_mem_levelGroup hs (fun j hj => ?_) _)
      (pinnedX_mem_levelGroup hγ hγJ c)
    simp [hδJ j hj, hγJ j hj]
  · have h1 := (hcomm hs K (pinnedX τ K δ t) (mem_rootSubgroup.2 ⟨t, rfl⟩) (pinnedX τ K γ c)
      (mem_rootSubgroup.2 ⟨c, rfl⟩)).eq
    rw [h1, mul_inv_cancel_right]
    exact pinnedX_mem_levelGroup hγ hγJ c

theorem pinnedX_mem_normalizer (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {J : Finset (Fin τ.rank)} {β : Fin τ.rank → ℤ} {j₀ : Fin τ.rank} (hj₀ : j₀ ∉ J)
    (hβ : 0 < β j₀) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hδJ : ∀ j, j ∉ J → δ j = 0) (t : K) :
    pinnedX τ K δ t ∈ Subgroup.normalizer (levelGroup τ K J β : Set (ModGL τ K)) := by
  have key : ∀ s : K, ∀ u ∈ levelGroup τ K J β,
      pinnedX τ K δ s * u * (pinnedX τ K δ s)⁻¹ ∈ levelGroup τ K J β := by
    intro s u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, hγJ, c, rfl⟩ := hx
      exact conj_mem_levelGroup hτ hj₀ hβ hδ hδJ hγ hγJ s c
    | one => simp [Subgroup.one_mem]
    | mul x y _ _ hx hy =>
      have e : pinnedX τ K δ s * (x * y) * (pinnedX τ K δ s)⁻¹ =
          (pinnedX τ K δ s * x * (pinnedX τ K δ s)⁻¹) *
            (pinnedX τ K δ s * y * (pinnedX τ K δ s)⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : pinnedX τ K δ s * x⁻¹ * (pinnedX τ K δ s)⁻¹ =
          (pinnedX τ K δ s * x * (pinnedX τ K δ s)⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key t h, fun hh => ?_⟩
  have h2 := key (-t) _ hh
  rw [← pinnedX_neg] at h2
  have e : (pinnedX τ K δ t)⁻¹ * (pinnedX τ K δ t * h * (pinnedX τ K δ t)⁻¹) *
      ((pinnedX τ K δ t)⁻¹)⁻¹ = h := by group
  rwa [e] at h2

theorem rootSL2_mem_normalizer [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {J : Finset (Fin τ.rank)} {β : Fin τ.rank → ℤ} {j₀ : Fin τ.rank} (hj₀ : j₀ ∉ J)
    (hβ : 0 < β j₀) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαJ : ∀ j, j ∉ J → α j = 0)
    (A : SL2 K) :
    rootSL2 τ K α A ∈ Subgroup.normalizer (levelGroup τ K J β : Set (ModGL τ K)) := by
  have hrange := (even_Chevalley_pinned_root_SL2_maps τ K hα).2.1
  have hmem : rootSL2 τ K α A ∈ (rootSL2 τ K α).range := ⟨A, rfl⟩
  rw [hrange] at hmem
  have hle : rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ≤
      Subgroup.normalizer (levelGroup τ K J β : Set (ModGL τ K)) := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
      exact pinnedX_mem_normalizer hτ hj₀ hβ hα hαJ t
    · intro g hg
      obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
      exact pinnedX_mem_normalizer hτ hj₀ hβ (IsRoot.neg hα)
        (fun j hj => by simp [hαJ j hj]) t
  exact hle hmem

theorem levelGroup_le_posUnipotent {J : Finset (Fin τ.rank)} {β : Fin τ.rank → ℤ}
    {j₀ : Fin τ.rank} (hj₀ : j₀ ∉ J) (hβ : 0 < β j₀) :
    levelGroup τ K J β ≤ posUnipotent τ K := by
  rw [levelGroup, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, hγJ, c, rfl⟩
  have hpos : 0 < height γ := by
    rw [IsRoot.height_pos_iff hγ]
    rcases hγ.nonneg_or_nonpos with h | h
    · exact h
    · exfalso
      have h1 := h j₀
      rw [hγJ j₀ hj₀] at h1
      omega
  have hle : rootSubgroup τ K γ ≤ posUnipotent τ K :=
    le_iSup₂_of_le (f := fun (α : Fin τ.rank → ℤ) (_ : α ∈ {α | IsRoot τ α ∧ 0 < height α}) =>
      rootSubgroup τ K α) γ ⟨hγ, hpos⟩ le_rfl
  exact hle (Subgroup.subset_closure ⟨c, rfl⟩)

@[expose] def StronglyOrthogonalCheck (τ : Tag) {k : ℕ} (α : Fin k → Fin τ.rank → ℤ) : Prop :=
  (∀ i, RootOps.isRootB τ (α i) = true) ∧
    ∀ i j, i ≠ j → iform (α i) (α j) = 0 ∧ RootOps.isRootB τ (α i + α j) = false ∧
      RootOps.isRootB τ (α i - α j) = false

theorem exists_levi_witness [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : ℕ} (α : Fin k → Fin τ.rank → ℤ)
    (hα : StronglyOrthogonalCheck τ α) {J : Finset (Fin τ.rank)}
    (hαJ : ∀ i j, j ∉ J → α i j = 0) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {j₀ : Fin τ.rank} (hj₀ : j₀ ∉ J) (hβj₀ : 0 < β j₀) :
    ∃ (ι : Fin k → (SL2 K →* adjointGroup τ K)) (U : Subgroup (adjointGroup τ K)),
      (∀ i, Function.Injective (ι i)) ∧
      (∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A) ∧
      U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ i, ∀ A : SL2 K, ι i A ∈ Subgroup.normalizer (U : Set (adjointGroup τ K)) := by
  have hroot : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hα.1 i)
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  let ι : Fin k → (SL2 K →* adjointGroup τ K) := fun i =>
    (rootSL2 τ K (α i)).codRestrict (adjointGroup τ K)
      (exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.1
  refine ⟨ι, (levelGroup τ K J β).comap (adjointGroup τ K).subtype, fun i A B hAB => ?_,
    fun i j hij A B => ?_, ?_, ?_, fun i A => ?_⟩
  · exact (even_Chevalley_pinned_root_SL2_maps τ K (hroot i)).1 (congrArg Subtype.val hAB)
  · obtain ⟨h0, hp, hm⟩ := hα.2 i j hij
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hroot i) (hroot j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)
  · intro hbot
    have hmem : (⟨pinnedX τ K β 1, pinnedX_mem_adjointGroup β 1⟩ : adjointGroup τ K) ∈
        (levelGroup τ K J β).comap (adjointGroup τ K).subtype :=
      pinnedX_mem_levelGroup hβ (fun _ _ => rfl) 1
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : pinnedX τ K β 1 = pinnedX τ K β 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val hmem
    exact one_ne_zero (pinnedX_injective τ K β h1)
  · have hU : IsPGroup 2 (posUnipotent τ K) := ((positive_root_triangularity.{0, 0} τ).2 K 2).2.1
    exact (hU.to_le (levelGroup_le_posUnipotent hj₀ hβj₀)).comap_subtype
  · exact Subgroup.le_normalizer_comap (adjointGroup τ K).subtype
      (rootSL2_mem_normalizer hτ hj₀ hβj₀ (hroot i) (hαJ i) A)

theorem exists_cartan_generic [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : ℕ} (α : Fin k → Fin τ.rank → ℤ)
    (hα : StronglyOrthogonalCheck τ α) {J : Finset (Fin τ.rank)}
    (hαJ : ∀ i j, j ∉ J → α i j = 0) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {j₀ : Fin τ.rank} (hj₀ : j₀ ∉ J) (hβj₀ : 0 < β j₀) :
    ∃ E U : Subgroup (adjointGroup τ K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧ U ≠ ⊥ ∧
      IsPGroup 2 ↥U ∧ E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K)) := by
  obtain ⟨ι, U, hι, hc, hU0, hU2, hN⟩ := exists_levi_witness (K := K) hτ α hα hαJ hβ hj₀ hβj₀
  obtain ⟨E, hEel, hEcard, hEN⟩ := exists_elemAbelian_three_pow ι hι
    (fun i j hij A B => hc i j hij A B)
  exact ⟨E, U, hEel, hEcard, hU0, hU2, hEN _ fun i => hN i _⟩

@[expose] def e6D4Roots : Fin 4 → Fin 6 → ℤ :=
  ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 1, 0]]

@[expose] def e6D4Nodes : Finset (Fin 6) := {1, 2, 3, 4}

theorem e6D4Roots_check : StronglyOrthogonalCheck Tag.E6 e6D4Roots := by
  unfold StronglyOrthogonalCheck
  decide +kernel

theorem e6D4Nodes_not_mem : (0 : Fin 6) ∉ e6D4Nodes := by
  decide +kernel

theorem e6_beta_pos : 0 < (Pi.single (0 : Fin 6) 1 : Fin 6 → ℤ) 0 := by
  simp

theorem e6_beta_isRoot : IsRoot Tag.E6 (Pi.single (0 : Fin 6) 1 : Fin 6 → ℤ) :=
  isRoot_single Tag.E6 (0 : Fin 6)

theorem e6D4Roots_supp : ∀ i j, j ∉ e6D4Nodes → e6D4Roots i j = 0 := by
  decide +kernel

theorem e6_levi_witness [Finite K] [CharP K 2] :
    ∃ (ι : Fin 4 → (SL2 K →* adjointGroup Tag.E6 K)) (U : Subgroup (adjointGroup Tag.E6 K)),
      (∀ i, Function.Injective (ι i)) ∧
      (∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A) ∧
      U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
      ∀ i, ∀ A : SL2 K, ι i A ∈ Subgroup.normalizer (U : Set (adjointGroup Tag.E6 K)) :=
  exists_levi_witness (Or.inr (Or.inl rfl)) e6D4Roots e6D4Roots_check e6D4Roots_supp
    (β := (Pi.single (0 : Fin 6) 1 : Fin 6 → ℤ)) e6_beta_isRoot (j₀ := (0 : Fin 6))
    e6D4Nodes_not_mem e6_beta_pos

end Lie

end E6CartanRankFourAux

section Main

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem e6CartanRankFour_holds : E6CartanRankFour := by
  intro S _ _ d q hd hq hiso
  obtain ⟨eL⟩ := hiso
  obtain ⟨d1, hv⟩ := d
  have hd' : d1 = TauCeti.LieTypeIndex.E6 q := hd
  subst hd'
  have hq1 : q.p = 2 := by rcases hq with h | h <;> exact h.1
  have hK : Nat.card (GaloisField 2 q.exponent) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 q.exponent q.exponent_pos.ne', hq1]
  obtain ⟨eB⟩ :=
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq1 (GaloisField 2 q.exponent) hK
  let eZ : AdjointQuotient Tag.E6 (GaloisField 2 q.exponent) ≃*
      ↥(adjointGroup Tag.E6 (GaloisField 2 q.exponent)) :=
    (QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := Tag.E6) (K := GaloisField 2 q.exponent))).trans
      QuotientGroup.quotientBot
  let eS : ↥(adjointGroup Tag.E6 (GaloisField 2 q.exponent)) ≃* S :=
    eZ.symm.trans (eB.trans eL.symm)
  have hZ : ∀ a : S, (∀ x : S, a * x = x * a) → a = 1 := by
    intro a ha
    have h1 : eS.symm a ∈ Subgroup.center ↥(adjointGroup Tag.E6 (GaloisField 2 q.exponent)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply eS.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (ha (eS g)).symm
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h1
    simpa using congrArg eS h1
  obtain ⟨ι, U, hι, hc, hU0, hU2, hN⟩ :=
    E6CartanRankFourAux.e6_levi_witness (K := GaloisField 2 q.exponent)
  let ψ : Fin 4 → SL(2, GaloisField 2 q.exponent) →* S := fun i => eS.toMonoidHom.comp (ι i)
  have hψ : ∀ i, Function.Injective (ψ i) := fun i => eS.injective.comp (hι i)
  have hψc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := fun i j hij A B => by
    show eS (ι i A) * eS (ι j B) = eS (ι j B) * eS (ι i A)
    rw [← map_mul, ← map_mul, hc i j hij A B]
  obtain ⟨E, hEel, hEcard, hEN⟩ := E6CartanRankFourAux.exists_elemAbelian_three_pow ψ hψ hψc
  have hUS0 : U.map eS.toMonoidHom ≠ ⊥ := fun h =>
    hU0 ((Subgroup.map_eq_bot_iff_of_injective U (f := eS.toMonoidHom) eS.injective).1 h)
  have hUS2 : IsPGroup 2 ↥(U.map eS.toMonoidHom) := hU2.map _
  have hEUS : E ≤ Subgroup.normalizer ((U.map eS.toMonoidHom : Subgroup S) : Set S) :=
    hEN _ fun i => Subgroup.le_normalizer_map eS.toMonoidHom
      (Subgroup.mem_map_of_mem _ (hN i CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.c3))
  exact E6CartanRankFourAux.inner_of_elemAbelian hZ hEel hEcard hUS0 hUS2 hEUS

end Main

section Sylow

set_option linter.unusedSectionVars false


theorem gen2318RankFour_of_sylow' (hU : Gen2318RankFourSylowUniq) : Gen2318RankFour :=
  gen2318RankFour_of_parts hU f4FourSL2_holds e6CartanRankFour_holds

end Sylow

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
