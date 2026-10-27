module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFactPiece
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Generic

theorem fixAll_prodCongr {S S' : Type*} [Group S] [Group S'] {ι' : Type*} (γ : ι' → MulAut S)
    (γ' : ι' → MulAut S') :
    fixAll (fun i => MulEquiv.prodCongr (γ i) (γ' i)) = (fixAll γ).prod (fixAll γ') := by
  ext ⟨x, y⟩
  have h : ∀ i, MulEquiv.prodCongr (γ i) (γ' i) (x, y) = (γ i x, γ' i y) := fun i => rfl
  simp only [mem_fixAll, mem_prod, h, Prod.mk.injEq]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

theorem derivedSeriesOf_subgroup_prod {M₁ M₂ : Type*} [Group M₁] [Group M₂] (H : Subgroup M₁)
    (H' : Subgroup M₂) (k : ℕ) :
    CFSG.Quasithin.derivedSeriesOf (H.prod H') k =
      (CFSG.Quasithin.derivedSeriesOf H k).prod (CFSG.Quasithin.derivedSeriesOf H' k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_succ,
      CFSG.Quasithin.derivedSeriesOf_succ, ih, commutator_prod_prod]

theorem perfectCore_subgroup_prod {M₁ M₂ : Type*} [Group M₁] [Group M₂] (H : Subgroup M₁)
    (H' : Subgroup M₂) : perfectCore (H.prod H') = (perfectCore H).prod (perfectCore H') := by
  ext x
  simp only [perfectCore, derivedSeriesOf_subgroup_prod, mem_iInf, mem_prod, forall_and]

variable {G : Type*} [Group G]

theorem eq_or_eq_of_sup_eq_sup {A B C D : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hCD : D ≤ centralizer (C : Set G)) (hsA : IsSimpleGroup A) (hsB : IsSimpleGroup B)
    (hsC : IsSimpleGroup C) (hnaC : ∃ a b : C, a * b ≠ b * a) (h : A ⊔ B = C ⊔ D) :
    C = A ∨ C = B :=
  F4Pilot.eq_or_eq_of_isSimpleGroup_of_le_sup hAB hsA hsB hsC hnaC (h ▸ le_sup_left)
    (h ▸ F4Pilot.sup_le_normalizer_left_of_le_centralizer hCD)

theorem exists_mul_ne_mul_of_commutator_eq {H : Subgroup G} (hH : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    ∃ a b : H, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hne
  rw [← hH, commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)

end Generic

section SL2

variable {K : Type*} [Field K]

theorem center_specialLinearGroup_two_eq_bot [CharP K 2] :
    center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

theorem isSimpleGroup_specialLinearGroup_two [CharP K 2] (hK : 4 ≤ Nat.card K) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  have e : SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_specialLinearGroup_two_eq_bot.symm)
  exact e.isSimpleGroup

variable {n : ℕ}

@[expose] noncomputable def blockSpecialLinearEquivOfCardTwo {I : Finset (Fin n)}
    (hI : I.card = 2) : SpecialLinearGroup (Fin 2) K ≃* blockSpecialLinear (K := K) I :=
  (reindexSpecialLinear ((finCongr hI.symm).trans I.equivFin.symm)).trans
    ((MonoidHom.ofInjective (blockEmbed_injective I)).trans
      (MulEquiv.subgroupCongr (range_blockEmbed I)))

theorem isSimpleGroup_blockSpecialLinear_of_card_two [CharP K 2] {I : Finset (Fin n)}
    (hI : I.card = 2) (hK : 4 ≤ Nat.card K) : IsSimpleGroup (blockSpecialLinear (K := K) I) := by
  have := isSimpleGroup_specialLinearGroup_two hK
  exact (blockSpecialLinearEquivOfCardTwo hI).symm.isSimpleGroup

end SL2

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

structure SwapNeighbourParam (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (X : Subgroup G)
    (N : Finset (Fin n)) where
  Ψ : blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N →* G
  range_eq : Ψ.range = centralizerPerfectCore X
  ker_le : Ψ.ker ≤ center (blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N)
  diag : ∀ x : blockSpecialLinear (K := K) N,
    Ψ (x, x) = ((e.symm (LinearFlag.proj n K x) : L) : G)
  N2 : ∀ (c : blockTorusParam (K := K) (∅ : Finset (Fin n)))
    (x y : blockSpecialLinear (K := K) N),
    Ψ (conjDiag (RingHom.id K) N c x, conjDiag (RingHom.id K) N c y) =
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Ψ (x, y) *
        ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹
  swap : ∀ x y : blockSpecialLinear (K := K) N, t * Ψ (x, y) * t⁻¹ = Ψ (y, x)

variable {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {X : Subgroup G} {N : Finset (Fin n)}

@[expose] noncomputable def SwapNeighbourParam.fst (P : SwapNeighbourParam e t X N)
    (I : Finset (Fin n)) : Subgroup G :=
  ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map
    (P.Ψ.comp (MonoidHom.inl _ _))

@[expose] noncomputable def SwapNeighbourParam.snd (P : SwapNeighbourParam e t X N)
    (I : Finset (Fin n)) : Subgroup G :=
  ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map
    (P.Ψ.comp (MonoidHom.inr _ _))

namespace SwapNeighbourParam

variable (P : SwapNeighbourParam e t X N)

theorem commute_inl_inr (x y : blockSpecialLinear (K := K) N) :
    Commute (P.Ψ (x, 1)) (P.Ψ (1, y)) := by
  have h : ((x, 1) : blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N) * (1, y) =
      (1, y) * (x, 1) := by
    ext <;> simp
  change P.Ψ (x, 1) * P.Ψ (1, y) = P.Ψ (1, y) * P.Ψ (x, 1)
  rw [← map_mul, h, map_mul]

theorem snd_le_centralizer_fst (I J : Finset (Fin n)) :
    P.snd J ≤ centralizer (P.fst I : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, -, rfl⟩
  exact (P.commute_inl_inr x y).eq

theorem fst_le_centralizer_snd (I J : Finset (Fin n)) :
    P.fst J ≤ centralizer (P.snd I : Set G) :=
  le_centralizer_iff.1 (P.snd_le_centralizer_fst J I)

theorem fst_le_centralizer_fst_of_disjoint {I J : Finset (Fin n)} (hIJ : Disjoint I J) :
    P.fst J ≤ centralizer (P.fst I : Set G) :=
  le_centralizer_iff.1 (map_subgroupOf_le_centralizer_of_disjoint hIJ _)

theorem snd_le_centralizer_snd_of_disjoint {I J : Finset (Fin n)} (hIJ : Disjoint I J) :
    P.snd J ≤ centralizer (P.snd I : Set G) :=
  le_centralizer_iff.1 (map_subgroupOf_le_centralizer_of_disjoint hIJ _)

theorem map_conj_fst (I : Finset (Fin n)) :
    (P.fst I).map (MulAut.conj t).toMonoidHom = P.snd I := by
  rw [fst, snd, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.swap x 1

theorem map_conj_snd (I : Finset (Fin n)) :
    (P.snd I).map (MulAut.conj t).toMonoidHom = P.fst I := by
  rw [fst, snd, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.swap 1 x

theorem mul_conj_mem_modelToG_of_mem_fst {I : Finset (Fin n)} {x : G} (hx : x ∈ P.fst I) :
    x * (t * x * t⁻¹) ∈ modelToG e (blockSL (K := K) I) := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [P.swap, ← map_mul, show ((a, 1) : blockSpecialLinear (K := K) N ×
    blockSpecialLinear (K := K) N) * (1, a) = (a, a) by ext <;> simp, P.diag]
  exact symm_mem_modelToG e (proj_mem_blockSL (mem_subgroupOf.1 ha))

theorem mul_conj_mem_modelToG_of_mem_snd {I : Finset (Fin n)} {x : G} (hx : x ∈ P.snd I) :
    x * (t * x * t⁻¹) ∈ modelToG e (blockSL (K := K) I) := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply]
  rw [P.swap, ← map_mul, show ((1, a) : blockSpecialLinear (K := K) N ×
    blockSpecialLinear (K := K) N) * (a, 1) = (a, a) by ext <;> simp, P.diag]
  exact symm_mem_modelToG e (proj_mem_blockSL (mem_subgroupOf.1 ha))

theorem exists_mem_fst_mul_conj_eq {I : Finset (Fin n)} (hIN : I ⊆ N) {y : G}
    (hy : y ∈ modelToG e (blockSL (K := K) I)) :
    ∃ x ∈ P.fst I, x * (t * x * t⁻¹) = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hy
  obtain ⟨b, hb, rfl⟩ := hz
  refine ⟨P.Ψ (⟨b, blockSpecialLinear_mono hIN hb⟩, 1),
    ⟨⟨b, blockSpecialLinear_mono hIN hb⟩, mem_subgroupOf.2 hb, rfl⟩, ?_⟩
  rw [P.swap, ← map_mul, show ((⟨b, blockSpecialLinear_mono hIN hb⟩, 1) :
    blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N) *
      (1, ⟨b, blockSpecialLinear_mono hIN hb⟩) =
      (⟨b, blockSpecialLinear_mono hIN hb⟩, ⟨b, blockSpecialLinear_mono hIN hb⟩) by
    ext <;> simp, P.diag]

theorem exists_mem_snd_mul_conj_eq {I : Finset (Fin n)} (hIN : I ⊆ N) {y : G}
    (hy : y ∈ modelToG e (blockSL (K := K) I)) :
    ∃ x ∈ P.snd I, x * (t * x * t⁻¹) = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hy
  obtain ⟨b, hb, rfl⟩ := hz
  refine ⟨P.Ψ (1, ⟨b, blockSpecialLinear_mono hIN hb⟩),
    ⟨⟨b, blockSpecialLinear_mono hIN hb⟩, mem_subgroupOf.2 hb, rfl⟩, ?_⟩
  rw [P.swap, ← map_mul, show ((1, ⟨b, blockSpecialLinear_mono hIN hb⟩) :
    blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N) *
      (⟨b, blockSpecialLinear_mono hIN hb⟩, 1) =
      (⟨b, blockSpecialLinear_mono hIN hb⟩, ⟨b, blockSpecialLinear_mono hIN hb⟩) by
    ext <;> simp, P.diag]

end SwapNeighbourParam

end Param

section Pieces

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {X : Subgroup G} {N : Finset (Fin n)}

namespace SwapNeighbourParam

variable (P : SwapNeighbourParam e t X N)

theorem pieceCore_eq_map [Finite G] [Finite K] {I : Finset (Fin n)} (hIN : I ⊆ N) {k : Fin n}
    (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I)
    (hXI : X ≤ modelToG e (blockTorus (K := K) I)) :
    pieceCore e I = (((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).prod
      ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N))).map P.Ψ := by
  set T := modelToG e (blockTorus (K := K) I)
  let f : T → blockTorus (K := K) I := fun d =>
    ⟨e ⟨(d : G), modelToG_le e _ d.2⟩, apply_mem_blockTorus_of_mem_modelToG e d.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    refine ⟨⟨((e.symm y : L) : G), symm_mem_modelToG e hy⟩, Subtype.ext ?_⟩
    simp [f]
  let γ : blockTorus (K := K) I → MulAut (blockSpecialLinear (K := K) N) :=
    fun d => conjDiag (RingHom.id K) N (blockTorusLift d)
  have hα : ∀ (d : T) (x : blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N),
      P.Ψ (MulEquiv.prodCongr (γ (f d)) (γ (f d)) x) = (d : G) * P.Ψ x * (d : G)⁻¹ := by
    rintro d ⟨x, y⟩
    change P.Ψ (γ (f d) x, γ (f d) y) = _
    rw [P.N2, proj_torusDiagSL_blockTorusLift]
    have hd : ((e.symm ((f d : blockTorus (K := K) I) : LinearFlag.projectiveSL n K) : L) : G) =
        (d : G) := by
      simp [f]
    rw [hd]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_le P.Ψ P.ker_le hXI P.range_eq
    (fun d => MulEquiv.prodCongr (γ (f d)) (γ (f d))) hα]
  congr 1
  rw [show (fixAll fun d : T => MulEquiv.prodCongr (γ (f d)) (γ (f d))) =
      fixAll (fun d : blockTorus (K := K) I => MulEquiv.prodCongr (γ d) (γ d)) from
    fixAll_comp_of_surjective (fun d : blockTorus (K := K) I => MulEquiv.prodCongr (γ d) (γ d)) hf,
    fixAll_prodCongr, perfectCore_subgroup_prod,
    perfectCore_fixAll_conjDiag_blockTorusLift (RingHom.id K) hIN hk hκ hperf]

theorem map_prod_eq_fst_sup_snd (I : Finset (Fin n)) :
    (((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).prod
      ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N))).map P.Ψ =
      P.fst I ⊔ P.snd I := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have h : ((x, y) : blockSpecialLinear (K := K) N × blockSpecialLinear (K := K) N) =
        (x, 1) * (1, y) := by ext <;> simp
    rw [h, map_mul]
    exact mul_mem (mem_sup_left ⟨x, hx, rfl⟩) (mem_sup_right ⟨y, hy, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(x, 1), ⟨hx, one_mem _⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨(1, y), ⟨one_mem _, hy⟩, rfl⟩

theorem pieceCore_eq_fst_sup_snd [Finite G] [Finite K] {I : Finset (Fin n)} (hIN : I ⊆ N)
    {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I)
    (hXI : X ≤ modelToG e (blockTorus (K := K) I)) :
    pieceCore e I = P.fst I ⊔ P.snd I := by
  rw [P.pieceCore_eq_map hIN hk hκ hperf hXI, P.map_prod_eq_fst_sup_snd]

theorem ker_comp_inl_le_center :
    (P.Ψ.comp (MonoidHom.inl _ _)).ker ≤ center (blockSpecialLinear (K := K) N) := by
  intro x hx
  have h := P.ker_le (show ((x, 1) : blockSpecialLinear (K := K) N ×
    blockSpecialLinear (K := K) N) ∈ P.Ψ.ker from hx)
  rw [mem_center_iff] at h ⊢
  intro y
  have := congrArg Prod.fst (h (y, 1))
  simpa using this

theorem ker_comp_inr_le_center :
    (P.Ψ.comp (MonoidHom.inr _ _)).ker ≤ center (blockSpecialLinear (K := K) N) := by
  intro x hx
  have h := P.ker_le (show ((1, x) : blockSpecialLinear (K := K) N ×
    blockSpecialLinear (K := K) N) ∈ P.Ψ.ker from hx)
  rw [mem_center_iff] at h ⊢
  intro y
  have := congrArg Prod.snd (h (1, y))
  simpa using this

@[expose] noncomputable def fstEquiv {I : Finset (Fin n)} (hIN : I ⊆ N) (hne : I ≠ N) :
    P.fst I ≃* blockSpecialLinear (K := K) I :=
  ((MonoidHom.ofInjective (injective_comp_subtype_of_ker_le_center hIN hne _
      P.ker_comp_inl_le_center)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]; rfl))).symm.trans
    (Subgroup.subgroupOfEquivOfLe (blockSpecialLinear_mono hIN))

@[expose] noncomputable def sndEquiv {I : Finset (Fin n)} (hIN : I ⊆ N) (hne : I ≠ N) :
    P.snd I ≃* blockSpecialLinear (K := K) I :=
  ((MonoidHom.ofInjective (injective_comp_subtype_of_ker_le_center hIN hne _
      P.ker_comp_inr_le_center)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]; rfl))).symm.trans
    (Subgroup.subgroupOfEquivOfLe (blockSpecialLinear_mono hIN))

end SwapNeighbourParam

end Pieces

section Factors

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {X : Subgroup G} {N : Finset (Fin n)}

theorem exists_mul_ne_mul_of_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (h : ∃ a b : B, a * b ≠ b * a) : ∃ a b : A, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨φ.symm a, φ.symm b, fun h' => hab ?_⟩
  have := congrArg φ h'
  simpa using this

theorem exists_mul_ne_mul_blockSpecialLinear_of_card_two [Finite K] [CharP K 2]
    {I : Finset (Fin n)} (hI : I.card = 2) (hK : 4 ≤ Nat.card K) :
    ∃ a b : blockSpecialLinear (K := K) I, a * b ≠ b * a := by
  have := isSimpleGroup_blockSpecialLinear_of_card_two (K := K) hI hK
  exact exists_mul_ne_mul_of_commutator_eq (commutator_blockSpecialLinear_eq_of_two_le hI.ge hK)
    ((nontrivial_iff_ne_bot _).1 inferInstance)

namespace SwapNeighbourParam

variable (P : SwapNeighbourParam e t X N)

theorem isSimpleGroup_fst [CharP K 2] {I : Finset (Fin n)} (hIN : I ⊆ N) (hne : I ≠ N)
    (hI : I.card = 2) (hK : 4 ≤ Nat.card K) : IsSimpleGroup (P.fst I) := by
  have := isSimpleGroup_blockSpecialLinear_of_card_two (K := K) hI hK
  exact (P.fstEquiv hIN hne).isSimpleGroup

theorem isSimpleGroup_snd [CharP K 2] {I : Finset (Fin n)} (hIN : I ⊆ N) (hne : I ≠ N)
    (hI : I.card = 2) (hK : 4 ≤ Nat.card K) : IsSimpleGroup (P.snd I) := by
  have := isSimpleGroup_blockSpecialLinear_of_card_two (K := K) hI hK
  exact (P.sndEquiv hIN hne).isSimpleGroup

theorem exists_mul_ne_mul_fst [Finite K] [CharP K 2] {I : Finset (Fin n)} (hIN : I ⊆ N)
    (hne : I ≠ N) (hI : I.card = 2) (hK : 4 ≤ Nat.card K) : ∃ a b : P.fst I, a * b ≠ b * a :=
  exists_mul_ne_mul_of_mulEquiv (P.fstEquiv hIN hne)
    (exists_mul_ne_mul_blockSpecialLinear_of_card_two hI hK)

theorem exists_mul_ne_mul_snd [Finite K] [CharP K 2] {I : Finset (Fin n)} (hIN : I ⊆ N)
    (hne : I ≠ N) (hI : I.card = 2) (hK : 4 ≤ Nat.card K) : ∃ a b : P.snd I, a * b ≠ b * a :=
  exists_mul_ne_mul_of_mulEquiv (P.sndEquiv hIN hne)
    (exists_mul_ne_mul_blockSpecialLinear_of_card_two hI hK)

end SwapNeighbourParam

theorem SwapNeighbourParam.fst_eq_or_eq [Finite G] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (P : SwapNeighbourParam e t X N) {X' : Subgroup G} {N' : Finset (Fin n)}
    (P' : SwapNeighbourParam e t X' N') {α : Finset (Fin n)} (hα : α.card = 2) (hαN : α ⊆ N)
    (hαN' : α ⊆ N') (hne : α ≠ N) (hne' : α ≠ N') {k k' : Fin n} (hk : k ∉ N) (hk' : k' ∉ N')
    {κ : Kˣ} (hκ : κ ≠ 1) (hX : X ≤ modelToG e (blockTorus (K := K) α))
    (hX' : X' ≤ modelToG e (blockTorus (K := K) α)) :
    P'.fst α = P.fst α ∨ P'.fst α = P.snd α := by
  have hperf := commutator_blockSpecialLinear_eq_of_two_le (F := K) hα.ge hK
  refine eq_or_eq_of_sup_eq_sup (P.snd_le_centralizer_fst α α) (P'.snd_le_centralizer_fst α α)
    (P.isSimpleGroup_fst hαN hne hα hK) (P.isSimpleGroup_snd hαN hne hα hK)
    (P'.isSimpleGroup_fst hαN' hne' hα hK) (P'.exists_mul_ne_mul_fst hαN' hne' hα hK) ?_
  rw [← P.pieceCore_eq_fst_sup_snd hαN hk hκ hperf hX,
    ← P'.pieceCore_eq_fst_sup_snd hαN' hk' hκ hperf hX']

theorem SwapNeighbourParam.snd_eq_or_eq [Finite G] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (P : SwapNeighbourParam e t X N) {X' : Subgroup G} {N' : Finset (Fin n)}
    (P' : SwapNeighbourParam e t X' N') {α : Finset (Fin n)} (hα : α.card = 2) (hαN : α ⊆ N)
    (hαN' : α ⊆ N') (hne : α ≠ N) (hne' : α ≠ N') {k k' : Fin n} (hk : k ∉ N) (hk' : k' ∉ N')
    {κ : Kˣ} (hκ : κ ≠ 1) (hX : X ≤ modelToG e (blockTorus (K := K) α))
    (hX' : X' ≤ modelToG e (blockTorus (K := K) α)) :
    P'.snd α = P.fst α ∨ P'.snd α = P.snd α := by
  have hperf := commutator_blockSpecialLinear_eq_of_two_le (F := K) hα.ge hK
  refine eq_or_eq_of_sup_eq_sup (P.snd_le_centralizer_fst α α)
    (P'.fst_le_centralizer_snd α α)
    (P.isSimpleGroup_fst hαN hne hα hK) (P.isSimpleGroup_snd hαN hne hα hK)
    (P'.isSimpleGroup_snd hαN' hne' hα hK) (P'.exists_mul_ne_mul_snd hαN' hne' hα hK) ?_
  rw [← P.pieceCore_eq_fst_sup_snd hαN hk hκ hperf hX, sup_comm,
    ← P'.pieceCore_eq_fst_sup_snd hαN' hk' hκ hperf hX']

end Factors

end CFSG.SeitzReduction.LinearPilot
