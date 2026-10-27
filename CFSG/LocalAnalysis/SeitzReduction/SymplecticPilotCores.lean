module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective ne_succ')
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono symm_mem_modelToG
  modelToG_le_centralizerPerfectCore)
open scoped MatrixGroups

section Weights

variable {K : Type} [Field K] {n : ℕ}

theorem matrix_mul_diagonal_comm_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix ι ι K) (w : ι → K) :
    g * diagonal w = diagonal w * g ↔ ∀ a b, w a ≠ w b → g a b = 0 := by
  constructor
  · intro h a b hab
    have h' := congrFun (congrFun h a) b
    rw [mul_diagonal, diagonal_mul] at h'
    have h'' : (w b - w a) * g a b = 0 := by
      rw [sub_mul, mul_comm (w b), h', sub_self]
    exact (mul_eq_zero.mp h'').resolve_left (sub_ne_zero.mpr (Ne.symm hab))
  · intro h
    ext a b
    rw [mul_diagonal, diagonal_mul]
    by_cases hab : w a = w b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]

theorem commute_diagSp_iff (x : StatedSp n K) (t : Fin n → Kˣ) :
    Commute x (diagSp K n t) ↔ ∀ a b, diagSpEntry t a ≠ diagSpEntry t b → mat n K x a b = 0 := by
  rw [← matrix_mul_diagonal_comm_iff, ← mat_diagSp, ← map_mul, ← map_mul, mat_injective.eq_iff]
  rfl

theorem commute_diagSp_diagSp (t s : Fin n → Kˣ) : Commute (diagSp K n t) (diagSp K n s) := by
  change diagSp K n t * diagSp K n s = diagSp K n s * diagSp K n t
  rw [← map_mul, ← map_mul, mul_comm]

theorem commute_diagSp_of_mem_suppGroup {S : Set (Fin n ⊕ Fin n)} {t : Fin n → Kˣ}
    (ht : ∀ a ∈ S, ∀ b ∈ S, diagSpEntry t a = diagSpEntry t b) {x : StatedSp n K}
    (hx : x ∈ suppGroup S) : Commute x (diagSp K n t) := by
  refine (commute_diagSp_iff x t).2 fun a b hab => ?_
  by_cases h : a ∈ S ∧ b ∈ S
  · exact absurd (ht a h.1 b h.2) hab
  · have hne : a ≠ b := fun e => hab (e ▸ rfl)
    rw [hx a b h, Matrix.one_apply_ne hne]

theorem commute_diagSp_leviEmbedGL {A : GL (Fin n) K} {t : Fin n → Kˣ}
    (hA : Commute A (TauCeti.diagGL t)) : Commute (leviEmbedGL K n A) (diagSp K n t) := by
  rw [diagSp_apply]
  exact hA.map (leviEmbedGL K n)

theorem blockMat_mul_diagonal_comm {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}
    (B : Matrix (Fin 2) (Fin 2) K) {w : κ → K} (hw : w p = w q) :
    CFSG.LieType.Steinberg.Sp.blockMat p q B * diagonal w =
      diagonal w * CFSG.LieType.Steinberg.Sp.blockMat p q B := by
  refine (matrix_mul_diagonal_comm_iff _ w).2 fun a b hab => ?_
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  simp only [CFSG.LieType.Steinberg.Sp.blockMat, of_apply]
  by_cases hap : a = p
  · subst hap
    by_cases hbp : b = a
    · exact absurd hbp.symm hab'
    · by_cases hbq : b = q
      · subst hbq
        exact absurd hw hab
      · simp [hbp, hbq]
  · by_cases haq : a = q
    · subst haq
      by_cases hbp : b = p
      · subst hbp
        exact absurd hw.symm hab
      · by_cases hbq : b = a
        · exact absurd hbq.symm hab'
        · simp [hap, hbp, hbq]
    · simp [hap, haq, Matrix.one_apply_ne hab']

end Weights

section SimpleRoots

variable (K : Type) [Field K] {n : ℕ}

@[expose] noncomputable def simpleRootHom (j : Fin n) : SL(2, K) →* StatedSp n K :=
  if h : j.val + 1 < n then shortBlock K (ne_succ' h) else longBlock K n j

@[expose] noncomputable def simpleRootSL2 (j : Fin n) : Subgroup (StatedSp n K) :=
  (simpleRootHom K j).range

variable {K}

theorem simpleRootHom_of_lt {j : Fin n} (h : j.val + 1 < n) :
    simpleRootHom K j = shortBlock K (ne_succ' h) := by
  simp only [simpleRootHom, h, ↓reduceDIte]

theorem simpleRootHom_of_not_lt {j : Fin n} (h : ¬j.val + 1 < n) :
    simpleRootHom K j = longBlock K n j := by
  simp only [simpleRootHom, h, ↓reduceDIte]

theorem simpleRootSL2_of_lt {j : Fin n} (h : j.val + 1 < n) :
    simpleRootSL2 K j = (shortBlock K (ne_succ' h)).range := by
  rw [simpleRootSL2, simpleRootHom_of_lt h]

theorem simpleRootSL2_of_not_lt {j : Fin n} (h : ¬j.val + 1 < n) :
    simpleRootSL2 K j = longRootSp2 K n j := by
  rw [simpleRootSL2, simpleRootHom_of_not_lt h, longRootSp2]

theorem simpleRootHom_injective (j : Fin n) : Function.Injective (simpleRootHom K j) := by
  by_cases h : j.val + 1 < n
  · rw [simpleRootHom_of_lt h]
    exact shortBlock_injective _
  · rw [simpleRootHom_of_not_lt h]
    exact longBlock_injective j

theorem commutator_simpleRootSL2_eq {c : Kˣ} (hc : c * c ≠ 1) (j : Fin n) :
    ⁅simpleRootSL2 K j, simpleRootSL2 K j⁆ = simpleRootSL2 K j := by
  have hperf : commutator SL(2, K) = ⊤ := Matrix.SL2.commutator_eq_top c.ne_zero (by
    intro h
    apply hc
    apply Units.ext
    rw [Units.val_mul, Units.val_one, ← sq, h])
  rw [simpleRootSL2, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]

theorem commutator_simpleRootSL2_eq_of_four_le (hK : 4 ≤ Nat.card K) (j : Fin n) :
    ⁅simpleRootSL2 K j, simpleRootSL2 K j⁆ = simpleRootSL2 K j := by
  obtain ⟨c, hc⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact commutator_simpleRootSL2_eq hc j

end SimpleRoots

section LeviCentralizer

variable {K : Type} [Field K] {n : ℕ}

theorem commute_shortBlock_diagSp {j j' : Fin n} (hjj' : j ≠ j') (A : SL(2, K))
    {t : Fin n → Kˣ} (ht : t j = t j') : Commute (shortBlock K hjj' A) (diagSp K n t) := by
  refine commute_diagSp_leviEmbedGL (A := CFSG.LieType.Steinberg.Sp.blockHom K hjj' A) ?_
  refine Units.ext ?_
  change CFSG.LieType.Steinberg.Sp.blockMat j j' (A : Matrix (Fin 2) (Fin 2) K) *
      (TauCeti.diagGL t : Matrix (Fin n) (Fin n) K) =
    (TauCeti.diagGL t : Matrix (Fin n) (Fin n) K) *
      CFSG.LieType.Steinberg.Sp.blockMat j j' (A : Matrix (Fin 2) (Fin 2) K)
  rw [TauCeti.diagGL_coe]
  exact blockMat_mul_diagonal_comm _ (by rw [ht])

theorem simpleRootSL2_le_centralizer_leviTorusSp {J : Finset (Fin n)} {j : Fin n} (hj : j ∈ J) :
    simpleRootSL2 K j ≤ centralizer (leviTorusSp K J : Set (StatedSp n K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  refine (Commute.eq ?_).symm
  by_cases h : j.val + 1 < n
  · rw [simpleRootSL2_of_lt h] at hx
    obtain ⟨A, rfl⟩ := hx
    exact commute_shortBlock_diagSp (ne_succ' h) A ((ht j hj).1 h)
  · rw [simpleRootSL2_of_not_lt h, longRootSp2_eq_suppGroup] at hx
    have h1 : t j = 1 := (ht j hj).2 (by omega)
    refine commute_diagSp_of_mem_suppGroup (S := coords j) (fun a ha b hb => ?_) hx
    rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 hb with rfl | rfl <;>
      simp [h1]

theorem diagSp_mem_centralizer_of_le {T : Subgroup (StatedSp n K)} (hT : T ≤ (diagSp K n).range)
    (s : Fin n → Kˣ) : diagSp K n s ∈ centralizer (T : Set (StatedSp n K)) := by
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨t, rfl⟩ := hT hx
  exact (commute_diagSp_diagSp t s).eq

theorem leviTorusSp_le_range (J : Finset (Fin n)) : leviTorusSp K J ≤ (diagSp K n).range := by
  rintro _ ⟨t, -, rfl⟩
  exact ⟨t, rfl⟩

theorem rootTorusSp_le_range (k : Fin n) : rootTorusSp K k ≤ (diagSp K n).range := by
  rintro _ ⟨κ, rfl⟩
  exact ⟨_, rfl⟩

theorem siegelTorus_le_range : siegelTorus K n ≤ (diagSp K n).range := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, rfl⟩

theorem siegelTorus_le_leviTorusSp {J : Finset (Fin n)} (hJ : ∀ j ∈ J, j.val + 1 < n) :
    siegelTorus K n ≤ leviTorusSp K J := by
  rw [siegelTorus_eq_leviTorusSp]
  refine leviTorusSp_anti fun j hj => ?_
  simpa using hJ j hj

end LeviCentralizer

section Cores

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

@[expose] noncomputable def pieceCore (J : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (leviTorusSp K J))

@[expose] noncomputable def neighbourCore (k : Fin n) : Subgroup G :=
  centralizerPerfectCore (modelToG e (rootTorusSp K k))

@[expose] noncomputable def siegelCore : Subgroup G :=
  centralizerPerfectCore (modelToG e (siegelTorus K n))

theorem pieceCore_def (J : Finset (Fin n)) :
    pieceCore e J = centralizerPerfectCore (modelToG e (leviTorusSp K J)) :=
  rfl

theorem neighbourCore_def (k : Fin n) :
    neighbourCore e k = centralizerPerfectCore (modelToG e (rootTorusSp K k)) :=
  rfl

theorem siegelCore_def : siegelCore e = centralizerPerfectCore (modelToG e (siegelTorus K n)) :=
  rfl

theorem siegelCore_eq_pieceCore :
    siegelCore e = pieceCore e (Finset.univ.filter fun j : Fin n => j.val + 1 < n) := by
  rw [siegelCore_def, pieceCore_def, siegelTorus_eq_leviTorusSp]

theorem pieceCore_mono {J J' : Finset (Fin n)} (h : J ⊆ J') : pieceCore e J ≤ pieceCore e J' :=
  centralizerPerfectCore_anti (modelToG_mono e (leviTorusSp_anti h))

theorem modelToG_rootTorusSp_le {k : Fin n} {J : Finset (Fin n)} (hk : k ∉ spSupport J) :
    modelToG e (rootTorusSp K k) ≤ modelToG e (leviTorusSp K J) :=
  modelToG_mono e (rootTorusSp_le_leviTorusSp hk)

theorem pieceCore_le_neighbourCore {k : Fin n} {J : Finset (Fin n)} (hk : k ∉ spSupport J) :
    pieceCore e J ≤ neighbourCore e k :=
  centralizerPerfectCore_anti (modelToG_rootTorusSp_le e hk)

theorem modelToG_siegelTorus_le {J : Finset (Fin n)} (hJ : ∀ j ∈ J, j.val + 1 < n) :
    modelToG e (siegelTorus K n) ≤ modelToG e (leviTorusSp K J) :=
  modelToG_mono e (siegelTorus_le_leviTorusSp hJ)

theorem pieceCore_le_siegelCore {J : Finset (Fin n)} (hJ : ∀ j ∈ J, j.val + 1 < n) :
    pieceCore e J ≤ siegelCore e :=
  centralizerPerfectCore_anti (modelToG_siegelTorus_le e hJ)

theorem modelToG_le_pieceCore {J : Finset (Fin n)} {A : Subgroup (StatedSp n K)}
    (hA : A ≤ centralizer (leviTorusSp K J : Set (StatedSp n K))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ pieceCore e J :=
  modelToG_le_centralizerPerfectCore e hA hperf

theorem modelToG_le_neighbourCore {k : Fin n} {A : Subgroup (StatedSp n K)}
    (hA : A ≤ centralizer (rootTorusSp K k : Set (StatedSp n K))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ neighbourCore e k :=
  modelToG_le_centralizerPerfectCore e hA hperf

theorem modelToG_le_siegelCore {A : Subgroup (StatedSp n K)}
    (hA : A ≤ centralizer (siegelTorus K n : Set (StatedSp n K))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ siegelCore e :=
  modelToG_le_centralizerPerfectCore e hA hperf

theorem modelToG_simpleRootSL2_le_pieceCore (hK : 4 ≤ Nat.card K) {J : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ J) : modelToG e (simpleRootSL2 K j) ≤ pieceCore e J :=
  modelToG_le_pieceCore e (simpleRootSL2_le_centralizer_leviTorusSp hj)
    (commutator_simpleRootSL2_eq_of_four_le hK j)

theorem iSup_modelToG_simpleRootSL2_le_pieceCore (hK : 4 ≤ Nat.card K) (J : Finset (Fin n)) :
    ⨆ j ∈ J, modelToG e (simpleRootSL2 K j) ≤ pieceCore e J :=
  iSup₂_le fun _ hj => modelToG_simpleRootSL2_le_pieceCore e hK hj

end Cores

section LeviFactors

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {m n : ℕ}

theorem modelToG_complSp_le_neighbourCore (e : L ≃* StatedSp (m + 1) K) (hK : 4 ≤ Nat.card K)
    (hm : 1 ≤ m) (k : Fin (m + 1)) : modelToG e (complSp K k) ≤ neighbourCore e k :=
  modelToG_le_neighbourCore e (complSp_le_centralizer_rootTorusSp k)
    (Subgroup.isPerfect_iff.1 (isQuasisimple_complSp hK hm k).1)

theorem modelToG_siegelLevi_le_siegelCore (e : L ≃* StatedSp n K) (hK : 4 ≤ Nat.card K)
    (hn : 2 ≤ n) : modelToG e (siegelLevi K n) ≤ siegelCore e :=
  modelToG_le_siegelCore e (siegelLevi_le_siegelLeviGL.trans
      siegelLeviGL_le_centralizer_siegelTorus)
    (Subgroup.isPerfect_iff.1 (isQuasisimple_siegelLevi hK hn).1)

theorem inSubgroup_layer_inf_centralizer_le_neighbourCore (e : L ≃* StatedSp (m + 1) K)
    (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (k : Fin (m + 1)) :
    inSubgroup layer (L ⊓ centralizer (modelToG e (rootTorusSp K k) : Set G)) ≤
      neighbourCore e k := by
  rw [modelToG, layer_inf_centralizer_rootTorusSp hK hm e k]
  exact modelToG_complSp_le_neighbourCore e hK hm k

end LeviFactors

section Normalizers

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G)) (J : Finset (Fin n)) :
    t ∈ normalizer (pieceCore e J : Set G) :=
  UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G)) (k : Fin n) :
    t ∈ normalizer (neighbourCore e k : Set G) :=
  UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem le_normalizer_siegelCore {t : G} (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer (siegelCore e : Set G) :=
  UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem symm_mem_normalizer_pieceCore {J : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ normalizer (leviTorusSp K J : Set (StatedSp n K))) :
    ((e.symm x : L) : G) ∈ normalizer (pieceCore e J : Set G) :=
  UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e hx

theorem symm_mem_normalizer_neighbourCore {k : Fin n} {x : StatedSp n K}
    (hx : x ∈ normalizer (rootTorusSp K k : Set (StatedSp n K))) :
    ((e.symm x : L) : G) ∈ normalizer (neighbourCore e k : Set G) :=
  UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e hx

theorem symm_mem_normalizer_siegelCore {x : StatedSp n K}
    (hx : x ∈ normalizer (siegelTorus K n : Set (StatedSp n K))) :
    ((e.symm x : L) : G) ∈ normalizer (siegelCore e : Set G) :=
  UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e hx

theorem diagSp_mem_normalizer_pieceCore (J : Finset (Fin n)) (s : Fin n → Kˣ) :
    ((e.symm (diagSp K n s) : L) : G) ∈ normalizer (pieceCore e J : Set G) :=
  symm_mem_normalizer_pieceCore e
    (centralizer_le_normalizer _ (diagSp_mem_centralizer_of_le (leviTorusSp_le_range J) s))

theorem diagSp_mem_normalizer_neighbourCore (k : Fin n) (s : Fin n → Kˣ) :
    ((e.symm (diagSp K n s) : L) : G) ∈ normalizer (neighbourCore e k : Set G) :=
  symm_mem_normalizer_neighbourCore e
    (centralizer_le_normalizer _ (diagSp_mem_centralizer_of_le (rootTorusSp_le_range k) s))

theorem diagSp_mem_normalizer_siegelCore (s : Fin n → Kˣ) :
    ((e.symm (diagSp K n s) : L) : G) ∈ normalizer (siegelCore e : Set G) :=
  symm_mem_normalizer_siegelCore e
    (centralizer_le_normalizer _ (diagSp_mem_centralizer_of_le siegelTorus_le_range s))

end Normalizers

section Alignment

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

theorem pieceCore_eq_perfectCore_inf {X : Subgroup G} {J : Finset (Fin n)}
    (hX : X ≤ modelToG e (leviTorusSp K J)) :
    pieceCore e J = perfectCore (centralizerPerfectCore X ⊓
      centralizer (modelToG e (leviTorusSp K J) : Set G)) :=
  UnitaryPilot.centralizerPerfectCore_modelToG_eq_perfectCore_inf e hX

theorem pieceCore_eq {k : Fin n} {J : Finset (Fin n)} (hk : k ∉ spSupport J) :
    pieceCore e J = perfectCore (neighbourCore e k ⊓
      centralizer (modelToG e (leviTorusSp K J) : Set G)) :=
  pieceCore_eq_perfectCore_inf e (modelToG_rootTorusSp_le e hk)

theorem perfectCore_neighbourCore_inf_eq {k l : Fin n} {J : Finset (Fin n)}
    (hk : k ∉ spSupport J) (hl : l ∉ spSupport J) :
    perfectCore (neighbourCore e k ⊓ centralizer (modelToG e (leviTorusSp K J) : Set G)) =
      perfectCore (neighbourCore e l ⊓ centralizer (modelToG e (leviTorusSp K J) : Set G)) := by
  rw [← pieceCore_eq e hk, ← pieceCore_eq e hl]

theorem pieceCore_eq_siegel {J : Finset (Fin n)} (hJ : ∀ j ∈ J, j.val + 1 < n) :
    pieceCore e J = perfectCore (siegelCore e ⊓
      centralizer (modelToG e (leviTorusSp K J) : Set G)) :=
  pieceCore_eq_perfectCore_inf e (modelToG_siegelTorus_le e hJ)

theorem perfectCore_neighbourCore_inf_eq_siegelCore {k : Fin n} {J : Finset (Fin n)}
    (hk : k ∉ spSupport J) (hJ : ∀ j ∈ J, j.val + 1 < n) :
    perfectCore (neighbourCore e k ⊓ centralizer (modelToG e (leviTorusSp K J) : Set G)) =
      perfectCore (siegelCore e ⊓ centralizer (modelToG e (leviTorusSp K J) : Set G)) := by
  rw [← pieceCore_eq e hk, ← pieceCore_eq_siegel e hJ]

end Alignment

end CFSG.SeitzReduction.SymplecticPilot
