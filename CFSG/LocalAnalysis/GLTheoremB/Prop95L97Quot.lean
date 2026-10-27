module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

@[expose] abbrev piM (M : Subgroup G) : ↥M →* Mt M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)

theorem piM_surjective (M : Subgroup G) : Function.Surjective (piM M) :=
  QuotientGroup.mk'_surjective _

theorem mem_tl {M X : Subgroup G} {y : Mt M} :
    y ∈ tl M X ↔ ∃ x : ↥M, (x : G) ∈ X ∧ piM M x = y := by
  simp [tl, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem piM_mem_tl {M X : Subgroup G} {x : ↥M} (hx : (x : G) ∈ X) : piM M x ∈ tl M X :=
  mem_tl.2 ⟨x, hx, rfl⟩

theorem mem_pCoreOf_iff {M : Subgroup G} {x : ↥M} :
    (x : G) ∈ pCoreOf 2 M ↔ x ∈ CFSG.pCore 2 ↥M := by
  unfold pCoreOf
  exact Subgroup.mem_map_iff_mem M.subtype_injective

theorem piM_eq_one_iff {M : Subgroup G} {x : ↥M} : piM M x = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
  rw [mem_pCoreOf_iff]
  exact QuotientGroup.eq_one_iff x

theorem tl_mono {M X Y : Subgroup G} (h : X ≤ Y) : tl M X ≤ tl M Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem tl_normal {M X : Subgroup G} (hX : (X.subgroupOf M).Normal) : (tl M X).Normal :=
  hX.map _ (piM_surjective M)

theorem isPGroup_subgroupOf {M X : Subgroup G} (hX : IsPGroup 2 X) :
    IsPGroup 2 (X.subgroupOf M) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := hX ⟨g.1, Subgroup.mem_subgroupOf.1 hg⟩
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩

theorem isPGroup_tl {M X : Subgroup G} (hX : IsPGroup 2 X) : IsPGroup 2 (tl M X) :=
  (isPGroup_subgroupOf hX).map (piM M)

theorem commutator_le_of_le {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    (⁅A, B⁆ : Subgroup G) ≤ M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have := M.mul_mem (M.mul_mem (hA ha) (hB hb)) (M.mul_mem (M.inv_mem (hA ha)) (M.inv_mem (hB hb)))
  simpa [commutatorElement_def, mul_assoc] using this

theorem subgroupOf_commutator {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    (⁅A, B⁆ : Subgroup G).subgroupOf M = ⁅A.subgroupOf M, B.subgroupOf M⁆ := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA, inf_eq_left.2 hB,
    inf_eq_left.2 (commutator_le_of_le hA hB)]

theorem tl_commutator {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    tl M ⁅A, B⁆ = ⁅tl M A, tl M B⁆ := by
  unfold tl
  rw [subgroupOf_commutator hA hB, Subgroup.map_commutator]

theorem pCore_two_quotient_eq_bot {X : Type*} [Group X] [Finite X] :
    CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  set N : Subgroup X := CFSG.pCore 2 X with hN
  set K : Subgroup X := (CFSG.pCore 2 (X ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := (CFSG.pCore_normal (p := 2) (G := X ⧸ N)).comap _
  have hKp : IsPGroup 2 K := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := X ⧸ N) ⟨_, hx⟩
    have hxa : x ^ (2 ^ a) ∈ N := by
      have h1 := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one, QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := 2) (G := X) ⟨_, hxa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
    rw [pow_add, pow_mul, h2]
  have hle : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ K := hy
  exact (QuotientGroup.eq_one_iff x).mpr (hle hx)

theorem hO_Mt (M : Subgroup G) :
    ∀ N : Subgroup (Mt M), N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
  le_bot_iff.1 ((CFSG.LieType.BorelTits.le_pCore 2 hN hp).trans
    (pCore_two_quotient_eq_bot (X := ↥M)).le)

theorem GLAPPrimeCoreOf_le (p : ℕ) (M : Subgroup G) : GLAPPrimeCoreOf p M ≤ M :=
  Subgroup.map_subtype_le _

theorem sigmaStar_le_of_hyp {p : ℕ} {M D : Subgroup G} (hD : Prop95Hyp p M D) : sigmaStar D ≤ M :=
  iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hD.clause_a d hd hd1

theorem gammaD_le_of_hyp {p : ℕ} {M D : Subgroup G} (hD : Prop95Hyp p M D) : gammaD D ≤ M :=
  (gammaD_le_sigmaStar D).trans (sigmaStar_le_of_hyp hD)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97
