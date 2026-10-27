module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignBlock

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped commutatorElement

section Blocks

variable {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem commutator_ctuBlock_eq (hF : Nat.card F = (2 ^ f) ^ 2) (hε : ε ≤ 1)
    {R : Finset (Fin N)} (h3 : 3 ≤ 2 * Rᶜ.card + ε) (hq : ¬(2 * Rᶜ.card + ε = 3 ∧ 2 ^ f = 2)) :
    ⁅ctuBlock (unitaryInvolution F 2 f) ε R, ctuBlock (unitaryInvolution F 2 f) ε R⁆ =
      ctuBlock (unitaryInvolution F 2 f) ε R := by
  have := isPerfect_SU_ctua hF h3 hq
  set g : SU (unitaryInvolution F 2 f) (2 * Rᶜ.card + ε) →* SU (unitaryInvolution F 2 f)
    (2 * N + ε) := (ctuBlock (unitaryInvolution F 2 f) ε R).subtype.comp
      (ctuaBlockEquiv (unitaryInvolution F 2 f) hε R).symm.toMonoidHom with hg
  have hrange : g.range = ctuBlock (unitaryInvolution F 2 f) ε R := by
    rw [hg, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, range_subtype]
  rw [← hrange, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem eq_one_of_mem_center_ctuBlock (hF : Nat.card F = (2 ^ f) ^ 2) (hε : ε ≤ 1)
    {R : Finset (Fin N)} (h3 : 3 ≤ 2 * Rᶜ.card + ε) (hq : (2 * Rᶜ.card + ε, 2 ^ f) ≠ (3, 2))
    {z : ctuBlock (unitaryInvolution F 2 f) ε R}
    (hz : z ∈ center (ctuBlock (unitaryInvolution F 2 f) ε R)) {k : Fin N} (hk : k ∉ R)
    (hzk : (z : SU (unitaryInvolution F 2 f) (2 * N + ε)) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := ctuaBlockEquiv (unitaryInvolution F 2 f) hε R with hB
  have hBz : B z ∈ center (SU (unitaryInvolution F 2 f) (2 * Rᶜ.card + ε)) := by
    rw [mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := B.surjective g
    rw [← map_mul, ← map_mul, hz g']
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_SU hF h3 hq hBz
  obtain ⟨a, ha⟩ := (mem_range_ctuaIdx_iff R (ctuCoord N ε (Sum.inl (Sum.inl k)))).2 (by
    rw [ctuCoord_mem_ctuPlanes]
    exact hk)
  have h1 : mat (unitaryInvolution F 2 f) (2 * Rᶜ.card + ε) (B z) a a = 1 := by
    rw [hB, mat_ctuaBlockEquiv, submatrix_apply, ha]
    refine (mem_ctuBlock.1 hzk _ _ (Or.inl ?_)).trans (one_apply_eq _)
    rw [ctuCoord_mem_ctuPlanes]
    simp
  rw [mat_apply, hc, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
  have hc1 : c = 1 := Units.ext h1
  apply B.injective
  rw [map_one]
  apply Subtype.ext
  rw [hc, hc1, map_one]
  rfl

end Blocks

section Inj

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

omit [Finite F] [CharP F 2] in
theorem ctuBlock_pair_le_left (σ : F ≃+* F) (k l : Fin N) :
    ctuBlock σ ε ({k, l} : Finset (Fin N)) ≤ ctuBlock σ ε ({k} : Finset (Fin N)) :=
  ctuBlock_anti (by simp)

omit [Finite F] [CharP F 2] in
theorem ctuBlock_pair_le_right (σ : F ≃+* F) (k l : Fin N) :
    ctuBlock σ ε ({k, l} : Finset (Fin N)) ≤ ctuBlock σ ε ({l} : Finset (Fin N)) :=
  ctuBlock_anti (by simp)

omit [Finite F] [CharP F 2] in
theorem mem_ctuBlock_pair {σ : F ≃+* F} {k l : Fin N} {x : SU σ (2 * N + ε)}
    (hx : x ∈ ctuBlock σ ε ({k} : Finset (Fin N))) (hx' : x ∈ ctuBlock σ ε ({l} : Finset (Fin N))) :
    x ∈ ctuBlock σ ε ({k, l} : Finset (Fin N)) := by
  have h := mem_ctuBlock_union hx hx'
  rwa [show ({k} ∪ {l} : Finset (Fin N)) = {k, l} from rfl] at h

theorem CtuParam.injective_overlap (hF : Nat.card F = (2 ^ f) ^ 2) {k l : Fin N} (hkl : k ≠ l)
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (h3 : 3 ≤ 2 * ({k} : Finset (Fin N))ᶜ.card + ε)
    (hq : (2 * ({k} : Finset (Fin N))ᶜ.card + ε, 2 ^ f) ≠ (3, 2)) :
    Function.Injective (P.Φ.comp (Subgroup.inclusion
      (ctuBlock_pair_le_left (ε := ε) (unitaryInvolution F 2 f) k l))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  have hz' : Subgroup.inclusion (ctuBlock_pair_le_left (ε := ε) (unitaryInvolution F 2 f) k l) z ∈
      P.Φ.ker := hz
  have h1 := eq_one_of_mem_center_ctuBlock hF hε h3 hq (P.ker_le hz') (k := l)
    (by simpa using Ne.symm hkl) (ctuBlock_pair_le_right _ k l z.2)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  exact congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) =>
    (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h1

end Inj

section Levi

variable {K F : Type} [Field K] [Field F] [CharP K 2] {N ε : ℕ} {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

omit [CharP K 2] in
theorem eq_or_eq_of_mem_ctuPlanes_singleton {l : Fin N} {a : Fin (2 * N + ε)}
    (ha : a ∈ ctuPlanes ε ({l} : Finset (Fin N))) :
    a = ctuCoord N ε (Sum.inl (Sum.inl l)) ∨ a = ctuCoord N ε (Sum.inl (Sum.inr l)) := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rw [ctuCoord_mem_ctuPlanes] at ha
  rcases w with (p | p) | i
  · left
    have : p = l := by simpa using ha
    rw [this]
  · right
    have : p = l := by simpa using ha
    rw [this]
  · exact absurd ha (not_inPlanes_inr _ i)

omit [CharP K 2] in
theorem ctuDiag_mulSingle_eq_iff {l : Fin N} {κ : Kˣ} (hκ : κ * κ ≠ 1) (a : Fin (2 * N + ε)) :
    (ctuDiag ε ι (Pi.mulSingle l κ) a = ι κ ↔ a = ctuCoord N ε (Sum.inl (Sum.inl l))) ∧
      (ctuDiag ε ι (Pi.mulSingle l κ) a = ι ((κ⁻¹ : Kˣ) : K) ↔
        a = ctuCoord N ε (Sum.inl (Sum.inr l))) := by
  have hκ1 : (κ : K) ≠ 1 := fun h => hκ (by rw [Units.val_eq_one.1 h, one_mul])
  have hκ2 : ((κ⁻¹ : Kˣ) : K) ≠ 1 := fun h => hκ1 (by
    rw [inv_eq_one.1 (Units.val_eq_one.1 h), Units.val_one])
  have hκ3 : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun h => hκ (by
    have h1 : κ = κ⁻¹ := Units.ext h
    calc κ * κ = κ * κ⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel κ)
  have i1 := ι.injective.ne hκ1
  have i2 := ι.injective.ne hκ2
  have i3 := ι.injective.ne hκ3
  rw [map_one] at i1 i2
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rcases w with (p | p) | i
  · rw [ctuDiag_inl_inl]
    by_cases h : p = l
    · subst h
      simp only [Pi.mulSingle_eq_same, Sum.inl.injEq, reduceCtorEq, iff_false]
      exact ⟨trivial, i3⟩
    · simp only [Pi.mulSingle_eq_of_ne h, Units.val_one, map_one, Sum.inl.injEq, h,
        reduceCtorEq, iff_false]
      exact ⟨Ne.symm i1, Ne.symm i2⟩
  · rw [ctuDiag_inl_inr]
    by_cases h : p = l
    · subst h
      simp only [Pi.mulSingle_eq_same, Sum.inl.injEq, reduceCtorEq, iff_false]
      exact ⟨Ne.symm i3, trivial⟩
    · simp only [Pi.mulSingle_eq_of_ne h, inv_one, Units.val_one, map_one, Sum.inl.injEq,
        Sum.inr.injEq, h, reduceCtorEq, iff_false]
      exact ⟨Ne.symm i1, Ne.symm i2⟩
  · rw [ctuDiag_inr]
    simp only [reduceCtorEq, iff_false]
    exact ⟨Ne.symm i1, Ne.symm i2⟩

theorem ctua_apply_eq_zero_of_commute_rootTorus {l : Fin N} {κ : Kˣ} (hκ : κ * κ ≠ 1)
    {x : SU σ (2 * N + ε)}
    (hx : ctuEmbed ε hε σ ι hι (rootTorusHom K N l κ) * x =
      x * ctuEmbed ε hε σ ι hι (rootTorusHom K N l κ))
    {a b : Fin (2 * N + ε)} (hab : a ≠ b)
    (hl : a ∈ ctuPlanes ε ({l} : Finset (Fin N)) ∨ b ∈ ctuPlanes ε ({l} : Finset (Fin N))) :
    ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b = 0 := by
  set d := ctuDiag ε ι (Pi.mulSingle l κ) with hd
  have h1 := congrFun (congrFun (congrArg (fun g : SU σ (2 * N + ε) =>
    ((g : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)) hx) a) b
  simp only [Subgroup.coe_mul, Units.val_mul] at h1
  rw [rootTorusHom_apply, coe_ctuEmbed_diagSp, diagonal_mul, mul_diagonal] at h1
  have hne : d a ≠ d b := by
    intro h
    have hw := fun c => ctuDiag_mulSingle_eq_iff (ε := ε) (ι := ι) (l := l) hκ c
    rcases hl with h2 | h2 <;> rcases eq_or_eq_of_mem_ctuPlanes_singleton h2 with h3 | h3
    · exact hab (h3.trans ((hw b).1.1 (h.symm.trans ((hw a).1.2 h3))).symm)
    · exact hab (h3.trans ((hw b).2.1 (h.symm.trans ((hw a).2.2 h3))).symm)
    · exact hab (((hw a).1.1 (h.trans ((hw b).1.2 h3))).trans h3.symm)
    · exact hab (((hw a).2.1 (h.trans ((hw b).2.2 h3))).trans h3.symm)
  have h2 : (d a - d b) * ((x : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b = 0 := by
    rw [sub_mul, h1]
    ring
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

theorem perfectCore_ctuBlock_inf_centralizer_rootTorus [Finite K] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hε : ε ≤ 1) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) (hK : 4 ≤ Nat.card K) {k l : Fin N}
    (h3 : 3 ≤ 2 * ({k, l} : Finset (Fin N))ᶜ.card + ε)
    (hq : ¬(2 * ({k, l} : Finset (Fin N))ᶜ.card + ε = 3 ∧ 2 ^ f = 2)) :
    perfectCore (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) ⊓
      centralizer (((rootTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) :
        Subgroup (SU (unitaryInvolution F 2 f) (2 * N + ε))) :
          Set (SU (unitaryInvolution F 2 f) (2 * N + ε)))) =
      ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  set C := ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) ⊓
    centralizer (((rootTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) :
      Subgroup (SU (unitaryInvolution F 2 f) (2 * N + ε))) :
        Set (SU (unitaryInvolution F 2 f) (2 * N + ε))) with hC
  apply le_antisymm
  · refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1).trans ?_
    rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero,
      Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hc : ⁅g₁, g₂⁆ ∈ C := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
    have hsupp : ∀ x ∈ C, ∀ a b, a ≠ b → (a ∈ ctuPlanes ε ({l} : Finset (Fin N)) ∨
        b ∈ ctuPlanes ε ({l} : Finset (Fin N))) →
        ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b = 0 := by
      intro x hx a b hab hl
      have hcomm := mem_centralizer_iff.1 hx.2 (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
        (rootTorusHom K N l κ)) ⟨_, ⟨κ, rfl⟩, rfl⟩
      exact ctua_apply_eq_zero_of_commute_rootTorus hκ hcomm hab hl
    set a₀ := ctuCoord N ε (Sum.inl (Sum.inl l)) with ha₀def
    have ha₀ : a₀ ∈ ctuPlanes ε ({l} : Finset (Fin N)) := by
      rw [ha₀def, ctuCoord_mem_ctuPlanes]
      simp
    have hmul : ∀ x ∈ C, ∀ y : SU (unitaryInvolution F 2 f) (2 * N + ε),
        (((x * y : SU (unitaryInvolution F 2 f) (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ =
        ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ *
          ((y : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ := by
      intro x hx y
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a₀]
      · intro b _ hb
        rw [hsupp x hx a₀ b (Ne.symm hb) (Or.inl ha₀), zero_mul]
      · simp
    have hinv : ∀ x ∈ C,
        ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ *
          (((x⁻¹ : SU (unitaryInvolution F 2 f) (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
            Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ = 1 := by
      intro x hx
      rw [← hmul x hx x⁻¹, mul_inv_cancel]
      exact one_apply_eq a₀
    have hχ : (((⁅g₁, g₂⁆ : SU (unitaryInvolution F 2 f) (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ = 1 := by
      rw [commutatorElement_def, hmul _ (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)),
        hmul _ (mul_mem hg₁ hg₂), hmul _ hg₁]
      calc _ = (((g₁ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
              a₀ a₀ * (((g₁⁻¹ : SU (unitaryInvolution F 2 f) (2 * N + ε)) :
                GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀) *
            (((g₂ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
              a₀ a₀ * (((g₂⁻¹ : SU (unitaryInvolution F 2 f) (2 * N + ε)) :
                GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀) := by
            ring
        _ = 1 := by rw [hinv _ hg₁, hinv _ hg₂, one_mul]
    have hcl : ⁅g₁, g₂⁆ ∈ ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)) := by
      rw [mem_ctuBlock]
      intro a b hab
      by_cases h : a = b
      · subst h
        have ha : a ∈ ctuPlanes ε ({l} : Finset (Fin N)) := hab.elim id id
        rcases eq_or_eq_of_mem_ctuPlanes_singleton ha with rfl | rfl
        · rw [hχ, one_apply_eq]
        · have hu := sum_mat_mul_mat (⁅g₁, g₂⁆ : SU (unitaryInvolution F 2 f) (2 * N + ε)) a₀
            (Fin.rev a₀)
          rw [Finset.sum_eq_single a₀, ite_eq_left rfl] at hu
          · rw [mat_apply, hχ, map_one, one_mul, ha₀def, ctuCoord_rev hε, ctuPar_inl, par_inl] at hu
            rw [hu, one_apply_eq]
          · intro t _ ht
            change unitaryInvolution F 2 f (((⁅g₁, g₂⁆ : SU (unitaryInvolution F 2 f) (2 * N + ε)) :
              GL (Fin (2 * N + ε)) F) t a₀) * _ = 0
            rw [hsupp _ hc t a₀ ht (Or.inr ha₀), map_zero, zero_mul]
          · simp
      · rw [one_apply_ne h]
        exact hsupp _ hc a b h hab
    exact mem_ctuBlock_pair hc.1 hcl
  · refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ (commutator_ctuBlock_eq hF hε h3 hq)
    intro x hx
    refine Subgroup.mem_inf.2 ⟨ctuBlock_pair_le_left _ k l hx, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N)) := by
      rw [spBlock_singleton]
      exact rootTorusSp_le_longRootSp2 l hy
    exact (commute_ctuBlock_ctuEmbed (ctuBlock_pair_le_right _ k l hx) hyl).symm

end Levi

end CFSG.SeitzReduction.SymplecticPilot
