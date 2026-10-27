module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LinearAlgebra.LinearGroups.Perfect
import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne)

section Blk

variable {F : Type} [Field F] {n : ℕ}

theorem commute_of_isBlk_of_diagonal {blk : Fin n → ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : IsBlk blk M) {d : Fin n → F} (hd : ∀ a b, blk a = blk b → blk a ≠ 0 → d a = d b) :
    M * diagonal d = diagonal d * M := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases h : blk a = blk b ∧ blk a ≠ 0
  · rw [hd a b h.1 h.2, mul_comm]
  · rw [hM a b h]
    by_cases hab : a = b
    · subst hab
      rw [one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne hab, zero_mul, mul_zero]

theorem mem_ctuBlock_of_isBlk {N ε : ℕ} {σ : F ≃+* F} {blk : Fin (2 * N + ε) → ℕ}
    {x : SU σ (2 * N + ε)} (hx : IsBlk blk (mat σ (2 * N + ε) x)) {R : Finset (Fin N)}
    (hR : ∀ a ∈ ctuPlanes ε R, blk a = 0) : x ∈ ctuBlock σ ε R := by
  rw [mem_ctuBlock]
  intro a b hab
  apply hx a b
  rintro ⟨h1, h2⟩
  rcases hab with ha | hb
  · exact h2 (hR a ha)
  · exact h2 (h1.trans (hR b hb))

end Blk

section Support

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {N ε : ℕ}

theorem val_of_mem_ctuPlanes_singleton {k : Fin N} {a : Fin (2 * N + ε)}
    (ha : a ∈ ctuPlanes ε {k}) : a.val = k.val ∨ a.val = 2 * N + ε - 1 - k.val := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rw [ctuCoord_mem_ctuPlanes] at ha
  rcases w with (p | p) | i
  · simp only [inPlanes_inl, planeOf_inl, Finset.mem_singleton] at ha
    subst ha
    exact Or.inl rfl
  · simp only [inPlanes_inl, planeOf_inr, Finset.mem_singleton] at ha
    subst ha
    exact Or.inr rfl
  · exact ha.elim

theorem rankOne_short_le_ctuBlock (hε : ε ≤ 1) {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) {k : Fin N} (hkj : k.val ≠ j.val)
    (hkj' : k.val ≠ j.val + 1) :
    rankOne (rootGroup σ hσ (2 * N + ε)) j ≤ ctuBlock σ ε {k} := by
  intro x hx
  refine mem_ctuBlock_of_isBlk (isBlk_short_of_mem hj hx).1 fun a ha => ?_
  have hk := k.2
  have hj2 := j.2
  have hav := val_of_mem_ctuPlanes_singleton ha
  have h1 : ¬(a = lowIdx j ∨ a = lowIdx ⟨j.val + 1, hj⟩) := by
    rintro (h | h) <;> simp only [Fin.ext_iff, val_lowIdx] at h <;> omega
  have h2 : ¬(a = Fin.rev (lowIdx j) ∨ a = Fin.rev (lowIdx ⟨j.val + 1, hj⟩)) := by
    rintro (h | h) <;> simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx] at h <;>
      omega
  unfold blkShort
  simp only [h1, h2, ↓reduceIte]

theorem rankOne_last_le_ctuBlock (hε : ε ≤ 1) {j : Fin ((2 * N + ε) / 2)}
    (hj : ¬j.val + 1 < (2 * N + ε) / 2) {k : Fin N} (hkj : k.val ≠ j.val) :
    rankOne (rootGroup σ hσ (2 * N + ε)) j ≤ ctuBlock σ ε {k} := by
  intro x hx
  refine mem_ctuBlock_of_isBlk (isBlk_last_of_mem hj hx) fun a ha => ?_
  have hk := k.2
  have hj2 := j.2
  have hav := val_of_mem_ctuPlanes_singleton ha
  rw [blkLast_eq_zero_iff]
  rintro (h | h | h)
  · rw [Fin.ext_iff, val_lowIdx] at h
    omega
  · rw [Fin.ext_iff, Fin.val_rev, val_lowIdx] at h
    omega
  · rw [Fin.ext_iff, Fin.val_rev] at h
    omega

theorem rankOne_le_ctuBlock (hε : ε ≤ 1) (j : Fin ((2 * N + ε) / 2)) {k : Fin N}
    (hkj : k.val ≠ j.val) (hkj' : k.val ≠ j.val + 1) :
    rankOne (rootGroup σ hσ (2 * N + ε)) j ≤ ctuBlock σ ε {k} := by
  by_cases hj : j.val + 1 < (2 * N + ε) / 2
  · exact rankOne_short_le_ctuBlock hε hj hkj hkj'
  · exact rankOne_last_le_ctuBlock hε hj hkj

end Support

section Torus

variable {K F : Type} [Field K] [Field F] [CharP K 2] {N ε : ℕ} {hε : ε ≤ 1}
  {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

variable (ε) in
@[expose] noncomputable def ctuDiag (ι : K →+* F) (t : Fin N → Kˣ) (a : Fin (2 * N + ε)) : F :=
  Sum.elim (fun u => ι (diagSpEntry t u)) (fun _ => 1) ((ctuCoord N ε).symm a)

omit [CharP K 2] in
theorem ctuDiag_inl_inl (t : Fin N → Kˣ) (p : Fin N) :
    ctuDiag ε ι t (ctuCoord N ε (Sum.inl (Sum.inl p))) = ι ((t p : Kˣ) : K) := by
  simp [ctuDiag]

omit [CharP K 2] in
theorem ctuDiag_inl_inr (t : Fin N → Kˣ) (p : Fin N) :
    ctuDiag ε ι t (ctuCoord N ε (Sum.inl (Sum.inr p))) = ι (((t p)⁻¹ : Kˣ) : K) := by
  simp [ctuDiag]

omit [CharP K 2] in
theorem ctuDiag_inr (t : Fin N → Kˣ) (i : Fin ε) :
    ctuDiag ε ι t (ctuCoord N ε (Sum.inr i)) = 1 := by
  simp [ctuDiag]

theorem coe_ctuEmbed_diagSp (t : Fin N → Kˣ) :
    (((ctuEmbed ε hε σ ι hι (diagSp K N t) : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = diagonal (ctuDiag ε ι t) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuEmbed_apply_ctuCoord, diagonal_apply]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rw [mat_diagSp]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, map_apply, diagonal_apply]
    simp only [Sum.inl.injEq]
    split_ifs with h
    · subst h
      simp [ctuDiag]
    · simp
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, one_apply]
    simp only [Sum.inr.injEq]
    split_ifs with h
    · subst h
      simp [ctuDiag]
    · rfl

theorem mat_ctuEmbed_diagSp (t : Fin N → Kˣ) :
    mat σ (2 * N + ε) (ctuEmbed ε hε σ ι hι (diagSp K N t)) = diagonal (ctuDiag ε ι t) :=
  coe_ctuEmbed_diagSp (hε := hε) (σ := σ) (hι := hι) t

theorem lowIdx_eq_ctuCoord {j : Fin ((2 * N + ε) / 2)} (hj : j.val < N) :
    lowIdx j = ctuCoord N ε (Sum.inl (Sum.inl ⟨j.val, hj⟩)) :=
  Fin.ext rfl

theorem rev_lowIdx_eq_ctuCoord (hε : ε ≤ 1) {j : Fin ((2 * N + ε) / 2)} (hj : j.val < N) :
    Fin.rev (lowIdx j) = ctuCoord N ε (Sum.inl (Sum.inr ⟨j.val, hj⟩)) := by
  rw [lowIdx_eq_ctuCoord hj, ctuCoord_rev hε]
  rfl

theorem commute_rankOne_short_ctuEmbed_diagSp {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) {t : Fin N → Kˣ}
    (ht : t ⟨j.val, by omega⟩ = t ⟨j.val + 1, by omega⟩) {x : SU σ (2 * N + ε)}
    (hx : x ∈ rankOne (rootGroup σ hσ (2 * N + ε)) j) :
    x * ctuEmbed ε hε σ ι hι (diagSp K N t) = ctuEmbed ε hε σ ι hι (diagSp K N t) * x := by
  have hjN : j.val + 1 < N := by omega
  apply mat_injective
  rw [map_mul, map_mul, mat_ctuEmbed_diagSp]
  refine commute_of_isBlk_of_diagonal (isBlk_short_of_mem hj hx).1 fun a b hab ha => ?_
  have hp := lowIdx_eq_ctuCoord (ε := ε) (j := j) (by omega)
  have hq := lowIdx_eq_ctuCoord (ε := ε) (j := ⟨j.val + 1, hj⟩) hjN
  have hp' := rev_lowIdx_eq_ctuCoord hε (j := j) (by omega)
  have hq' := rev_lowIdx_eq_ctuCoord hε (j := ⟨j.val + 1, hj⟩) hjN
  have key : ∀ c, blkShort j hj c ≠ 0 →
      ctuDiag ε ι t c = ι ((t ⟨j.val, by omega⟩ : Kˣ) : K) ∧ blkShort j hj c = 1 ∨
        ctuDiag ε ι t c = ι (((t ⟨j.val, by omega⟩)⁻¹ : Kˣ) : K) ∧ blkShort j hj c = 2 := by
    intro c hc
    by_cases h1 : blkShort j hj c = 1
    · left
      refine ⟨?_, h1⟩
      rcases (blkShort_eq_one_iff hj c).1 h1 with rfl | rfl
      · rw [hp, ctuDiag_inl_inl]
      · rw [hq, ctuDiag_inl_inl, ← ht]
    · right
      have h2 : blkShort j hj c = 2 := by
        unfold blkShort at h1 hc ⊢
        split_ifs at h1 hc ⊢ <;> simp_all
      refine ⟨?_, h2⟩
      rcases (blkShort_eq_two_iff hj c).1 h2 with rfl | rfl
      · rw [hp', ctuDiag_inl_inr]
      · rw [hq', ctuDiag_inl_inr, ← ht]
  rcases key a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases key b (hab ▸ ha) with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h1, h3]
  · omega
  · omega
  · rw [h1, h3]

theorem commute_rankOne_last_ctuEmbed_diagSp {j : Fin ((2 * N + ε) / 2)}
    (hj : ¬j.val + 1 < (2 * N + ε) / 2) {t : Fin N → Kˣ} (ht : t ⟨j.val, by omega⟩ = 1)
    {x : SU σ (2 * N + ε)} (hx : x ∈ rankOne (rootGroup σ hσ (2 * N + ε)) j) :
    x * ctuEmbed ε hε σ ι hι (diagSp K N t) = ctuEmbed ε hε σ ι hι (diagSp K N t) * x := by
  apply mat_injective
  rw [map_mul, map_mul, mat_ctuEmbed_diagSp]
  have hp := lowIdx_eq_ctuCoord (ε := ε) (j := j) (by omega)
  have hp' := rev_lowIdx_eq_ctuCoord hε (j := j) (by omega)
  have key : ∀ c, blkLast j c ≠ 0 → ctuDiag ε ι t c = 1 := by
    intro c hc
    rcases (blkLast_eq_one_iff c).1 (blkLast_eq_one_of_ne_zero hc) with rfl | rfl | h
    · rw [hp, ctuDiag_inl_inl, ht, Units.val_one, map_one]
    · rw [hp', ctuDiag_inl_inr, ht, inv_one, Units.val_one, map_one]
    · obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective c
      rw [ctuCoord_rev hε] at h
      have h' := (ctuCoord N ε).injective h
      rcases w with u | i
      · rcases u with u | u <;> simp [ctuPar] at h'
      · exact ctuDiag_inr t i
  exact commute_of_isBlk_of_diagonal (isBlk_last_of_mem hj hx) fun a b _ ha => by
    rw [key a ha, key b (by rwa [← ‹blkLast j a = blkLast j b›])]

end Torus

section Perfect

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem isPerfect_rankOne (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {n : ℕ} (hn : 3 ≤ n)
    (j : Fin (n / 2)) :
    Group.IsPerfect (rankOne (rootGroup (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hF) n) j) := by
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hj : j.val + 1 < n / 2
  · have : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect
        (CFSG.LinearGroups.exists_finset_card_eq_four (by rw [hF]; nlinarith))
    exact Group.IsPerfect.ofSurjective
      (f := (CFSG.LieType.Steinberg.rankOneShortEquiv
        (hσ := unitaryInvolution_involutive hF) hj).symm.toMonoidHom) (MulEquiv.surjective _)
  · by_cases he : Even n
    · obtain ⟨e⟩ := CFSG.LieType.Steinberg.nonempty_rankOne_last_even_mulEquiv hF he (by omega) hj
      obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
      have : Group.IsPerfect (SpecialLinearGroup (Fin 2)
          (CFSG.LieType.Steinberg.fixedSubfield F 2 f)) :=
        CFSG.LinearGroups.special_linear_dimension_two_perfect
          (CFSG.LinearGroups.exists_finset_card_eq_four
            (by rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]; exact hq))
      have : Group.IsPerfect (SU (unitaryInvolution F 2 f) 2) := Group.IsPerfect.ofSurjective
        (f := (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).toMonoidHom) (MulEquiv.surjective _)
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) (MulEquiv.surjective _)
    · obtain ⟨e⟩ := CFSG.LieType.Steinberg.nonempty_rankOne_last_odd_mulEquiv hF he (by omega) hj
      have : Group.IsPerfect (SU (unitaryInvolution F 2 f) 3) :=
        (isQuasisimple_SU hF (n := 3) le_rfl (fun h => by
          have := (Prod.mk.inj h).2
          omega)).1
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) (MulEquiv.surjective _)

variable {K : Type} [Field K] [CharP K 2] {N ε : ℕ} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}

theorem ctuEmbed_shortTorus_mem_rankOne (hF : Nat.card F = (2 ^ f) ^ 2) (hε : ε ≤ 1)
    {j : Fin ((2 * N + ε) / 2)} (hj : j.val + 1 < (2 * N + ε) / 2) (κ : Kˣ) :
    ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N
      (Pi.mulSingle ⟨j.val, by omega⟩ κ * Pi.mulSingle ⟨j.val + 1, by omega⟩ κ⁻¹)) ∈
        rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
          (2 * N + ε)) j := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  refine levelTorus_le_rankOne (unitaryInvolution_involutive hF) hζ
    (fun _ hx => exists_norm_eq hF hx) j ?_
  unfold levelTorus
  rw [dite_eq_left hj]
  refine Subgroup.subset_closure ⟨Units.map ι κ, ?_⟩
  rw [coe_ctuEmbed_diagSp]
  congr 1
  have hjN : j.val + 1 < N := by omega
  have ha := lowIdx_eq_ctuCoord (ε := ε) (j := j) (by omega)
  have hb := lowIdx_eq_ctuCoord (ε := ε) (j := ⟨j.val + 1, hj⟩) hjN
  have hne : (⟨j.val, by omega⟩ : Fin N) ≠ ⟨j.val + 1, hjN⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  funext s
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective s
  simp only [shortTorusFun, ha, hb, ctuCoord_rev hε, ctuPar_inl, par_inl,
    (ctuCoord N ε).injective.eq_iff, Units.coe_map, MonoidHom.coe_ofClass, hι]
  rcases w with (p | p) | i
  · rw [ctuDiag_inl_inl]
    by_cases h1 : p = ⟨j.val, by omega⟩
    · subst h1
      simp [hne]
    · by_cases h2 : p = ⟨j.val + 1, hjN⟩
      · subst h2
        simp [Ne.symm hne]
      · simp [h1, h2]
  · rw [ctuDiag_inl_inr]
    by_cases h1 : p = ⟨j.val, by omega⟩
    · subst h1
      simp [hne]
    · by_cases h2 : p = ⟨j.val + 1, hjN⟩
      · subst h2
        simp [Ne.symm hne]
      · simp [h1, h2]
  · rw [ctuDiag_inr]
    simp

theorem ctuEmbed_rootTorusHom_mem_rankOne (hF : Nat.card F = (2 ^ f) ^ 2) (hε : ε ≤ 1)
    {j : Fin ((2 * N + ε) / 2)} (hj : ¬j.val + 1 < (2 * N + ε) / 2) (κ : Kˣ) :
    ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (rootTorusHom K N ⟨j.val, by omega⟩ κ) ∈
        rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
          (2 * N + ε)) j := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  refine levelTorus_le_rankOne (unitaryInvolution_involutive hF) hζ
    (fun _ hx => exists_norm_eq hF hx) j (longGen_mem_levelTorus hj (Units.map ι κ) (hι κ) ?_)
  rw [rootTorusHom_apply, coe_ctuEmbed_diagSp]
  congr 1
  have ha := lowIdx_eq_ctuCoord (ε := ε) (j := j) (by omega)
  funext s
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective s
  simp only [longTorusFun, ha, ctuCoord_rev hε, ctuPar_inl, par_inl,
    (ctuCoord N ε).injective.eq_iff, Units.coe_map, MonoidHom.coe_ofClass]
  rcases w with (p | p) | i
  · rw [ctuDiag_inl_inl]
    by_cases h1 : p = ⟨j.val, by omega⟩
    · subst h1
      simp
    · simp [h1]
  · rw [ctuDiag_inl_inr]
    by_cases h1 : p = ⟨j.val, by omega⟩
    · subst h1
      simp
    · simp [h1]
  · rw [ctuDiag_inr]
    simp

end Perfect

end CFSG.SeitzReduction.SymplecticPilot
