module

public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.Q3.Q3TPSGN
public import CFSG.ClassicalInvolution.Q3.Q3TPSNorm
public import CFSG.ClassicalInvolution.Q3.Q3TWWRowBPair
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.ClassicalInvolution.Q3.Q3TY5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWC

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair shortBlock)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

@[expose] def PartnerPatternBPair3 {G : Type} [Group G] (m : ℕ) (Ω : Set (Subgroup G))
    (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin m → Subgroup G, (∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) ∧ (∀ a, Commutes K (j a)) ∧
    (∀ a : Fin m, 1 ≤ a.val → j a ≤ Subgroup.centralizer ({t} : Set G)) ∧
    (∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b)) ∧
    (∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) ∧
    (∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockPair (GaloisField 3 1) W (j a) (j b)) ∧
    (∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (j a))

section Short

theorem sl2Upper_cube {F : Type} [Field F] [CharP F 3] (c : F) :
    (CFSG.LieType.Steinberg.sl2Upper c) ^ 3 = 1 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, CFSG.LieType.Steinberg.sl2Upper, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (c) * h3

theorem sl2Lower_cube {F : Type} [Field F] [CharP F 3] (c : F) :
    (CFSG.LieType.Steinberg.sl2Lower c) ^ 3 = 1 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, CFSG.LieType.Steinberg.sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (c) * h3

theorem sl2_mem_closure_cube {F : Type} [Field F] [CharP F 3] (A : SL(2, F)) :
    A ∈ Subgroup.closure {g : SL(2, F) | g ^ 3 = 1} := by
  have h : A ∈ Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c}) := by
    rw [closure_tv_two]
    trivial
  refine Subgroup.closure_mono ?_ h
  rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact (by rw [tv01_eq_sl2Upper]; exact sl2Upper_cube c : (tv 0 1 c : SL(2, F)) ^ 3 = 1)
  · exact (by rw [tv10_eq_sl2Lower]; exact sl2Lower_cube c : (tv 1 0 c : SL(2, F)) ^ 3 = 1)

theorem le_closure_cube_one_of_symplecticBlockPair {G : Type} [Group G] {W U V : Subgroup G}
    (h : SymplecticBlockPair (GaloisField 3 1) W U V) :
    V ≤ Subgroup.closure {x : G | x ∈ V ∧ x ^ 3 = 1} := by
  obtain ⟨θ, c, -, -, -, -, hV⟩ := h
  let φ : SL(2, GaloisField 3 1) →* G :=
    θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp
      (shortBlock (GaloisField 3 1) (zero_ne_one : (0 : Fin 2) ≠ 1)))
  have hVφ : V = φ.range := by
    rw [← hV]
    simp only [φ, MonoidHom.range_comp]
  intro x hx
  rw [hVφ] at hx
  obtain ⟨A, rfl⟩ := hx
  have hA := sl2_mem_closure_cube A
  have hmap : φ A ∈ (Subgroup.closure {g : SL(2, GaloisField 3 1) | g ^ 3 = 1}).map φ :=
    ⟨A, hA, rfl⟩
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨hVφ ▸ ⟨g, rfl⟩, by rw [← map_pow, hg, map_one]⟩

end Short

section Chain


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

def toS3 (c : TCtx3 tY nY Ω K z) : Q3TP.TCtxS3 tY nY Ω K z where
  hΩ := c.hΩ
  hex := c.hex
  hK := c.hK
  hz := c.hz
  hP1 := c.hP1
  hO3 := c.hO3
  d := c.d
  hQ₀ := c.hQ₀
  hY := ⟨c.hY.sc, c.hY.perfK, c.hY.pow3, c.hY.central, c.hY.cop⟩

theorem commutes_partner_of_short3 (c : TCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {S : Subgroup G}
    (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) (hSK : Commutes K S)
    (hgen : S ≤ Subgroup.closure {x : G | x ∈ S ∧ x ^ 3 = 1}) : Commutes β S := by
  have hcent : S ≤ Subgroup.centralizer (β : Set G) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro s ⟨hsS, hs3⟩
    have hst : s * t * s⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hSt hsS)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hsK : ∀ k ∈ K, s * k * s⁻¹ = k := fun k hk => by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hSK k hk s hsS).symm
    have hnorm := Q3TPS.TCtxS3.normalizes_of_cube_one (toS3 c) hsingle hβ ht hs3 hst
    have hcen := Q3TPS.centralizes_of_cube_one hs3 hKβ hsK hnorm
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    have := hcen b hb
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  intro b hb s hs
  exact Subgroup.mem_centralizer_iff.mp (hcent hs) b hb

variable (hMFZ : Gaps.FundNoncentral 3)

include hMFZ in
theorem chain_of_patternB3 {N : ℕ} (hN : 5 ≤ N) {K : Subgroup G} {z : G}
    (c : TCtx3 .POmegaOdd (N - 2) (conjClass3 K) K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    {β : Subgroup G} (hβ : β ∈ conjClass3 K) {t : G} (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hpat : PartnerPatternBPair3 (N - 2) (conjClass3 K) K β t) :
    ∃ U : Fin N → Subgroup G, (∀ k : Fin N, k.val + 1 < N → U k ∈ conjClass3 K) ∧
      (∀ i j : Fin N, i.val + 1 < j.val → Commutes (U i) (U j)) ∧
      (∀ i j : Fin N, i.val + 1 = j.val → j.val + 1 < N →
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
      ∀ i j : Fin N, i.val + 2 = N → j.val + 1 = N →
        ∃ W, SymplecticBlockPair (GaloisField 3 1) W (U i) (U j) := by
  obtain ⟨j, hjΩ, hjK, hjt, hjcomm, hjpair, hjsp, hβj⟩ := hpat
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hβj' : ∀ i : Fin (N - 2), 1 ≤ i.val → Commutes β (j i) := by
    intro i hi
    by_cases hlong : i.val + 1 < N - 2
    · exact c.commutes_partner_of_centralizes3 hMFZ hsingle D hβ ht hKβ
        (mem_centralizingMembers_of_commutes (hjΩ i hlong) c.hz.mem (hjK i).symm) (hjt i hi)
        (hjK i)
    · have hi' : i.val + 1 = N - 2 := by have := i.2; omega
      obtain ⟨a, ha⟩ : ∃ a : Fin (N - 2), a.val + 2 = N - 2 :=
        ⟨⟨N - 4, by omega⟩, by simp only; omega⟩
      obtain ⟨W, hW⟩ := hjsp a i ha hi'
      exact commutes_partner_of_short3 c hsingle hβ ht hKβ (hjt i hi) (hjK i)
        (le_closure_cube_one_of_symplecticBlockPair hW)
  let U : Fin N → Subgroup G := fun k =>
    if h0 : k.val = 0 then K else if h1 : k.val = 1 then β else j ⟨k.val - 2, by omega⟩
  have hU0 : ∀ k : Fin N, k.val = 0 → U k = K := fun k h => by simp [U, h]
  have hU1 : ∀ k : Fin N, k.val = 1 → U k = β := fun k h => by simp [U, h]
  have hUj : ∀ k : Fin N, (h : 2 ≤ k.val) → U k = j ⟨k.val - 2, by omega⟩ := by
    intro k h
    simp only [U]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_or_ge k.val 2 with hk2 | hk2
    · rcases Nat.lt_or_ge k.val 1 with hk1 | hk1
      · rw [hU0 k (by omega)]
        exact hK
      · rw [hU1 k (by omega)]
        exact hβ
    · rw [hUj k hk2]
      exact hjΩ _ (by simp only; omega)
  · intro a b hab u hu v hv
    rcases Nat.lt_or_ge a.val 2 with ha | ha
    · rcases Nat.lt_or_ge a.val 1 with ha0 | ha1
      · rw [hU0 a (by omega)] at hu
        rw [hUj b (by omega)] at hv
        exact hjK _ u hu v hv
      · rw [hU1 a (by omega)] at hu
        rw [hUj b (by omega)] at hv
        exact hβj' ⟨b.val - 2, by omega⟩ (by simp only; omega) u hu v hv
    · rw [hUj a ha] at hu
      rw [hUj b (by omega)] at hv
      exact hjcomm _ _ (by simp only; omega) u hu v hv
  · intro a b hab hb
    rcases Nat.lt_or_ge a.val 2 with ha | ha
    · rcases Nat.lt_or_ge a.val 1 with ha0 | ha1
      · rw [hU0 a (by omega), hU1 b (by omega)]
        exact hKβ
      · rw [hU1 a (by omega), hUj b (by omega)]
        have hb0 : (⟨b.val - 2, by omega⟩ : Fin (N - 2)) = ⟨0, by omega⟩ :=
          Fin.ext (by simp only; omega)
        rw [hb0]
        exact hβj ⟨0, by omega⟩ rfl
    · rw [hUj a ha, hUj b (by omega)]
      exact hjpair _ _ (by simp only; omega) (by simp only; omega)
  · intro a b ha hb
    rw [hUj a (by omega), hUj b (by omega)]
    exact hjsp _ _ (by simp only; omega) (by simp only; omega)

end Chain

end CFSG.ClassicalInvolution.Q3.Q3TWC
