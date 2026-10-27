module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Norm

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

@[expose] noncomputable def normElt (m : ℕ) [NeZero m] (g : ModGL τ L) : ModGL τ L :=
  ((Finset.univ : Finset (ZMod m)).toList.map fun κ => iterHom S.D.step κ.val g).prod

theorem normElt_factor_data (hτ : τ ≠ .G2) (ψ : L →+* L) (m : ℕ) [NeZero m] (zu : ModGL τ L)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ aN bN aN' bN' : ℕ → Module.End L (RootModule τ L),
      aN 0 ≠ 0 ∧ aN' 0 ≠ 0 ∧
      (SimplyLacedTag τ → 2 ≤ Module.finrank L (LinearMap.range (aN' 0)) ∧
        Module.finrank L (LinearMap.range (bN 0)) ≤ 1) ∧
      (∀ t : L, ((zu * pinnedX τ L γ t * zu⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) =
        1 + t • aN 0 + t ^ 2 • bN 0) ∧
      (∀ t : L, ((normElt S m (zu * pinnedX τ L γ t * zu⁻¹) : ModGL τ L) :
          Module.End L (RootModule τ L)) =
        ((Finset.univ : Finset (ZMod m)).toList.map fun κ =>
          1 + (t ^ (S.D.q ^ κ.val)) • aN κ.val + (t ^ (S.D.q ^ κ.val)) ^ 2 • bN κ.val).prod) ∧
      (∀ t : L, ((Units.map (entrywiseHom ψ) (normElt S m (zu * pinnedX τ L γ t * zu⁻¹)) :
          ModGL τ L) : Module.End L (RootModule τ L)) =
        ((Finset.univ : Finset (ZMod m)).toList.map fun κ =>
          1 + (ψ (t ^ (S.D.q ^ κ.val))) • aN' κ.val +
            (ψ (t ^ (S.D.q ^ κ.val))) ^ 2 • bN' κ.val).prod) := by
  have hdata := fun κ : ZMod m => exists_factor_data S hτ ψ zu hγ κ.val
  choose aZ bZ aZ' bZ' haZ haZ' hrkZ hE1 hE2 using hdata
  have hcast : ∀ κ : ZMod m, ((κ.val : ℕ) : ZMod m) = κ := ZMod.natCast_zmod_val
  refine ⟨fun n => aZ (n : ZMod m), fun n => bZ (n : ZMod m), fun n => aZ' (n : ZMod m),
    fun n => bZ' (n : ZMod m), ?_, ?_, ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simpa using haZ 0
  · simpa using haZ' 0
  · intro hsl
    have := hrkZ 0 hsl
    have h0 : ((0 : ℕ) : ZMod m) = 0 := Nat.cast_zero
    beta_reduce
    rw [h0]
    exact this
  · have h := hE1 0 t
    rw [ZMod.val_zero, iterHom_zero, pow_zero, pow_one] at h
    simpa using h
  · unfold normElt
    rw [units_coe_list_prod]
    congr 1
    refine List.map_congr_left fun κ _ => ?_
    simp only [hcast]
    exact hE1 κ t
  · unfold normElt
    rw [map_list_prod, List.map_map, units_coe_list_prod]
    congr 1
    refine List.map_congr_left fun κ _ => ?_
    simp only [Function.comp, hcast]
    exact hE2 κ t

variable {m : ℕ} [NeZero m]

theorem zmod_vals_nodup : ((Finset.univ : Finset (ZMod m)).toList.map ZMod.val).Nodup :=
  List.Nodup.map (ZMod.val_injective m) (Finset.nodup_toList _)

theorem zero_mem_zmod_vals : 0 ∈ ((Finset.univ : Finset (ZMod m)).toList.map ZMod.val) :=
  List.mem_map.2 ⟨0, Finset.mem_toList.2 (Finset.mem_univ _), ZMod.val_zero⟩

theorem zmod_vals_lt : ∀ k ∈ ((Finset.univ : Finset (ZMod m)).toList.map ZMod.val), k < m := by
  intro k hk
  obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hk
  exact ZMod.val_lt κ

theorem commute_conj_pinnedX_of_norm (hτ : τ ≠ .G2) (zu : ModGL τ L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {K : Type} [Field K] [Fintype K] (ι : K →+* L)
    (hK : Fintype.card K = S.D.q ^ m) (hq3 : 3 ≤ S.D.q) (hQ4 : 4 ≤ S.D.q ^ m) {z : ModGL τ L}
    (hz : ∀ t : K, Commute z (normElt S m (zu * pinnedX τ L γ (ι t) * zu⁻¹))) :
    ∀ c : L, Commute z (zu * pinnedX τ L γ c * zu⁻¹) := by
  classical
  obtain ⟨aN, bN, aN', bN', ha, ha', hrk, hE0, hE1, hE2⟩ :=
    normElt_factor_data S hτ (RingHom.id L) m zu hγ
  set ks := (Finset.univ : Finset (ZMod m)).toList.map ZMod.val with hks
  have hsq : ∀ (x : L) (n : ℕ), x ^ (2 * n) = (x ^ n) ^ 2 := fun x n => by
    rw [← pow_mul, mul_comm]
  have hmain : ∀ t : K,
      (z : Module.End L (RootModule τ L)) * evAt (ι t) (prodList S.D.q aN bN ks) =
        evAt (ι t) (prodList S.D.q aN bN ks) * (z : Module.End L (RootModule τ L)) := by
    intro t
    have hf := congrArg (fun g : ModGL τ L => (g : Module.End L (RootModule τ L))) (hz t).eq
    simp only [Units.val_mul] at hf
    rw [hE1] at hf
    have hR : evAt (ι t) (prodList S.D.q aN bN ks) =
        ((Finset.univ : Finset (ZMod m)).toList.map fun κ =>
          1 + ((ι t) ^ (S.D.q ^ κ.val)) • aN κ.val +
            ((ι t) ^ (S.D.q ^ κ.val)) ^ 2 • bN κ.val).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, hsq]
    rw [hR]
    exact hf
  obtain ⟨hza, hzb⟩ := commute_coeff_one_two ι hq3 (Nat.pos_of_ne_zero (NeZero.ne m)) hK hQ4 ks
    zmod_vals_nodup zero_mem_zmod_vals zmod_vals_lt aN bN (z : Module.End L (RootModule τ L))
    hmain
  intro c
  have hform := hE0 c
  generalize zu * pinnedX τ L γ c * zu⁻¹ = W at hform ⊢
  show z * W = W * z
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hform]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hza, hzb]

theorem false_of_fixed_by_twist_of_norm (hτ : τ ≠ .G2) (zu : ModGL τ L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {K : Type} [Field K] [Fintype K] (ι : K →+* L)
    (hK : Fintype.card K = S.D.q ^ m) {r f j : ℕ} [ExpChar L r] (hr : r.Prime)
    (hq : S.D.q = r ^ f) (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ) (hj0 : 0 < j) (hjf : j < f)
    (z' : ModGL τ L)
    (hfix : ∀ t : K, z' * Units.map (entrywiseHom (iterateFrobenius L r j))
        (normElt S m (zu * pinnedX τ L γ (ι t) * zu⁻¹)) * z'⁻¹ =
      normElt S m (zu * pinnedX τ L γ (ι t) * zu⁻¹)) : False := by
  classical
  have hr2 := hr.two_le
  have hf2 : 2 ≤ f := by omega
  have hrf4 : 4 ≤ r ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
      _ ≤ r ^ f := Nat.pow_le_pow_right (by omega) hf2
  have hms : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hKcard' : Fintype.card K = (r ^ f) ^ m := by rw [hK, hq]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L →+* L, ψ = iterateFrobenius L r j := ⟨_, rfl⟩
  rw [← hψ] at hfix
  have hψpow : ∀ x : L, ψ x = x ^ (r ^ j) := fun x => by rw [hψ, iterateFrobenius_def]
  obtain ⟨aN, bN, aN', bN', ha, ha', hrk, hE0, hE1, hE2⟩ :=
    normElt_factor_data S hτ ψ m zu hγ
  simp only [hq] at hE1 hE2
  set ks := (Finset.univ : Finset (ZMod m)).toList.map ZMod.val with hks
  have hsq : ∀ (x : L) (n : ℕ), x ^ (2 * n) = (x ^ n) ^ 2 := fun x n => by
    rw [← pow_mul, mul_comm]
  have hmain : ∀ t : K,
      (z' : Module.End L (RootModule τ L)) *
        evAt ((ι t) ^ (r ^ j)) (prodList (r ^ f) aN' bN' ks) *
          (↑z'⁻¹ : Module.End L (RootModule τ L)) =
        evAt (ι t) (prodList (r ^ f) aN bN ks) := by
    intro t
    have hfA := congrArg (fun g : ModGL τ L => (g : Module.End L (RootModule τ L))) (hfix t)
    simp only [Units.val_mul] at hfA
    rw [hE1, hE2] at hfA
    have hR : evAt (ι t) (prodList (r ^ f) aN bN ks) =
        ((Finset.univ : Finset (ZMod m)).toList.map fun κ =>
          1 + ((ι t) ^ (r ^ f) ^ κ.val) • aN κ.val +
            ((ι t) ^ (r ^ f) ^ κ.val) ^ 2 • bN κ.val).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, hsq]
    have hL : evAt ((ι t) ^ (r ^ j)) (prodList (r ^ f) aN' bN' ks) =
        ((Finset.univ : Finset (ZMod m)).toList.map fun κ =>
          1 + (ψ ((ι t) ^ (r ^ f) ^ κ.val)) • aN' κ.val +
            (ψ ((ι t) ^ (r ^ f) ^ κ.val)) ^ 2 • bN' κ.val).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, hsq, hψpow]
      rw [pow_right_comm ((ι t)) ((r ^ f) ^ κ.val) (r ^ j)]
    rw [hR, hL]
    exact hfA
  by_cases hex : r ^ j = 2 ∧ r ^ f = 4
  · obtain ⟨hrj, hrf⟩ := hex
    have hsl : SimplyLacedTag τ := by
      rcases hq4 with h | h
      · exact absurd (by rw [hq, hrf]) h
      · exact h
    have hm4 := twisted_conj_q4 ι hms (by rw [hKcard', hrf]) ks zmod_vals_nodup
      zero_mem_zmod_vals zmod_vals_lt aN bN aN' bN' z' (fun t => by
        have := hmain t
        rwa [hrf, hrj] at this)
    obtain ⟨hr2', hr1⟩ := hrk hsl
    have h3 := finrank_range_conj_eq z' (aN' 0)
    rw [hm4] at h3
    omega
  · refine no_twisted_conj ι hr hj0 hjf hms hKcard' hrf4 ?_ ks zmod_vals_nodup
      zero_mem_zmod_vals zmod_vals_lt aN bN aN' bN' ha ha' z' hmain
    intro hc2
    have hr2' : r = 2 := by
      have : r ∣ 2 := by
        rw [← hc2]
        exact dvd_pow_self r hj0.ne'
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
    subst hr2'
    have hf3 : f ≠ 2 := fun hf2' => hex ⟨hc2, by rw [hf2']; norm_num⟩
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) (by omega)

end Norm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
