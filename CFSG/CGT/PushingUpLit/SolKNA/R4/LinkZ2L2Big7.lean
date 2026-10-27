module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Normalize

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F]

theorem zmod_add_self_eq_zero {N : ℕ} [NeZero N] (i : ZMod (2 * N)) (hi : i + i = 0) :
    i = 0 ∨ i = (N : ZMod (2 * N)) := by
  haveI : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hdvd : 2 * N ∣ i.val + i.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val, hi]
  obtain ⟨k, hk⟩ := hdvd
  have hlt : i.val < 2 * N := ZMod.val_lt i
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    have : 2 * N * 2 ≤ 2 * N * k := Nat.mul_le_mul_left (2 * N) h
    omega
  interval_cases k
  · left
    have h0 : i.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val i, h0, Nat.cast_zero]
  · right
    have h1 : i.val = N := by omega
    rw [← ZMod.natCast_zmod_val i, h1]

theorem quaternion_a_add_self {N : ℕ} [NeZero N] :
    (((N : ℕ) : ZMod (2 * N)) + ((N : ℕ) : ZMod (2 * N))) = 0 := by
  rw [← Nat.cast_add, show N + N = 2 * N by ring, ZMod.natCast_self]

theorem quaternion_a_mul_self {N : ℕ} [NeZero N] :
    (QuaternionGroup.a ((N : ℕ) : ZMod (2 * N)) : QuaternionGroup N) *
      QuaternionGroup.a ((N : ℕ) : ZMod (2 * N)) = 1 := by
  rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
  congr 1
  exact quaternion_a_add_self

theorem quaternion_a_ne_one {N : ℕ} [NeZero N] :
    (QuaternionGroup.a ((N : ℕ) : ZMod (2 * N)) : QuaternionGroup N) ≠ 1 := by
  intro h
  have h0 : ((N : ℕ) : ZMod (2 * N)) = 0 := by
    rw [QuaternionGroup.one_def] at h
    exact QuaternionGroup.a.inj h
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have := Nat.le_of_dvd hN h0
  omega

theorem quaternion_a_central {N : ℕ} [NeZero N] (x : QuaternionGroup N) :
    x * QuaternionGroup.a ((N : ℕ) : ZMod (2 * N)) =
      QuaternionGroup.a ((N : ℕ) : ZMod (2 * N)) * x := by
  cases x with
  | a i => rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
  | xa i =>
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
    have hneg : ((N : ℕ) : ZMod (2 * N)) = -((N : ℕ) : ZMod (2 * N)) :=
      eq_neg_of_add_eq_zero_left quaternion_a_add_self
    rw [sub_eq_add_neg, ← hneg]

theorem quaternion_sq_eq_one_iff {N : ℕ} [NeZero N] (x : QuaternionGroup N) :
    x * x = 1 ↔ x = 1 ∨ x = QuaternionGroup.a ((N : ℕ) : ZMod (2 * N)) := by
  constructor
  · intro hx
    cases x with
    | a i =>
      rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at hx
      rcases zmod_add_self_eq_zero i (QuaternionGroup.a.inj hx) with rfl | rfl
      · exact Or.inl QuaternionGroup.one_def.symm
      · exact Or.inr rfl
    | xa i =>
      rw [← pow_two, QuaternionGroup.xa_sq, QuaternionGroup.one_def] at hx
      have h0 : ((N : ℕ) : ZMod (2 * N)) = 0 := QuaternionGroup.a.inj hx
      rw [ZMod.natCast_eq_zero_iff] at h0
      have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      have := Nat.le_of_dvd hN h0
      omega
  · rintro (rfl | rfl)
    · rw [one_mul]
    · exact quaternion_a_mul_self

theorem mulAut_conj_conj (n m : X) :
    (MulAut.conj (MulAut.conj n : MulAut X)) (MulAut.conj m) = MulAut.conj (n * m * n⁻¹) := by
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]

@[expose] noncomputable def embConjBy (E : PGamEmb X F) (n : X) : PGamEmb X F where
  ρ := E.ρ.comp (MulAut.conj (MulAut.conj n : MulAut X)).toMonoidHom
  inj := fun _ _ h => (MulAut.conj (MulAut.conj n : MulAut X)).injective (E.inj h)
  inner := by
    intro m hm
    have hmem : n * m * n⁻¹ ∈ genFittingFStar X :=
      (CFSG.ClassicalInvolution.genFittingFStar_normal X).conj_mem m hm n
    obtain ⟨g, hg⟩ := E.inner (n * m * n⁻¹) hmem
    refine ⟨g, ?_⟩
    change E.ρ ((MulAut.conj (MulAut.conj n : MulAut X)) (MulAut.conj m)) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
    rw [mulAut_conj_conj]
    exact hg
  onto := by
    intro g
    obtain ⟨n', hn', hg⟩ := E.onto g
    refine ⟨n⁻¹ * n' * n, ?_, ?_⟩
    · simpa [mul_assoc] using
        (CFSG.ClassicalInvolution.genFittingFStar_normal X).conj_mem n' hn' n⁻¹
    · change E.ρ ((MulAut.conj (MulAut.conj n : MulAut X)) (MulAut.conj (n⁻¹ * n' * n))) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
      rw [mulAut_conj_conj, show n * (n⁻¹ * n' * n) * n⁻¹ = n' by group]
      exact hg
  conjInj := E.conjInj

theorem embConjBy_conj (E : PGamEmb X F) (n x : X) :
    (embConjBy E n).ρ (MulAut.conj x) = E.ρ (MulAut.conj (n * x * n⁻¹)) := by
  change E.ρ ((MulAut.conj (MulAut.conj n : MulAut X)) (MulAut.conj x)) =
    E.ρ (MulAut.conj (n * x * n⁻¹))
  rw [mulAut_conj_conj]

theorem exists_normalized_emb (hs : IsSimpleGroup ↥(genFittingFStar X)) {p f : ℕ} (hp2 : p ≠ 2)
    (hf : Even f) (hl : LieModel (TL4.FStarQuot X) .PSL 2 p f) {z : X} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzN : z ∈ genFittingFStar X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ 4 ≤ p ^ f ∧ p.Prime ∧
      ∃ E : PGamEmb X F, E.ρ (MulAut.conj z) = SemidirectProduct.inl (pD (-1)) := by
  obtain ⟨F, _, _, hF, hp, h4, ⟨E⟩⟩ := exists_pgamEmb hs hp2 hl
  obtain ⟨hK, h2⟩ := field_facts hp hp2 hF h4
  obtain ⟨g, rfl⟩ := hf
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h4u : 4 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have hmod : p ^ (g + g) % 4 = 1 := by
      have hsq : p ^ (g + g) = (p ^ g) ^ 2 := by
        rw [show g + g = g * 2 by ring, pow_mul]
      rw [hsq, Nat.pow_mod]
      have hlt : p ^ g % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have hodd4 : p ^ g % 4 % 2 = 1 := by
        rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 4)]
        exact Nat.odd_iff.mp hpodd.pow
      generalize p ^ g % 4 = r at hlt hodd4 ⊢
      interval_cases r <;> simp_all
    have : 1 ≤ p ^ (g + g) := Nat.one_le_pow _ _ hp.pos
    omega
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_units h4u
  obtain ⟨g₀, hg₀⟩ := E.inner z hzN
  obtain ⟨s₀, hs₀⟩ := pD_neg_one_mem i hi
  have hg₀inv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g₀ := by
    refine ⟨fun h => hz1 ?_, ?_⟩
    · apply E.conjInj
      apply E.inj
      rw [hg₀, h, map_one, map_one, map_one, map_one]
    · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      apply inl_inj'
      rw [map_one, map_one, map_pow, map_pow, ← hg₀, ← map_pow, ← map_pow, sq, hz2, map_one,
        map_one]
  have hs₀inv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s₀ := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, map_one] at hs₀
      exact neg_one_ne_one_units h2 (pD_eq_one_iff.mp hs₀.symm)
    · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [map_pow, hs₀, pD_pow, map_one, show ((-1 : Fˣ)) ^ 2 = 1 by norm_num, pD_one]
  obtain ⟨gc, hgc⟩ := psl2_involutions_conjugate_of_odd_prime_power F hK g₀ s₀ hg₀inv hs₀inv
  obtain ⟨n, -, hn⟩ := E.onto gc
  have hzρ : E.ρ (MulAut.conj (n * z * n⁻¹)) = SemidirectProduct.inl (pD (-1)) := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hn, hg₀, ← map_inv, ← map_mul,
      ← map_mul, ← map_inv, ← map_mul, ← map_mul, hgc, hs₀]
  exact ⟨F, inferInstance, inferInstance, hF, h4, hp, ⟨embConjBy E n, by
    rw [embConjBy_conj]
    exact hzρ⟩⟩

theorem quatInvolution_sq {Q : Subgroup X} {r : ℕ} (hr : 4 ≤ r) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    quatInvolution r e * quatInvolution r e = 1 := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h' : e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) *
      e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) = 1 := by
    rw [← map_mul, quaternion_a_mul_self, map_one]
  simpa [quatInvolution, Subgroup.coe_mul] using congrArg (fun z : ↥Q => (z : X)) h'

theorem quatInvolution_ne_one {Q : Subgroup X} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) : quatInvolution r e ≠ 1 := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  intro h
  have h1 : e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) = 1 := by
    apply Subtype.ext
    simpa [quatInvolution] using h
  have h2 := congrArg e h1
  rw [MulEquiv.apply_symm_apply, map_one] at h2
  exact quaternion_a_ne_one h2

theorem quatInvolution_mem {Q : Subgroup X} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) : quatInvolution r e ∈ Q :=
  (e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))).2

theorem quatInvolution_comm {Q : Subgroup X} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {y : X} (hy : y ∈ Q) :
    y * quatInvolution r e = quatInvolution r e * y := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc : ∀ z : ↥Q, z * e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) =
      e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) * z := by
    intro z
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact quaternion_a_central (e z)
  simpa [quatInvolution, Subgroup.coe_mul] using
    congrArg (fun z : ↥Q => (z : X)) (hc ⟨y, hy⟩)

theorem eq_quatInvolution_of_sq {Q : Subgroup X} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {y : X} (hy : y ∈ Q) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    y = quatInvolution r e := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  let y' : ↥Q := ⟨y, hy⟩
  let A : ZMod (2 * 2 ^ (r - 2)) := ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))
  have hy' : y' * y' = 1 := by
    apply Subtype.ext
    simpa [y'] using hy2
  have hy'e : e y' * e y' = 1 := by
    rw [← map_mul, hy', map_one]
  have hew : e (e.symm (QuaternionGroup.a A)) = QuaternionGroup.a A := MulEquiv.apply_symm_apply e _
  have heq : e y' = QuaternionGroup.a A := by
    rcases (quaternion_sq_eq_one_iff (e y')).mp hy'e with h | h
    · exfalso
      apply hy1
      have h1 : y' = 1 := by
        apply e.injective
        rw [h, map_one]
      simpa [y'] using congrArg (fun z : ↥Q => (z : X)) h1
    · exact h
  have hw : (⟨quatInvolution r e, quatInvolution_mem hr e⟩ : ↥Q) = e.symm (QuaternionGroup.a A) :=
    Subtype.ext rfl
  have : y' = ⟨quatInvolution r e, quatInvolution_mem hr e⟩ := by
    apply e.injective
    rw [heq, hw, hew]
  exact congrArg (fun z : ↥Q => (z : X)) this

theorem quatInvolution_mem_fstar (hidx : (genFittingFStar X).index ≤ 2) {Q : Subgroup X} {r : ℕ}
    (hr : 4 ≤ r) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    quatInvolution r e ∈ genFittingFStar X := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hsqN : ∀ x : X, x * x ∈ genFittingFStar X := by
    intro x
    rcases (by omega : (genFittingFStar X).index = 1 ∨ (genFittingFStar X).index = 2 ∨
        (genFittingFStar X).index = 0) with h | h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top _
    · exact Subgroup.mul_self_mem_of_index_two h x
    · exact absurd h Subgroup.index_ne_zero_of_finite
  have h2r : 2 ^ (r - 2) = 2 ^ (r - 3) + 2 ^ (r - 3) := by
    rw [show r - 2 = (r - 3) + 1 by omega, pow_succ]
    ring
  have hsq_a : (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))) :
        QuaternionGroup (2 ^ (r - 2))) *
      QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))) =
      QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
    rw [QuaternionGroup.a_mul_a]
    congr 1
    rw [← Nat.cast_add, h2r]
  have hx : ((e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : X) *
      ((e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : X) =
      quatInvolution r e := by
    have h1 : e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) *
        e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) =
        e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) := by
      rw [← map_mul, hsq_a]
    simpa [quatInvolution, Subgroup.coe_mul] using
      congrArg (fun z : ↥Q => (z : X)) h1
  have := hsqN ((e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : X)
  rwa [hx] at this

end Normalize

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
