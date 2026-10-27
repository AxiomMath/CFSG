module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs
public import CFSG.ClassicalInvolution.Q3.TL4D1MBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE

section S3Lemmas

theorem not_hasS3Quot_of_card_lt {E : Type} [Group E] [Finite E] (h : Nat.card E < 6) :
    ¬ HasS3Quot E := by
  rintro ⟨π, hπ⟩
  have h1 := Nat.card_le_card_of_surjective π hπ
  have h2 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  omega

theorem not_hasS3Quot_of_odd_gen {H : Type} [Group H] (P : Subgroup H)
    (h : P ≤ Subgroup.closure {y : H | y ∈ P ∧ Odd (orderOf y)}) : ¬ HasS3Quot ↥P := by
  rintro ⟨π, hπ⟩
  let s : ↥P →* ℤˣ := Equiv.Perm.sign.comp π
  have hodd : ∀ y : ↥P, Odd (orderOf (y : H)) → s y = 1 := by
    intro y hy
    have h2 : (s y) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (s y) with h | h <;> rw [h] <;> simp
    have h1 : orderOf (s y) ∣ orderOf (y : H) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_map_dvd s y
    have h3 : orderOf (s y) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h4 : Odd (orderOf (s y)) := hy.of_dvd_nat h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h5 | h5
    · exact orderOf_eq_one_iff.mp h5
    · rw [h5] at h4
      exact absurd h4 (by decide)
  have hle : Subgroup.closure {y : H | y ∈ P ∧ Odd (orderOf y)} ≤ s.ker.map P.subtype := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyP, hy⟩
    exact ⟨⟨y, hyP⟩, hodd ⟨y, hyP⟩ hy, rfl⟩
  have hK : ∀ x : ↥P, s x = 1 := by
    intro x
    obtain ⟨x', hx', hxx'⟩ := hle (h x.2)
    have : x' = x := Subtype.ext hxx'
    rw [← this]
    exact hx'
  obtain ⟨x, hx⟩ := hπ (Equiv.swap (0 : Fin 3) 1)
  have h6 := hK x
  simp only [s, MonoidHom.comp_apply, hx, Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)] at h6
  exact absurd h6 (by decide)

end S3Lemmas

section PermBar

theorem permBar_eq_one_sq {k : ℕ} (x : AEQ k) (h : TL4.permBar k x = 1) : x * x = 1 := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  have hw : w.perm = 1 := by
    have h' : TL4.permBar k (mkQ k w) = 1 := h
    rwa [TL4.permBar_mkQ] at h'
  have hww : w * w = 1 := by
    refine Wr.ext (funext fun i => ?_) ?_
    · show w.vec i + w.vec (w.perm.symm i) = 0
      rw [hw]
      exact Wr.zmod_two_add_self _
    · show w.perm * w.perm = 1
      rw [hw, mul_one]
  show mkQ k w * mkQ k w = 1
  rw [← map_mul, hww, map_one]

theorem hasS3Quot_map_permBar {k : ℕ} (E : Subgroup (AEQ k)) (h : HasS3Quot ↥E) :
    HasS3Quot ↥(E.map (TL4.permBar k)) := by
  refine HasS3Quot.of_surjective ((TL4.permBar k).subgroupMap E)
    (MonoidHom.subgroupMap_surjective _ _) (fun x hx => ⟨1, ?_⟩) h
  have h1 : TL4.permBar k (x : AEQ k) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    simpa using this
  apply Subtype.ext
  have := permBar_eq_one_sq _ h1
  simpa [pow_two] using this

end PermBar

section PermComb

open Equiv Equiv.Perm Finset

variable {α : Type} [Fintype α] [DecidableEq α]

theorem eq_one_of_sign_one_of_card_support_le_two {σ : Perm α} (hs : sign σ = 1)
    (h : #σ.support ≤ 2) : σ = 1 := by
  by_contra hne
  have h0 : #σ.support ≠ 0 := fun h0 => hne (Equiv.Perm.card_support_eq_zero.mp h0)
  have h1 : #σ.support ≠ 1 := Equiv.Perm.card_support_ne_one σ
  have h2 : #σ.support = 2 := by omega
  have h3 := (Equiv.Perm.card_support_eq_two.mp h2).sign_eq
  rw [hs] at h3
  exact absurd h3 (by decide)

theorem false_of_pow_two_support_six {σ : Perm α} (h2 : σ ^ 2 = 1) (h6 : #σ.support = 6)
    (hs : sign σ = 1) : False := by
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hsum : σ.cycleType.sum = #σ.support := Equiv.Perm.sum_cycleType σ
  have hc : σ.cycleType.card = 3 := by
    have : σ.cycleType.sum = σ.cycleType.card * 2 := by
      conv_lhs => rw [hct]
      simp
    omega
  rw [Equiv.Perm.sign_of_cycleType, hsum, h6, hc] at hs
  exact absurd hs (by decide)

end PermComb

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
