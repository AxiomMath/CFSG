module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpIso
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpCount
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpVal
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421MonoGood
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421R

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof K421BaseProof CFSG.Open

@[expose] def tc (Q : ℕ) : ℕ := if 3 ∣ Q - 1 then Q - 1 else Q + 1

section Count

variable {F : Type} [Field F] [CharP F 2]

@[expose] def tmGL (α β : F) (h : Nrm F α β = 1) : GL (Fin 2) F :=
  ⟨tm F α β, tm F (α + β) β,
    by
      have h2 := two_eq_zero_F F
      have e1 : α * (α + β) + β * β = Nrm F α β := by simp only [Nrm]; ring
      have e2 : α * β + β * (α + β) + β * β = 0 := by linear_combination (α * β + β ^ 2) * h2
      rw [tm_mul, e1, e2, h, tm_one],
    by
      have h2 := two_eq_zero_F F
      have e1 : (α + β) * α + β * β = Nrm F α β := by simp only [Nrm]; ring
      have e2 : (α + β) * β + β * α + β * β = 0 := by linear_combination (α * β + β ^ 2) * h2
      rw [tm_mul, e1, e2, h, tm_one]⟩

theorem tmGL_mem (α β : F) (h : Nrm F α β = 1) : tmGL α β h ∈ Tall F := ⟨α, β, h, rfl⟩

noncomputable def tallEquiv (F : Type) [Field F] [CharP F 2] :
    ↥(Tall F) ≃ {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} :=
  Equiv.ofBijective
    (fun g => ⟨((g.1 : GL (Fin 2) F).val 0 0, (g.1 : GL (Fin 2) F).val 0 1), by
      obtain ⟨α, β, hn, hg⟩ := g.2
      rw [hg]
      simpa [tm, Nrm] using hn⟩)
    ⟨by
      intro g g' h
      obtain ⟨α, β, hn, hg⟩ := g.2
      obtain ⟨α', β', hn', hg'⟩ := g'.2
      have h1 := congrArg Subtype.val h
      simp only [Prod.mk.injEq] at h1
      rw [hg, hg'] at h1
      simp only [tm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h1
      apply Subtype.ext
      apply Units.ext
      rw [hg, hg', h1.1, h1.2],
    by
      rintro ⟨⟨α, β⟩, h⟩
      have hn : Nrm F α β = 1 := h
      exact ⟨⟨tmGL α β hn, tmGL_mem α β hn⟩, by simp [tmGL, tm]⟩⟩

theorem card_Tall [Finite F] : Nat.card ↥(Tall F) = tc (Nat.card F) := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (tallEquiv F), K421SpCountProof.card_norm_one_eq, tc]

end Count

section Rall

variable (F : Type) [Field F] [CharP F 2]

theorem card_Bsub : Nat.card ↥(Bsub F) = Nat.card ↥(Tall F) ^ 3 := by
  rw [Bsub, ← Nat.card_congr (MonoidHom.ofInjective Bhom_injective).toEquiv, Nat.card_pi]
  simp

theorem s_not_mem_Bsub : (monoSp F).s ∉ Bsub F := by
  rintro ⟨y, hy⟩
  have h : bd (fun j => (((y j : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      bc F sMat := congrArg (fun g : ↥(SpI F) => ((g : GL Idx F) : Matrix Idx Idx F)) hy
  have h1 := congrFun (congrFun h (1, 0)) (0, 0)
  simp [bd, bc, sMat] at h1

theorem s_sq_not_mem_Bsub : (monoSp F).s ^ 2 ∉ Bsub F := by
  intro h
  apply s_not_mem_Bsub F
  have h4 : (monoSp F).s = ((monoSp F).s ^ 2) ^ 2 := by
    rw [← pow_mul]
    have : (monoSp F).s ^ 4 = (monoSp F).s := by
      rw [(monoSp F).s_pow_mod]
      norm_num
    exact this.symm
  rw [h4]
  exact (Bsub F).pow_mem h 2

@[expose] def Rall : Subgroup ↥(SpI F) where
  carrier := {g | ∃ b ∈ Bsub F, ∃ k : ℕ, g = b * (monoSp F).s ^ k}
  mul_mem' := by
    rintro _ _ ⟨b, hb, k, rfl⟩ ⟨b', hb', l, rfl⟩
    refine ⟨b * ((monoSp F).s ^ k * b' * ((monoSp F).s ^ k)⁻¹),
      (Bsub F).mul_mem hb ((monoBase F).sigPow_mem k hb'), k + l, ?_⟩
    rw [pow_add]
    group
  one_mem' := ⟨1, (Bsub F).one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨b, hb, k, rfl⟩
    have hinv : ((monoSp F).s ^ k)⁻¹ = (monoSp F).s ^ (2 * k) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      have h3 : k + 2 * k = 3 * k := by ring
      rw [h3, pow_mul, (monoSp F).s_pow, one_pow]
    refine ⟨(monoSp F).s ^ (2 * k) * b⁻¹ * ((monoSp F).s ^ (2 * k))⁻¹,
      (monoBase F).sigPow_mem (2 * k) ((Bsub F).inv_mem hb), 2 * k, ?_⟩
    rw [_root_.mul_inv_rev, hinv]
    group

theorem card_Rall : Nat.card ↥(Rall F) = 3 * Nat.card ↥(Bsub F) := by
  let φ : ↥(Bsub F) × Fin 3 → ↥(Rall F) := fun p =>
    ⟨p.1 * (monoSp F).s ^ (p.2 : ℕ), p.1, p.1.2, p.2, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨b, k⟩ ⟨b', l⟩ h
      have h' : (b : ↥(SpI F)) * (monoSp F).s ^ (k : ℕ) = b' * (monoSp F).s ^ (l : ℕ) :=
        congrArg Subtype.val h
      have hk : (monoSp F).s ^ (k : ℕ) * ((monoSp F).s ^ (l : ℕ))⁻¹ ∈ Bsub F := by
        have e : (monoSp F).s ^ (k : ℕ) * ((monoSp F).s ^ (l : ℕ))⁻¹ =
            (b : ↥(SpI F))⁻¹ * b' := by
          calc (monoSp F).s ^ (k : ℕ) * ((monoSp F).s ^ (l : ℕ))⁻¹
              = (b : ↥(SpI F))⁻¹ * ((b : ↥(SpI F)) * (monoSp F).s ^ (k : ℕ)) *
                  ((monoSp F).s ^ (l : ℕ))⁻¹ := by group
            _ = (b : ↥(SpI F))⁻¹ * (b' * (monoSp F).s ^ (l : ℕ)) *
                  ((monoSp F).s ^ (l : ℕ))⁻¹ := by rw [h']
            _ = (b : ↥(SpI F))⁻¹ * b' := by group
        rw [e]
        exact (Bsub F).mul_mem ((Bsub F).inv_mem b.2) b'.2
      have hkl : k = l := by
        rw [(monoSp F).s_pow_mul_inv] at hk
        have hcases : ((k : ℕ) + 2 * (l : ℕ)) % 3 = 0 ∨ ((k : ℕ) + 2 * (l : ℕ)) % 3 = 1 ∨
            ((k : ℕ) + 2 * (l : ℕ)) % 3 = 2 := by omega
        rcases hcases with h0 | h1 | h2
        · apply Fin.ext
          omega
        · rw [h1, pow_one] at hk
          exact absurd hk (s_not_mem_Bsub F)
        · rw [h2] at hk
          exact absurd hk (s_sq_not_mem_Bsub F)
      subst hkl
      have : b = b' := Subtype.ext (mul_right_cancel h')
      rw [this]
    · rintro ⟨g, b, hb, k, rfl⟩
      refine ⟨(⟨b, hb⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show b * (monoSp F).s ^ (k % 3) = b * (monoSp F).s ^ k
      rw [← (monoSp F).s_pow_mod]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod]
  simp [mul_comm]

end Rall

section Sylow

variable (F : Type) [Field F] [Finite F] [CharP F 2]

theorem factorization_statedSp_tc :
    (Nat.card (CFSG.Open.StatedSp 3 F)).factorization 3 =
      3 * padicValNat 3 (tc (Nat.card F)) + 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F 2
  have hQ : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hQ2 : 2 ≤ Nat.card F := by
    rw [hQ]
    exact Nat.le_self_pow n.ne_zero 2
  have h3 : ¬ 3 ∣ Nat.card F := by
    rw [hQ]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  by_cases h : 3 ∣ Nat.card F - 1
  · have hN : Nat.card F % 3 = 1 := by omega
    rw [K421RProof.factorization_statedSp_three hN, tc, if_pos h]
  · have hN : Nat.card F % 3 = 2 := by omega
    rw [K421SpValProof.factorization_statedSp_three_of_two hN, tc, if_neg h]

theorem factorization_SpI :
    (Nat.card ↥(SpI F)).factorization 3 = 3 * padicValNat 3 (tc (Nat.card F)) + 1 := by
  rw [Nat.card_congr (spIEquiv F).toEquiv, factorization_statedSp_tc]

theorem factorization_Rall :
    (Nat.card ↥(Rall F)).factorization 3 = 3 * padicValNat 3 (tc (Nat.card F)) + 1 := by
  rw [card_Rall, card_Bsub, card_Tall]
  have hne : tc (Nat.card F) ≠ 0 := by
    intro h0
    have := card_Tall (F := F)
    rw [h0] at this
    exact Nat.card_pos.ne' this
  rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 3 hne), Nat.factorization_pow]
  simp [Nat.factorization_def _ Nat.prime_three, padicValNat_self]
  ring

theorem exists_sylow_le_Rall : ∃ P : Sylow 3 ↥(SpI F), (P : Subgroup ↥(SpI F)) ≤ Rall F := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P0⟩ : Nonempty (Sylow 3 ↥(Rall F)) := inferInstance
  have hcard : Nat.card ((P0 : Subgroup ↥(Rall F)).map (Rall F).subtype) =
      3 ^ (Nat.card ↥(SpI F)).factorization 3 := by
    rw [Subgroup.card_map_of_injective (Rall F).subtype_injective, Sylow.card_eq_multiplicity,
      factorization_Rall, factorization_SpI]
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  exact Subgroup.map_subtype_le _

theorem hconj_sp {E : Subgroup ↥(SpI F)} (hE : IsElemAbelian 3 E) :
    ∃ g : ↥(SpI F), E.map (MulAut.conj g).toMonoidHom ≤ (monoSp F).A0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_sylow_le_Rall F
  have hp : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨Q, hEQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(SpI F) Q P
  have hQP : (Q : Subgroup ↥(SpI F)).map (MulAut.conj g).toMonoidHom = (P : Subgroup ↥(SpI F)) := by
    rw [← sylow_smul_coe, hg]
  have hE1 : IsElemAbelian 3 (E.map (MulAut.conj g).toMonoidHom) :=
    K21bTransProof.isElemAbelian_map_inj (MulAut.conj g).injective hE
  have hE1R : ∀ e ∈ E.map (MulAut.conj g).toMonoidHom, ∃ b ∈ (monoBase F).B, ∃ k : ℕ,
      e = b * (monoSp F).s ^ k := by
    intro e he
    have : e ∈ Rall F := hP (hQP ▸ Subgroup.map_mono hEQ he)
    exact this
  obtain ⟨g', hg'⟩ := (monoBase F).exists_conj_le_A0 hE1 hE1R
  refine ⟨g' * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have := hg' (Subgroup.mem_map.mpr ⟨(MulAut.conj g) z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩)
  have h1 : (MulAut.conj (g' * g)) z = (MulAut.conj g') ((MulAut.conj g) z) := by
    simp [MulAut.conj_apply, mul_assoc]
  show (MulAut.conj (g' * g)) z ∈ (monoSp F).A0
  rw [h1]
  exact this

end Sylow

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
