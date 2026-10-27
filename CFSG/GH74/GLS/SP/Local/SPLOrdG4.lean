module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG3
public import CFSG.GH74.GLS.SP.Local.SPLOrdWr
public import CFSG.GH74.GLS.SP.Local.SPLOrdG2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.ShultStronglyClosedTI.InvolutionCounting
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

theorem card_subtype_comp {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (P : B → Prop) :
    Nat.card {a : A // P (f a)} = Nat.card f.ker * Nat.card {b : B // P b} := by
  classical
  have : Finite B := Finite.of_surjective f hf
  have : Fintype A := Fintype.ofFinite A
  have : Fintype B := Fintype.ofFinite B
  have hfib : ∀ b : B, Nat.card {a : A // f a = b} = Nat.card f.ker := by
    intro b
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf b)
  have h1 : Nat.card {a : A // P (f a)} = (Finset.univ.filter (fun a : A => P (f a))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : Nat.card {b : B // P b} = (Finset.univ.filter (fun b : B => P b)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, h2, Finset.card_eq_sum_card_fiberwise (f := f)
    (t := Finset.univ.filter (fun b : B => P b))
    (fun a ha => by simpa using (Finset.mem_filter.mp ha).2)]
  have h3 : ∀ b ∈ Finset.univ.filter (fun b : B => P b),
      ((Finset.univ.filter (fun a : A => P (f a))).filter (fun a => f a = b)).card =
        Nat.card f.ker := by
    intro b hb
    rw [← hfib b, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]; exact (Finset.mem_filter.mp hb).2
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, mul_comm]

section G4

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem rz_four (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    4 * thompsonPairCount D.t D.z D.z =
      Nat.card ↥D.K₁ * Nat.card {u : ↥D.K₁ // ∃ k : ℕ, Odd k ∧
        ((u : G) ^ k = 1 ∨ (u : G) ^ k = D.z)} := by
  have h := zside_count D.K₁ D.K₂ D.z D.t hs.comps.comm hs.comps.inf_eq hs.syl.z_inv
    (t_mul_t D hs) (z_comm_t D hs) (t_not_mem_K D hs) (t_conj_K₁ D hs) (t_conj_K₂ D hs)
  unfold thompsonPairCount
  rw [thompsonPairs_z_eq D hs hc]
  exact h

theorem odd_iff_diag (hs : SPLSetup D.toSPLNot0) (u : ↥D.K₁) :
    (∃ k : ℕ, Odd k ∧ ((u : G) ^ k = 1 ∨ (u : G) ^ k = D.z)) ↔
      Odd (orderOf (diagHom D hs u)) := by
  constructor
  · rintro ⟨k, hk, h⟩
    have hz : diagHom D hs ⟨D.z, z_mem_K₁ (D := D.toSPLNot0) hs⟩ = 1 := diagHom_z D hs
    have hpow : (diagHom D hs u) ^ k = 1 := by
      rw [← map_pow]
      rcases h with h | h
      · have : u ^ k = 1 := Subtype.ext (by simpa using h)
        rw [this, map_one]
      · have : u ^ k = ⟨D.z, z_mem_K₁ (D := D.toSPLNot0) hs⟩ := Subtype.ext (by simpa using h)
        rw [this, hz]
    exact hk.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · intro hodd
    refine ⟨orderOf (diagHom D hs u), hodd, ?_⟩
    have h1 : u ^ orderOf (diagHom D hs u) ∈ (diagHom D hs).ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have h2 := mem_zpowers_of_mem_ker_diagHom D hs h1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h2
    rcases zpow_z_cases D hs j with h3 | h3
    · left; rw [← Subgroup.coe_pow, ← hj, h3]
    · right; rw [← Subgroup.coe_pow, ← hj, h3]

theorem N_eq (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card {u : ↥D.K₁ // ∃ k : ℕ, Odd k ∧ ((u : G) ^ k = 1 ∨ (u : G) ^ k = D.z)} =
      2 * Nat.card {γ : ↥D.I // Odd (orderOf (γ : G))} := by
  have hrange : ∀ k : ↥D.K₁, diagHom D hs k ∈ D.I := by
    intro k
    rw [I_eq_diag D hs hc]; exact ⟨k, rfl⟩
  let Φ : ↥D.K₁ →* ↥D.I := (diagHom D hs).codRestrict D.I hrange
  have hΦ : Function.Surjective Φ := by
    intro γ
    have : (γ : G) ∈ (diagHom D hs).range := by rw [← I_eq_diag D hs hc]; exact γ.2
    obtain ⟨k, hk⟩ := this
    exact ⟨k, Subtype.ext hk⟩
  have hker : Φ.ker = (diagHom D hs).ker := MonoidHom.ker_codRestrict _ _ _
  have h := card_subtype_comp Φ hΦ (fun γ => Odd (orderOf (γ : G)))
  rw [hker, ker_diagHom D hs] at h
  have e : ∀ u : ↥D.K₁, (∃ k : ℕ, Odd k ∧ ((u : G) ^ k = 1 ∨ (u : G) ^ k = D.z)) ↔
      Odd (orderOf ((Φ u : ↥D.I) : G)) := fun u => odd_iff_diag D hs u
  have : Nat.card {u : ↥D.K₁ // ∃ k : ℕ, Odd k ∧ ((u : G) ^ k = 1 ∨ (u : G) ^ k = D.z)} =
      Nat.card {a : ↥D.K₁ // Odd (orderOf ((Φ a : ↥D.I) : G))} :=
    Nat.card_congr (Equiv.subtypeEquivRight e)
  rw [this]
  exact h

theorem rz_eq (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    thompsonPairCount D.t D.z D.z =
      Nat.card ↥D.I * Nat.card {γ : ↥D.I // Odd (orderOf (γ : G))} := by
  have h4 := rz_four D hs hc
  rw [N_eq D hs hc, ← card_K₁_eq D hs hc] at h4
  nlinarith [h4]

end G4

end CFSG.GH74.GLS.SP.Local
