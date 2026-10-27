module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem normalizer_le_of_normalizer_le [Fact p.Prime] {S S' : Sylow p M}
    (hS : normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M) :
    normalizer (((S' : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M : Type _) S S'
  have h1 : (S : Subgroup M).map (MulAut.conj m) = (S' : Subgroup M) := by
    have h := Sylow.coe_subgroup_smul (g := m) (P := S)
    rw [hm] at h
    exact h.symm
  have h2 : ((S' : Subgroup M).map M.subtype : Subgroup G)
      = ((S : Subgroup M).map M.subtype).map (MulAut.conj (m : G)) := by
    rw [← h1, map_subtype_map_conj]
  rw [h2, normalizer_map_conj]
  exact (Subgroup.map_mono hS).trans (map_conj_eq_self m.2).le

theorem normalizer_map_subtype_le_iff (hp : p.Prime) (S S' : Sylow p M) :
    normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M ↔
      normalizer (((S' : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M :=
  have : Fact p.Prime := ⟨hp⟩
  ⟨normalizer_le_of_normalizer_le, normalizer_le_of_normalizer_le⟩

theorem normalizer_le_of_normalizer_le_of_card_eq (hp : p.Prime) {P Q : Subgroup G}
    (hP : P ≤ M) (hPcard : Nat.card P = p ^ (Nat.card M).factorization p)
    (hQ : Q ≤ M) (hQcard : Nat.card Q = p ^ (Nat.card M).factorization p)
    (hPN : normalizer (P : Set G) ≤ M) : normalizer (Q : Set G) ≤ M := by
  obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hp (P := P)).2 ⟨hP, hPcard⟩
  obtain ⟨T, hT⟩ := (exists_sylow_map_subtype_eq_iff hp (P := Q)).2 ⟨hQ, hQcard⟩
  rw [← hT]
  exact (normalizer_map_subtype_le_iff hp S T).1 (by rw [hS]; exact hPN)

theorem sigmaPrimes_subset_conj_smul (M : Subgroup G) (g : G) :
    sigmaPrimes M ⊆ sigmaPrimes (MulAut.conj g • M) := by
  intro p hpmem
  have hp : p.Prime := prime_of_mem_sigmaPrimes hpmem
  have hinj : Function.Injective ((MulAut.conj g : MulAut G) : G →* G) :=
    (MulAut.conj g).injective
  rw [conj_smul_eq_map_conj]
  have hcard : Nat.card (M.map ((MulAut.conj g : MulAut G) : G →* G)) = Nat.card M :=
    Subgroup.card_map_of_injective hinj
  rw [mem_sigmaPrimes_iff_exists_subgroup hp] at hpmem ⊢
  obtain ⟨hd, P, hPle, hPcard, hPN⟩ := hpmem
  refine ⟨by rw [hcard]; exact hd, P.map ((MulAut.conj g : MulAut G) : G →* G),
    Subgroup.map_mono hPle, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hcard]; exact hPcard
  · rw [normalizer_map_conj]; exact Subgroup.map_mono hPN

theorem sigmaPrimes_conj_smul (M : Subgroup G) (g : G) :
    sigmaPrimes (MulAut.conj g • M) = sigmaPrimes M := by
  refine le_antisymm ?_ (sigmaPrimes_subset_conj_smul M g)
  have h := sigmaPrimes_subset_conj_smul (MulAut.conj g • M) g⁻¹
  rwa [map_inv MulAut.conj g, inv_smul_smul] at h

omit [Finite G] in
theorem coe_conj_inv_smul (M : Subgroup G) (g : G) :
    ((MulAut.conj g⁻¹ • M : Subgroup G) : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G) := by
  rw [conj_smul_eq_map_conj]
  ext x
  simp [MulAut.conj, mul_assoc]

theorem sigmaPrimes_eq_of_coe_eq_conj_image {N : Subgroup G} {g : G}
    (h : (N : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G)) : sigmaPrimes N = sigmaPrimes M := by
  have hN : N = MulAut.conj g⁻¹ • M := SetLike.coe_injective (by rw [h, coe_conj_inv_smul])
  rw [hN, sigmaPrimes_conj_smul]

end

end CFSG.FeitThompson
