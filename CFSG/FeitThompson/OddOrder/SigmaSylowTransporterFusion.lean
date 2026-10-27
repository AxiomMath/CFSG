module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

omit [Finite G] in
theorem map_conj_map_conj (P : Subgroup G) (a b : G) :
    (P.map (MulAut.conj b : G →* G)).map (MulAut.conj a : G →* G)
      = P.map (MulAut.conj (a * b) : G →* G) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj, mul_assoc]

theorem mem_of_map_conj_inv_le (hp : p ∈ sigmaPrimes M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) {g : G}
    (h : P.map (MulAut.conj g⁻¹ : G →* G) ≤ M) : g ∈ M := by
  have hprime : p.Prime := prime_of_mem_sigmaPrimes hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hprime (P := P)).2 ⟨hPM, hPcard⟩
  have hcardQ : Nat.card (P.map (MulAut.conj g⁻¹ : G →* G)) = p ^ (Nat.card M).factorization p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]; exact hPcard
  obtain ⟨T, hT⟩ := (exists_sylow_map_subtype_eq_iff hprime
    (P := P.map (MulAut.conj g⁻¹ : G →* G))).2 ⟨h, hcardQ⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M : Type _) T S
  have h1 : (T : Subgroup M).map (MulAut.conj m) = (S : Subgroup M) := by
    have hh := Sylow.coe_subgroup_smul (g := m) (P := T)
    rw [hm] at hh
    exact hh.symm
  have h2 : (P.map (MulAut.conj g⁻¹ : G →* G)).map (MulAut.conj (m : G) : G →* G) = P := by
    rw [← hT, ← map_subtype_map_conj, h1, hS]
  rw [map_conj_map_conj] at h2
  have h3 : (m : G) * g⁻¹ ∈ normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 h2
  have h4 : (m : G) * g⁻¹ ∈ M := by
    refine ((mem_sigmaPrimes_iff_forall hprime).1 hp).2 S ?_
    rw [hS]; exact h3
  have hg : g⁻¹ ∈ M := by
    have := M.mul_mem (M.inv_mem m.2) h4
    simpa [← mul_assoc] using this
  simpa using M.inv_mem hg

theorem map_conj_inv_le_iff_mem (hp : p ∈ sigmaPrimes M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) {g : G} :
    P.map (MulAut.conj g⁻¹ : G →* G) ≤ M ↔ g ∈ M := by
  refine ⟨mem_of_map_conj_inv_le hp hPM hPcard, fun hg => ?_⟩
  rw [← map_conj_eq_self (M.inv_mem hg)]
  exact Subgroup.map_mono hPM

theorem mem_of_sylow_map_conj_inv_le (hp : p ∈ sigmaPrimes M) (S : Sylow p M) {g : G}
    (h : (((S : Subgroup M).map M.subtype : Subgroup G)).map (MulAut.conj g⁻¹ : G →* G) ≤ M) :
    g ∈ M := by
  have hprime : p.Prime := prime_of_mem_sigmaPrimes hp
  obtain ⟨hle, hcard⟩ := (exists_sylow_map_subtype_eq_iff hprime
    (P := ((S : Subgroup M).map M.subtype : Subgroup G))).1 ⟨S, rfl⟩
  exact mem_of_map_conj_inv_le hp hle hcard h

theorem mem_of_conj_image_subset (hp : p ∈ sigmaPrimes M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) {g : G}
    (h : (fun a => g⁻¹ * a * g) '' (P : Set G) ⊆ (M : Set G)) : g ∈ M := by
  refine mem_of_map_conj_inv_le hp hPM hPcard fun x hx => h ?_
  rw [← coe_conj_inv_smul, conj_smul_eq_map_conj]
  exact hx

end

end CFSG.FeitThompson
