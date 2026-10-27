module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYDih

public section

namespace CFSG.EvenSporadicStandard.Fin76b.S16

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

theorem f1_dihedral_of_check {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    {τ0T ρT τT : Table} (h : f1Check n sift τ0T ρT τT = true) :
    ∃ a b : Equiv.Perm (Fin n), a ∈ P ∧ b ∈ P ∧ a * tp n τ0T = tp n τ0T * a ∧
      b * tp n τ0T = tp n τ0T * b ∧ a ^ 8 = 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧
      Nat.card ↥(closure ({a, b} : Set (Equiv.Perm (Fin n)))) = 16 := by
  have hn : n < 2 ^ 32 := hD.lt
  simp only [f1Check, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    and_assoc] at h
  obtain ⟨hp0, hpρ, hpτ, hsρ, hsτ, hcρ, hcτ, h8, h4, hτ2, hρinv, hτρ, hnot⟩ := h
  have R0 : Rep n τ0T (tp n τ0T) := rep_tp hp0
  have Rρ : Rep n ρT (tp n ρT) := rep_tp hpρ
  have Rτ : Rep n τT (tp n τT) := rep_tp hpτ
  have Rρi : Rep n (invT n ρT) (tp n ρT)⁻¹ := rep_invT Rρ hρinv
  have hτ2' : tp n τT * tp n τT = 1 := by
    have := sq_eq_one_of_invoOK Rτ hτ2
    rwa [pow_two] at this
  have hτinv : (tp n τT)⁻¹ = tp n τT := inv_eq_of_mul_eq_one_right hτ2'
  have ha8 : tp n ρT ^ 8 = 1 := (tblEq_iff_eq (Rep.powT hn Rρ 8) (Rep.idT hn)).1 h8
  have ha4 : tp n ρT ^ 4 ≠ 1 := fun hh => by
    have := (tblEq_iff_eq (Rep.powT hn Rρ 4) (Rep.idT hn)).2 hh
    rw [this] at h4
    exact Bool.noConfusion h4
  have hba : tp n τT * tp n ρT * (tp n τT)⁻¹ = (tp n ρT)⁻¹ := by
    rw [hτinv]
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rτ Rρ) Rτ) Rρi).1 hτρ
  have hb : ∀ i : ℕ, tp n τT ≠ tp n ρT ^ i := by
    intro i hi
    have hmod : tp n ρT ^ i = tp n ρT ^ (i % 8) := by
      conv_lhs => rw [← Nat.mod_add_div i 8, pow_add, pow_mul, ha8, one_pow, mul_one]
    have h1 := hnot (i % 8) (Nat.mod_lt _ (by norm_num))
    have h2 : tblEq n τT (powT n (i % 8) ρT) = true :=
      (tblEq_iff_eq Rτ (Rep.powT hn Rρ (i % 8))).2 (hi.trans hmod)
    rw [h2] at h1
    exact Bool.noConfusion h1
  exact ⟨tp n ρT, tp n τT, (hD.sift _ _ Rρ).1 hsρ, (hD.sift _ _ Rτ).1 hsτ,
    (commTT_iff Rρ R0).1 hcρ, (commTT_iff Rτ R0).1 hcτ, ha8, hτ2', hba,
    dihedral8_of_rel ha8 ha4 hτ2' hba hb⟩

theorem hall_of_rows {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {u τ0 : Equiv.Perm (Fin n)}
    {rows : List ClassRow} (hrows : ∀ r ∈ rows, (r.outer = true ↔ tp n r.rep ∉ P))
    (hcov : ∀ t ∈ P ⊔ zpowers u, orderOf t = 2 →
      ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹)
    (honly : ∀ r ∈ rows, r.outer = true → tp n r.rep = τ0) :
    ∀ ρ ∈ P ⊔ zpowers u, ρ * ρ = 1 → ρ ∉ P → ∃ g ∈ P, ρ = g * τ0 * g⁻¹ := by
  intro ρ hρR hρ2 hρP
  have hρ1 : ρ ≠ 1 := fun h => hρP (h ▸ one_mem _)
  have hord : orderOf ρ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hρ2) hρ1
  obtain ⟨r, hr, g, hg, hρg⟩ := hcov ρ hρR hord
  have hrep : tp n r.rep ∉ P := fun hmem => hρP (by
    rw [hρg]
    exact mul_mem (mul_mem hg hmem) (inv_mem hg))
  have hout : r.outer = true := (hrows r hr).2 hrep
  exact ⟨g, hg, by rw [hρg, honly r hr hout]⟩

end CFSG.EvenSporadicStandard.Fin76b.S16
