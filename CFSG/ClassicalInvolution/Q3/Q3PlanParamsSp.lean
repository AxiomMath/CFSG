module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortSp
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open CFSG.Open (IsSubnormal)
open CFSG.ClassicalInvolution.ModelFacts (exists_mul_of_commute exists_mul_eq_stdInv stdInv
  nonempty_mulEquiv_longRootGroup_sp nonempty_mulEquiv_complGroup_sp comm_of_mem_longRootGroup
  comm_of_mem_complGroup subsingleton_statedSp_zero open_isQuasisimple two_ne_zero_galoisField)
open scoped MatrixGroups

section Sp

variable {F : Type} [Field F] {n : ℕ}

theorem sp_commute_of_isSubnormal (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) {z : StatedSp n F}
    (hz : z * z = 1) {N : Subgroup (StatedSp n F)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({z} : Set (StatedSp n F))))
    (hsolv : Group.IsSolvable N) : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  obtain ⟨S, g, hSg⟩ := exists_mul_eq_stdInv h2 hz
  have hzg : z = g * stdInv F S * g⁻¹ := eq_mul_inv_of_mul_eq hSg
  obtain ⟨eL⟩ := nonempty_mulEquiv_longRootGroup_sp h2 hzg
  obtain ⟨eC⟩ := nonempty_mulEquiv_complGroup_sp h2 hzg
  have hNC : N ≤ Subgroup.centralizer ({z} : Set (StatedSp n F)) :=
    CFSG.ClassicalInvolution.isSubnormal_le hNs
  have key : ∀ (A : Subgroup (StatedSp n F)) (k : ℕ) (e : StatedSp k F ≃* A),
      A ≤ Subgroup.centralizer ({z} : Set (StatedSp n F)) →
      (∀ c ∈ Subgroup.centralizer ({z} : Set (StatedSp n F)), ∀ x ∈ A, c * x * c⁻¹ ∈ A) →
      ∀ x ∈ N, ∀ a ∈ A, x * a = a * x := by
    intro A k e hAC hAn x hx a ha
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (StatedSp 0 F) := subsingleton_statedSp_zero
      obtain ⟨u, hu⟩ := e.surjective ⟨a, ha⟩
      have hu1 : u = 1 := Subsingleton.elim _ _
      rw [hu1, map_one] at hu
      have ha1 : a = 1 := (congrArg Subtype.val hu).symm
      rw [ha1, mul_one, one_mul]
    · have hq : CFSG.Open.IsQuasisimple ↥A :=
        CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
          (open_isQuasisimple (CFSG.LieType.Universal.Symplectic.isQuasisimple k F hk
            (Or.inl (Or.inr h4))))
      exact commute_of_isSubnormal_of_isSolvable hq hAC (le_normalizer_of_forall_conj_mem hAn)
        hNs hsolv x hx a ha
  have hL := key (longRootGroup z) S.card eL
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroup h2 hz hx))
    (fun c hc x hx => conj_mem_longRootGroup (Subgroup.mem_centralizer_singleton_iff.mp hc) hx)
  have hC := key (complGroup z) (Sᶜ).card eC
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_complGroup h2 hz hx))
    (fun c hc x hx => CFSG.ClassicalInvolution.Balance.conj_mem_complGroup'
      (Subgroup.mem_centralizer_singleton_iff.mp hc) hx)
  intro a ha b hb
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    exists_mul_of_commute h2 hz (Subgroup.mem_centralizer_singleton_iff.mp (hNC ha))
  have hbx : b * x = x * b := hL b hb x hx
  have hby : b * y = y * b := hC b hb y hy
  calc x * y * b = x * (y * b) := by group
    _ = x * (b * y) := by rw [hby]
    _ = (x * b) * y := by group
    _ = (b * x) * y := by rw [hbx]
    _ = b * (x * y) := by group

end Sp

theorem classicalMemberParameters3At_PSp : ClassicalMemberParameters3At .PSp := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  have he : 1 ≤ e := hadm.2.1
  have h5 : 5 ≤ r ^ e := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have h4 : 4 ≤ Nat.card (GaloisField r e) := by
    rw [GaloisField.card r e (by omega)]
    omega
  have h2 : (2 : GaloisField r e) ≠ 0 := two_ne_zero_galoisField e hr2
  have : Finite (modelUniv .PSp n r e hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr trivial hadm
  refine false_of_isClassicalMember3_of_oddGenerated ψ hψ hker ?_ h
  intro w hw N _ hNs hsolv _
  exact derivedSeries_two_eq_bot_of_commute (sp_commute_of_isSubnormal h4 h2 hw hNs hsolv)

end CFSG.ClassicalInvolution.Q3
