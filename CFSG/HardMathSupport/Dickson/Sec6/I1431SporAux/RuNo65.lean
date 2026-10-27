module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.RankThree.PartOne.KS.RuFiveCentralizers
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier
  CFSG.HardMathSupport.Solomon.Coordinator

theorem card_centralizer_inf_conj_eq {X : Type*} [Group X] {P : Subgroup X} {h : X} (hP : h ∈ P)
    (a : X) :
    Nat.card ↥(Subgroup.centralizer ({h⁻¹ * a * h} : Set X) ⊓ P) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set X) ⊓ P) := by
  have e : (Subgroup.centralizer ({h⁻¹ * a * h} : Set X) ⊓ P : Subgroup X) =
      (Subgroup.centralizer ({a} : Set X) ⊓ P).map (MulAut.conj h⁻¹).toMonoidHom := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨hg, hgP⟩
      refine ⟨h * g * h⁻¹, ⟨?_, P.mul_mem (P.mul_mem hP hgP) (P.inv_mem hP)⟩, by group⟩
      calc h * g * h⁻¹ * a = h * (g * (h⁻¹ * a * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * a * h) * g) * h⁻¹ := by rw [hg]
        _ = a * (h * g * h⁻¹) := by group
    · rintro ⟨y, ⟨hy, hyP⟩, rfl⟩
      refine ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hP) hyP) hP⟩
      calc h⁻¹ * y * h * (h⁻¹ * a * h) = h⁻¹ * (y * a) * h := by group
        _ = h⁻¹ * (a * y) * h := by rw [hy]
        _ = h⁻¹ * a * h * (h⁻¹ * y * h) := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]

section Ru


theorem noOrder65_ruP : NoOrder 65 ↥ruP := by
  intro g hg
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, ⟨hC1, hC1c⟩, -⟩ :=
    R3E_Ru_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine no_order_mul_of_lines (p := 5) (r := 13) hQP (card_eq_of_sylow_subgroupOf hQP hQsyl)
    ruFiveLine (lines_of_eq hlines) (fun j => ?_) g.2 (by
      rw [Subgroup.orderOf_coe]; exact hg)
  obtain ⟨hjP, hjconj⟩ := htrans j
  have hr : ruFiveRecordOf j = 0 ∨ ruFiveRecordOf j = 1 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hcard : Nat.card ↥(Subgroup.centralizer ({ruFiveLine j} : Set (Equiv.Perm (Fin 4060))) ⊓
      ruP) = Nat.card ↥(Subgroup.centralizer
        ({ruFiveLine (ruFiveRecordOf j)} : Set (Equiv.Perm (Fin 4060))) ⊓ ruP) := by
    have h := card_centralizer_inf_conj_eq (P := ruP) (h := (ruFiveTransporter j)⁻¹)
      (ruP.inv_mem hjP) (ruFiveLine (ruFiveRecordOf j))
    rw [inv_inv] at h
    rw [← hjconj]
    exact h
  rw [hcard]
  rcases hr with hr | hr
  · rw [hr, ← hC0, hC0c]
    norm_num
  · rw [hr, ← hC1, hC1c]
    norm_num

theorem noOrder65_Ru :
    NoOrder 65 NativeSporadic.Ru := fun g hg =>
  noOrder65_ruP (ruEquivP g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end Ru

end CFSG.HardMathSupport.Dickson.Sec6.I1431
