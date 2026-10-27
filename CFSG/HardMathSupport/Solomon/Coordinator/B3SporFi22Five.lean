module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestFi22

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Monster.B.Fischer

section Lines

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem gLAPPrimeCoreOf_inf_eq_bot_of_lines (hp : p.Prime) {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*} (line : ι → G)
    (hlines : ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j))
    (hline : ∀ j, GLAPPrimeCoreOf p (Subgroup.centralizer ({line j} : Set G) ⊓ P) = ⊥) :
    ∀ y ∈ P, orderOf y = p → GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G) ⊓ P) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  intro y hyP hyo
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full hQP hQ hyP hyo
  have hto : orderOf (g⁻¹ * y * g) = p := by
    have := (MulAut.conj g⁻¹ : G ≃* G).orderOf_eq y
    simpa [MulAut.conj_apply, hyo] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers (g⁻¹ * y * g)) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have ht : GLAPPrimeCoreOf p
      (Subgroup.centralizer ({g⁻¹ * y * g} : Set G) ⊓ P) = ⊥ := by
    rw [centralizer_singleton_eq_of_zpowers hj]
    exact hline j
  have hk : ∀ q ∈ P, g * q * g⁻¹ ∈ P := fun q hq =>
    P.mul_mem (P.mul_mem hgP hq) (P.inv_mem hgP)
  have hk' : ∀ q ∈ P, g⁻¹ * q * g ∈ P := fun q hq =>
    P.mul_mem (P.mul_mem (P.inv_mem hgP) hq) hgP
  have hy : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [hy, ← map_conj_centralizer_inf hk hk' (g⁻¹ * y * g),
    ← map_glaPPrimeCoreOf_of_injective p _ (MulAut.conj g : G ≃* G).injective, ht,
    Subgroup.map_bot]

theorem oPrimeCoreTrivialAt_subgroup_of_inf (P : Subgroup G)
    (h : ∀ y ∈ P, orderOf y = p → GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G) ⊓ P) = ⊥) :
    OPrimeCoreTrivialAt p ↥P := by
  intro x hx
  have hy := h x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
  have hmap := map_glaPPrimeCoreOf_of_injective p P.subtype P.subtype_injective
    (Subgroup.centralizer ({x} : Set ↥P))
  rw [map_centralizer_subtype, hy] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hmap

theorem oPrimeCoreTrivialAt_subgroup_of_mulEquiv {G₀ G₁ : Type*} [Group G₀] [Group G₁]
    {H : Subgroup G₀} {H' : Subgroup G₁} (e : ↥H ≃* ↥H') (h : OPrimeCoreTrivialAt p ↥H') :
    OPrimeCoreTrivialAt p ↥H :=
  OPrimeCoreTrivialAt.of_mulEquiv e h

end Lines


theorem gLAPPrimeCoreOf_inf_fi22P_eq_bot_five :
    ∀ y ∈ fi22P, orderOf y = 5 →
      GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P) = ⊥ := by
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlines, -⟩, -⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact gLAPPrimeCoreOf_inf_eq_bot_of_lines Nat.prime_five hQP
    (card_eq_of_sylow_subgroupOf hQP hQsyl) fi22FiveLine (lines_of_eq hlines)
    gLAPPrimeCoreOf_fi22FiveLine_eq_bot

theorem oPrimeCoreTrivialAt_Fi22J_five : OPrimeCoreTrivialAt 5 CFSG.Sporadic.Fi22.J :=
  oPrimeCoreTrivialAt_subgroup_of_mulEquiv (CFSG.Sporadic.Fi22.fi22EquivJ.symm.trans fi22PermEquiv)
    (oPrimeCoreTrivialAt_subgroup_of_inf fi22P gLAPPrimeCoreOf_inf_fi22P_eq_bot_five)

end CFSG.HardMathSupport.Solomon.Coordinator
