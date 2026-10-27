module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

theorem le_planeClosure_of_invariant_coprime
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {E : Subgroup (MulAut G)}
    (hE : CFSG.Open.IsElemAbelian p E)
    (hcard : p ^ 2 ≤ Nat.card E)
    {Q : Subgroup G}
    (hEQ : ∀ e ∈ E, Q.map e.toMonoidHom = Q)
    (hcop : ¬ p ∣ Nat.card Q) :
    Q ≤ planeClosure E := by
  have : CFSG.IsElementaryAbelian p E := hE.isElementaryAbelian
  let ρ : E →* MulAut Q :=
    { toFun := fun e => ((e : MulAut G).subgroupMap Q).trans
        (MulEquiv.subgroupCongr (hEQ e e.2))
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  let : MulDistribMulAction E Q := MulDistribMulAction.compHom Q ρ
  have hsmul : ∀ (e : E) (x : Q), ((e • x : Q) : G) = (e : MulAut G) (x : G) := by
    intro e x
    rfl
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation
    (p := p) (A := E) (H := Q) hcard hcop
  have hle : (⨆ (a : E) (_ : a ≠ 1),
      fixedPointSubgroup (Subgroup.zpowers a) Q) ≤ (planeClosure E).comap Q.subtype := by
    refine iSup₂_le fun a ha => fun x hx => ?_
    rw [Subgroup.mem_comap]
    have hfix : a • x = x :=
      (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).mp hx
    have hfixG : (a : MulAut G) (x : G) = x := by
      have h := congrArg Subtype.val hfix
      rw [hsmul] at h
      exact h
    exact mem_planeClosure_of_fixed a.2 (fun h1 => ha (Subtype.ext h1)) hfixG
  rw [hgen] at hle
  intro x hx
  have hthis := hle (Subgroup.mem_top (⟨x, hx⟩ : Q))
  rw [Subgroup.mem_comap] at hthis
  exact hthis

end CFSG.LieType.SeitzGeneration
