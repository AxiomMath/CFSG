module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcAssembly
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitBasic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroup

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

structure InnerHeisCfg {P : Type} [Group P] (x g y : P) (J : Subgroup P) : Prop where
  comm : g * y * g⁻¹ * y⁻¹ = x
  order : orderOf x = 3
  comp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set P)) J
  mem : x ∈ J
  ord : (Nat.card J).factorization 3 = 3
  centralizes : ∀ L : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({x} : Set P)) L →
    ∀ l ∈ L, g * l = l * g ∧ y * l = l * y

theorem innerHeisCfg_of_coreCfg {P : Type} [Group P] (hZ : Subgroup.center P = ⊥) {g y x : P}
    {J : Subgroup P} (c : CoreCfg (MulAut.conj g) (MulAut.conj y) x J) : InnerHeisCfg x g y J := by
  have hinj : Function.Injective (MulAut.conj : P →* MulAut P) := conj_injective_of_center_bot hZ
  refine ⟨?_, c.order, c.comp, c.mem, c.ord, fun L hL l hl => ?_⟩
  · apply hinj
    simp only [map_mul, map_inv]
    exact c.comm
  · obtain ⟨h1, h2⟩ := c.centralizes L hL l hl
    rw [MulAut.conj_apply] at h1 h2
    refine ⟨?_, ?_⟩
    · calc g * l = (g * l * g⁻¹) * g := by group
        _ = l * g := by rw [h1]
    · calc y * l = (y * l * y⁻¹) * y := by group
        _ = l * y := by rw [h2]

set_option linter.unusedSectionVars false

theorem nonD4LieContraOnF4TwoOdd_of_model
    (h : ∀ n : ℕ, Odd n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      ∀ (x g y : ↥(adjointGroup Tag.F4 F)) (J : Subgroup ↥(adjointGroup Tag.F4 F)),
        ¬ InnerHeisCfg x g y J) :
    NonD4LieContraOnF4TwoOdd := by
  intro X _ _ K Q₁ Q J t q c r hv hr2 hrodd he _
  classical
  obtain ⟨x, Q', J', hcfg⟩ := c.exists_sCfg
  obtain ⟨e0⟩ := he
  obtain ⟨F, _, _, hF, -, ⟨eF⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 r hv
  set P := ↥(adjointGroup Tag.F4 F)
  let eS : (↥K ⧸ Subgroup.center ↥K) ≃* P := e0.trans eF
  obtain ⟨a, b, J'', hcore⟩ := hcfg.coreCfg_of_mulEquiv eS
  have hZ : Subgroup.center P = ⊥ := center_adjointGroup_eq_bot
  have hcyc : IsCyclic (Outer P) := CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isCyclic_outer_F4
  have hle := commutator_le_inner_of_isCyclic hcyc
  obtain ⟨g, rfl⟩ : ∃ g : P, MulAut.conj g = a := by
    obtain ⟨g, hg⟩ := hle hcore.a_mem
    exact ⟨g, hg⟩
  obtain ⟨y, rfl⟩ : ∃ y : P, MulAut.conj y = b := by
    obtain ⟨y, hy⟩ := hle hcore.b_mem
    exact ⟨y, hy⟩
  have hcard : Nat.card F = 2 ^ r.exponent := by
    rw [hF, TauCeti.PrimePower.card_def, hr2]
  exact h r.exponent hrodd F hcard (eS x) g y J'' (innerHeisCfg_of_coreCfg hZ hcore)

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
