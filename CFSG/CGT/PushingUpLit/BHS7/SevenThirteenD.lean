module

public import CFSG.CGT.PushingUpLit.BHS7.ModuleW
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {P T M V W Z : Subgroup Γ}

theorem commutator_pCoreOf_eq_bot (hT : IsSylowOf 2 T P) (hMP : M < P)
    (hMu : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ M) (hW : IsModuleW P T V W)
    (hPV : P ≤ Subgroup.normalizer (V : Set Γ)) (hZT : Z ≤ T)
    (hZn : T ≤ Subgroup.normalizer (Z : Set Γ))
    (hA : Z ⊓ pCoreOf 2 P ≤ Subgroup.centralizer (V : Set Γ)) (hZP : ¬ Z ≤ pCoreOf 2 P) :
    ⁅W, pCoreOf 2 P⁆ = ⊥ := by
  set K : Subgroup Γ := opResidual 2 P with hK
  set Q : Subgroup Γ := pCoreOf 2 P with hQ
  have hTpP : IsSylowTwoOf T P := isSylowTwoOf_of_isSylowOf hT
  have hQT : Q ≤ T := hTpP.pCoreOf_le
  have hQP : P ≤ Subgroup.normalizer (Q : Set Γ) := le_normalizer_pCoreOf_self P
  have hPC : P ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ) :
      Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      B6.le_normalizer_centralizer hPV hg⟩
  set N₂ : Subgroup Γ := stabTrivSub P Q (P ⊓ Subgroup.centralizer (V : Set Γ)) hPC with hN₂
  have hZN₂ : ∀ z ∈ Z, z ∈ N₂ := by
    intro z hz
    refine ⟨hT.1 (hZT hz), fun q hq => ?_⟩
    have hqT : q ∈ T := hQT hq
    have h1 : z * q * z⁻¹ * q⁻¹ ∈ Z := by
      have : q * z⁻¹ * q⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZn hqT) z⁻¹).mp (Z.inv_mem hz)
      have e : z * q * z⁻¹ * q⁻¹ = z * (q * z⁻¹ * q⁻¹) := by group
      rw [e]
      exact Z.mul_mem hz this
    have h2 : z * q * z⁻¹ * q⁻¹ ∈ Q := by
      have : z * q * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQP (hT.1 (hZT hz))) q).mp hq
      exact Q.mul_mem this (Q.inv_mem hq)
    have h3 := hA ⟨h1, h2⟩
    exact ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 P h2, h3⟩
  have hKN₂ : K ≤ N₂ := by
    by_contra hnot
    have := stabTrivSub_inf_le_pCoreOf hT hMP hMu hQP hPC hnot
    exact hZP fun z hz => this ⟨hZN₂ z hz, hZT hz⟩
  have hKQ : ⁅K, Q⁆ ≤ Subgroup.centralizer (V : Set Γ) := by
    rw [Subgroup.commutator_le]
    intro k hk q hq
    exact (hKN₂ hk).2 q hq |>.2
  have h1 : ⁅⁅K, Q⁆, W⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy w hw
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hKQ hy) w (hW.le_V hw)).symm
  have h2 : ⁅⁅Q, W⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Q W, eq_bot_iff, Subgroup.commutator_le]
    intro y hy k hk
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hW.pCore_comm_le hy).2 k hk).symm
  have h3 : ⁅⁅W, K⁆, Q⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := W) (H₂ := K) (H₃ := Q) h1 h2
  rwa [hW.comm_eq] at h3

omit [Finite Γ] in
theorem centralizer_inf_le_pCoreOf (hW : IsModuleW P T V W) :
    Subgroup.centralizer (W : Set Γ) ⊓ T ≤ pCoreOf 2 P := by
  intro x hx
  refine hW.cen_le x hx.2 fun w hw => ?_
  have h1 : x * w * x⁻¹ * w⁻¹ = 1 := by
    have := Subgroup.mem_centralizer_iff.mp hx.1 w hw
    calc x * w * x⁻¹ * w⁻¹ = (w * x) * x⁻¹ * w⁻¹ := by rw [this]
      _ = 1 := by group
  rw [h1]
  exact Subgroup.one_mem _

end CFSG.CGT.PushingUpLit.BHS7
