module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerInvariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddModule

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

structure OddAbelianSetting (G N A : Subgroup (V ≃ₗ[k] V)) : Prop where
  N_le : N ≤ G
  N_normal : (N.subgroupOf G).Normal
  N_abelian : ∀ x y : N, x * y = y * x
  N_odd : Odd (Nat.card N)
  A_le : A ≤ G
  A_elem : CFSG.IsElementaryAbelian 2 A
  A_ne : A ≠ ⊥
  offender : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A
  strict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
    weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A
  comm_ne : ⁅N, A⁆ ≠ ⊥

structure ThreePlane (G N A : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V) : Prop where
  card_k : Nat.card k = 2
  card_A : Nat.card A = 2
  card_L : Nat.card ↥(⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) = 3
  L_le_N : ⁅N, A⁆ ≤ N
  L_normal_N : ((⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)).subgroupOf N).Normal
  N_normal_G : (N.subgroupOf G).Normal
  I_eq : I = commGL ⁅N, A⁆ ⊤
  inv_A : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I
  inv_N : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) N I
  finrank_I : Module.finrank k ↥I = 2
  card_I : Nat.card ↥I = 4
  action : ∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I,
    Function.Bijective (resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I hW)
  V_eq : I ⊔ fixGL A = ⊤
  N_eq : N = (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) ⊔ (N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V)))
  disjoint : Disjoint (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V))
    (N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V)))
  cent_eq : N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V)) =
    N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) I
  I_eq' : I = commGL (⁅N, A⁆ ⊔ A) ⊤
  weight_eq : weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} (h : OddAbelianSetting G N A)

private instance instFiniteGL : Finite (V ≃ₗ[k] V) := finite_linearEquiv

include h

omit [CharP k 2] [Finite V] in
theorem A_le_normalizer_N : A ≤ Subgroup.normalizer (N : Set (V ≃ₗ[k] V)) :=
  h.A_le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.N_le).1 h.N_normal)

omit [CharP k 2] in
theorem coprime_AN : Nat.Coprime (Nat.card A) (Nat.card N) := by
  have := h.A_elem
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.IsElementaryAbelian.isPGroup 2 A)
  rw [hn]
  exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 h.N_odd)

omit [CharP k 2] [Finite V] in
theorem L_le_N : ⁅N, A⁆ ≤ N := commutator_le_left h.A_le_normalizer_N

omit [CharP k 2] [Finite V] in
theorem A_le_normalizer_L :
    A ≤ Subgroup.normalizer ((⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) :=
  le_normalizer_commutator h.A_le_normalizer_N

omit [CharP k 2] in
theorem comm_comm : ⁅⁅N, A⁆, A⁆ = ⁅N, A⁆ :=
  commutator_commutator_eq N A h.A_le_normalizer_N h.N_abelian h.coprime_AN

omit [CharP k 2] [Finite V] in
theorem L_odd : Odd (Nat.card ↥(⁅N, A⁆ : Subgroup (V ≃ₗ[k] V))) :=
  Odd.of_dvd_nat h.N_odd (Subgroup.card_dvd_of_le h.L_le_N)

omit [CharP k 2] [Finite V] in
theorem hmax : ∀ B : Subgroup (V ≃ₗ[k] V), B ≤ A →
    weight (MonoidHom.id (V ≃ₗ[k] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A := by
  intro B hB
  rcases hB.lt_or_eq with hlt | heq
  · by_cases hbot : B = ⊥
    · rw [hbot, weight_bot]; exact h.offender
    · exact (h.strict B (bot_lt_iff_ne_bot.2 hbot) hlt).le
  · rw [heq]

theorem exists_module : ∃ I : Submodule k V,
    IsGoodModule (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ I ∧ I ⊓ fixGL ⁅N, A⁆ = ⊥ ∧
      Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I := by
  have hnt : ¬ (⊤ : Submodule k V) ≤ fixGL ⁅N, A⁆ := by
    intro hle
    apply h.comm_ne
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro v
    exact hle Submodule.mem_top l hl
  obtain ⟨I, hI, hI0⟩ := exists_good_oddOrder (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ h.L_odd hnt
  refine ⟨I, hI, hI0, ?_⟩
  exact bestOffender_invariance_strict (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ A h.A_le_normalizer_L
    h.A_elem h.comm_comm (noPQuotient_two_of_odd h.L_odd) (centralPChief_two_of_odd h.L_odd)
    h.hmax h.strict hI.inv hI.comm hI.irr

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
