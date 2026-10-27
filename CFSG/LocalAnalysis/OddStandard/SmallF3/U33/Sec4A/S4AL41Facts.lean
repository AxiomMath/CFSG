module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Defs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure L41Basic (t : G) (S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  S_eq : S = twoCore t ⊔ wreathGrp x₁ x₂ lam
  card_S : Nat.card S = 2 ^ 5 * Nat.card (twoCore t)
  normal_W : NormalIn (ctxW t x₁ x₂) S
  index_W : (ctxW t x₁ x₂).relIndex S = 2
  center_S : S ⊓ centralizer (S : Set G) = twoCore t ⊔ zpowers (x₁ * x₂)
  center_omega : ∀ g ∈ S ⊓ centralizer (S : Set G), g ^ 2 = 1 → g ∈ closure {t, (x₁ * x₂) ^ 2}
  deriv_S : ⁅S, S⁆ = ⁅wreathGrp x₁ x₂ lam, wreathGrp x₁ x₂ lam⁆
  omega_deriv : (x₁ * x₂) ^ 2 ∈ ⁅S, S⁆ ∧
    ∀ g ∈ ⁅S, S⁆, g * g = 1 → g = 1 ∨ g = (x₁ * x₂) ^ 2
  A_elem : CFSG.Open.IsElemAbelian 2 (ctxE t x₁ x₂) ∧ Nat.card (ctxE t x₁ x₂) = 8
  m2_S : ∀ E : Subgroup G, E ≤ S → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 8
  rank_S : ∀ Q : Subgroup G, Q ≤ S → ∃ s : Finset G, s.card ≤ 4 ∧ closure (s : Set G) = Q
  normal_elem_le : ∀ E : Subgroup G, NormalIn E S → CFSG.Open.IsElemAbelian 2 E →
    E ≤ ctxE t x₁ x₂
  invol_S : ∀ f ∈ S, f * f = 1 → f ∈ wreathGrp x₁ x₂ lam ∨ t * f ∈ wreathGrp x₁ x₂ lam
  norm_S_le : ∀ n ∈ normalizer (S : Set G), n ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)
  cent_A : centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  cent_W : centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  norm_A : invCent t ⊓ normalizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) =
    ctxW t x₁ x₂ ⊔ closure {rho, lam}
  norm_W : invCent t ⊓ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) =
    ctxW t x₁ x₂ ⊔ closure {rho, lam}
  sigma3 : Nonempty (↥(closure {rho, lam}) ≃* Equiv.Perm (Fin 3))

structure L41Fusion (t : G) (S : Subgroup G) (x₁ x₂ lam : G) : Prop where
  not_conj_z : ∀ g : G, g * t * g⁻¹ ≠ (x₁ * x₂) ^ 2
  not_conj_T : ∀ u ∈ wreathGrp x₁ x₂ lam, ∀ g : G, g * t * g⁻¹ ≠ u
  conj_tu : ∀ u ∈ wreathGrp x₁ x₂ lam, u * u = 1 → u ≠ 1 → ∃ g : G, g * t * g⁻¹ = t * u
  orbit_NS : conjIn (normalizer (S : Set G)) t = t • (zpowers ((x₁ * x₂) ^ 2) : Set G)
  card_P_le : Nat.card (twoCore t) ≤ 4
  tG_A : ∀ a ∈ ctxE t x₁ x₂, (∃ g : G, g * t * g⁻¹ = a) ↔ ∃ f ∈ fourGrp x₁ x₂, a = t * f
  zG_A : ∀ a ∈ ctxE t x₁ x₂, (∃ g : G, g * (x₁ * x₂) ^ 2 * g⁻¹ = a) ↔
    a ∈ fourGrp x₁ x₂ ∧ a ≠ 1

structure L41Normalizer (t : G) (S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  normal_F2 : NormalIn (fourGrp x₁ x₂) (l41N t x₁ x₂)
  quot_N : Sec4SectionIso (l41N t x₁ x₂) (ctxW t x₁ x₂) (Equiv.Perm (Fin 4))
  orbit_t : conjIn (l41N t x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)
  O2_eq : l41O2 t x₁ x₂ = l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  card_O2 : Nat.card (l41O2 t x₁ x₂) = 4 * Nat.card (ctxW t x₁ x₂)
  N_eq : l41N t x₁ x₂ = l41O2 t x₁ x₂ ⊔ closure {rho, lam}
  V_le : l41V S t x₁ x₂ ≤ l41N t x₁ x₂
  V_pGroup : IsPGroup 2 (l41V S t x₁ x₂)
  V_sylow : ¬ 2 ∣ (l41V S t x₁ x₂).relIndex (l41N t x₁ x₂)
  V_not_sylow : 2 ∣ (l41V S t x₁ x₂).index
  card_V : Nat.card (l41V S t x₁ x₂) = 8 * Nat.card (ctxW t x₁ x₂)
  cent_V_t : l41V S t x₁ x₂ ⊓ invCent t = S
  cent_V_A : l41V S t x₁ x₂ ⊓ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  quot_V : Sec4SectionIso (l41V S t x₁ x₂) (ctxW t x₁ x₂) (DihedralGroup 4)

@[expose] def L41E8Fact (t : G) (S : Subgroup G) (x₁ x₂ : G) : Prop :=
  ∃ E : Subgroup G, E ≤ l41O2 t x₁ x₂ ∧ NormalIn E (l41V S t x₁ x₂) ∧
    CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ E ⊓ ctxW t x₁ x₂ = fourGrp x₁ x₂ ∧
    ¬ E ≤ ctxW t x₁ x₂ ∧ (∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e) ∧
    ∀ e ∈ E, ∀ v ∈ l41V S t x₁ x₂, ⁅e, v⁆ ∈ fourGrp x₁ x₂

structure L41NbarFacts (t : G) (x₁ x₂ rho : G) : Prop where
  center_Nbar : {n | n ∈ l41N t x₁ x₂ ∧ ∀ m ∈ l41N t x₁ x₂, ⁅n, m⁆ ∈ fourGrp x₁ x₂} =
    ((zpowers t ⊔ fourGrp x₁ x₂ : Subgroup G) : Set G)
  cent_O2_rho : l41O2 t x₁ x₂ ⊓ centralizer ({rho} : Set G) = zpowers t
  cent_O2bar_rho : {q | q ∈ l41O2 t x₁ x₂ ∧ ⁅q, rho⁆ ∈ fourGrp x₁ x₂} =
    ((zpowers t ⊔ fourGrp x₁ x₂ : Subgroup G) : Set G)

structure L41RFacts (t : G) (S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  card_R : Nat.card (l41R t x₁ x₂ rho) = 2 ^ 6
  normal_R : NormalIn (l41R t x₁ x₂ rho) (l41N t x₁ x₂)
  t_not_mem : t ∉ l41R t x₁ x₂ rho
  O2_eq : l41O2 t x₁ x₂ = l41R t x₁ x₂ rho ⊔ zpowers t
  cent_rho : l41R t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = ⊥
  cent_t : l41R t x₁ x₂ rho ⊓ invCent t = baseGrp x₁ x₂
  orbit_t : conjIn (l41R t x₁ x₂ rho) t = t • (fourGrp x₁ x₂ : Set G)
  fourGrp_le : fourGrp x₁ x₂ ≤ l41R t x₁ x₂ rho
  fourGrp_central : ∀ f ∈ fourGrp x₁ x₂, ∀ r ∈ l41R t x₁ x₂ rho, f * r = r * f
  comm_le : ⁅l41R t x₁ x₂ rho, l41R t x₁ x₂ rho⁆ ≤ fourGrp x₁ x₂
  sq_mem : ∀ r ∈ l41R t x₁ x₂ rho, r * r ∈ fourGrp x₁ x₂
  V_eq : l41V S t x₁ x₂ = l41R t x₁ x₂ rho ⊔ closure {t, lam}

@[expose] def L41HS29Fact (t : G) (x₁ x₂ lam rho : G) : Prop :=
  IsMulCommutative (l41R t x₁ x₂ rho) ∨
    (Nonempty (↥(l41R t x₁ x₂ rho) ≃* CFSG.GH74.GLS.Bg.TwoGroups.SylSL3_4) ∧
      (Nonempty (↥(l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) ≃* DihedralGroup 4) ∨
        Nonempty (↥(l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) ≃* QuaternionGroup 2)) ∧
      (Nonempty (↥(l41R t x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ≃* DihedralGroup 4) ∨
        Nonempty (↥(l41R t x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ≃* QuaternionGroup 2)))

structure L41YFacts (t : G) (S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  exists_F : ∃ F' : Subgroup G, F' ≤ l41R t x₁ x₂ rho ∧ CFSG.Open.IsElemAbelian 2 F' ∧
    Nat.card F' = 4 ∧ baseGrp x₁ x₂ ⊓ F' = ⊥ ∧ baseGrp x₁ x₂ ⊔ F' = l41R t x₁ x₂ rho ∧
    (∀ g ∈ closure {rho, t * lam}, ∀ f ∈ F', g * f * g⁻¹ ∈ F') ∧
    l41Y t x₁ x₂ rho = fourGrp x₁ x₂ ⊔ F'
  Y_elem : CFSG.Open.IsElemAbelian 2 (l41Y t x₁ x₂ rho) ∧ Nat.card (l41Y t x₁ x₂ rho) = 16
  cent_Y_t : l41Y t x₁ x₂ rho ⊓ invCent t = fourGrp x₁ x₂
  card_cent_Y_lam : Nat.card ↥(l41Y t x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) = 4
  card_cent_Y_lamt : Nat.card ↥(l41Y t x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) = 4
  quot_V_R : Sec4SectionIso (l41V S t x₁ x₂) (l41R t x₁ x₂ rho) (CFSG.GH74.GLS.Bg.TwoGroups.E2 2)
  cent_V_R : l41V S t x₁ x₂ ⊓ centralizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) =
    l41R t x₁ x₂ rho
  cent_V_Y : l41V S t x₁ x₂ ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
    l41R t x₁ x₂ rho
  cent_V_F2 : l41V S t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
    l41F t x₁ x₂ rho
  cent_Y_V : l41Y t x₁ x₂ rho ⊓ centralizer ((l41V S t x₁ x₂ : Subgroup G) : Set G) =
    zpowers ((x₁ * x₂) ^ 2)
  center_F : l41F t x₁ x₂ rho ⊓ centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) =
    baseGrp x₁ x₂
  E16_V : ∀ E : Subgroup G, IsE16In (l41V S t x₁ x₂) E → E = l41Y t x₁ x₂ rho
  char_Y : ((l41Y t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)).Characteristic
  char_R : ((l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)).Characteristic
  char_F2 : ((fourGrp x₁ x₂).subgroupOf (l41V S t x₁ x₂)).Characteristic
  char_F : ((l41F t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)).Characteristic
  char_B : ((baseGrp x₁ x₂).subgroupOf (l41V S t x₁ x₂)).Characteristic

@[expose] def L41UniqueYFact (t : G) (S : Subgroup G) (x₁ x₂ rho : G) : Prop :=
  (∀ W' : Subgroup G, IsPGroup 2 W' → l41V S t x₁ x₂ ≤ W' →
    NormalIn (l41Y t x₁ x₂ rho) W' ∧
      ∀ Y₁ : Subgroup G, NormalIn Y₁ W' → CFSG.Open.IsElemAbelian 2 Y₁ → Nat.card Y₁ = 16 →
        Y₁ = l41Y t x₁ x₂ rho) ∧
    ¬ 2 ∣ (normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)).index

structure L41MBasic (t : G) (x₁ x₂ lam rho : G) : Prop where
  orbit_tk : ∀ k ∈ l41R t x₁ x₂ rho,
    conjIn (l41R t x₁ x₂ rho) (t * k) = (t * k) • (fourGrp x₁ x₂ : Set G)
  cent_tk : ∀ k ∈ l41R t x₁ x₂ rho,
    l41R t x₁ x₂ rho ⊓ centralizer ({t * k} : Set G) = baseGrp x₁ x₂
  card_invol_tR : {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1}.ncard = 16
  normal_R : NormalIn (l41R t x₁ x₂ rho) (l41M t x₁ x₂ rho)
  normal_Y : NormalIn (l41Y t x₁ x₂ rho) (l41M t x₁ x₂ rho)
  cent_F : centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) = baseGrp x₁ x₂
  oddCore_M : CFSG.oddCore (l41M t x₁ x₂ rho) = ⊥
  J0_F : CFSG.ambientMaxCardThompson (l41F t x₁ x₂ rho) = l41R t x₁ x₂ rho
  cent_M_t : invCent t ⊓ l41M t x₁ x₂ rho = ctxW t x₁ x₂ ⊔ closure {rho, lam}
  sylow3 : ¬ 3 ∣ (zpowers rho).relIndex (l41M t x₁ x₂ rho)
  card_M : ∃ k : ℕ, Nat.card (l41M t x₁ x₂ rho) = 2 ^ k * 3

structure L41QFacts (t : G) (x₁ x₂ lam rho : G) : Prop where
  F_lt_Q : l41F t x₁ x₂ rho < l41Q t x₁ x₂ rho
  quot_Q : Sec4SectionIso (l41Q t x₁ x₂ rho) (l41F t x₁ x₂ rho) (CFSG.GH74.GLS.Bg.TwoGroups.E2 2)
  M_eq : l41M t x₁ x₂ rho = l41Q t x₁ x₂ rho ⊔ closure {rho, lam}
  cent_Q_rho : l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = zpowers t
  cent_Qbar_t : {q | q ∈ l41Q t x₁ x₂ rho ∧ ⁅q, t⁆ ∈ l41Y t x₁ x₂ rho} =
    ((ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G)
  cent_Qbar_rho : {q | q ∈ l41Q t x₁ x₂ rho ∧ ⁅q, rho⁆ ∈ l41Y t x₁ x₂ rho} =
    ((zpowers t ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G)
  orbit_t : conjIn (l41Q t x₁ x₂ rho) t =
    {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1}

structure L41Q1Facts (t : G) (x₁ x₂ lam rho : G) : Prop where
  t_not_mem : t ∉ l41Q1 t x₁ x₂ rho
  Q_eq : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t
  R_le : l41R t x₁ x₂ rho ≤ l41Q1 t x₁ x₂ rho
  normal_Q1 : NormalIn (l41Q1 t x₁ x₂ rho) (l41M t x₁ x₂ rho)
  card_Q1 : Nat.card (l41Q1 t x₁ x₂ rho) = 2 ^ 8
  Y_le : l41Y t x₁ x₂ rho ≤ l41Q1 t x₁ x₂ rho
  comm_le : ⁅l41Q1 t x₁ x₂ rho, l41Q1 t x₁ x₂ rho⁆ ≤ l41Y t x₁ x₂ rho
  quot_Q1 : Sec4SectionIso (l41Q1 t x₁ x₂ rho) (l41Y t x₁ x₂ rho)
      (CFSG.GH74.GLS.Bg.TwoGroups.E2 4) ∨
    Sec4SectionIso (l41Q1 t x₁ x₂ rho) (l41Y t x₁ x₂ rho) CFSG.GH74.GLS.Bg.TwoGroups.Z4Z4
  V1_pGroup : IsPGroup 2 (l41V1 t x₁ x₂ rho lam)
  V1_sylow : ¬ 2 ∣ (l41V1 t x₁ x₂ rho lam).relIndex (l41M t x₁ x₂ rho)
  card_V1 : Nat.card (l41V1 t x₁ x₂ rho lam) = 2 ^ 10
  V1_not_sylow : 2 ∣ (l41V1 t x₁ x₂ rho lam).index
  cent_Q1_Y : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho ∨
    l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41Q1 t x₁ x₂ rho

end CFSG.OddStandard.SmallF3.HarrisU33
