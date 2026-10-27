module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

section General

variable {G : Type} [Group G] [Finite G]

private theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

private theorem card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
    Nat.card (Set.range fun c : H => σ c * F * (σ c)⁻¹) =
      ((centralizer ({F} : Set P)).comap σ).index := by
  refine card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, mem_centralizer_singleton_iff, map_mul, map_inv]
  constructor
  · intro h
    calc (σ a)⁻¹ * σ b * F = (σ a)⁻¹ * (σ b * F * (σ b)⁻¹) * σ b := by group
      _ = (σ a)⁻¹ * (σ a * F * (σ a)⁻¹) * σ b := by rw [h]
      _ = F * ((σ a)⁻¹ * σ b) := by group
  · intro h
    calc σ a * F * (σ a)⁻¹ = σ a * (F * ((σ a)⁻¹ * σ b)) * (σ b)⁻¹ := by group
      _ = σ a * ((σ a)⁻¹ * σ b * F) * (σ b)⁻¹ := by rw [h]
      _ = σ b * F * (σ b)⁻¹ := by group

theorem card_eq_ncard_conjIn_mul (H : Subgroup G) (s : G) :
    Nat.card H = (conjIn H s).ncard * Nat.card (H ⊓ centralizer ({s} : Set G) : Subgroup G) := by
  have hrange : conjIn H s = Set.range (fun c : H => (c : G) * s * (c : G)⁻¹) := by
    ext u
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
  have h1 : Nat.card ↥(Set.range fun c : H => (c : G) * s * (c : G)⁻¹) =
      ((centralizer ({s} : Set G)).comap H.subtype).index := card_conj_orbit H.subtype s
  have h2 := Subgroup.card_mul_index ((centralizer ({s} : Set G)).comap H.subtype)
  have h3 : Nat.card ↥((centralizer ({s} : Set G)).comap H.subtype) =
      Nat.card ↥(H ⊓ centralizer ({s} : Set G)) := by
    have e := Subgroup.inf_subgroupOf_left (centralizer ({s} : Set G)) H
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : H ⊓ centralizer ({s} : Set G) ≤ H)).toEquiv, e]
    rfl
  rw [hrange, ← _root_.Nat.card_coe_set_eq (Set.range fun c : H => (c : G) * s * (c : G)⁻¹),
    h1, ← h2, ← h3]
  exact mul_comm _ _

theorem ncard_smul_subgroup (V : Subgroup G) (s : G) :
    (s • (V : Set G)).ncard = Nat.card V := by
  rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.cast (SetLike.coe_sort_coe V))

end General

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem card_CQ_of_conjIn_eq {s : G}
    (h : conjIn (ctxQ t tau x₁ x₂ rho) s = s • (fourGrp x₁ x₂ : Set G)) :
    Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ 4 := by
  have hOS := card_eq_ncard_conjIn_mul (ctxQ t tau x₁ x₂ rho) s
  rw [h, ncard_smul_subgroup, card_fourGrp hc, hc.card_Q] at hOS
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [h64] at hOS
  rw [h16]
  omega

theorem conjIn_Q_eq {s : G} (hsO : s ∈ ctxO t tau x₁ x₂) (hs1 : s * s = 1)
    (hM : conjIn (ctxM t tau x₁ x₂) s = s • (fourGrp x₁ x₂ : Set G))
    (hcomm : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂) :
    conjIn (ctxQ t tau x₁ x₂ rho) s = s • (fourGrp x₁ x₂ : Set G) := by
  apply Set.Subset.antisymm
  · rintro u ⟨k, hkQ, rfl⟩
    have hmem : k * s * k⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) s :=
      ⟨k, hc.Q_le_M hkQ, rfl⟩
    rwa [hM] at hmem
  · rintro u ⟨v, hv, rfl⟩
    change s * v ∈ conjIn (ctxQ t tau x₁ x₂ rho) s
    obtain ⟨b, hb, hbv⟩ := exists_comm_eq hc hsO hs1 hcomm hv
    refine ⟨b, hb, ?_⟩
    have h1 : b * s * b⁻¹ = v * s := by
      rw [← hbv]; group
    rw [h1, V_comm_O hc hsO hv]

theorem card_CQ_t :
    Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 :=
  card_CQ_of_conjIn_eq hc (conjIn_Q_eq hc hc.t_mem_O hc.t_mul_self hc.tM (comm_t_eq hc))

theorem card_CQ_tau :
    Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) : Subgroup G) = 2 ^ 4 :=
  card_CQ_of_conjIn_eq hc (conjIn_Q_eq hc hc.tau_mem_O hc.tau_mul_self hc.tauM (comm_tau_eq hc))

theorem card_CQ_ttau :
    Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) : Subgroup G) = 2 ^ 4 :=
  card_CQ_of_conjIn_eq hc (conjIn_Q_eq hc (mul_mem hc.t_mem_O hc.tau_mem_O)
    ((s_facts hc (Or.inr (Or.inr rfl))).1) hc.ttauM (comm_ttau_eq hc))

theorem conjIn_Q_eq_of_noncentral (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) {a : G}
    (haQ : a ∈ ctxQ t tau x₁ x₂ rho) (ha : a ∉ fourGrp x₁ x₂) :
    conjIn (ctxQ t tau x₁ x₂ rho) a = a • (fourGrp x₁ x₂ : Set G) := by
  apply Set.Subset.antisymm
  · rintro u ⟨b, hbQ, rfl⟩
    have hv : b * a * b⁻¹ * a⁻¹ ∈ fourGrp x₁ x₂ :=
      comm_Q_O_mem_V hc hbQ (hc.Q_le_O haQ)
    refine ⟨b * a * b⁻¹ * a⁻¹, hv, ?_⟩
    change a * (b * a * b⁻¹ * a⁻¹) = b * a * b⁻¹
    have hcomm : a * (b * a * b⁻¹ * a⁻¹) = (b * a * b⁻¹ * a⁻¹) * a :=
      V_comm_O hc (hc.Q_le_O haQ) hv
    rw [hcomm]; group
  · rintro u ⟨v, hv, rfl⟩
    change a * v ∈ conjIn (ctxQ t tau x₁ x₂ rho) a
    obtain ⟨w, hwQ, hwv⟩ := pairing_Q hc hs haQ ha (inv_mem hv)
    refine ⟨w, hwQ, ?_⟩
    have h1 : w * a * w⁻¹ * a⁻¹ = v := by
      calc w * a * w⁻¹ * a⁻¹ = (a * w * a⁻¹ * w⁻¹)⁻¹ := by group
        _ = (v⁻¹)⁻¹ := by rw [hwv]
        _ = v := by group
    calc w * a * w⁻¹ = (w * a * w⁻¹ * a⁻¹) * a := by group
      _ = v * a := by rw [h1]
      _ = a * v := (V_comm_O hc (hc.Q_le_O haQ) hv).symm

theorem card_CQ_of_noncentral (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) {a : G}
    (haQ : a ∈ ctxQ t tau x₁ x₂ rho) (ha : a ∉ fourGrp x₁ x₂) :
    Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({a} : Set G) : Subgroup G) = 2 ^ 4 :=
  card_CQ_of_conjIn_eq hc (conjIn_Q_eq_of_noncentral hc hs haQ ha)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
