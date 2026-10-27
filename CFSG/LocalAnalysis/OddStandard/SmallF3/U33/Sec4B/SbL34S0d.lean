module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem exists_comm_eq {s : G} (hsO : s ∈ ctxO t tau x₁ x₂) (hs1 : s * s = 1)
    (hcomm : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂) {v : G}
    (hv : v ∈ fourGrp x₁ x₂) : ∃ b ∈ ctxQ t tau x₁ x₂ rho, b * s * b⁻¹ * s⁻¹ = v := by
  let D : Subgroup G :=
    { carrier := {v : G | ∃ b ∈ ctxQ t tau x₁ x₂ rho, b * s * b⁻¹ * s⁻¹ = v}
      one_mem' := ⟨1, one_mem _, by group⟩
      mul_mem' := by
        rintro v₁ v₂ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩
        refine ⟨b₂ * b₁, mul_mem hb₂ hb₁, ?_⟩
        have hb₂O : b₂ ∈ ctxO t tau x₁ x₂ := hc.Q_le_O hb₂
        have hV₁ : b₁ * s * b₁⁻¹ * s⁻¹ ∈ fourGrp x₁ x₂ := comm_Q_O_mem_V hc hb₁ hsO
        have hcomm' : b₂ * (b₁ * s * b₁⁻¹ * s⁻¹) = (b₁ * s * b₁⁻¹ * s⁻¹) * b₂ :=
          V_comm_O hc hb₂O hV₁
        calc (b₂ * b₁) * s * (b₂ * b₁)⁻¹ * s⁻¹
            = b₂ * (b₁ * s * b₁⁻¹) * b₂⁻¹ * s⁻¹ := by group
          _ = b₂ * ((b₁ * s * b₁⁻¹ * s⁻¹) * s) * b₂⁻¹ * s⁻¹ := by
                conv_lhs =>
                  rw [show b₁ * s * b₁⁻¹ = (b₁ * s * b₁⁻¹ * s⁻¹) * s by group]
          _ = (b₂ * (b₁ * s * b₁⁻¹ * s⁻¹) * b₂⁻¹) * (b₂ * s * b₂⁻¹ * s⁻¹) := by
                group
          _ = (b₁ * s * b₁⁻¹ * s⁻¹) * (b₂ * s * b₂⁻¹ * s⁻¹) := by
                rw [show b₂ * (b₁ * s * b₁⁻¹ * s⁻¹) * b₂⁻¹ = b₁ * s * b₁⁻¹ * s⁻¹ by
                  rw [hcomm']; group]
      inv_mem' := by
        rintro v ⟨b, hb, rfl⟩
        refine ⟨b⁻¹, inv_mem hb, ?_⟩
        have hbO : b ∈ ctxO t tau x₁ x₂ := hc.Q_le_O hb
        have hV : b * s * b⁻¹ * s⁻¹ ∈ fourGrp x₁ x₂ := comm_Q_O_mem_V hc hb hsO
        have hcomm' : b⁻¹ * (b * s * b⁻¹ * s⁻¹)⁻¹ = (b * s * b⁻¹ * s⁻¹)⁻¹ * b⁻¹ :=
          V_comm_O hc (inv_mem hbO) (inv_mem hV)
        calc b⁻¹ * s * (b⁻¹)⁻¹ * s⁻¹
            = b⁻¹ * (b * s * b⁻¹ * s⁻¹)⁻¹ * b := by group
          _ = (b * s * b⁻¹ * s⁻¹)⁻¹ := by rw [hcomm']; group }
  have hDle : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro b hb g hg
    rcases mem_zpowers_eq_one_or_eq hs1 hg with rfl | rfl
    · refine ⟨1, one_mem _, ?_⟩
      rw [commutatorElement_def]
      group
    · exact ⟨b, hb, by rw [commutatorElement_def]⟩
  exact hDle (by rw [hcomm]; exact hv)

theorem conjIn_U_eq {s : G} (hsO : s ∈ ctxO t tau x₁ x₂) (hs1 : s * s = 1)
    (hM : conjIn (ctxM t tau x₁ x₂) s = s • (fourGrp x₁ x₂ : Set G))
    (hcomm : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂) :
    conjIn (ctxU t tau x₁ x₂ lam) s = s • (fourGrp x₁ x₂ : Set G) := by
  apply Set.Subset.antisymm
  · rintro u ⟨k, hkU, rfl⟩
    have hmem : k * s * k⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) s :=
      ⟨k, U_le_M hc hkU, rfl⟩
    rwa [hM] at hmem
  · rintro u ⟨v, hv, rfl⟩
    change s * v ∈ conjIn (ctxU t tau x₁ x₂ lam) s
    obtain ⟨b, hb, hbv⟩ := exists_comm_eq hc hsO hs1 hcomm hv
    refine ⟨b, O_le_U hc (hc.Q_le_O hb), ?_⟩
    have h1 : b * s * b⁻¹ = v * s := by
      rw [← hbv]; group
    rw [h1, V_comm_O hc hsO hv]

theorem normal_CQ {s : G} (hsO : s ∈ ctxO t tau x₁ x₂)
    (hM : conjIn (ctxM t tau x₁ x₂) s = s • (fourGrp x₁ x₂ : Set G)) :
    NormalIn (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G)) (ctxM t tau x₁ x₂) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    exact hc.Q_le_M hk.1
  · intro g hg k hk
    obtain ⟨hkQ, hkC⟩ := hk
    refine ⟨hc.normal_Q.2 g hg k hkQ, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hks : k * s = s * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
    have hmem : g⁻¹ * s * g ∈ conjIn (ctxM t tau x₁ x₂) s :=
      ⟨g⁻¹, inv_mem hg, by group⟩
    rw [hM, Set.mem_smul_set] at hmem
    obtain ⟨v, hv, hsv⟩ := hmem
    rw [smul_eq_mul] at hsv
    have hkv : k * v = v * k := V_comm_O hc (hc.Q_le_O hkQ) hv
    have h1 : k * (g⁻¹ * s * g) = (g⁻¹ * s * g) * k := by
      rw [← hsv]
      calc k * (s * v) = (k * s) * v := by group
        _ = (s * k) * v := by rw [hks]
        _ = s * (k * v) := by group
        _ = s * (v * k) := by rw [hkv]
        _ = (s * v) * k := by group
    calc (g * k * g⁻¹) * s = g * (k * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * k) * g⁻¹ := by rw [h1]
      _ = s * (g * k * g⁻¹) := by group

theorem tauU_eq : conjIn (ctxU t tau x₁ x₂ lam) tau = tau • (fourGrp x₁ x₂ : Set G) :=
  conjIn_U_eq hc hc.tau_mem_O hc.tau_mul_self hc.tauM (comm_tau_eq hc)

theorem ttauU_eq :
    conjIn (ctxU t tau x₁ x₂ lam) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G) :=
  conjIn_U_eq hc (mul_mem hc.t_mem_O hc.tau_mem_O)
    ((s_facts hc (Or.inr (Or.inr rfl))).1) hc.ttauM (comm_ttau_eq hc)

theorem normal_CQtau :
    NormalIn (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G)) (ctxM t tau x₁ x₂) :=
  normal_CQ hc hc.tau_mem_O hc.tauM

theorem normal_CQttau :
    NormalIn (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) (ctxM t tau x₁ x₂) :=
  normal_CQ hc (mul_mem hc.t_mem_O hc.tau_mem_O) hc.ttauM

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
