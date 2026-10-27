module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Grp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem O_normal_M (t tau x₁ x₂ : G) : NormalIn (ctxO t tau x₁ x₂) (ctxM t tau x₁ x₂) :=
  ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 (ctxM t tau x₁ x₂), fun _ hg _ hk =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ctxM t tau x₁ x₂) hg) _).mp hk⟩

section Basic

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem U_le_M : ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ := hc.U_sylow.1

theorem O_le_U : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := le_sup_left

theorem card_U : Nat.card (ctxU t tau x₁ x₂ lam) = 2 ^ 9 := by
  have hfac : (3 * 2 ^ 9).factorization 2 = 9 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      Nat.factorization_pow_self Nat.prime_two]
  rw [S4B.card_eq_of_isSylowIn hc.U_sylow, hc.card_M, hfac]

theorem lam_not_mem_O : lam ∉ ctxO t tau x₁ x₂ := by
  intro hlam
  have hU_eq : ctxU t tau x₁ x₂ lam = ctxO t tau x₁ x₂ := by
    rw [ctxU, sup_eq_left]
    exact Subgroup.zpowers_le.mpr hlam
  have h1 : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 9 := by
    rw [← hU_eq]
    exact card_U hc
  rw [hc.card_O] at h1
  exact absurd h1 (by norm_num)

theorem mem_T_iff {s : G} :
    s ∈ closure ({t, tau} : Set G) ↔ s = 1 ∨ s = t ∨ s = tau ∨ s = t * tau :=
  mem_closure_pair_iff hc.t_mul_self hc.tau_mul_self hc.t_comm_tau s

theorem T_le_O : closure ({t, tau} : Set G) ≤ ctxO t tau x₁ x₂ := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hc.t_mem_O
  · exact hc.tau_mem_O

theorem T_le_M : closure ({t, tau} : Set G) ≤ ctxM t tau x₁ x₂ :=
  (T_le_O hc).trans hc.O_le_M

theorem V_le_O : fourGrp x₁ x₂ ≤ ctxO t tau x₁ x₂ := hc.V_le_Q.trans hc.Q_le_O

theorem V_comm_O {a u : G} (ha : a ∈ ctxO t tau x₁ x₂) (hu : u ∈ fourGrp x₁ x₂) :
    a * u = u * a := by
  have ha' : a ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hc.O_eq_CV]
    exact ha
  exact (Subgroup.mem_centralizer_iff.mp ha'.2 u hu).symm

theorem O_decomp {a : G} (ha : a ∈ ctxO t tau x₁ x₂) :
    ∃ b ∈ ctxQ t tau x₁ x₂ rho, ∃ s ∈ closure ({t, tau} : Set G), a = b * s := by
  have hT_le_norm :
      closure ({t, tau} : Set G) ≤ Subgroup.normalizer (ctxQ t tau x₁ x₂ rho) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs k hk
    exact hc.normal_Q.2 s (T_le_M hc hs) k hk
  have ha' : a ∈ closure ({t, tau} : Set G) ⊔ ctxQ t tau x₁ x₂ rho := by
    rw [sup_comm, ← hc.O_eq_Q]
    exact ha
  have ha'' : a ∈ (closure ({t, tau} : Set G) : Set G) * (ctxQ t tau x₁ x₂ rho : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT_le_norm]
    exact ha'
  rw [Set.mem_mul] at ha''
  obtain ⟨s, hs, b, hb, hsb⟩ := ha''
  refine ⟨s * b * s⁻¹, ?_, s, hs, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hT_le_norm hs) b).mp hb
  · rw [← hsb]
    group

theorem Q_inf_T : ctxQ t tau x₁ x₂ rho ⊓ closure ({t, tau} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases (mem_T_iff hc).mp hx.2 with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hx.1 hc.t_not_mem_Q
  · exact absurd hx.1 hc.tau_not_mem_Q
  · exact absurd hx.1 hc.ttau_not_mem_Q

theorem Q_inf_X_le_V {x : G} (hxQ : x ∈ ctxQ t tau x₁ x₂ rho) (hxX : x ∈ ctxX t tau x₁ x₂) :
    x ∈ fourGrp x₁ x₂ := by
  rcases S4A.mem_ctxX_cases hc.toCtx hc.l44.1 hxX with hV | hV | hV | hV
  · exact hV
  · rw [Set.mem_smul_set] at hV
    obtain ⟨f, hf, hfu⟩ := hV
    exfalso
    apply hc.t_not_mem_Q
    have ht : t = x * f⁻¹ := by
      rw [smul_eq_mul] at hfu
      exact eq_mul_inv_of_mul_eq hfu
    have hmem : x * f⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hxQ (inv_mem (hc.V_le_Q hf))
    rwa [← ht] at hmem
  · rw [Set.mem_smul_set] at hV
    obtain ⟨f, hf, hfu⟩ := hV
    exfalso
    apply hc.tau_not_mem_Q
    have htau : tau = x * f⁻¹ := by
      rw [smul_eq_mul] at hfu
      exact eq_mul_inv_of_mul_eq hfu
    have hmem : x * f⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hxQ (inv_mem (hc.V_le_Q hf))
    rwa [← htau] at hmem
  · rw [Set.mem_smul_set] at hV
    obtain ⟨f, hf, hfu⟩ := hV
    exfalso
    apply hc.ttau_not_mem_Q
    have httau : t * tau = x * f⁻¹ := by
      rw [smul_eq_mul] at hfu
      exact eq_mul_inv_of_mul_eq hfu
    have hmem : x * f⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hxQ (inv_mem (hc.V_le_Q hf))
    rwa [← httau] at hmem

theorem comm_Q_O_mem_V {b s : G} (hb : b ∈ ctxQ t tau x₁ x₂ rho) (hs : s ∈ ctxO t tau x₁ x₂) :
    b * s * b⁻¹ * s⁻¹ ∈ fourGrp x₁ x₂ := by
  have hQ : s * b⁻¹ * s⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.normal_Q.2 s (hc.O_le_M hs) b⁻¹ (inv_mem hb)
  have hX : b * s * b⁻¹ * s⁻¹ ∈ ctxX t tau x₁ x₂ :=
    hc.O_quot.2 b (hc.Q_le_O hb) s hs
  exact Q_inf_X_le_V hc (by simpa only [mul_assoc] using mul_mem hb hQ) hX

theorem O_comm_le {a a' : G} (ha : a ∈ ctxO t tau x₁ x₂) (ha' : a' ∈ ctxO t tau x₁ x₂) :
    a * a' * a⁻¹ * a'⁻¹ ∈ fourGrp x₁ x₂ := by
  obtain ⟨b₁, hb₁, s₁, hs₁, rfl⟩ := O_decomp hc ha
  obtain ⟨b₂, hb₂, s₂, hs₂, rfl⟩ := O_decomp hc ha'
  have h1 : s₁ * b₂ * s₁⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.normal_Q.2 s₁ (T_le_M hc hs₁) b₂ hb₂
  have h2 : s₂ * b₁ * s₂⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.normal_Q.2 s₂ (T_le_M hc hs₂) b₁ hb₁
  have hc1 : b₁ * (s₁ * b₂ * s₁⁻¹) ∈ ctxQ t tau x₁ x₂ rho := mul_mem hb₁ h1
  have hc2 : b₂ * (s₂ * b₁ * s₂⁻¹) ∈ ctxQ t tau x₁ x₂ rho := mul_mem hb₂ h2
  have hs : s₁ * s₂ = s₂ * s₁ :=
    congrArg Subtype.val
      ((elemAbelian_closure_pair hc.t_mul_self hc.tau_mul_self hc.t_comm_tau).1.is_comm.comm
        ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩)
  have haa' : (b₁ * s₁) * (b₂ * s₂) = (b₁ * (s₁ * b₂ * s₁⁻¹)) * (s₁ * s₂) := by group
  have ha'a : (b₂ * s₂) * (b₁ * s₁) = (b₂ * (s₂ * b₁ * s₂⁻¹)) * (s₁ * s₂) := by
    rw [hs]; group
  have hcomm : (b₁ * s₁) * (b₂ * s₂) * (b₁ * s₁)⁻¹ * (b₂ * s₂)⁻¹
      = (b₁ * (s₁ * b₂ * s₁⁻¹)) * (b₂ * (s₂ * b₁ * s₂⁻¹))⁻¹ := by
    rw [show (b₁ * s₁) * (b₂ * s₂) * (b₁ * s₁)⁻¹ * (b₂ * s₂)⁻¹
          = (b₁ * s₁) * (b₂ * s₂) * ((b₂ * s₂) * (b₁ * s₁))⁻¹ by group,
      haa', ha'a]
    group
  have hmemQ : (b₁ * s₁) * (b₂ * s₂) * (b₁ * s₁)⁻¹ * (b₂ * s₂)⁻¹ ∈
      ctxQ t tau x₁ x₂ rho := by
    rw [hcomm]
    exact mul_mem hc1 (inv_mem hc2)
  have hX : (b₁ * s₁) * (b₂ * s₂) * (b₁ * s₁)⁻¹ * (b₂ * s₂)⁻¹ ∈ ctxX t tau x₁ x₂ :=
    hc.O_quot.2 (b₁ * s₁) (mul_mem (hc.Q_le_O hb₁) (T_le_O hc hs₁))
      (b₂ * s₂) (mul_mem (hc.Q_le_O hb₂) (T_le_O hc hs₂))
  exact Q_inf_X_le_V hc hmemQ hX

theorem O_sq_mem_V {a : G} (ha : a ∈ ctxO t tau x₁ x₂) : a * a ∈ fourGrp x₁ x₂ := by
  obtain ⟨b, hb, s, hs, rfl⟩ := O_decomp hc ha
  have hcV : s * b * s⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := by
    have h : b * s * b⁻¹ * s⁻¹ ∈ fourGrp x₁ x₂ :=
      comm_Q_O_mem_V (b := b) (s := s) hc hb (T_le_O hc hs)
    have hinv := inv_mem h
    rwa [show (b * s * b⁻¹ * s⁻¹)⁻¹ = s * b * s⁻¹ * b⁻¹ by group] at hinv
  have hbV : b * b ∈ fourGrp x₁ x₂ := by
    have h := hc.Q_quot.1 b hb
    rwa [pow_two] at h
  have hss : s * s = 1 := by
    have h := (elemAbelian_closure_pair hc.t_mul_self hc.tau_mul_self hc.t_comm_tau).2 s hs
    rwa [pow_two] at h
  have hbc : b * (s * b * s⁻¹ * b⁻¹) = (s * b * s⁻¹ * b⁻¹) * b :=
    V_comm_O hc (hc.Q_le_O hb) hcV
  have hgoal : (b * s) * (b * s) = (s * b * s⁻¹ * b⁻¹) * (b * b) := by
    calc (b * s) * (b * s)
        = b * (s * b * s⁻¹) * (s * s) := by group
      _ = b * (s * b * s⁻¹) := by rw [hss, mul_one]
      _ = b * ((s * b * s⁻¹ * b⁻¹) * b) := by group
      _ = (b * (s * b * s⁻¹ * b⁻¹)) * b := by group
      _ = ((s * b * s⁻¹ * b⁻¹) * b) * b := by rw [hbc]
      _ = (s * b * s⁻¹ * b⁻¹) * (b * b) := by group
  rw [hgoal]
  exact mul_mem hcV hbV

end Basic

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
