module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma31Elem

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private abbrev p0_c4 (hc : Ctx8c t L S x₁ x₂ lam rho tau) : Ctx4 t L S x₁ x₂ lam rho tau :=
  hc.toCtx8b.toCtx8a.toCtx8.toCtx10.toCtx4

private theorem p0_t_mem_X (t tau x₁ x₂ : G) : t ∈ ctxX t tau x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private theorem p0_V_le_X (t tau x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ :=
  ((p0_V_le_N_le_X t tau x₁ x₂).1).trans ((p0_V_le_N_le_X t tau x₁ x₂).2)

private theorem p0_comm_of_mem_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative ↥(ctxW t x₁ x₂) := hc.abelian_W
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(ctxW t x₁ x₂)) ⟨b, hb⟩)

private theorem p0_baseGrp_comm (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative ↥(baseGrp x₁ x₂) := (hc.wreath.baseGrp_eq).1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(baseGrp x₁ x₂)) ⟨b, hb⟩)

private theorem p0_fourGrp_le_baseGrp (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [(hc.wreath.fourGrp_eq_omega).1]
  refine (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr ?_
  intro a ha
  exact ha.1

private theorem p0_baseGrp_le_W (t x₁ x₂ : G) : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ :=
  le_sup_right

private theorem p0_zpowers_t_le_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Subgroup.zpowers t ≤ ctxW t x₁ x₂ := by
  rw [ctxW, ← hc.l43]
  exact le_sup_left

private theorem p0_X_comm (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    IsMulCommutative (ctxX t tau x₁ x₂) := by
  have htt : Commute t tau := (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have hty : Commute t (x₁ ^ 2) :=
    (S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).1)).symm
  have htz : Commute t ((x₁ * x₂) ^ 2) := S4A.t_commute_z hc.toCtx0
  have htay : Commute tau (x₁ ^ 2) := S4A.tau_commute_y hc.toCtx
  have htaz : Commute tau ((x₁ * x₂) ^ 2) := S4A.tau_commute_z hc.toCtx
  have hyz : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) := S4A.y_commute_z hc.wreath
  rw [ctxX]
  refine Subgroup.isMulCommutative_closure ?_
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact htt
      | exact htt.symm
      | exact hty
      | exact hty.symm
      | exact htz
      | exact htz.symm
      | exact htay
      | exact htay.symm
      | exact htaz
      | exact htaz.symm
      | exact hyz
      | exact hyz.symm

private theorem p0_tau_comm_mem_V (hc : Ctx4 t L S x₁ x₂ lam rho tau) {v : G}
    (hv : v ∈ fourGrp x₁ x₂) : tau * v = v * tau := by
  haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := p0_X_comm hc
  exact congrArg Subtype.val (mul_comm'
    (⟨tau, Subgroup.subset_closure (by simp)⟩ : ↥(ctxX t tau x₁ x₂))
    (⟨v, p0_V_le_X t tau x₁ x₂ hv⟩ : ↥(ctxX t tau x₁ x₂)))

private theorem p0_t_mem_cent_V (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    t ∈ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := p0_X_comm hc
  exact congrArg Subtype.val (mul_comm'
    (⟨v, p0_V_le_X t tau x₁ x₂ hv⟩ : ↥(ctxX t tau x₁ x₂))
    (⟨t, Subgroup.subset_closure (by simp)⟩ : ↥(ctxX t tau x₁ x₂)))

private theorem p0_conj_mem_V_of_mem_X (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a v : G}
    (ha : a ∈ ctxX t tau x₁ x₂) (hv : v ∈ fourGrp x₁ x₂) :
    a * v * a⁻¹ ∈ fourGrp x₁ x₂ := by
  haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := p0_X_comm hc
  have hcomm : a * v = v * a :=
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(ctxX t tau x₁ x₂))
      (⟨v, p0_V_le_X t tau x₁ x₂ hv⟩ : ↥(ctxX t tau x₁ x₂)))
  have heq : a * v * a⁻¹ = v := by rw [hcomm]; group
  rw [heq]; exact hv

private theorem p0_commutator_mem_V_of_gens (hc : Ctx4 t L S x₁ x₂ lam rho tau) {g : G}
    (ht : g * t * g⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂)
    (htau : g * tau * g⁻¹ * tau⁻¹ ∈ fourGrp x₁ x₂)
    (hy : g * x₁ ^ 2 * g⁻¹ * (x₁ ^ 2)⁻¹ ∈ fourGrp x₁ x₂)
    (hz : g * (x₁ * x₂) ^ 2 * g⁻¹ * ((x₁ * x₂) ^ 2)⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ x ∈ ctxX t tau x₁ x₂, g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂ := by
  intro x hx
  rw [ctxX] at hx
  refine Subgroup.closure_induction
    (p := fun x _ => g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂) ?_ ?_ ?_ ?_ hx
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    exacts [ht, htau, hy, hz]
  · simpa using one_mem (fourGrp x₁ x₂)
  · intro a b ha hb pa pb
    have hconj : a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ ∈ fourGrp x₁ x₂ :=
      p0_conj_mem_V_of_mem_X hc ha pb
    have heq : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
        (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [heq]; exact mul_mem pa hconj
  · intro a ha pa
    have hconj : a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ ∈ fourGrp x₁ x₂ :=
      p0_conj_mem_V_of_mem_X hc (inv_mem ha) (inv_mem pa)
    have heq : g * a⁻¹ * g⁻¹ * (a⁻¹)⁻¹ =
        a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rwa [heq]

private theorem p0_commutator_eq_sq_of_conj_eq_inv {a b : G} (h : b * a * b⁻¹ = a⁻¹) :
    a * b * a⁻¹ * b⁻¹ = a ^ 2 := by
  have h2 : b * (a⁻¹ * b⁻¹) = a := by
    have := congrArg Inv.inv h
    simpa [mul_inv_rev] using this
  rw [show a * b * a⁻¹ * b⁻¹ = a * (b * (a⁻¹ * b⁻¹)) by group, h2, pow_two]

private theorem p0_mul_comm_of_commutator_eq_one {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) :
    a * b = b * a := by
  have h1 : a * b * a⁻¹ = b := by
    have := congrArg (· * b) h
    simpa [mul_assoc] using this
  have := congrArg (· * a) h1
  simpa [mul_assoc] using this

private theorem p0_tau_conj_baseGrp (hc : Ctx4 t L S x₁ x₂ lam rho tau) {b : G}
    (hb : b ∈ baseGrp x₁ x₂) : tau * b * tau⁻¹ = b⁻¹ := by
  rw [baseGrp] at hb
  refine Subgroup.closure_induction (p := fun b _ => tau * b * tau⁻¹ = b⁻¹) ?_ ?_ ?_ ?_ hb
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hc.tau_x₁
    · exact hc.tau_x₂
  · simp
  · intro y z hy hz ihy ihz
    have hyz : y * z = z * y :=
      p0_comm_of_mem_W hc (p0_baseGrp_le_W t x₁ x₂ hy) (p0_baseGrp_le_W t x₁ x₂ hz)
    calc tau * (y * z) * tau⁻¹ = (tau * y * tau⁻¹) * (tau * z * tau⁻¹) := by group
      _ = y⁻¹ * z⁻¹ := by rw [ihy, ihz]
      _ = (y * z)⁻¹ := by rw [hyz]; group
  · intro y hy ihy
    rw [show tau * y⁻¹ * tau⁻¹ = (tau * y * tau⁻¹)⁻¹ by group, ihy]

private theorem p0_cent_W_tau_le (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({tau} : Set G) ≤
      Subgroup.zpowers t ⊔ fourGrp x₁ x₂ := by
  intro c hc'
  obtain ⟨hcW, hcC⟩ := Subgroup.mem_inf.mp hc'
  have htau_c : c * tau = tau * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hW_eq : ctxW t x₁ x₂ = Subgroup.zpowers t ⊔ baseGrp x₁ x₂ := by rw [ctxW, hc.l43]
  rw [hW_eq] at hcW
  have hnorm : ∀ k ∈ baseGrp x₁ x₂, ∀ h ∈ Subgroup.zpowers t,
      k * h * k⁻¹ ∈ Subgroup.zpowers t := by
    intro k hk h hh
    have hkh : k * h = h * k :=
      p0_comm_of_mem_W hc (p0_baseGrp_le_W t x₁ x₂ hk) (p0_zpowers_t_le_W hc hh)
    rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  obtain ⟨p, hp, b, hb, hcp⟩ :=
    (mem_sup_iff_of_normalizes (H := Subgroup.zpowers t) (K := baseGrp x₁ x₂) hnorm).mp hcW
  have htτ : t * tau = tau * t := (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have htp : tau * p * tau⁻¹ = p := by
    have hle : Subgroup.zpowers t ≤ Subgroup.centralizer ({tau} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr htτ)
    have hcomm : p * tau = tau * p := Subgroup.mem_centralizer_singleton_iff.mp (hle hp)
    rw [← hcomm]; group
  have htb : tau * b * tau⁻¹ = b⁻¹ := p0_tau_conj_baseGrp hc hb
  have h1 : tau * c * tau⁻¹ = p * b⁻¹ := by
    rw [hcp]
    calc tau * (p * b) * tau⁻¹ = (tau * p * tau⁻¹) * (tau * b * tau⁻¹) := by group
      _ = p * b⁻¹ := by rw [htp, htb]
  have hc_eq : tau * c * tau⁻¹ = c := by rw [← htau_c]; group
  have hbinv : b⁻¹ = b := by
    have h2 : p * b⁻¹ = p * b := by rw [← h1, hc_eq, hcp]
    exact mul_left_cancel h2
  have hbb : b * b = 1 := by
    calc b * b = b * b⁻¹ := by rw [hbinv]
      _ = 1 := mul_inv_cancel b
  have hb2 : b ^ 2 = 1 := by rwa [pow_two]
  have hbV : b ∈ fourGrp x₁ x₂ := by
    rw [(hc.wreath.fourGrp_eq_omega).1]
    exact Subgroup.subset_closure ⟨hb, hb2⟩
  rw [hcp]
  exact Subgroup.mul_mem_sup hp hbV

private theorem p0_m12Rel (hc : Ctx4 t L S x₁ x₂ lam rho tau) : M12Rel x₁ x₂ lam tau := by
  have htau1 : tau ≠ 1 := by
    intro h
    apply hc.tau_not_mem
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.one_mem (twoCore t))
  exact
    { toWreathRel := hc.wreath
      ord_tau := orderOf_eq_prime (by simpa [pow_two] using hc.l44.1) htau1
      comm_lam_tau := hc.tau_lam.symm
      tau_x₁ := hc.tau_x₁
      tau_x₂ := hc.tau_x₂ }

private theorem p0_cent_U_t (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    ctxU t tau x₁ x₂ lam ⊓ Subgroup.centralizer ({t} : Set G) = S := by
  have hS_le : S ≤ ctxU t tau x₁ x₂ lam ⊓ Subgroup.centralizer ({t} : Set G) :=
    le_inf hc.S_le_U hc.le_invCent
  have hQ : IsPGroup 2 ↥(ctxU t tau x₁ x₂ lam ⊓ Subgroup.centralizer ({t} : Set G)) :=
    hc.U_sylow.2.1.to_le inf_le_left
  exact S4A.eq_of_isPGroup_of_odd_relIndex hS_le inf_le_right hQ hc.relIndex_odd

theorem p0_X_le_R (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    ctxX t tau x₁ x₂ ≤ ctxR t tau x₁ x₂ := by
  intro x hx
  haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := p0_X_comm (p0_c4 hc)
  refine ⟨Subgroup.le_normalizer hx, ?_, ?_⟩
  · intro y hy
    have hcomm : x * y = y * x :=
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(ctxX t tau x₁ x₂)) ⟨y, hy⟩)
    have heq : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hcomm]; group
    rw [heq]; exact one_mem _
  · intro v hv
    have hcomm : x * v = v * x :=
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(ctxX t tau x₁ x₂))
        (⟨v, p0_V_le_X t tau x₁ x₂ hv⟩ : ↥(ctxX t tau x₁ x₂)))
    have heq : x * v * x⁻¹ = v := by rw [hcomm]; group
    rw [heq]

theorem p0_R_le_O (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
  intro g hg
  obtain ⟨hgM, -, hgV⟩ := hg
  rw [hc.toCtx8b.O_eq_C]
  refine ⟨hgM, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr (fun v hv => by
    have h := hgV v hv
    calc v * g = (g * v * g⁻¹) * g := by rw [h]
      _ = g * v := by group)

theorem p0_normal_R (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxR t tau x₁ x₂) (ctxM t tau x₁ x₂) := by
  refine ⟨fun g hg => hg.1, ?_⟩
  intro m hm g hg
  obtain ⟨hgM, hgX, hgV⟩ := hg
  refine ⟨mul_mem (mul_mem hm hgM) (inv_mem hm), ?_, ?_⟩
  · intro x hx
    have hmX : m⁻¹ * x * m ∈ ctxX t tau x₁ x₂ := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hm) x).mp hx
    have h1 : g * (m⁻¹ * x * m) * g⁻¹ * (m⁻¹ * x * m)⁻¹ ∈ fourGrp x₁ x₂ := hgX _ hmX
    have h2 := hc.toCtx8b.toCtx8a.normal_V.2 m hm _ h1
    have heq : (m * g * m⁻¹) * x * (m * g * m⁻¹)⁻¹ * x⁻¹ =
        m * (g * (m⁻¹ * x * m) * g⁻¹ * (m⁻¹ * x * m)⁻¹) * m⁻¹ := by group
    rw [heq]; exact h2
  · intro v hv
    have hmV : m⁻¹ * v * m ∈ fourGrp x₁ x₂ := by
      simpa using hc.toCtx8b.toCtx8a.normal_V.2 m⁻¹ (inv_mem hm) v hv
    have h1 : g * (m⁻¹ * v * m) * g⁻¹ = m⁻¹ * v * m := hgV _ hmV
    have heq : (m * g * m⁻¹) * v * (m * g * m⁻¹)⁻¹ =
        m * (g * (m⁻¹ * v * m) * g⁻¹) * m⁻¹ := by group
    rw [heq, h1]; group

theorem p0_tau_conj_mem (hc : Ctx8c t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) : g * tau * g⁻¹ ∈ tau • (fourGrp x₁ x₂ : Set G) := by
  have hc4 := p0_c4 hc
  have htauN : tau ∈ ctxN tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have huN : g * tau * g⁻¹ ∈ ctxN tau x₁ x₂ :=
    hc.toCtx8b.toCtx8a.normal_N.2 g hg tau htauN
  rcases l12_N_cases hc4 huN with huV | htuV
  · exfalso
    have hconjV : g⁻¹ * (g * tau * g⁻¹) * g ∈ fourGrp x₁ x₂ := by
      simpa using hc.toCtx8b.toCtx8a.normal_V.2 g⁻¹ (inv_mem hg) _ huV
    have heq : g⁻¹ * (g * tau * g⁻¹) * g = tau := by group
    rw [heq] at hconjV
    exact l12_tau_not_mem_V hc4 hconjV
  · refine Set.mem_smul_set.mpr ⟨tau * (g * tau * g⁻¹), htuV, ?_⟩
    have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
    show tau * (tau * (g * tau * g⁻¹)) = g * tau * g⁻¹
    rw [← mul_assoc, htau2, one_mul]

private theorem p0_x1_mem_R (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    x₁ ∈ ctxR t tau x₁ x₂ := by
  have hc4 := p0_c4 hc
  refine ⟨(p0_gens_mem_M hc4).2.2.1, ?_, ?_⟩
  · refine p0_commutator_mem_V_of_gens hc4 ?_ ?_ ?_ ?_
    · have hcomm : x₁ * t = t * x₁ :=
        p0_comm_of_mem_W hc4 (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
          (Subgroup.mem_sup_left hc4.hyp.mem_twoCore)
      have heq : x₁ * t * x₁⁻¹ * t⁻¹ = 1 := by rw [hcomm]; group
      rw [heq]; exact one_mem _
    · have heq : x₁ * tau * x₁⁻¹ * tau⁻¹ = x₁ ^ 2 :=
        p0_commutator_eq_sq_of_conj_eq_inv hc4.tau_x₁
      rw [heq]; exact Subgroup.subset_closure (by simp)
    · have heq : x₁ * x₁ ^ 2 * x₁⁻¹ * (x₁ ^ 2)⁻¹ = 1 := by group
      rw [heq]; exact one_mem _
    · have hcomm : x₁ * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ :=
        p0_baseGrp_comm hc4 (Subgroup.subset_closure (by simp))
          (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))) 2)
      have heq : x₁ * (x₁ * x₂) ^ 2 * x₁⁻¹ * ((x₁ * x₂) ^ 2)⁻¹ = 1 := by rw [hcomm]; group
      rw [heq]; exact one_mem _
  · intro v hv
    have hcomm : x₁ * v = v * x₁ :=
      p0_baseGrp_comm hc4 (Subgroup.subset_closure (by simp)) (p0_fourGrp_le_baseGrp hc4 hv)
    have heq : x₁ * v * x₁⁻¹ = v := by rw [hcomm]; group
    rw [heq]

private theorem p0_x2_mem_R (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    x₂ ∈ ctxR t tau x₁ x₂ := by
  have hc4 := p0_c4 hc
  refine ⟨(p0_gens_mem_M hc4).2.2.2.1, ?_, ?_⟩
  · refine p0_commutator_mem_V_of_gens hc4 ?_ ?_ ?_ ?_
    · have hcomm : x₂ * t = t * x₂ :=
        p0_comm_of_mem_W hc4 (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
          (Subgroup.mem_sup_left hc4.hyp.mem_twoCore)
      have heq : x₂ * t * x₂⁻¹ * t⁻¹ = 1 := by rw [hcomm]; group
      rw [heq]; exact one_mem _
    · have heq : x₂ * tau * x₂⁻¹ * tau⁻¹ = x₂ ^ 2 :=
        p0_commutator_eq_sq_of_conj_eq_inv hc4.tau_x₂
      rw [heq, hc4.wreath.x₂_sq]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · have hcomm : x₂ * x₁ ^ 2 = x₁ ^ 2 * x₂ :=
        p0_baseGrp_comm hc4 (Subgroup.subset_closure (by simp))
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2)
      have heq : x₂ * x₁ ^ 2 * x₂⁻¹ * (x₁ ^ 2)⁻¹ = 1 := by rw [hcomm]; group
      rw [heq]; exact one_mem _
    · have hcomm : x₂ * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₂ :=
        p0_baseGrp_comm hc4 (Subgroup.subset_closure (by simp))
          (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))) 2)
      have heq : x₂ * (x₁ * x₂) ^ 2 * x₂⁻¹ * ((x₁ * x₂) ^ 2)⁻¹ = 1 := by rw [hcomm]; group
      rw [heq]; exact one_mem _
  · intro v hv
    have hcomm : x₂ * v = v * x₂ :=
      p0_baseGrp_comm hc4 (Subgroup.subset_closure (by simp)) (p0_fourGrp_le_baseGrp hc4 hv)
    have heq : x₂ * v * x₂⁻¹ = v := by rw [hcomm]; group
    rw [heq]

theorem p0_x₁_x₂_mem_R (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    x₁ ∈ ctxR t tau x₁ x₂ ∧ x₂ ∈ ctxR t tau x₁ x₂ :=
  ⟨p0_x1_mem_R hc, p0_x2_mem_R hc⟩

theorem p0_mem_R_iff (hc : Ctx8c t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxO t tau x₁ x₂) :
    g ∈ ctxR t tau x₁ x₂ ↔ g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
  have hc4 := p0_c4 hc
  have hgM : g ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hg
  have hgC : ∀ v ∈ fourGrp x₁ x₂, v * g = g * v := by
    have hg' : g ∈ ctxM t tau x₁ x₂ ⊓
        Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rwa [← hc.toCtx8b.O_eq_C]
    exact Subgroup.mem_centralizer_iff.mp hg'.2
  constructor
  · intro hgR
    have hmem : g * t * g⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ :=
      hgR.2.1 t (Subgroup.subset_closure (by simp))
    refine Set.mem_smul_set.mpr ⟨g * t * g⁻¹ * t⁻¹, hmem, ?_⟩
    have haux : t * (g * t * g⁻¹ * t⁻¹) = (g * t * g⁻¹ * t⁻¹) * t := by
      haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := p0_X_comm hc4
      exact congrArg Subtype.val (mul_comm'
        (⟨t, p0_t_mem_X t tau x₁ x₂⟩ : ↥(ctxX t tau x₁ x₂))
        (⟨_, p0_V_le_X t tau x₁ x₂ hmem⟩ : ↥(ctxX t tau x₁ x₂)))
    calc t * (g * t * g⁻¹ * t⁻¹) = (g * t * g⁻¹ * t⁻¹) * t := haux
      _ = g * t * g⁻¹ := by group
  · intro hgt
    obtain ⟨v, hv, hv_eq₀⟩ := Set.mem_smul_set.mp hgt
    have hv_eq : t * v = g * t * g⁻¹ := by rwa [smul_eq_mul] at hv_eq₀
    haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := p0_X_comm hc4
    have htv : t * v = v * t :=
      congrArg Subtype.val (mul_comm'
        (⟨t, p0_t_mem_X t tau x₁ x₂⟩ : ↥(ctxX t tau x₁ x₂))
        (⟨v, p0_V_le_X t tau x₁ x₂ hv⟩ : ↥(ctxX t tau x₁ x₂)))
    have htw : tau * v = v * tau := p0_tau_comm_mem_V hc4 hv
    refine ⟨hgM, ?_, ?_⟩
    · refine p0_commutator_mem_V_of_gens hc4 ?_ ?_ ?_ ?_
      · have heq : g * t * g⁻¹ * t⁻¹ = v := by
          rw [← hv_eq]; rw [htv]; group
        rw [heq]; exact hv
      · obtain ⟨w, hw, hw_eq₀⟩ := Set.mem_smul_set.mp (p0_tau_conj_mem hc hgM)
        have hw_eq : tau * w = g * tau * g⁻¹ := by rwa [smul_eq_mul] at hw_eq₀
        have htw' : tau * w = w * tau := p0_tau_comm_mem_V hc4 hw
        have heq : g * tau * g⁻¹ * tau⁻¹ = w := by
          rw [← hw_eq]; rw [htw']; group
        rw [heq]; exact hw
      · have hgy : g * x₁ ^ 2 * g⁻¹ = x₁ ^ 2 := by
          have h := hgC (x₁ ^ 2) (Subgroup.subset_closure (by simp))
          calc g * x₁ ^ 2 * g⁻¹ = (g * x₁ ^ 2) * g⁻¹ := by group
            _ = (x₁ ^ 2 * g) * g⁻¹ := by rw [← h]
            _ = x₁ ^ 2 := by group
        have heq : g * x₁ ^ 2 * g⁻¹ * (x₁ ^ 2)⁻¹ = 1 := by rw [hgy]; group
        rw [heq]; exact one_mem _
      · have hgz : g * (x₁ * x₂) ^ 2 * g⁻¹ = (x₁ * x₂) ^ 2 := by
          have h := hgC ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp))
          calc g * (x₁ * x₂) ^ 2 * g⁻¹ = (g * (x₁ * x₂) ^ 2) * g⁻¹ := by group
            _ = ((x₁ * x₂) ^ 2 * g) * g⁻¹ := by rw [← h]
            _ = (x₁ * x₂) ^ 2 := by group
        have heq : g * (x₁ * x₂) ^ 2 * g⁻¹ * ((x₁ * x₂) ^ 2)⁻¹ = 1 := by rw [hgz]; group
        rw [heq]; exact one_mem _
    · intro v hv
      have h := hgC v hv
      calc g * v * g⁻¹ = (g * v) * g⁻¹ := by group
        _ = (v * g) * g⁻¹ := by rw [← h]
        _ = v := by group

private theorem p0_mem_X_of_mem_R_centralizes (hc : Ctx8c t L S x₁ x₂ lam rho tau) {g : G}
    (hgR : g ∈ ctxR t tau x₁ x₂)
    (hgt : g * t * g⁻¹ * t⁻¹ = 1) (hgtau : g * tau * g⁻¹ * tau⁻¹ = 1) :
    g ∈ ctxX t tau x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := p0_c4 hc
  have hgO : g ∈ ctxO t tau x₁ x₂ := p0_R_le_O hc hgR
  have hgV : ∀ v ∈ fourGrp x₁ x₂, g * v * g⁻¹ = v := hgR.2.2
  have hgt_comm : g * t = t * g := p0_mul_comm_of_commutator_eq_one hgt
  have hgtau_comm : g * tau = tau * g := p0_mul_comm_of_commutator_eq_one hgtau
  have hgS : g ∈ S := by
    have hgU : g ∈ ctxU t tau x₁ x₂ lam := Subgroup.mem_sup_left hgO
    have hgC : g ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgt_comm
    have hmem : g ∈ ctxU t tau x₁ x₂ lam ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hgU, hgC⟩
    rwa [p0_cent_U_t hc] at hmem
  have hS_eq : S = Subgroup.zpowers t ⊔ m12Grp x₁ x₂ lam tau := by
    rw [hc.S_eq, hc4.l43]
  have htcent : ∀ s ∈ S, t * s = s * t := by
    intro s hs
    have htC : t ∈ Subgroup.centralizer (S : Set G) :=
      (Subgroup.mem_inf.mp (hc4.toCtx.center_ge (Subgroup.subset_closure (by simp)))).2
    exact (Subgroup.mem_centralizer_iff.mp htC s hs).symm
  have hnorm : ∀ k ∈ m12Grp x₁ x₂ lam tau, ∀ h ∈ Subgroup.zpowers t,
      k * h * k⁻¹ ∈ Subgroup.zpowers t := by
    intro k hk h hh
    have hkS : k ∈ S := by rw [hS_eq]; exact Subgroup.mem_sup_right hk
    have hkt : k * t = t * k := (htcent k hkS).symm
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hconj : k * t ^ i * k⁻¹ = t ^ i := by
      calc k * t ^ i * k⁻¹ = (k * t * k⁻¹) ^ i := by rw [conj_zpow]
        _ = t ^ i := by
              rw [show k * t * k⁻¹ = t by rw [hkt, mul_assoc, mul_inv_cancel, mul_one]]
    rw [hconj]
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
  obtain ⟨h, hh, k, hk, hg_eq⟩ :=
    (mem_sup_iff_of_normalizes (H := Subgroup.zpowers t) (K := m12Grp x₁ x₂ lam tau) hnorm).mp
      (by rwa [hS_eq] at hgS)
  have hhC : h ∈ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr (p0_t_mem_cent_V hc4)) hh
  have hgC : g ∈ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h := hgV v hv
    calc v * g = (g * v * g⁻¹) * g := by rw [h]
      _ = g * v := by group
  have hkC : k ∈ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hk_eq : k = h⁻¹ * g := by rw [hg_eq]; group
    rw [hk_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hhC) hgC
  have hkm : k ∈ m12Grp x₁ x₂ lam tau ⊓
      Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := ⟨hk, hkC⟩
  have hk_base : k ∈ baseGrp x₁ x₂ ⊔ Subgroup.zpowers tau := by
    rwa [M12Rel.centralizer_fourGrp (p0_m12Rel hc4)] at hkm
  have hgWτ : g ∈ ctxW t x₁ x₂ ⊔ Subgroup.zpowers tau := by
    have hmem : g ∈ Subgroup.zpowers t ⊔ (baseGrp x₁ x₂ ⊔ Subgroup.zpowers tau) := by
      rw [hg_eq]
      exact Subgroup.mul_mem_sup hh hk_base
    have heq : Subgroup.zpowers t ⊔ (baseGrp x₁ x₂ ⊔ Subgroup.zpowers tau) =
        ctxW t x₁ x₂ ⊔ Subgroup.zpowers tau := by
      rw [ctxW, hc4.l43, sup_assoc]
    rwa [heq] at hmem
  have htau_norm : tau ∈ Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hc4.toCtx.normal_W.2 tau hc4.tau_mem h hh
    · intro hh
      have h2 := hc4.toCtx.normal_W.2 tau hc4.tau_mem (tau * h * tau⁻¹) hh
      have htau2 : tau * tau = 1 := by simpa [pow_two] using hc4.l44.1
      have htauinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2
      have h3 : tau * (tau * h * tau⁻¹) * tau⁻¹ = h := by
        calc tau * (tau * h * tau⁻¹) * tau⁻¹ = (tau * tau) * h * (tau⁻¹ * tau⁻¹) := by group
          _ = h := by rw [htau2, htauinv, htau2, one_mul, mul_one]
      rwa [h3] at h2
  have hnormW : ∀ k ∈ Subgroup.zpowers tau, ∀ h ∈ ctxW t x₁ x₂,
      k * h * k⁻¹ ∈ ctxW t x₁ x₂ := by
    intro k hk h hh
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr htau_norm hk) h).mp hh
  obtain ⟨w, hw, e, he, hg_eq2⟩ :=
    (mem_sup_iff_of_normalizes (H := ctxW t x₁ x₂) (K := Subgroup.zpowers tau) hnormW).mp hgWτ
  have he_tau : e * tau = tau * e :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl) he)
  have hw_tau : w * tau = tau * w := by
    have htau2 : tau * tau = 1 := by simpa [pow_two] using hc4.l44.1
    have htauinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2
    have he_eq : e⁻¹ * tau = tau * e⁻¹ := by
      have h := congrArg Inv.inv he_tau
      simpa [mul_inv_rev, htauinv] using h.symm
    have hw_eq : w = g * e⁻¹ := by rw [hg_eq2]; group
    rw [hw_eq]
    calc g * e⁻¹ * tau = g * (e⁻¹ * tau) := by group
      _ = g * (tau * e⁻¹) := by rw [he_eq]
      _ = g * tau * e⁻¹ := by group
      _ = tau * g * e⁻¹ := by rw [hgtau_comm]
      _ = tau * (g * e⁻¹) := by group
  have hw_inf : w ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({tau} : Set G) :=
    ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr hw_tau⟩
  have hw_tzv : w ∈ Subgroup.zpowers t ⊔ fourGrp x₁ x₂ := p0_cent_W_tau_le hc4 hw_inf
  have hwX : w ∈ ctxX t tau x₁ x₂ := (sup_le
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    (p0_V_le_X t tau x₁ x₂)) hw_tzv
  have heX : e ∈ ctxX t tau x₁ x₂ :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) he
  rw [hg_eq2]
  exact Subgroup.mul_mem _ hwX heX

theorem p0_exists_hom (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    ∃ φ : ↥(ctxR t tau x₁ x₂) →* ↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂),
      ∀ g : ↥(ctxR t tau x₁ x₂), φ g = 1 → (g : G) ∈ ctxX t tau x₁ x₂ := by
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := (hc.wreath.fourGrp_eq_omega).2.1.1
  refine ⟨MonoidHom.mk' (fun g : ↥(ctxR t tau x₁ x₂) =>
      (⟨(g : G) * t * (g : G)⁻¹ * t⁻¹, g.2.2.1 t htX⟩,
       ⟨(g : G) * tau * (g : G)⁻¹ * tau⁻¹, g.2.2.1 tau htauX⟩)) ?_, ?_⟩
  · intro g h
    apply Prod.ext
    · apply Subtype.ext
      have hfix : (g : G) * ((h : G) * t * (h : G)⁻¹ * t⁻¹) * (g : G)⁻¹ =
          (h : G) * t * (h : G)⁻¹ * t⁻¹ :=
        g.2.2.2 _ (h.2.2.1 t htX)
      show (g : G) * (h : G) * t * ((g : G) * (h : G))⁻¹ * t⁻¹ =
          ((g : G) * t * (g : G)⁻¹ * t⁻¹) * ((h : G) * t * (h : G)⁻¹ * t⁻¹)
      rw [show (g : G) * (h : G) * t * ((g : G) * (h : G))⁻¹ * t⁻¹ =
          ((g : G) * ((h : G) * t * (h : G)⁻¹ * t⁻¹) * (g : G)⁻¹) *
            ((g : G) * t * (g : G)⁻¹ * t⁻¹) by group, hfix]
      exact congrArg Subtype.val (mul_comm'
        (⟨_, h.2.2.1 t htX⟩ : ↥(fourGrp x₁ x₂))
        (⟨_, g.2.2.1 t htX⟩ : ↥(fourGrp x₁ x₂)))
    · apply Subtype.ext
      have hfix : (g : G) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹) * (g : G)⁻¹ =
          (h : G) * tau * (h : G)⁻¹ * tau⁻¹ :=
        g.2.2.2 _ (h.2.2.1 tau htauX)
      show (g : G) * (h : G) * tau * ((g : G) * (h : G))⁻¹ * tau⁻¹ =
          ((g : G) * tau * (g : G)⁻¹ * tau⁻¹) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹)
      rw [show (g : G) * (h : G) * tau * ((g : G) * (h : G))⁻¹ * tau⁻¹ =
          ((g : G) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹) * (g : G)⁻¹) *
            ((g : G) * tau * (g : G)⁻¹ * tau⁻¹) by group, hfix]
      exact congrArg Subtype.val (mul_comm'
        (⟨_, h.2.2.1 tau htauX⟩ : ↥(fourGrp x₁ x₂))
        (⟨_, g.2.2.1 tau htauX⟩ : ↥(fourGrp x₁ x₂)))
  · intro g hg1
    have hct1 : (⟨(g : G) * t * (g : G)⁻¹ * t⁻¹, g.2.2.1 t htX⟩ :
        ↥(fourGrp x₁ x₂)) = 1 := by
      simpa using congrArg Prod.fst hg1
    have hctau1 : (⟨(g : G) * tau * (g : G)⁻¹ * tau⁻¹, g.2.2.1 tau htauX⟩ :
        ↥(fourGrp x₁ x₂)) = 1 := by
      simpa using congrArg Prod.snd hg1
    have hgt : (g : G) * t * (g : G)⁻¹ * t⁻¹ = 1 := by
      have := congrArg Subtype.val hct1
      simpa using this
    have hgtau : (g : G) * tau * (g : G)⁻¹ * tau⁻¹ = 1 := by
      have := congrArg Subtype.val hctau1
      simpa using this
    exact p0_mem_X_of_mem_R_centralizes hc g.2 hgt hgtau

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
