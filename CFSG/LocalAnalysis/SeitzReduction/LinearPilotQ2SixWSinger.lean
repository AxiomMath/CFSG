module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBX

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix

@[expose] def singerFive : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]

@[expose] def singerFiveInv : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 0, 0, 0, 0]

theorem singerFive_mul_singerFiveInv : singerFive * singerFiveInv = 1 := by
  decide +kernel

theorem singerFiveInv_mul_singerFive : singerFiveInv * singerFive = 1 := by
  decide +kernel

theorem singerFive_mulVec_e0 :
    singerFive *ᵥ (Pi.single 0 1 : Fin 5 → ZMod 2) = Pi.single 1 1 := by
  decide +kernel

theorem singerFive_mulVec_e1 :
    singerFive *ᵥ (Pi.single 1 1 : Fin 5 → ZMod 2) = Pi.single 2 1 := by
  decide +kernel

theorem singerFive_mulVec_e2 :
    singerFive *ᵥ (Pi.single 2 1 : Fin 5 → ZMod 2) = Pi.single 3 1 := by
  decide +kernel

theorem singerFive_mulVec_e3 :
    singerFive *ᵥ (Pi.single 3 1 : Fin 5 → ZMod 2) = Pi.single 4 1 := by
  decide +kernel

theorem singerFive_mulVec_e4 :
    singerFive *ᵥ (Pi.single 4 1 : Fin 5 → ZMod 2) = Pi.single 0 1 + Pi.single 2 1 := by
  decide +kernel

theorem singer_system_five (a b c d : Fin 5 → ZMod 2)
    (h1 : singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ a))) =
      d + singerFive *ᵥ (singerFive *ᵥ b))
    (h2 : singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ b)) = c + singerFive *ᵥ (singerFive *ᵥ a))
    (h3 : singerFive *ᵥ (singerFive *ᵥ c) = b) (h4 : singerFive *ᵥ d = a + singerFive *ᵥ a) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  subst h3
  have hd : d = singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ a))) +
      singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ c))) := by
    rw [h1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  subst hd
  have key : ∀ a c : Fin 5 → ZMod 2,
      singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ c)))) =
        c + singerFive *ᵥ (singerFive *ᵥ a) →
      singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ a))) +
        singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ c)))) =
        a + singerFive *ᵥ a → a = 0 ∧ c = 0 := by
    decide +kernel
  obtain ⟨ha, hc⟩ := key a c h2 h4
  subst ha hc
  simp

section Construction

variable {G : Type*} [Group G] {V : Subgroup G} {t : G}

theorem pow_two_conj_eq_five {b : ElemBasis V 5} {y : G}
    (hy : ∀ x, y * b x * y⁻¹ = b (singerFive *ᵥ x)) (z : Fin 5 → ZMod 2) :
    y ^ 2 * b z * (y ^ 2)⁻¹ = b (singerFive *ᵥ (singerFive *ᵥ z)) := by
  have h2 : y ^ 2 = y * y := by rw [pow_succ, pow_one]
  calc y ^ 2 * b z * (y ^ 2)⁻¹ = y * (y * b z * y⁻¹) * y⁻¹ := by rw [h2]; group
    _ = _ := by rw [hy, hy]

theorem pow_five_conj_eq_five {b : ElemBasis V 5} {y : G}
    (hy : ∀ x, y * b x * y⁻¹ = b (singerFive *ᵥ x)) (z : Fin 5 → ZMod 2) :
    y ^ 5 * b z * (y ^ 5)⁻¹ =
      b (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ (singerFive *ᵥ z))))) := by
  have h5 : y ^ 5 = y * y * y * y * y := by
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  calc y ^ 5 * b z * (y ^ 5)⁻¹ =
        y * (y * (y * (y * (y * b z * y⁻¹) * y⁻¹) * y⁻¹) * y⁻¹) * y⁻¹ := by rw [h5]; group
    _ = _ := by rw [hy, hy, hy, hy, hy]

theorem exists_singer_base_five (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    (b : ElemBasis V 5) {y : G} (hyV : y ∈ normalizer (V : Set G)) (hyt : y * t = t * y)
    (hy : ∀ x, y * b x * y⁻¹ = b (singerFive *ᵥ x)) :
    ∃ p ∈ seitzRadX V t, t * p * t⁻¹ * p⁻¹ = b (Pi.single 0 1) ∧
      y ^ 5 * p * (y ^ 5)⁻¹ * (p * (y ^ 2 * p * (y ^ 2)⁻¹))⁻¹ ∈ V := by
  obtain ⟨x₀, hx₀, hφx₀⟩ := hsurj (b (Pi.single 0 1)) (b.mem _)
  have hy5V : y ^ 5 ∈ normalizer (V : Set G) := pow_mem hyV 5
  have hy2V : y ^ 2 ∈ normalizer (V : Set G) := pow_mem hyV 2
  have hy5t : y ^ 5 * t = t * y ^ 5 := ((Commute.pow_left hyt 5) : _)
  have hy2t : y ^ 2 * t = t * y ^ 2 := ((Commute.pow_left hyt 2) : _)
  have hx₅ : y ^ 5 * x₀ * (y ^ 5)⁻¹ ∈ seitzRadX V t :=
    conj_mem_seitzRadX_of_commute ht htV hy5V hy5t hx₀
  have hx₂ : y ^ 2 * x₀ * (y ^ 2)⁻¹ ∈ seitzRadX V t :=
    conj_mem_seitzRadX_of_commute ht htV hy2V hy2t hx₀
  have hφx₅ : t * (y ^ 5 * x₀ * (y ^ 5)⁻¹) * t⁻¹ * (y ^ 5 * x₀ * (y ^ 5)⁻¹)⁻¹ =
      b (Pi.single 0 1) * b (Pi.single 2 1) := by
    rw [tcomm_conj_of_commute hy5t, hφx₀, pow_five_conj_eq_five hy, singerFive_mulVec_e0,
      singerFive_mulVec_e1, singerFive_mulVec_e2, singerFive_mulVec_e3, singerFive_mulVec_e4,
      b.map_add]
  have hφx₂ : t * (y ^ 2 * x₀ * (y ^ 2)⁻¹) * t⁻¹ * (y ^ 2 * x₀ * (y ^ 2)⁻¹)⁻¹ =
      b (Pi.single 2 1) := by
    rw [tcomm_conj_of_commute hy2t, hφx₀, pow_two_conj_eq_five hy, singerFive_mulVec_e0,
      singerFive_mulVec_e1]
  set d := y ^ 5 * x₀ * (y ^ 5)⁻¹ * (x₀ * (y ^ 2 * x₀ * (y ^ 2)⁻¹))⁻¹ with hd
  have hdX : d ∈ seitzRadX V t := mul_mem hx₅ (inv_mem (mul_mem hx₀ hx₂))
  have hφd : t * d * t⁻¹ * d⁻¹ = 1 := by
    rw [hd, tcomm_mul_of_mem_seitzRadX ht htV htnV hx₅ (inv_mem (mul_mem hx₀ hx₂)),
      tcomm_inv_of_mem_seitzRadX ht htV htnV (mul_mem hx₀ hx₂),
      tcomm_mul_of_mem_seitzRadX ht htV htnV hx₀ hx₂, hφx₅, hφx₀, hφx₂, mul_inv_cancel]
  have hdU : d ∈ V ⊔ zpowers t := hker ⟨(mem_seitzRadX.1 hdX).1, tcomm_eq_one_iff.1 hφd⟩
  rcases (mem_sup_zpowers_iff ht (mem_normalizer_of_forall_commute htV)).1 hdU with hdV | hdtV
  · exact ⟨x₀, hx₀, hφx₀, hdV⟩
  · refine ⟨x₀ * t, mul_mem hx₀ (mem_seitzRadX_self hV2 ht htV hker), ?_, ?_⟩
    · rw [tcomm_mul_of_mem_seitzRadX ht htV htnV hx₀ (mem_seitzRadX_self hV2 ht htV hker), hφx₀,
        show t * t * t⁻¹ * t⁻¹ = (1 : G) by group, mul_one]
    · have hY : y ^ 5 * (x₀ * t) * (y ^ 5)⁻¹ = (y ^ 5 * x₀ * (y ^ 5)⁻¹) * t := by
        calc y ^ 5 * (x₀ * t) * (y ^ 5)⁻¹ = y ^ 5 * x₀ * (y ^ 5)⁻¹ * (y ^ 5 * t) * (y ^ 5)⁻¹ := by
              group
          _ = _ := by rw [hy5t]; group
      have hY2 : y ^ 2 * (x₀ * t) * (y ^ 2)⁻¹ = (y ^ 2 * x₀ * (y ^ 2)⁻¹) * t := by
        calc y ^ 2 * (x₀ * t) * (y ^ 2)⁻¹ = y ^ 2 * x₀ * (y ^ 2)⁻¹ * (y ^ 2 * t) * (y ^ 2)⁻¹ := by
              group
          _ = _ := by rw [hy2t]; group
      have heq : y ^ 5 * (x₀ * t) * (y ^ 5)⁻¹ * (x₀ * t * (y ^ 2 * (x₀ * t) * (y ^ 2)⁻¹))⁻¹ =
          (d * t) * (t * x₀ * t⁻¹ * x₀⁻¹) := by
        rw [hY, hY2, hd]
        calc y ^ 5 * x₀ * (y ^ 5)⁻¹ * t * (x₀ * t * (y ^ 2 * x₀ * (y ^ 2)⁻¹ * t))⁻¹ =
            y ^ 5 * x₀ * (y ^ 5)⁻¹ * (y ^ 2 * x₀ * (y ^ 2)⁻¹)⁻¹ * t⁻¹ * x₀⁻¹ := by group
          _ = y ^ 5 * x₀ * (y ^ 5)⁻¹ * (y ^ 2 * x₀ * (y ^ 2)⁻¹)⁻¹ * x₀⁻¹ * (t * t) * x₀ * t⁻¹ *
              x₀⁻¹ := by
            rw [ht]; group
          _ = _ := by group
      rw [heq]
      exact mul_mem hdtV (tcomm_mem_of_mem_seitzRadX ht htV htnV hx₀)

theorem exists_abelian_of_singer_five (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    (hcomm : ∀ x ∈ seitzRadX V t, ∀ y ∈ seitzRadX V t, x * y * x⁻¹ * y⁻¹ ∈ V)
    (b : ElemBasis V 5) {y : G} (hyV : y ∈ normalizer (V : Set G)) (hyt : y * t = t * y)
    (hy : ∀ x, y * b x * y⁻¹ = b (singerFive *ᵥ x)) :
    ∃ W₁ : Subgroup G, W₁ ≤ seitzRadX V t ∧ V ≤ W₁ ∧ (∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v) ∧
      t ∉ W₁ ∧ ∀ v ∈ V, ∃ w ∈ W₁, t * w * t⁻¹ * w⁻¹ = v := by
  obtain ⟨p, hpX, hφp, hp5⟩ := exists_singer_base_five hV2 ht htV htnV hker hsurj b hyV hyt hy
  set P : ℕ → G := fun k => y ^ k * p * (y ^ k)⁻¹ with hPdef
  have hPX : ∀ k, P k ∈ seitzRadX V t := fun k =>
    conj_mem_seitzRadX_of_commute ht htV (pow_mem hyV k) (Commute.pow_left hyt k) hpX
  have hPs : ∀ k, P (k + 1) = y * P k * y⁻¹ := fun k => by
    simp only [hPdef, pow_succ']
    group
  have hP0 : P 0 = p := by simp [hPdef]
  have hφP : ∀ k, t * P (k + 1) * t⁻¹ * (P (k + 1))⁻¹ = y * (t * P k * t⁻¹ * (P k)⁻¹) * y⁻¹ :=
    fun k => by
      rw [hPs]
      exact tcomm_conj_of_commute hyt _
  have hφ0 : t * P 0 * t⁻¹ * (P 0)⁻¹ = b (Pi.single 0 1) := by rw [hP0]; exact hφp
  have hφ1 : t * P 1 * t⁻¹ * (P 1)⁻¹ = b (Pi.single 1 1) := by
    rw [hφP 0, hφ0, hy, singerFive_mulVec_e0]
  have hφ2 : t * P 2 * t⁻¹ * (P 2)⁻¹ = b (Pi.single 2 1) := by
    rw [hφP 1, hφ1, hy, singerFive_mulVec_e1]
  have hφ3 : t * P 3 * t⁻¹ * (P 3)⁻¹ = b (Pi.single 3 1) := by
    rw [hφP 2, hφ2, hy, singerFive_mulVec_e2]
  have hφ4 : t * P 4 * t⁻¹ * (P 4)⁻¹ = b (Pi.single 4 1) := by
    rw [hφP 3, hφ3, hy, singerFive_mulVec_e3]
  have hu : P 5 * (P 0 * P 2)⁻¹ ∈ V := by
    rw [hP0]
    exact hp5
  have hcV : ∀ i j, P i * P j * (P i)⁻¹ * (P j)⁻¹ ∈ V := fun i j =>
    hcomm _ (hPX i) _ (hPX j)
  choose g hg using fun i j => b.exists_eq (hcV i j)
  have hgy : ∀ i j, singerFive *ᵥ g i j = g (i + 1) (j + 1) := fun i j => by
    apply b.injective
    rw [← hy, hg, hg, hPs, hPs]
    exact xcomm_conj y (P i) (P j)
  have hgd : ∀ i, g i i = 0 := fun i => by
    apply b.injective
    rw [hg, b.map_zero]
    group
  have hgs : ∀ i j, g j i = g i j := fun i j => by
    apply b.injective
    rw [hg, hg, xcomm_swap]
    exact inv_eq_of_mul_eq_one_right (hV2 _ (hcV i j))
  have hg5 : ∀ k, g k 5 = g k 0 + g k 2 := fun k => by
    apply b.injective
    rw [b.map_add, hg, hg, hg]
    set u := P 5 * (P 0 * P 2)⁻¹ with hudef
    have hP5 : P 5 = u * (P 0 * P 2) := by rw [hudef]; group
    have hku : P k * u * (P k)⁻¹ * u⁻¹ = 1 := by
      rw [mul_comm_of_mem_seitzRadX (hPX k) hu]
      group
    rw [hP5, xcomm_mul_right (mul_comm_of_forall_mul_self_eq_one hV2 hu
      (hcomm _ (hPX k) _ (mul_mem (hPX 0) (hPX 2)))), hku, one_mul,
      xcomm_mul_right (mul_comm_of_mem_seitzRadX (hPX 0) (hcV k 2))]
  have e01 : singerFive *ᵥ g 0 1 = g 1 2 := hgy 0 1
  have e12 : singerFive *ᵥ g 1 2 = g 2 3 := hgy 1 2
  have e23 : singerFive *ᵥ g 2 3 = g 3 4 := hgy 2 3
  have e34 : singerFive *ᵥ g 3 4 = g 0 4 + g 2 4 := by rw [hgy 3 4, hg5 4, hgs 0 4, hgs 2 4]
  have e02 : singerFive *ᵥ g 0 2 = g 1 3 := hgy 0 2
  have e13 : singerFive *ᵥ g 1 3 = g 2 4 := hgy 1 3
  have e24 : singerFive *ᵥ g 2 4 = g 0 3 + g 2 3 := by rw [hgy 2 4, hg5 3, hgs 0 3, hgs 2 3]
  have e03 : singerFive *ᵥ g 0 3 = g 1 4 := hgy 0 3
  have e14 : singerFive *ᵥ g 1 4 = g 0 2 := by rw [hgy 1 4, hg5 2, hgd, add_zero, hgs 0 2]
  have e04 : singerFive *ᵥ g 0 4 = g 0 1 + g 1 2 := by rw [hgy 0 4, hg5 1, hgs 0 1]
  obtain ⟨h01, h02, h03, h04⟩ := singer_system_five (g 0 1) (g 0 2) (g 0 3) (g 0 4)
    (by rw [e01, e12, e23, e34, e02, e13]) (by rw [e02, e13, e24, e01, e12]) (by rw [e03, e14])
    (by rw [e04, e01])
  have h12 : g 1 2 = 0 := by rw [← e01, h01, Matrix.mulVec_zero]
  have h23 : g 2 3 = 0 := by rw [← e12, h12, Matrix.mulVec_zero]
  have h34 : g 3 4 = 0 := by rw [← e23, h23, Matrix.mulVec_zero]
  have h13 : g 1 3 = 0 := by rw [← e02, h02, Matrix.mulVec_zero]
  have h24 : g 2 4 = 0 := by rw [← e13, h13, Matrix.mulVec_zero]
  have h14 : g 1 4 = 0 := by rw [← e03, h03, Matrix.mulVec_zero]
  have hz : ∀ i j : ℕ, i < 5 → j < 5 → g i j = 0 := by
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      first | exact hgd _ | assumption | (rwa [hgs])
  have hPc : ∀ i j : ℕ, i < 5 → j < 5 → P i * P j = P j * P i := fun i j hi hj => by
    have h := hg i j
    rw [hz i j hi hj, b.map_zero] at h
    have h' : P i * P j * (P i)⁻¹ * (P j)⁻¹ * (P j * P i) = P j * P i := by rw [← h, one_mul]
    rw [← h']
    group
  set S : Set G := (V : Set G) ∪ Set.range (fun i : Fin 5 => P i) with hSdef
  have hSc : ∀ a ∈ S, ∀ a' ∈ S, a * a' = a' * a := by
    rintro a (ha | ⟨i, rfl⟩) a' (ha' | ⟨j, rfl⟩)
    · exact mul_comm_of_forall_mul_self_eq_one hV2 ha ha'
    · exact (mul_comm_of_mem_seitzRadX (hPX j) ha).symm
    · exact mul_comm_of_mem_seitzRadX (hPX i) ha'
    · exact hPc i j i.2 j.2
  set W₁ := closure S with hW₁def
  have hWc : W₁ ≤ centralizer (W₁ : Set G) := by
    rw [hW₁def, centralizer_closure]
    exact (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun a' ha' => hSc a' ha' a ha
  have hab : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    ((mem_centralizer_iff.1 (hWc hv)) w hw).symm
  have hVX : V ≤ seitzRadX V t := fun v hv => by
    have h : v ∈ V ⊔ zpowers t := mem_sup_left hv
    rw [← seitzRadX_inf_centralizer_eq hV2 ht htV hker] at h
    exact (Subgroup.mem_inf.1 h).1
  have hW₁X : W₁ ≤ seitzRadX V t := by
    rw [hW₁def, closure_le]
    rintro a (ha | ⟨i, rfl⟩)
    · exact hVX ha
    · exact hPX i
  have hVW₁ : V ≤ W₁ := fun v hv => subset_closure (Or.inl hv)
  have hPW : ∀ i : Fin 5, P i ∈ W₁ := fun i => subset_closure (Or.inr ⟨i, rfl⟩)
  refine ⟨W₁, hW₁X, hVW₁, hab, fun htW => ?_, ?_⟩
  ·
    have h := hab t htW (P 0) (hPW 0)
    have h1 : b (Pi.single 0 1) = 1 := by
      rw [← hφ0, h]
      group
    exact absurd (b.eq_one_iff.1 h1) (by decide)
  ·
    let H : Subgroup G :=
      { carrier := {v | ∃ w ∈ W₁, t * w * t⁻¹ * w⁻¹ = v}
        mul_mem' := by
          rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
          exact ⟨w * w', mul_mem hw hw',
            tcomm_mul_of_mem_seitzRadX ht htV htnV (hW₁X hw) (hW₁X hw')⟩
        one_mem' := ⟨1, one_mem _, by group⟩
        inv_mem' := by
          rintro _ ⟨w, hw, rfl⟩
          exact ⟨w⁻¹, inv_mem hw, tcomm_inv_of_mem_seitzRadX ht htV htnV (hW₁X hw)⟩ }
    have hbH : ∀ i, b (Pi.single i 1) ∈ H := by
      intro i
      fin_cases i
      · exact ⟨P 0, hPW 0, hφ0⟩
      · exact ⟨P 1, hPW 1, hφ1⟩
      · exact ⟨P 2, hPW 2, hφ2⟩
      · exact ⟨P 3, hPW 3, hφ3⟩
      · exact ⟨P 4, hPW 4, hφ4⟩
    intro v hv
    obtain ⟨z, rfl⟩ := b.exists_eq hv
    exact b.mem_of_forall_single hbH z

theorem eq_of_le_seitzRadX_of_card_five [Finite G] (hVc : Nat.card V = 2 ^ 5)
    (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    {A B : Subgroup G} (hAX : A ≤ seitzRadX V t) (hBX : B ≤ seitzRadX V t)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hBc : ∀ a ∈ B, ∀ a' ∈ B, a * a' = a' * a)
    (hA : Nat.card A = 2 ^ 10) (hB : Nat.card B = 2 ^ 10) : A = B := by
  have hU : Nat.card (V ⊔ zpowers t : Subgroup G) = 2 ^ 6 := by
    rw [card_sup_zpowers_eq ht (mem_normalizer_of_forall_commute htV) htnV, hVc]
    norm_num
  have hXc : Nat.card (seitzRadX V t) = 2 ^ 11 := by
    rw [card_seitzRadX hV2 ht htV htnV hker hsurj, hU, hVc]
    norm_num
  have hA'c : Nat.card (A.subgroupOf (seitzRadX V t)) = 2 ^ 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv, hA]
  have hB'c : Nat.card (B.subgroupOf (seitzRadX V t)) = 2 ^ 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv, hB]
  have hA'i : (A.subgroupOf (seitzRadX V t)).index = 2 := by
    have h := (A.subgroupOf (seitzRadX V t)).card_mul_index
    rw [hA'c, hXc] at h
    omega
  have hB'i : (B.subgroupOf (seitzRadX V t)).index = 2 := by
    have h := (B.subgroupOf (seitzRadX V t)).card_mul_index
    rw [hB'c, hXc] at h
    omega
  have htX : t ∈ seitzRadX V t := mem_seitzRadX_self hV2 ht htV hker
  have hct : Nat.card (centralizer ({(⟨t, htX⟩ : seitzRadX V t)} : Set (seitzRadX V t))) ≤
      2 ^ 6 := by
    have hle : (centralizer ({(⟨t, htX⟩ : seitzRadX V t)} : Set (seitzRadX V t))).map
        (seitzRadX V t).subtype ≤ V ⊔ zpowers t := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← seitzRadX_inf_centralizer_eq hV2 ht htV hker]
      exact ⟨x.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))⟩
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (seitzRadX V t).subtype_injective, hU] at h1
  have hinf : 2 ^ 9 ≤ Nat.card (A.subgroupOf (seitzRadX V t) ⊓ B.subgroupOf (seitzRadX V t) :
      Subgroup (seitzRadX V t)) := by
    have h1 := (A.subgroupOf (seitzRadX V t) ⊓ B.subgroupOf (seitzRadX V t)).card_mul_index
    have h2 : (A.subgroupOf (seitzRadX V t) ⊓ B.subgroupOf (seitzRadX V t)).index ≤ 4 :=
      (Subgroup.index_inf_le).trans (by rw [hA'i, hB'i])
    rw [hXc] at h1
    have h3 := Nat.mul_le_mul_left
      (Nat.card (A.subgroupOf (seitzRadX V t) ⊓ B.subgroupOf (seitzRadX V t) :
        Subgroup (seitzRadX V t))) h2
    omega
  have heq := eq_of_index_eq_two_of_commute hA'i hB'i
    (fun a ha a' ha' => Subtype.ext (hAc _ ha _ ha'))
    (fun a ha a' ha' => Subtype.ext (hBc _ ha _ ha'))
    (t := ⟨t, htX⟩) (by omega)
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.2 hAX, inf_eq_left.2 hBX] at heq

end Construction

theorem exists_wOne_of_seitzRadX_five {G : Type*} [Group G] [Finite G] {V L₁ : Subgroup G}
    {t : G} (hVc : Nat.card V = 2 ^ 5) (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    (hsq : ∀ x ∈ seitzRadX V t, x * x ∈ V)
    (hcomm : ∀ x ∈ seitzRadX V t, ∀ y ∈ seitzRadX V t, x * y * x⁻¹ * y⁻¹ ∈ V)
    (hL₁t : L₁ ≤ centralizer ({t} : Set G)) (hL₁V : L₁ ≤ normalizer (V : Set G))
    (haut : ∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹) :
    ∃ W₁ : Subgroup G, W₁ ≤ seitzRadX V t ∧ Nat.card W₁ = 2 ^ 10 ∧
      (∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v) ∧ (∀ w ∈ W₁, w * w ∈ V) ∧
      W₁ ⊓ centralizer ({t} : Set G) = V ∧ t ∈ normalizer (W₁ : Set G) ∧
      L₁ ≤ normalizer (W₁ : Set G) := by
  obtain ⟨b⟩ := exists_elemBasis hVc hV2
  obtain ⟨y, hyL, hy⟩ := b.exists_conj_eq_of_forall_mulEquiv haut singerFive singerFiveInv
    singerFive_mul_singerFiveInv singerFiveInv_mul_singerFive
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 (hL₁t hyL)
  obtain ⟨W₁, hW₁X, hVW₁, hab, htW₁, honto⟩ :=
    exists_abelian_of_singer_five hV2 ht htV htnV hker hsurj hcomm b (hL₁V hyL) hyt hy
  obtain ⟨hcard, hinf⟩ :=
    card_and_inf_centralizer_of_le_seitzRadX hV2 ht htV htnV hker hW₁X hVW₁ htW₁ honto
  have hcard' : Nat.card W₁ = 2 ^ 10 := by
    rw [hcard, hVc]
    norm_num
  refine ⟨W₁, hW₁X, hcard', hab, fun w hw => hsq w (hW₁X hw), hinf, ?_, ?_⟩
  ·
    have key : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ := fun w hw => by
      have h := mul_mem (hVW₁ (tcomm_mem_of_mem_seitzRadX ht htV htnV (hW₁X hw))) hw
      rwa [show t * w * t⁻¹ * w⁻¹ * w = t * w * t⁻¹ by group] at h
    rw [mem_normalizer_iff]
    intro w
    refine ⟨key w, fun h => ?_⟩
    have h2 := key _ h
    rwa [show t * (t * w * t⁻¹) * t⁻¹ = (t * t) * w * (t * t)⁻¹ by group, ht, one_mul, inv_one,
      mul_one] at h2
  ·
    intro l hl
    have hlt : l * t = t * l := mem_centralizer_singleton_iff.1 (hL₁t hl)
    have hW₂X : W₁.map (MulAut.conj l).toMonoidHom ≤ seitzRadX V t := by
      rintro _ ⟨w, hw, rfl⟩
      exact conj_mem_seitzRadX_of_commute ht htV (hL₁V hl) hlt (hW₁X hw)
    have hW₂c : Nat.card (W₁.map (MulAut.conj l).toMonoidHom) = 2 ^ 10 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hcard']
    have hW₂ab : ∀ v ∈ W₁.map (MulAut.conj l).toMonoidHom,
        ∀ w ∈ W₁.map (MulAut.conj l).toMonoidHom, v * w = w * v := by
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc l * v * l⁻¹ * (l * w * l⁻¹) = l * (v * w) * l⁻¹ := by group
        _ = l * (w * v) * l⁻¹ := by rw [hab v hv w hw]
        _ = l * w * l⁻¹ * (l * v * l⁻¹) := by group
    have heq := eq_of_le_seitzRadX_of_card_five hVc hV2 ht htV htnV hker hsurj hW₁X hW₂X hab
      hW₂ab hcard' hW₂c
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [heq]
      exact ⟨w, hw, rfl⟩
    · intro hw
      rw [heq] at hw
      obtain ⟨w', hw', h⟩ := hw
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      have h' : w' = w := by
        have := congrArg (fun g => l⁻¹ * g * l) h
        simpa only [show ∀ g : G, l⁻¹ * (l * g * l⁻¹) * l = g from fun g => by group] using this
      rwa [← h']

theorem wOneOfXCardInput_five : WOneOfXCardInput 5 :=
  fun _ _ _ _ _ _ hVc hV2 ht htV htnV hker hsurj hsq hcomm hL₁t hL₁V haut _ =>
    exists_wOne_of_seitzRadX_five hVc hV2 ht htV htnV hker hsurj hsq hcomm hL₁t hL₁V haut

end CFSG.SeitzReduction.LinearPilot
