module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWAOrbit
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveAbelian
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBBasis

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix

@[expose] def singerC : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

@[expose] def singerCInv : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

theorem singerC_mul_singerCInv : singerC * singerCInv = 1 := by
  decide +kernel

theorem singerCInv_mul_singerC : singerCInv * singerC = 1 := by
  decide +kernel

theorem singerC_mulVec_e0 : singerC *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) = Pi.single 1 1 := by
  decide +kernel

theorem singerC_mulVec_e1 : singerC *ᵥ (Pi.single 1 1 : Fin 4 → ZMod 2) = Pi.single 2 1 := by
  decide +kernel

theorem singerC_mulVec_e2 : singerC *ᵥ (Pi.single 2 1 : Fin 4 → ZMod 2) = Pi.single 3 1 := by
  decide +kernel

theorem singerC_mulVec_e3 :
    singerC *ᵥ (Pi.single 3 1 : Fin 4 → ZMod 2) = Pi.single 0 1 + Pi.single 1 1 := by
  decide +kernel

theorem singer_system (q r s : Fin 4 → ZMod 2)
    (h1 : singerC *ᵥ (singerC *ᵥ (singerC *ᵥ (singerC *ᵥ q))) = q + s)
    (h2 : singerC *ᵥ r = s) (h3 : singerC *ᵥ s = r + singerC *ᵥ (singerC *ᵥ q)) :
    q = 0 ∧ r = 0 ∧ s = 0 := by
  subst h2
  have key : ∀ q r : Fin 4 → ZMod 2,
      singerC *ᵥ (singerC *ᵥ (singerC *ᵥ (singerC *ᵥ q))) = q + singerC *ᵥ r →
      singerC *ᵥ (singerC *ᵥ r) = r + singerC *ᵥ (singerC *ᵥ q) → q = 0 ∧ r = 0 := by
    decide +kernel
  obtain ⟨hq, hr⟩ := key q r h1 h3
  subst hq hr
  exact ⟨rfl, rfl, by rw [Matrix.mulVec_zero]⟩

section Commutators

variable {G : Type*} [Group G]

theorem xcomm_mul_right {a b c : G}
    (h : b * (a * c * a⁻¹ * c⁻¹) = (a * c * a⁻¹ * c⁻¹) * b) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹)) * b⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * ((a * c * a⁻¹ * c⁻¹) * b) * b⁻¹ := by rw [h]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group

theorem xcomm_swap (a b : G) : b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by
  group

theorem xcomm_conj (y a b : G) :
    y * (a * b * a⁻¹ * b⁻¹) * y⁻¹ =
      (y * a * y⁻¹) * (y * b * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * b * y⁻¹)⁻¹ := by
  group

end Commutators

theorem ElemBasis.mem_of_forall_single {G : Type*} [Group G] {V : Subgroup G} {m : ℕ}
    (b : ElemBasis V m) {H : Subgroup G} (hH : ∀ i, b (Pi.single i 1) ∈ H)
    (z : Fin m → ZMod 2) : b z ∈ H := by
  classical
  have hsingle : ∀ i (c : ZMod 2), b (Pi.single i c) ∈ H := by
    intro i c
    rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl
    · rw [Pi.single_zero, b.map_zero]
      exact one_mem H
    · exact hH i
  have hs : ∀ s : Finset (Fin m), b (∑ i ∈ s, Pi.single i (z i)) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, b.map_zero]
      exact one_mem H
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, b.map_add]
      exact mul_mem (hsingle a (z a)) ih
  have h := hs Finset.univ
  rwa [Finset.univ_sum_single] at h

section Construction

variable {G : Type*} [Group G] {V : Subgroup G} {t : G}

theorem conj_mem_seitzRadX_of_commute (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) {l : G}
    (hlV : l ∈ normalizer (V : Set G)) (hlt : l * t = t * l) {x : G} (hx : x ∈ seitzRadX V t) :
    l * x * l⁻¹ ∈ seitzRadX V t := by
  obtain ⟨hxC, hxN⟩ := mem_seitzRadX.1 hx
  have hlU := mem_normalizer_sup_zpowers ht htV hlV hlt
  exact mem_seitzRadX.2 ⟨conj_mem_centralizer_of_mem_normalizer hlV hxC,
    mul_mem (mul_mem hlU hxN) (inv_mem hlU)⟩

theorem mul_comm_of_mem_seitzRadX {x v : G} (hx : x ∈ seitzRadX V t) (hv : v ∈ V) :
    x * v = v * x :=
  ((mem_centralizer_iff.1 (mem_seitzRadX.1 hx).1) v hv).symm

theorem mem_seitzRadX_self (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t) :
    t ∈ seitzRadX V t := by
  have h : t ∈ V ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rw [← seitzRadX_inf_centralizer_eq hV2 ht htV hker] at h
  exact (Subgroup.mem_inf.1 h).1

theorem pow_four_conj_eq {b : ElemBasis V 4} {y : G} (hy : ∀ x, y * b x * y⁻¹ = b (singerC *ᵥ x))
    (z : Fin 4 → ZMod 2) :
    y ^ 4 * b z * (y ^ 4)⁻¹ = b (singerC *ᵥ (singerC *ᵥ (singerC *ᵥ (singerC *ᵥ z)))) := by
  have h4 : y ^ 4 = y * y * y * y := by rw [pow_succ, pow_succ, pow_succ, pow_one]
  calc y ^ 4 * b z * (y ^ 4)⁻¹ = y * (y * (y * (y * b z * y⁻¹) * y⁻¹) * y⁻¹) * y⁻¹ := by
        rw [h4]; group
    _ = _ := by rw [hy, hy, hy, hy]

theorem exists_singer_base (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    (b : ElemBasis V 4) {y : G} (hyV : y ∈ normalizer (V : Set G)) (hyt : y * t = t * y)
    (hy : ∀ x, y * b x * y⁻¹ = b (singerC *ᵥ x)) :
    ∃ p ∈ seitzRadX V t, t * p * t⁻¹ * p⁻¹ = b (Pi.single 0 1) ∧
      y ^ 4 * p * (y ^ 4)⁻¹ * (p * (y * p * y⁻¹))⁻¹ ∈ V := by
  obtain ⟨x₀, hx₀, hφx₀⟩ := hsurj (b (Pi.single 0 1)) (b.mem _)
  have hy4V : y ^ 4 ∈ normalizer (V : Set G) := pow_mem hyV 4
  have hy4t : y ^ 4 * t = t * y ^ 4 := ((Commute.pow_left hyt 4) : _)
  have hx₄ : y ^ 4 * x₀ * (y ^ 4)⁻¹ ∈ seitzRadX V t :=
    conj_mem_seitzRadX_of_commute ht htV hy4V hy4t hx₀
  have hx₁ : y * x₀ * y⁻¹ ∈ seitzRadX V t := conj_mem_seitzRadX_of_commute ht htV hyV hyt hx₀
  have hφx₄ : t * (y ^ 4 * x₀ * (y ^ 4)⁻¹) * t⁻¹ * (y ^ 4 * x₀ * (y ^ 4)⁻¹)⁻¹ =
      b (Pi.single 0 1) * b (Pi.single 1 1) := by
    rw [tcomm_conj_of_commute hy4t, hφx₀, pow_four_conj_eq hy, singerC_mulVec_e0,
      singerC_mulVec_e1, singerC_mulVec_e2, singerC_mulVec_e3, b.map_add]
  have hφx₁ : t * (y * x₀ * y⁻¹) * t⁻¹ * (y * x₀ * y⁻¹)⁻¹ = b (Pi.single 1 1) := by
    rw [tcomm_conj_of_commute hyt, hφx₀, hy, singerC_mulVec_e0]
  set d := y ^ 4 * x₀ * (y ^ 4)⁻¹ * (x₀ * (y * x₀ * y⁻¹))⁻¹ with hd
  have hdX : d ∈ seitzRadX V t := mul_mem hx₄ (inv_mem (mul_mem hx₀ hx₁))
  have hφd : t * d * t⁻¹ * d⁻¹ = 1 := by
    rw [hd, tcomm_mul_of_mem_seitzRadX ht htV htnV hx₄ (inv_mem (mul_mem hx₀ hx₁)),
      tcomm_inv_of_mem_seitzRadX ht htV htnV (mul_mem hx₀ hx₁),
      tcomm_mul_of_mem_seitzRadX ht htV htnV hx₀ hx₁, hφx₄, hφx₀, hφx₁, mul_inv_cancel]
  have hdU : d ∈ V ⊔ zpowers t := hker ⟨(mem_seitzRadX.1 hdX).1, tcomm_eq_one_iff.1 hφd⟩
  rcases (mem_sup_zpowers_iff ht (mem_normalizer_of_forall_commute htV)).1 hdU with hdV | hdtV
  · exact ⟨x₀, hx₀, hφx₀, hdV⟩
  · refine ⟨x₀ * t, mul_mem hx₀ (mem_seitzRadX_self hV2 ht htV hker), ?_, ?_⟩
    · rw [tcomm_mul_of_mem_seitzRadX ht htV htnV hx₀ (mem_seitzRadX_self hV2 ht htV hker), hφx₀,
        show t * t * t⁻¹ * t⁻¹ = (1 : G) by group, mul_one]
    · have hY : y ^ 4 * (x₀ * t) * (y ^ 4)⁻¹ = (y ^ 4 * x₀ * (y ^ 4)⁻¹) * t := by
        calc y ^ 4 * (x₀ * t) * (y ^ 4)⁻¹ = y ^ 4 * x₀ * (y ^ 4)⁻¹ * (y ^ 4 * t) * (y ^ 4)⁻¹ := by
              group
          _ = _ := by rw [hy4t]; group
      have hY1 : y * (x₀ * t) * y⁻¹ = (y * x₀ * y⁻¹) * t := by
        calc y * (x₀ * t) * y⁻¹ = y * x₀ * y⁻¹ * (y * t) * y⁻¹ := by group
          _ = _ := by rw [hyt]; group
      have heq : y ^ 4 * (x₀ * t) * (y ^ 4)⁻¹ * (x₀ * t * (y * (x₀ * t) * y⁻¹))⁻¹ =
          (d * t) * (t * x₀ * t⁻¹ * x₀⁻¹) := by
        rw [hY, hY1, hd]
        calc y ^ 4 * x₀ * (y ^ 4)⁻¹ * t * (x₀ * t * (y * x₀ * y⁻¹ * t))⁻¹ =
            y ^ 4 * x₀ * (y ^ 4)⁻¹ * (y * x₀ * y⁻¹)⁻¹ * t⁻¹ * x₀⁻¹ := by group
          _ = y ^ 4 * x₀ * (y ^ 4)⁻¹ * (y * x₀ * y⁻¹)⁻¹ * x₀⁻¹ * (t * t) * x₀ * t⁻¹ * x₀⁻¹ := by
            rw [ht]; group
          _ = _ := by group
      rw [heq]
      exact mul_mem hdtV (tcomm_mem_of_mem_seitzRadX ht htV htnV hx₀)

theorem exists_abelian_of_singer (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    (hcomm : ∀ x ∈ seitzRadX V t, ∀ y ∈ seitzRadX V t, x * y * x⁻¹ * y⁻¹ ∈ V)
    (b : ElemBasis V 4) {y : G} (hyV : y ∈ normalizer (V : Set G)) (hyt : y * t = t * y)
    (hy : ∀ x, y * b x * y⁻¹ = b (singerC *ᵥ x)) :
    ∃ W₁ : Subgroup G, W₁ ≤ seitzRadX V t ∧ V ≤ W₁ ∧ (∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v) ∧
      t ∉ W₁ ∧ ∀ v ∈ V, ∃ w ∈ W₁, t * w * t⁻¹ * w⁻¹ = v := by
  obtain ⟨p, hpX, hφp, hp4⟩ := exists_singer_base hV2 ht htV htnV hker hsurj b hyV hyt hy
  set P : ℕ → G := fun k => y ^ k * p * (y ^ k)⁻¹ with hPdef
  have hPX : ∀ k, P k ∈ seitzRadX V t := fun k =>
    conj_mem_seitzRadX_of_commute ht htV (pow_mem hyV k) (Commute.pow_left hyt k) hpX
  have hPs : ∀ k, P (k + 1) = y * P k * y⁻¹ := fun k => by
    simp only [hPdef, pow_succ']
    group
  have hP0 : P 0 = p := by simp [hPdef]
  have hP1 : P 1 = y * p * y⁻¹ := by simp [hPdef]
  have hφP : ∀ k, t * P (k + 1) * t⁻¹ * (P (k + 1))⁻¹ = y * (t * P k * t⁻¹ * (P k)⁻¹) * y⁻¹ :=
    fun k => by
      rw [hPs]
      exact tcomm_conj_of_commute hyt _
  have hφ0 : t * P 0 * t⁻¹ * (P 0)⁻¹ = b (Pi.single 0 1) := by rw [hP0]; exact hφp
  have hφ1 : t * P 1 * t⁻¹ * (P 1)⁻¹ = b (Pi.single 1 1) := by
    rw [hφP 0, hφ0, hy, singerC_mulVec_e0]
  have hφ2 : t * P 2 * t⁻¹ * (P 2)⁻¹ = b (Pi.single 2 1) := by
    rw [hφP 1, hφ1, hy, singerC_mulVec_e1]
  have hφ3 : t * P 3 * t⁻¹ * (P 3)⁻¹ = b (Pi.single 3 1) := by
    rw [hφP 2, hφ2, hy, singerC_mulVec_e2]
  have hu : P 4 * (P 0 * P 1)⁻¹ ∈ V := by
    rw [hP0, hP1]
    exact hp4
  have hcV : ∀ i j, P i * P j * (P i)⁻¹ * (P j)⁻¹ ∈ V := fun i j =>
    hcomm _ (hPX i) _ (hPX j)
  choose g hg using fun i j => b.exists_eq (hcV i j)
  have hgy : ∀ i j, singerC *ᵥ g i j = g (i + 1) (j + 1) := fun i j => by
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
  have hg4 : ∀ k, g k 4 = g k 0 + g k 1 := fun k => by
    apply b.injective
    rw [b.map_add, hg, hg, hg]
    set u := P 4 * (P 0 * P 1)⁻¹ with hudef
    have hP4 : P 4 = u * (P 0 * P 1) := by rw [hudef]; group
    have hku : P k * u * (P k)⁻¹ * u⁻¹ = 1 := by
      rw [mul_comm_of_mem_seitzRadX (hPX k) hu]
      group
    rw [hP4, xcomm_mul_right (mul_comm_of_forall_mul_self_eq_one hV2 hu
      (hcomm _ (hPX k) _ (mul_mem (hPX 0) (hPX 1)))), hku, one_mul,
      xcomm_mul_right (mul_comm_of_mem_seitzRadX (hPX 0) (hcV k 1))]
  have e03 : singerC *ᵥ g 0 3 = g 0 1 := by rw [hgy 0 3, hg4 1, hgd, add_zero, hgs]
  have e01 : singerC *ᵥ g 0 1 = g 1 2 := hgy 0 1
  have e12 : singerC *ᵥ g 1 2 = g 2 3 := hgy 1 2
  have e23 : singerC *ᵥ g 2 3 = g 0 3 + g 1 3 := by rw [hgy 2 3, hg4 3, hgs 0 3, hgs 1 3]
  have e02 : singerC *ᵥ g 0 2 = g 1 3 := hgy 0 2
  have e13 : singerC *ᵥ g 1 3 = g 0 2 + g 1 2 := by rw [hgy 1 3, hg4 2, hgs 0 2, hgs 1 2]
  obtain ⟨h03, h02, h13⟩ := singer_system (g 0 3) (g 0 2) (g 1 3)
    (by rw [e03, e01, e12, e23]) e02 (by rw [e13, e03, e01])
  have h01 : g 0 1 = 0 := by rw [← e03, h03, Matrix.mulVec_zero]
  have h12 : g 1 2 = 0 := by rw [← e01, h01, Matrix.mulVec_zero]
  have h23 : g 2 3 = 0 := by rw [← e12, h12, Matrix.mulVec_zero]
  have hz : ∀ i j : ℕ, i < 4 → j < 4 → g i j = 0 := by
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      first | exact hgd _ | assumption | (rwa [hgs])
  have hPc : ∀ i j : ℕ, i < 4 → j < 4 → P i * P j = P j * P i := fun i j hi hj => by
    have h := hg i j
    rw [hz i j hi hj, b.map_zero] at h
    have h' : P i * P j * (P i)⁻¹ * (P j)⁻¹ * (P j * P i) = P j * P i := by rw [← h, one_mul]
    rw [← h']
    group
  set S : Set G := (V : Set G) ∪ Set.range (fun i : Fin 4 => P i) with hSdef
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
  have hPW : ∀ i : Fin 4, P i ∈ W₁ := fun i => subset_closure (Or.inr ⟨i, rfl⟩)
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
    intro v hv
    obtain ⟨z, rfl⟩ := b.exists_eq hv
    exact b.mem_of_forall_single hbH z

theorem card_and_inf_centralizer_of_le_seitzRadX [Finite G] (hV2 : ∀ v ∈ V, v * v = 1)
    (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    {W₁ : Subgroup G} (hW₁X : W₁ ≤ seitzRadX V t) (hVW₁ : V ≤ W₁) (htW₁ : t ∉ W₁)
    (honto : ∀ v ∈ V, ∃ w ∈ W₁, t * w * t⁻¹ * w⁻¹ = v) :
    Nat.card W₁ = Nat.card V * Nat.card V ∧ W₁ ⊓ centralizer ({t} : Set G) = V := by
  have hinf : W₁ ⊓ centralizer ({t} : Set G) = V := by
    apply le_antisymm
    · intro w hw'
      obtain ⟨hw, hwt⟩ := Subgroup.mem_inf.1 hw'
      have h : w ∈ V ⊔ zpowers t := by
        rw [← seitzRadX_inf_centralizer_eq hV2 ht htV hker]
        exact Subgroup.mem_inf.2 ⟨hW₁X hw, hwt⟩
      rcases (mem_sup_zpowers_iff ht (mem_normalizer_of_forall_commute htV)).1 h with h | h
      · exact h
      · refine absurd ?_ htW₁
        have h2 := mul_mem (inv_mem hw) (hVW₁ h)
        rwa [inv_mul_cancel_left] at h2
    · intro v hv
      exact Subgroup.mem_inf.2 ⟨hVW₁ hv, mem_centralizer_singleton_iff.2 (htV v hv)⟩
  refine ⟨?_, hinf⟩
  set φ := (seitzTcommHom ht htV htnV).comp (Subgroup.inclusion hW₁X) with hφ
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨w, hw, hwv⟩ := honto v hv
    exact ⟨⟨w, hw⟩, Subtype.ext hwv⟩
  have hkerφ : φ.ker = V.subgroupOf W₁ := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h' : t * (w : G) * t⁻¹ * (w : G)⁻¹ = 1 := congrArg Subtype.val h
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨w.2, tcomm_eq_one_iff.1 h'⟩
    · intro h
      apply Subtype.ext
      show t * (w : G) * t⁻¹ * (w : G)⁻¹ = 1
      rw [← htV _ h]
      group
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurjφ).toEquiv, hkerφ,
    Nat.card_congr (subgroupOfEquivOfLe hVW₁).toEquiv]

theorem eq_of_le_seitzRadX_of_card [Finite G] (hVc : Nat.card V = 2 ^ 4)
    (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    {A B : Subgroup G} (hAX : A ≤ seitzRadX V t) (hBX : B ≤ seitzRadX V t)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hBc : ∀ a ∈ B, ∀ a' ∈ B, a * a' = a' * a)
    (hA : Nat.card A = 2 ^ 8) (hB : Nat.card B = 2 ^ 8) : A = B := by
  have hU : Nat.card (V ⊔ zpowers t : Subgroup G) = 2 ^ 5 := by
    rw [card_sup_zpowers_eq ht (mem_normalizer_of_forall_commute htV) htnV, hVc]
    norm_num
  have hXc : Nat.card (seitzRadX V t) = 2 ^ 9 := by
    rw [card_seitzRadX hV2 ht htV htnV hker hsurj, hU, hVc]
    norm_num
  have hA'c : Nat.card (A.subgroupOf (seitzRadX V t)) = 2 ^ 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv, hA]
  have hB'c : Nat.card (B.subgroupOf (seitzRadX V t)) = 2 ^ 8 := by
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
      2 ^ 5 := by
    have hle : (centralizer ({(⟨t, htX⟩ : seitzRadX V t)} : Set (seitzRadX V t))).map
        (seitzRadX V t).subtype ≤ V ⊔ zpowers t := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← seitzRadX_inf_centralizer_eq hV2 ht htV hker]
      exact ⟨x.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))⟩
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (seitzRadX V t).subtype_injective, hU] at h1
  have hinf : 2 ^ 7 ≤ Nat.card (A.subgroupOf (seitzRadX V t) ⊓ B.subgroupOf (seitzRadX V t) :
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

theorem exists_wOne_of_seitzRadX {G : Type*} [Group G] [Finite G] {V L₁ : Subgroup G} {t : G}
    (hVc : Nat.card V = 2 ^ 4) (hV2 : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    (hsq : ∀ x ∈ seitzRadX V t, x * x ∈ V)
    (hcomm : ∀ x ∈ seitzRadX V t, ∀ y ∈ seitzRadX V t, x * y * x⁻¹ * y⁻¹ ∈ V)
    (hL₁t : L₁ ≤ centralizer ({t} : Set G)) (hL₁V : L₁ ≤ normalizer (V : Set G))
    (haut : ∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹) :
    ∃ W₁ : Subgroup G, W₁ ≤ seitzRadX V t ∧ Nat.card W₁ = 2 ^ 8 ∧
      (∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v) ∧ (∀ w ∈ W₁, w * w ∈ V) ∧
      W₁ ⊓ centralizer ({t} : Set G) = V ∧ t ∈ normalizer (W₁ : Set G) ∧
      L₁ ≤ normalizer (W₁ : Set G) := by
  obtain ⟨b⟩ := exists_elemBasis hVc hV2
  obtain ⟨y, hyL, hy⟩ := b.exists_conj_eq_of_forall_mulEquiv haut singerC singerCInv
    singerC_mul_singerCInv singerCInv_mul_singerC
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 (hL₁t hyL)
  obtain ⟨W₁, hW₁X, hVW₁, hab, htW₁, honto⟩ :=
    exists_abelian_of_singer hV2 ht htV htnV hker hsurj hcomm b (hL₁V hyL) hyt hy
  obtain ⟨hcard, hinf⟩ :=
    card_and_inf_centralizer_of_le_seitzRadX hV2 ht htV htnV hker hW₁X hVW₁ htW₁ honto
  have hcard' : Nat.card W₁ = 2 ^ 8 := by
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
    have hW₂c : Nat.card (W₁.map (MulAut.conj l).toMonoidHom) = 2 ^ 8 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hcard']
    have hW₂ab : ∀ v ∈ W₁.map (MulAut.conj l).toMonoidHom,
        ∀ w ∈ W₁.map (MulAut.conj l).toMonoidHom, v * w = w * v := by
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc l * v * l⁻¹ * (l * w * l⁻¹) = l * (v * w) * l⁻¹ := by group
        _ = l * (w * v) * l⁻¹ := by rw [hab v hv w hw]
        _ = l * w * l⁻¹ * (l * v * l⁻¹) := by group
    have heq := eq_of_le_seitzRadX_of_card hVc hV2 ht htV htnV hker hsurj hW₁X hW₂X hab hW₂ab
      hcard' hW₂c
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

end CFSG.SeitzReduction.LinearPilot
