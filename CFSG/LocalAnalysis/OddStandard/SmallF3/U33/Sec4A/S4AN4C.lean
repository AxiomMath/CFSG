module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41P2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_comm_of_conj_eq {n g : G} (h : n * g * n⁻¹ = g) : g * n = n * g := by
  calc g * n = (n * g * n⁻¹) * n := by rw [h]
    _ = n * g := by group

theorem n4_conj_eq_of_comm {n g : G} (h : g * n = n * g) : n * g * n⁻¹ = g := by
  calc n * g * n⁻¹ = (g * n) * n⁻¹ := by rw [h]
    _ = g := by group

theorem n4_fix_of_fix_mul {n a b : G} (ha2 : a * a = 1) (h1 : n * a * n⁻¹ = a)
    (h2 : n * (a * b) * n⁻¹ = a * b) : n * b * n⁻¹ = b := by
  have e1 : n * b * n⁻¹ = (n * a * n⁻¹) * (n * (a * b) * n⁻¹) := by
    calc n * b * n⁻¹ = n * ((a * a) * b) * n⁻¹ := by rw [ha2, one_mul]
      _ = (n * a * n⁻¹) * (n * (a * b) * n⁻¹) := by group
  rw [e1, h1, h2, ← mul_assoc, ha2, one_mul]

theorem n4_mem_smul_iff {F : Subgroup G} {a x : G} : x ∈ a • (F : Set G) ↔ ∃ f ∈ F, x = a * f := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, h.symm⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, h.symm⟩

theorem n4_four_le_A (t x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
  rw [pt_ctxE_eq_sup]
  exact le_sup_right

theorem n4_t_mem_A (t x₁ x₂ : G) : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)

theorem n4_y_mem_four (x₁ x₂ : G) : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)

theorem n4_z_mem_four (x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

theorem n4_card_four (h : Ctx0 t L S x₁ x₂ lam rho) : Nat.card ↥(fourGrp x₁ x₂) = 4 :=
  (h.wreath.fourGrp_eq_omega).2.2

theorem n4_card_omega (h : Ctx0 t L S x₁ x₂ lam rho) :
    Nat.card ↥(t • (fourGrp x₁ x₂ : Set G)) = 4 := by
  rw [Nat.card_coe_set_eq, Set.ncard_smul_set, ← Nat.card_coe_set_eq]
  exact n4_card_four h

theorem n4_t_mem_omega (t x₁ x₂ : G) : t ∈ t • (fourGrp x₁ x₂ : Set G) :=
  n4_mem_smul_iff.mpr ⟨1, Subgroup.one_mem _, (mul_one t).symm⟩

theorem n4_rho_cube (h : Ctx0 t L S x₁ x₂ lam rho) : rho ^ 3 = 1 := by
  have := pow_orderOf_eq_one rho
  rwa [h.ord_rho] at this

theorem n4_lam_sq (h : Ctx0 t L S x₁ x₂ lam rho) : lam * lam = 1 := by
  have := pow_orderOf_eq_one lam
  rw [h.wreath.ord_lam, pow_two] at this
  exact this

theorem n4_mem_N_of_normalizer_W (h : L41GPh1 t L S x₁ x₂ lam rho) {n : G}
    (hn : n ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)) : n ∈ l41N t x₁ x₂ := by
  refine mem_normalizer_of_conj_mem (fun a ha => ?_)
  have hnaW : n * a * n⁻¹ ∈ ctxW t x₁ x₂ :=
    (Subgroup.mem_normalizer_iff.mp hn a).mp (b1_ctxE_le_ctxW h.toCtx0 ha)
  have ha2 : a * a = 1 := by
    have := h.basic.A_elem.1.2 a ha
    rwa [pow_two] at this
  refine l41_omega_ctxW_le h hnaW ?_
  calc n * a * n⁻¹ * (n * a * n⁻¹) = n * (a * a) * n⁻¹ := by group
    _ = 1 := by rw [ha2]; group

theorem n4_S_le_N (h : L41GPh1 t L S x₁ x₂ lam rho) : S ≤ l41N t x₁ x₂ := fun s hs =>
  n4_mem_N_of_normalizer_W h
    (mem_normalizer_of_conj_mem fun w hw => h.basic.normal_W.2 s hs w hw)

theorem n4_normalizer_S_le_N (h : L41GPh1 t L S x₁ x₂ lam rho) {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n ∈ l41N t x₁ x₂ :=
  n4_mem_N_of_normalizer_W h (h.basic.norm_S_le n hn)

theorem n4_K_le_N (h : L41GPh1 t L S x₁ x₂ lam rho) : closure {rho, lam} ≤ l41N t x₁ x₂ := by
  intro k hk
  have hk' : k ∈ invCent t ⊓ normalizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
    rw [h.basic.norm_A]
    exact Subgroup.mem_sup_right hk
  exact hk'.2

theorem n4_K_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : closure {rho, lam} ≤ L := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact h.rho_mem
  · exact (generators_mem_L h).2.2

theorem n4_K_fix_t (h : Ctx0 t L S x₁ x₂ lam rho) {k : G} (hk : k ∈ closure {rho, lam}) :
    k * t * k⁻¹ = t := by
  have hkH : k ∈ invCent t := L_le_invCent h.hyp (n4_K_le_L h hk)
  have hc : k * t = t * k := mem_invCent_iff.mp hkH
  calc k * t * k⁻¹ = t * k * k⁻¹ := by rw [hc]
    _ = t := by group

theorem n4_normal_F2 (h : L41GPh3 t L S x₁ x₂ lam rho) :
    NormalIn (fourGrp x₁ x₂) (l41N t x₁ x₂) := by
  refine ⟨(n4_four_le_A t x₁ x₂).trans Subgroup.le_normalizer, fun n hn f hf => ?_⟩
  by_cases hf1 : f = 1
  · rw [hf1]
    simp
  · have hfA : f ∈ ctxE t x₁ x₂ := n4_four_le_A t x₁ x₂ hf
    obtain ⟨g, hg⟩ := (h.fusion.zG_A f hfA).mpr ⟨hf, hf1⟩
    have hnfA : n * f * n⁻¹ ∈ ctxE t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hn f).mp hfA
    refine ((h.fusion.zG_A _ hnfA).mp ⟨n * g, ?_⟩).1
    calc n * g * (x₁ * x₂) ^ 2 * (n * g)⁻¹ = n * (g * (x₁ * x₂) ^ 2 * g⁻¹) * n⁻¹ := by group
      _ = n * f * n⁻¹ := by rw [hg]

theorem n4_omega_inv (h : L41GPh3 t L S x₁ x₂ lam rho) :
    ∀ n ∈ l41N t x₁ x₂, ∀ u ∈ t • (fourGrp x₁ x₂ : Set G),
      n * u * n⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
  intro n hn u hu
  obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hu
  have huA : t * f ∈ ctxE t x₁ x₂ :=
    Subgroup.mul_mem _ (n4_t_mem_A t x₁ x₂) (n4_four_le_A t x₁ x₂ hf)
  obtain ⟨g, hg⟩ := (h.fusion.tG_A _ huA).mpr ⟨f, hf, rfl⟩
  have hnA : n * (t * f) * n⁻¹ ∈ ctxE t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hn _).mp huA
  obtain ⟨f', hf', hf'e⟩ := (h.fusion.tG_A _ hnA).mp ⟨n * g, by
    calc n * g * t * (n * g)⁻¹ = n * (g * t * g⁻¹) * n⁻¹ := by group
      _ = n * (t * f) * n⁻¹ := by rw [hg]⟩
  exact n4_mem_smul_iff.mpr ⟨f', hf', hf'e⟩

theorem n4_rho_moves (h : Ctx0 t L S x₁ x₂ lam rho) {f : G} (hf : f ∈ fourGrp x₁ x₂)
    (hf1 : f ≠ 1) : rho * f * rho⁻¹ ≠ f := by
  intro hfix
  have hfB : f ∈ baseGrp x₁ x₂ := pt_four_le_base x₁ x₂ hf
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hfB
  have hfC : f ∈ centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact n4_comm_of_conj_eq hfix
  have hfP : f ∈ twoCore t := by
    rw [← h.cent_rho]
    exact ⟨hfW, hfC⟩
  have hmem : f ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨hfP, hfB⟩
  rw [pt_inf_base h, Subgroup.mem_bot] at hmem
  exact hf1 hmem

theorem n4_lam_y (h : WreathRel x₁ x₂ lam) :
    lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  have hcomm : Commute x₁ x₂ := h.comm
  have hx₁4 : x₁ ^ 4 = 1 := by
    rw [← h.ord_x₁]
    exact pow_orderOf_eq_one x₁
  have hz : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := hcomm.mul_pow 2
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₂ ^ 2 := by
    rw [hz, ← mul_assoc, ← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hx₁4, one_mul]
  rw [hyz, ← conj_pow (a := lam) (b := x₁) (i := 2), h.conj_x₁]

theorem n4_lam_moves (h : Ctx0 t L S x₁ x₂ lam rho) : lam * x₁ ^ 2 * lam⁻¹ ≠ x₁ ^ 2 := by
  intro hfix
  rw [n4_lam_y h.wreath] at hfix
  exact (z_mul_self_ne_one h).2 (mul_left_cancel (hfix.trans (mul_one _).symm))

theorem n4_exists_conj_F (h : L41GPh3 t L S x₁ x₂ lam rho)
    (σ : Equiv.Perm ↥(nonid (fourGrp x₁ x₂))) :
    ∃ k ∈ closure {rho, lam}, ∀ x : ↥(nonid (fourGrp x₁ x₂)),
      ((σ x : ↥(nonid (fourGrp x₁ x₂))) : G) = k * x * k⁻¹ := by
  have hX : ∀ k ∈ closure {rho, lam}, ∀ x ∈ nonid (fourGrp x₁ x₂),
      k * x * k⁻¹ ∈ nonid (fourGrp x₁ x₂) :=
    conj_mem_nonid (fun k hk f hf => (n4_normal_F2 h).2 k (n4_K_le_N h.toL41GPh1 hk) f hf)
  have hy : x₁ ^ 2 ∈ nonid (fourGrp x₁ x₂) :=
    ⟨n4_y_mem_four x₁ x₂, (y_mul_self_ne_one h.wreath).2⟩
  have hs := conjAct_surjective_of_card_three hX (card_nonid (n4_card_four h.toCtx0))
    (Subgroup.subset_closure (by simp) : rho ∈ closure {rho, lam})
    (Subgroup.subset_closure (by simp) : lam ∈ closure {rho, lam}) (n4_rho_cube h.toCtx0)
    (n4_lam_sq h.toCtx0) ⟨x₁ ^ 2, hy, n4_rho_moves h.toCtx0 hy.1 hy.2⟩
    ⟨x₁ ^ 2, hy, n4_lam_moves h.toCtx0⟩
  exact exists_conj_of_surjective hX hs σ

theorem n4_exists_swap (h : L41GPh3 t L S x₁ x₂ lam rho) :
    ∃ n ∈ l41N t x₁ x₂, n * t * n⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hmem : t * (x₁ * x₂) ^ 2 ∈ conjIn (normalizer (S : Set G)) t := by
    rw [h.fusion.orbit_NS]
    exact n4_mem_smul_iff.mpr ⟨(x₁ * x₂) ^ 2, Subgroup.mem_zpowers _, rfl⟩
  obtain ⟨n, hn, hnt⟩ := hmem
  exact ⟨n, n4_normalizer_S_le_N h.toL41GPh1 hn, hnt⟩

theorem n4_trans (h : L41GPh3 t L S x₁ x₂ lam rho) {f : G} (hf : f ∈ fourGrp x₁ x₂) :
    ∃ n ∈ l41N t x₁ x₂, n * t * n⁻¹ = t * f := by
  by_cases hf1 : f = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hf1]
    simp
  · classical
    obtain ⟨n₀, hn₀, hn₀t⟩ := n4_exists_swap h
    have hz : (x₁ * x₂) ^ 2 ∈ nonid (fourGrp x₁ x₂) :=
      ⟨n4_z_mem_four x₁ x₂, (z_mul_self_ne_one h.toCtx0).2⟩
    have hfn : f ∈ nonid (fourGrp x₁ x₂) := ⟨hf, hf1⟩
    obtain ⟨k, hk, hkx⟩ :=
      n4_exists_conj_F h (Equiv.swap (⟨(x₁ * x₂) ^ 2, hz⟩ : ↥(nonid (fourGrp x₁ x₂))) ⟨f, hfn⟩)
    have hkz : k * (x₁ * x₂) ^ 2 * k⁻¹ = f := by
      have := hkx ⟨(x₁ * x₂) ^ 2, hz⟩
      rw [Equiv.swap_apply_left] at this
      exact this.symm
    refine ⟨k * n₀, Subgroup.mul_mem _ (n4_K_le_N h.toL41GPh1 hk) hn₀, ?_⟩
    calc k * n₀ * t * (k * n₀)⁻¹ = k * (n₀ * t * n₀⁻¹) * k⁻¹ := by group
      _ = k * (t * (x₁ * x₂) ^ 2) * k⁻¹ := by rw [hn₀t]
      _ = (k * t * k⁻¹) * (k * (x₁ * x₂) ^ 2 * k⁻¹) := by group
      _ = t * f := by rw [n4_K_fix_t h.toCtx0 hk, hkz]

theorem n4_orbit_t (h : L41GPh3 t L S x₁ x₂ lam rho) :
    conjIn (l41N t x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G) := by
  ext u
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact n4_omega_inv h n hn t (n4_t_mem_omega t x₁ x₂)
  · intro hu
    obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hu
    obtain ⟨n, hn, hnt⟩ := n4_trans h hf
    exact ⟨n, hn, hnt⟩

theorem n4_exists_conj_omega (h : L41GPh3 t L S x₁ x₂ lam rho)
    (σ : Equiv.Perm ↥(t • (fourGrp x₁ x₂ : Set G))) :
    ∃ n ∈ l41N t x₁ x₂, ∀ x : ↥(t • (fourGrp x₁ x₂ : Set G)),
      ((σ x : ↥(t • (fourGrp x₁ x₂ : Set G))) : G) = n * x * n⁻¹ := by
  have h0 := h.toCtx0
  have ht : t ∈ t • (fourGrp x₁ x₂ : Set G) := n4_t_mem_omega t x₁ x₂
  have hKN := n4_K_le_N h.toL41GPh1
  have hfix : ∀ k ∈ closure {rho, lam}, k * t * k⁻¹ = t := fun k hk => n4_K_fix_t h0 hk
  have hρK : rho ∈ closure {rho, lam} := Subgroup.subset_closure (by simp)
  have hlK : lam ∈ closure {rho, lam} := Subgroup.subset_closure (by simp)
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := n4_y_mem_four x₁ x₂
  have hy1 : x₁ ^ 2 ≠ 1 := (y_mul_self_ne_one h.wreath).2
  have hX' : ∀ k ∈ closure {rho, lam}, ∀ x ∈ t • (fourGrp x₁ x₂ : Set G) \ {t},
      k * x * k⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) \ {t} := by
    intro k hk x hx
    obtain ⟨hxΩ, hxt⟩ := hx
    obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hxΩ
    have hkf : k * f * k⁻¹ ∈ fourGrp x₁ x₂ := (n4_normal_F2 h).2 k (hKN hk) f hf
    have e : k * (t * f) * k⁻¹ = t * (k * f * k⁻¹) := by
      calc k * (t * f) * k⁻¹ = (k * t * k⁻¹) * (k * f * k⁻¹) := by group
        _ = t * (k * f * k⁻¹) := by rw [hfix k hk]
    rw [e]
    refine ⟨n4_mem_smul_iff.mpr ⟨_, hkf, rfl⟩, fun hmem => hxt ?_⟩
    have h1 : t * (k * f * k⁻¹) = t := Set.mem_singleton_iff.mp hmem
    have h2 : k * f * k⁻¹ = 1 := mul_left_cancel (h1.trans (mul_one t).symm)
    have h3 : f = 1 := by
      calc f = k⁻¹ * (k * f * k⁻¹) * k := by group
        _ = 1 := by rw [h2]; group
    rw [h3, mul_one]
    exact Set.mem_singleton t
  have hcard : Nat.card ↥(t • (fourGrp x₁ x₂ : Set G) \ {t}) = 3 := by
    rw [Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem ht]
    have h4 : (t • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact n4_card_omega h0
    omega
  have hty : t * x₁ ^ 2 ∈ t • (fourGrp x₁ x₂ : Set G) \ {t} :=
    ⟨n4_mem_smul_iff.mpr ⟨_, hy, rfl⟩, fun hmem =>
      hy1 (mul_left_cancel ((Set.mem_singleton_iff.mp hmem).trans (mul_one t).symm))⟩
  have hρm : ∃ x ∈ t • (fourGrp x₁ x₂ : Set G) \ {t}, rho * x * rho⁻¹ ≠ x := by
    refine ⟨t * x₁ ^ 2, hty, fun hfix' => n4_rho_moves h0 hy hy1 ?_⟩
    have e : rho * (t * x₁ ^ 2) * rho⁻¹ = t * (rho * x₁ ^ 2 * rho⁻¹) := by
      calc rho * (t * x₁ ^ 2) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * x₁ ^ 2 * rho⁻¹) := by group
        _ = t * (rho * x₁ ^ 2 * rho⁻¹) := by rw [hfix rho hρK]
    rw [e] at hfix'
    exact mul_left_cancel hfix'
  have hlm : ∃ x ∈ t • (fourGrp x₁ x₂ : Set G) \ {t}, lam * x * lam⁻¹ ≠ x := by
    refine ⟨t * x₁ ^ 2, hty, fun hfix' => n4_lam_moves h0 ?_⟩
    have e : lam * (t * x₁ ^ 2) * lam⁻¹ = t * (lam * x₁ ^ 2 * lam⁻¹) := by
      calc lam * (t * x₁ ^ 2) * lam⁻¹ = (lam * t * lam⁻¹) * (lam * x₁ ^ 2 * lam⁻¹) := by group
        _ = t * (lam * x₁ ^ 2 * lam⁻¹) := by rw [hfix lam hlK]
    rw [e] at hfix'
    exact mul_left_cancel hfix'
  have h₀ : ∀ σ₀ : Equiv.Perm ↥(t • (fourGrp x₁ x₂ : Set G) \ {t}), ∃ k ∈ closure {rho, lam},
      ∀ x : ↥(t • (fourGrp x₁ x₂ : Set G) \ {t}),
        ((σ₀ x : ↥(t • (fourGrp x₁ x₂ : Set G) \ {t})) : G) = k * x * k⁻¹ := fun σ₀ =>
    exists_conj_of_surjective hX'
      (conjAct_surjective_of_card_three hX' hcard hρK hlK (n4_rho_cube h0) (n4_lam_sq h0) hρm hlm)
      σ₀
  refine exists_conj_of_trans_stab ht (n4_omega_inv h) hKN (fun x hx => ?_)
    (fun σ' hσ' => exists_conj_of_stab ht hfix h₀ σ' hσ') σ
  obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hx
  exact n4_trans h hf

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
