module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AHS29A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Y11A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_mem_Y_iff (h : L41GPh10 t L S x₁ x₂ lam rho) {g : G} :
    g ∈ l41Y t x₁ x₂ rho ↔ g ∈ l41R t x₁ x₂ rho ∧ g * g = 1 := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨Subgroup.one_mem _, mul_one 1⟩
    | mul x y _ _ hx hy =>
      refine ⟨Subgroup.mul_mem _ hx.1 hy.1, ?_⟩
      have hc : x * y = y * x := m13_comm_R h hx.1 hy.1
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hc]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx.2, hy.2, one_mul]
    | inv x _ hx =>
      refine ⟨Subgroup.inv_mem _ hx.1, ?_⟩
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx.2, inv_one]
  · intro hg
    exact Subgroup.subset_closure hg

@[expose] def m11Sq (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ↥(l41R t x₁ x₂ rho) →* ↥(l41R t x₁ x₂ rho) :=
  MonoidHom.mk' (fun r => ⟨(r : G) * (r : G), Subgroup.mul_mem _ r.2 r.2⟩) (fun a b => by
    apply Subtype.ext
    have hc : (a : G) * (b : G) = (b : G) * (a : G) := m13_comm_R h a.2 b.2
    show (a : G) * (b : G) * ((a : G) * (b : G)) = (a : G) * (a : G) * ((b : G) * (b : G))
    calc (a : G) * (b : G) * ((a : G) * (b : G))
        = (a : G) * ((b : G) * (a : G)) * (b : G) := by group
      _ = (a : G) * ((a : G) * (b : G)) * (b : G) := by rw [← hc]
      _ = (a : G) * (a : G) * ((b : G) * (b : G)) := by group)

theorem m11Sq_apply (h : L41GPh10 t L S x₁ x₂ lam rho) (r : ↥(l41R t x₁ x₂ rho)) :
    ((m11Sq h r : ↥(l41R t x₁ x₂ rho)) : G) = (r : G) * (r : G) := rfl

theorem m11Sq_ker (h : L41GPh10 t L S x₁ x₂ lam rho) :
    (m11Sq h).ker = (l41Y t x₁ x₂ rho).subgroupOf (l41R t x₁ x₂ rho) := by
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, m11_mem_Y_iff h]
  constructor
  · intro h1
    have h2 := congrArg Subtype.val h1
    rw [m11Sq_apply] at h2
    exact ⟨r.2, h2⟩
  · rintro ⟨-, h2⟩
    exact Subtype.ext h2

theorem m11Sq_range (h : L41GPh10 t L S x₁ x₂ lam rho) :
    (m11Sq h).range = (fourGrp x₁ x₂).subgroupOf (l41R t x₁ x₂ rho) := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    rw [Subgroup.mem_subgroupOf, m11Sq_apply]
    exact h.rfacts.sq_mem _ r.2
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    have hsq : ∀ b : G, b ∈ l41R t x₁ x₂ rho →
        b * b ∈ (m11Sq h).range.map (l41R t x₁ x₂ rho).subtype :=
      fun b hb => Subgroup.mem_map.mpr ⟨m11Sq h ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
    have hF : fourGrp x₁ x₂ ≤ (m11Sq h).range.map (l41R t x₁ x₂ rho).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · have := hsq x₁ (m13_x_mem_R h.toL41GPh3).1
        rwa [← pow_two] at this
      · have := hsq (x₁ * x₂) (Subgroup.mul_mem _ (m13_x_mem_R h.toL41GPh3).1
          (m13_x_mem_R h.toL41GPh3).2)
        rwa [← pow_two] at this
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp (hF hu)
    have : w = u := Subtype.ext hwu
    rwa [← this]

theorem m11_card_Y (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nat.card (l41Y t x₁ x₂ rho) = 16 := by
  have h1 := card_ker_mul_card_range (m11Sq h)
  have h2 : Nat.card (m11Sq h).range = 4 := by
    rw [m11Sq_range h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      h.rfacts.fourGrp_le).toEquiv]
    exact n4_card_four h.toCtx0
  have h3 : Nat.card (m11Sq h).ker = Nat.card (l41Y t x₁ x₂ rho) := by
    rw [m11Sq_ker h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (m13_Y_le_R t x₁ x₂ rho)).toEquiv]
  rw [h2, h3, h.rfacts.card_R] at h1
  omega

theorem m11_comm_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {a b : G} (ha : a ∈ l41Y t x₁ x₂ rho)
    (hb : b ∈ l41Y t x₁ x₂ rho) : a * b = b * a :=
  m13_comm_R h (m13_Y_le_R t x₁ x₂ rho ha) (m13_Y_le_R t x₁ x₂ rho hb)

theorem m11_fourGrp_sq (h : Ctx0 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ fourGrp x₁ x₂) :
    g * g = 1 := by
  have := h.wreath.fourGrp_eq_omega.2.1.2 g hg
  rwa [pow_two] at this

theorem m11_fourGrp_le_B (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.pow_mem _ hx₁ 2
  · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hx₁ hx₂) 2

theorem m11_fourGrp_le_Y (h : L41GPh10 t L S x₁ x₂ lam rho) :
    fourGrp x₁ x₂ ≤ l41Y t x₁ x₂ rho := fun g hg =>
  (m11_mem_Y_iff h).mpr ⟨h.rfacts.fourGrp_le hg, m11_fourGrp_sq h.toCtx0 hg⟩

theorem m11_Y_elem (h : L41GPh10 t L S x₁ x₂ lam rho) :
    CFSG.Open.IsElemAbelian 2 (l41Y t x₁ x₂ rho) := by
  refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (m11_comm_Y h a.2 b.2), ?_⟩
  intro x hx
  rw [pow_two]
  exact ((m11_mem_Y_iff h).mp hx).2

theorem m11_Y_inf_cent_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41Y t x₁ x₂ rho ⊓ invCent t = fourGrp x₁ x₂ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgY, hgt⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgR, hg2⟩ := (m11_mem_Y_iff h).mp hgY
    have hgB : g ∈ baseGrp x₁ x₂ := by
      rw [← h.rfacts.cent_t]
      exact Subgroup.mem_inf.mpr ⟨hgR, hgt⟩
    rw [h.wreath.fourGrp_eq_omega.1]
    exact Subgroup.subset_closure ⟨hgB, by rw [pow_two]; exact hg2⟩
  · intro g hg
    refine Subgroup.mem_inf.mpr ⟨m11_fourGrp_le_Y h hg, ?_⟩
    rw [mem_invCent_iff]
    exact (m13_t_comm_base h.toL41GPh5 (m11_fourGrp_le_B x₁ x₂ hg)).symm

theorem m11_mem_closure_pair_iff {a b k : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : k ∈ closure ({a, b} : Set G) ↔ k = 1 ∨ k = a ∨ k = b ∨ k = a * b := by
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * a = a * b := hab.symm
  have e3 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
  have e4 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have e5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e6 : a * b * (a * b) = 1 := by rw [mul_assoc, e3, ha]
  constructor
  · intro hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl hx))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
        simp only [one_mul, mul_one, ha, hb, e1, e2, e3, e4, e5, e6, eq_self_iff_true, true_or,
          or_true]
    | inv x _ hx =>
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · simp
      · rw [ha1]
        simp
      · rw [hb1]
        simp
      · rw [mul_inv_rev, hb1, ha1, e2]
        simp
  · rintro (hk | hk | hk | hk) <;> rw [hk]
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem m11_mem_K_iff (h : L41GPh5 t L S x₁ x₂ lam rho) {k : G} :
    k ∈ closure ({t, lam} : Set G) ↔ k = 1 ∨ k = t ∨ k = lam ∨ k = t * lam :=
  m11_mem_closure_pair_iff (t_mul_self h.hyp) (n4_lam_sq h.toCtx0)
    (m13_t_comm_L h (generators_mem_L h.toCtx0).2.2)

theorem m11_K_le_nR (h : L41GPh8 t L S x₁ x₂ lam rho) :
    closure ({t, lam} : Set G) ≤ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [Subgroup.closure_le]
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  obtain ⟨-, hlamN, htN⟩ := n4_mem_normalizer_R h
  rcases hk with hk | hk
  · rw [hk]
    exact htN
  · rw [hk]
    exact hlamN

theorem m11_mem_V_cases (h : L41GPh8 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ l41V S t x₁ x₂) :
    ∃ r ∈ l41R t x₁ x₂ rho, g = r ∨ g = r * t ∨ g = r * lam ∨ g = r * (t * lam) := by
  rw [h.rfacts.V_eq] at hg
  have hg' : g ∈ ((l41R t x₁ x₂ rho ⊔ closure ({t, lam} : Set G) : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (m11_K_le_nR h)] at hg'
  obtain ⟨r, hr, k, hk, rfl⟩ := Set.mem_mul.mp hg'
  refine ⟨r, hr, ?_⟩
  rcases (m11_mem_K_iff h.toL41GPh5).mp hk with hk | hk | hk | hk
  · exact Or.inl (by rw [hk, mul_one])
  · exact Or.inr (Or.inl (by rw [hk]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hk])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hk])))

theorem m11_R_le_V (h : L41GPh8 t L S x₁ x₂ lam rho) :
    l41R t x₁ x₂ rho ≤ l41V S t x₁ x₂ := by
  rw [h.rfacts.V_eq]
  exact le_sup_left

theorem m11_t_mem_V (h : L41GPh8 t L S x₁ x₂ lam rho) : t ∈ l41V S t x₁ x₂ := by
  rw [h.rfacts.V_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem m11_lam_mem_V (h : L41GPh8 t L S x₁ x₂ lam rho) : lam ∈ l41V S t x₁ x₂ := by
  rw [h.rfacts.V_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem m11_card_V (h : L41GPh8 t L S x₁ x₂ lam rho) : Nat.card (l41V S t x₁ x₂) = 256 := by
  have h1 := h.normalizerFacts.card_V
  have hP : twoCore t = zpowers t := h.p2
  have hcP : Nat.card (twoCore t) = 2 := by
    rw [hP, Nat.card_zpowers, h.hyp.ord_t]
  have hW := pt_card_W h.toCtx0
  rw [hcP] at hW
  omega

theorem m11_conj_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G)) {u : G}
    (hu : u ∈ l41Y t x₁ x₂ rho) : g * u * g⁻¹ ∈ l41Y t x₁ x₂ rho := by
  obtain ⟨huR, hu2⟩ := (m11_mem_Y_iff h).mp hu
  refine (m11_mem_Y_iff h).mpr ⟨(Subgroup.mem_normalizer_iff.mp hg u).mp huR, ?_⟩
  calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    _ = 1 := by rw [hu2]; group

theorem m11_mem_normalizer_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G)) :
    g ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun u hu => m11_conj_Y h hg hu

end Y11A

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
