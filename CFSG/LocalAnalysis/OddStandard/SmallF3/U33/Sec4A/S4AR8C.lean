module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR8A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR8B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ANbB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section R

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_R_le_O (h : L41GPh1 t L S x₁ x₂ lam rho) :
    l41R t x₁ x₂ rho ≤ l41O2 t x₁ x₂ := by
  refine Subgroup.commutator_le.mpr (fun q hq g hg => ?_)
  have hgN : g ∈ l41N t x₁ x₂ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact Subgroup.zpow_mem _ (n4_rho_mem_N h) k
  have e : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ hq (pCoreOf_two_conj_mem hgN (Subgroup.inv_mem _ hq))

theorem n4_base_le_R (h : L41GPh3 t L S x₁ x₂ lam rho) :
    baseGrp x₁ x₂ ≤ l41R t x₁ x₂ rho := by
  rw [← h.comm_rho]
  exact Subgroup.commutator_mono (n4_W_le_O h) le_rfl

theorem n4_four_le_R (h : L41GPh3 t L S x₁ x₂ lam rho) :
    fourGrp x₁ x₂ ≤ l41R t x₁ x₂ rho :=
  (pt_four_le_base x₁ x₂).trans (n4_base_le_R h)

theorem n4_t_mem_O (h : L41GPh3 t L S x₁ x₂ lam rho) : t ∈ l41O2 t x₁ x₂ :=
  n4_W_le_O h (Subgroup.mem_sup_left h.hyp.mem_twoCore)

theorem n4_t_not_mem_four (h : Ctx0 t L S x₁ x₂ lam rho) : t ∉ fourGrp x₁ x₂ := by
  intro ht
  have hmem : t ∈ twoCore t ⊓ baseGrp x₁ x₂ :=
    ⟨h.hyp.mem_twoCore, pt_four_le_base x₁ x₂ ht⟩
  rw [pt_inf_base h, Subgroup.mem_bot] at hmem
  have h1 := h.hyp.ord_t
  rw [hmem, orderOf_one] at h1
  omega

theorem n4_R_main (h : L41GPh7 t L S x₁ x₂ lam rho) :
    (l41R t x₁ x₂ rho).relIndex (l41O2 t x₁ x₂) = 2 ∧ t ∉ l41R t x₁ x₂ rho := by
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hP : twoCore t = zpowers t := h.p2
  have htO : t ∈ l41O2 t x₁ x₂ := n4_t_mem_O h.toL41GPh3
  have hFcomm : ∀ a ∈ zpowers t, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => n4_zpowers_t_comm h.toL41GPh5 ha (pt_four_le_L h.toCtx0 hb)
  let FΓ : Subgroup ↥(l41O2 t x₁ x₂) := (fourGrp x₁ x₂).subgroupOf (l41O2 t x₁ x₂)
  haveI hnorm : FΓ.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using n4_O_norm_F h.toL41GPh3 (g : G) g.2 (x : G) hx⟩
  let c : ↥(l41O2 t x₁ x₂) →* ↥(l41O2 t x₁ x₂) :=
    { toFun := fun q => ⟨rho * q * rho⁻¹, pCoreOf_two_conj_mem hρN q.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hc : ∀ q : ↥(l41O2 t x₁ x₂), ((c q : ↥(l41O2 t x₁ x₂)) : G) = rho * q * rho⁻¹ :=
    fun _ => rfl
  have hc3 : ∀ x, c (c (c x)) = x := by
    intro x
    apply Subtype.ext
    rw [hc, hc, hc]
    have h3 : rho * rho * rho = 1 := by
      have := n4_rho_cube h.toCtx0
      rwa [pow_succ, pow_two] at this
    have e : rho * (rho * (rho * (x : G) * rho⁻¹) * rho⁻¹) * rho⁻¹ =
        (rho * rho * rho) * (x : G) * (rho * rho * rho)⁻¹ := by group
    rw [e, h3]
    group
  have hcF : ∀ f ∈ FΓ, c f ∈ FΓ := by
    intro f hf
    rw [Subgroup.mem_subgroupOf] at hf ⊢
    rw [hc]
    exact (n4_normal_F2 h.toL41GPh3).2 rho hρN _ hf
  have hab : ∀ x y : ↥(l41O2 t x₁ x₂), x * y * x⁻¹ * y⁻¹ ∈ FΓ := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    have := n4_O_comm h.toL41GPh6 x.2 y.2
    rw [commutatorElement_def] at this
    simpa using this
  have hsq : ∀ x : ↥(l41O2 t x₁ x₂), x * x ∈ FΓ := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    simpa using n4_O_sq h.toL41GPh6 x.2
  let τ : ↥(l41O2 t x₁ x₂) := ⟨t, htO⟩
  have hτ : c τ = τ := by
    apply Subtype.ext
    rw [hc]
    exact n4_conj_eq_of_comm (mem_invCent_iff.mp (L_le_invCent h.hyp h.rho_mem)).symm
  have hτF : τ ∉ FΓ := by
    rw [Subgroup.mem_subgroupOf]
    exact n4_t_not_mem_four h.toCtx0
  have hker : ∀ x : ↥(l41O2 t x₁ x₂), c x * x⁻¹ ∈ FΓ → x ∈ FΓ ⊔ zpowers τ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : ⁅(x : G), rho⁆ ∈ fourGrp x₁ x₂ := by
      have e : ⁅(x : G), rho⁆ = ((c x : G) * (x : G)⁻¹)⁻¹ := by
        rw [hc, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.inv_mem _ (by simpa using hx)
    have hmem : (x : G) ∈ ((zpowers t ⊔ fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← h.nbar.cent_O2bar_rho]
      exact ⟨x.2, hx'⟩
    obtain ⟨p, hp, f, hf, hpf⟩ := (mem_sup_iff_of_commute hFcomm).mp hmem
    have hpO : p ∈ l41O2 t x₁ x₂ := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      exact Subgroup.zpow_mem _ htO k
    have hfO : f ∈ l41O2 t x₁ x₂ := by
      have hfA : f ∈ ctxW t x₁ x₂ :=
        Subgroup.mem_sup_right (pt_four_le_base x₁ x₂ hf)
      exact n4_W_le_O h.toL41GPh3 hfA
    have hx2 : x = (⟨p, hpO⟩ : ↥(l41O2 t x₁ x₂)) * ⟨f, hfO⟩ := Subtype.ext hpf
    rw [hx2, sup_comm]
    refine Subgroup.mul_mem_sup ?_ ?_
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simp [τ])⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hf
  obtain ⟨RΓ, hR, hidx, hτR⟩ := coprime_core FΓ c hc3 hcF hab hsq τ hτ hτF hker
  have hone : ∀ q : ↥(l41O2 t x₁ x₂),
      ⁅(q : G), rho⁆ ∈ RΓ.map (l41O2 t x₁ x₂).subtype := by
    intro q
    refine Subgroup.mem_map.mpr ⟨q * (c q)⁻¹, (hR _).mpr ⟨q, 1, Subgroup.one_mem _, by simp⟩, ?_⟩
    rw [commutatorElement_def]
    simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, hc]
    group
  have hRmap : RΓ.map (l41O2 t x₁ x₂).subtype = l41R t x₁ x₂ rho := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨q, f, hf, rfl⟩ := (hR y).mp hy
      rw [Subgroup.mem_subgroupOf] at hf
      have hq : ⁅(q : G), rho⁆ ∈ l41R t x₁ x₂ rho :=
        Subgroup.commutator_mem_commutator q.2 (Subgroup.mem_zpowers rho)
      have e : (((q * (c q)⁻¹ * f : ↥(l41O2 t x₁ x₂))) : G) = ⁅(q : G), rho⁆ * (f : G) := by
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc]
        group
      simp only [Subgroup.subtype_apply]
      rw [e]
      exact Subgroup.mul_mem _ hq (n4_four_le_R h.toL41GPh3 hf)
    · refine Subgroup.commutator_le.mpr (fun q hq g hg => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hmod : rho ^ (k % 3) = rho ^ k := by
        have := zpow_mod_orderOf rho k
        rwa [h.ord_rho] at this
      rw [← hmod]
      have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk with hk | hk | hk
      · rw [hk]
        simp
      · rw [hk]
        simpa using hone ⟨q, hq⟩
      · rw [hk, zpow_two]
        have e : ⁅q, rho * rho⁆ = ⁅q, rho⁆ * ⁅rho * q * rho⁻¹, rho⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h2 := hone (c ⟨q, hq⟩)
        rw [hc] at h2
        exact Subgroup.mul_mem _ (hone ⟨q, hq⟩) h2
  refine ⟨?_, ?_⟩
  · have hsub : (l41R t x₁ x₂ rho).subgroupOf (l41O2 t x₁ x₂) = RΓ := by
      ext y
      rw [Subgroup.mem_subgroupOf, ← hRmap]
      constructor
      · intro hy
        obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
        have : y' = y := Subtype.ext hyy
        rwa [← this]
      · intro hy
        exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    show ((l41R t x₁ x₂ rho).subgroupOf (l41O2 t x₁ x₂)).index = 2
    rw [hsub]
    exact hidx
  · intro htR
    rw [← hRmap] at htR
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp htR
    have : y = τ := Subtype.ext hyt
    exact hτR (this ▸ hy)

theorem n4_card_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    Nat.card (l41R t x₁ x₂ rho) = 2 ^ 6 := by
  have hRO := n4_R_le_O h.toL41GPh1
  have h1 := Subgroup.relIndex_mul_card (H := l41R t x₁ x₂ rho) (K := l41O2 t x₁ x₂)
  rw [inf_eq_left.mpr hRO, (n4_R_main h).1] at h1
  have hP : twoCore t = zpowers t := h.p2
  have hcP : Nat.card (twoCore t) = 2 := by
    rw [hP, Nat.card_zpowers, h.hyp.ord_t]
  have hW := pt_card_W h.toCtx0
  rw [hcP] at hW
  have hO := n4_card_O2 h.toL41GPh3
  omega

end R

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
