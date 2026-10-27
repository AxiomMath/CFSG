module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YSplit
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckWedge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeCheck

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Matrix

theorem hom_wedge_of_coords {G : Type*} [Group G]
    {A Λ : Subgroup G} (κ : G → (Fin 4 → ZMod 2))
    (hκmul : ∀ a ∈ A, ∀ b ∈ A, κ (a * b) = κ a + κ b)
    (hκker : ∀ a ∈ A, κ a = 0 → a = 1)
    (hκsurj : ∀ v, ∃ a ∈ A, κ a = v)
    (gens : Fin 3 → G) (hgΛ : ∀ g, gens g ∈ Λ)
    (hgA : ∀ g, ∀ a ∈ A, gens g * a * (gens g)⁻¹ ∈ A)
    (hκconj : ∀ g, ∀ a ∈ A, κ (gens g * a * (gens g)⁻¹) = wedgeMatW g *ᵥ κ a) :
    ∀ β : G → G → G, (∀ a ∈ A, ∀ b ∈ A, β a b ∈ A) →
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, β (a * b) c = β a c * β b c) →
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, β a (b * c) = β a b * β a c) →
    (∀ a ∈ A, β a a = 1) →
    (∀ l ∈ Λ, ∀ a ∈ A, ∀ b ∈ A, β (l * a * l⁻¹) (l * b * l⁻¹) = l * β a b * l⁻¹) →
    ∀ a ∈ A, ∀ b ∈ A, β a b = 1 := by
  intro β hβA hβ₁ hβ₂ hβ₃ hβ₄
  have hκ1 : κ 1 = 0 := by
    have := hκmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  have hκinj : ∀ {x y : G}, x ∈ A → y ∈ A → κ x = κ y → x = y := by
    intro x y hx hy hxy
    have hxi : κ x⁻¹ = κ x := by
      have := hκmul x hx x⁻¹ (inv_mem hx)
      rw [mul_inv_cancel, hκ1] at this
      calc κ x⁻¹ = (κ x + κ x) + κ x⁻¹ := by rw [CharTwo.add_self_eq_zero, zero_add]
        _ = κ x + (κ x + κ x⁻¹) := by rw [add_assoc]
        _ = κ x := by rw [← this, add_zero]
    have h0 : κ (x⁻¹ * y) = 0 := by
      rw [hκmul _ (inv_mem hx) _ hy, hxi, hxy, CharTwo.add_self_eq_zero]
    have := hκker _ (mul_mem (inv_mem hx) hy) h0
    calc x = x * (x⁻¹ * y) := by rw [this, mul_one]
      _ = y := by group
  choose σ hσA hσκ using hκsurj
  have hσ : ∀ {a : G}, a ∈ A → σ (κ a) = a := fun ha => hκinj (hσA _) ha (hσκ _)
  set β' : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) :=
    fun u v => κ (β (σ u) (σ v)) with hβ'
  have hσmul : ∀ u v, σ (u + v) = σ u * σ v := fun u v => hκinj (hσA _)
    (mul_mem (hσA u) (hσA v)) (by rw [hσκ, hκmul _ (hσA u) _ (hσA v), hσκ, hσκ])
  have hzero := hom_wedge_W β'
    (fun u u' v => by
      simp only [hβ']
      rw [hσmul, hβ₁ _ (hσA u) _ (hσA u') _ (hσA v), hκmul _ (hβA _ (hσA u) _ (hσA v)) _
        (hβA _ (hσA u') _ (hσA v))])
    (fun u v v' => by
      simp only [hβ']
      rw [hσmul, hβ₂ _ (hσA u) _ (hσA v) _ (hσA v'), hκmul _ (hβA _ (hσA u) _ (hσA v)) _
        (hβA _ (hσA u) _ (hσA v'))])
    (fun u => by simp only [hβ']; rw [hβ₃ _ (hσA u), hκ1])
    (fun g u v => by
      simp only [hβ']
      have hgu : σ (wedgeMatW g *ᵥ u) = gens g * σ u * (gens g)⁻¹ := by
        rw [← hσκ u, ← hκconj g _ (hσA u), hσ (hgA g _ (hσA u)), hσκ]
      have hgv : σ (wedgeMatW g *ᵥ v) = gens g * σ v * (gens g)⁻¹ := by
        rw [← hσκ v, ← hκconj g _ (hσA v), hσ (hgA g _ (hσA v)), hσκ]
      rw [hgu, hgv, hβ₄ _ (hgΛ g) _ (hσA u) _ (hσA v), hκconj g _ (hβA _ (hσA u) _ (hσA v))])
  intro a ha b hb
  have h1 := hzero (κ a) (κ b)
  simp only [hβ', hσ ha, hσ hb] at h1
  exact hκker _ (hβA a ha b hb) h1

@[expose] noncomputable def Data.fCoordG {G : Type} [Group G] (d : Data G) (x : G) :
    Fin 4 → ZMod 2 := by
  classical
  exact if hx : x ∈ d.L then fCoord (d.η ⟨x, hx⟩) else 0

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem fCoordG_ι (α : SU52) : d.fCoordG (d.ι α) = fCoord α := by
  simp only [Data.fCoordG, d.ι_mem α, ↓reduceDIte, η_ι]

omit [Finite G] in
theorem hom_wedge_F (β : G → G → G)
    (hβA : ∀ a ∈ d.F, ∀ b ∈ d.F, β a b ∈ d.F)
    (hβ₁ : ∀ a ∈ d.F, ∀ b ∈ d.F, ∀ c ∈ d.F, β (a * b) c = β a c * β b c)
    (hβ₂ : ∀ a ∈ d.F, ∀ b ∈ d.F, ∀ c ∈ d.F, β a (b * c) = β a b * β a c)
    (hβ₃ : ∀ a ∈ d.F, β a a = 1)
    (hβ₄ : ∀ l ∈ d.Lev, ∀ a ∈ d.F, ∀ b ∈ d.F, β (l * a * l⁻¹) (l * b * l⁻¹) = l * β a b * l⁻¹) :
    ∀ a ∈ d.F, ∀ b ∈ d.F, β a b = 1 := by
  refine hom_wedge_of_coords (A := d.F) (Λ := d.Lev) d.fCoordG ?_ ?_ ?_
    (fun g => d.ι (wgSU g)) (fun g => ?_) (fun g a ha => Lev_conj_mem_F ?_ ha) ?_ β hβA hβ₁
    hβ₂ hβ₃ hβ₄
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β', hβ', rfl⟩
    rw [← map_mul, fCoordG_ι, fCoordG_ι, fCoordG_ι, fCoord_mul hα hβ']
  · rintro _ ⟨α, hα, rfl⟩ h0
    rw [fCoordG_ι] at h0
    rw [fCoord_ker hα h0, map_one]
  · intro v
    obtain ⟨α, hα, e⟩ := fCoord_surj v
    exact ⟨d.ι α, d.ι_mem_pull_iff.2 hα, by rw [fCoordG_ι, e]⟩
  · exact ⟨wgSU g, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (isUnit_det_wgA g).ne_zero, rfl⟩,
      rfl⟩
  · exact ⟨wgSU g, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (isUnit_det_wgA g).ne_zero, rfl⟩,
      rfl⟩
  · rintro g _ ⟨α, hα, rfl⟩
    rw [ι_conj, fCoordG_ι, fCoordG_ι, fCoord_conj_wgSU g hα]

theorem U_comm_mul_left
    (h : d.Hyp) {x y z : G} (hx : x ∈ d.U) (hy : y ∈ d.U)
    (hz : z ∈ d.U) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz := h.commutator_U_mem_F hy hz
  have e : ⁅x * y, z⁆ = (x * ⁅y, z⁆ * x⁻¹) * ⁅x, z⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, h.U_comm_F hx hyz, mul_inv_cancel_right]
  exact h.F_comm hyz (h.commutator_U_mem_F hx hz)

theorem U_comm_mul_right
    (h : d.Hyp) {x y z : G} (hx : x ∈ d.U) (hy : y ∈ d.U)
    (hz : z ∈ d.U) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hxz := h.commutator_U_mem_F hx hz
  have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, h.U_comm_F hy hxz, mul_inv_cancel_right]

theorem eq_mul_of_crossed_eq_E₂
    (h : d.Hyp) {x y : G} (hx : x ∈ d.E₂) (hy : y ∈ d.E₂)
    (hxy : x⁻¹ * d.t * x * d.t = y⁻¹ * d.t * y * d.t) : x⁻¹ * y ∈ d.F := by
  have hk : x * y⁻¹ ∈ d.F := by
    rw [← h.E₂_inf_H]
    refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem hy), mem_centralizer_singleton_iff.2 ?_⟩
    have e1 : x⁻¹ * d.t * x = y⁻¹ * d.t * y := mul_right_cancel hxy
    calc x * y⁻¹ * d.t = x * (y⁻¹ * d.t * y) * y⁻¹ := by group
      _ = x * (x⁻¹ * d.t * x) * y⁻¹ := by rw [e1]
      _ = d.t * (x * y⁻¹) := by group
  have e : x⁻¹ * y = x⁻¹ * (x * y⁻¹)⁻¹ * x := by group
  rw [e, mul_assoc, ← h.U_comm_F (h.E₂_le_U hx) (inv_mem hk), ← mul_assoc, inv_mul_cancel,
    one_mul]
  exact inv_mem hk

theorem E₂_comm
    (h : d.Hyp) {x y : G}
    (hx : x ∈ d.E₂) (hy : y ∈ d.E₂) : x * y = y * x := by
  have hlift : ∀ a ∈ d.F, ∃ z ∈ d.E₂, z⁻¹ * d.t * z * d.t = a := fun a ha =>
    h.exists_E₂_crossed_eq ha
  choose! s hsE hscr using hlift
  have hU : ∀ {z}, z ∈ d.E₂ → z ∈ d.U := fun hz => h.E₂_le_U hz
  have hcr : ∀ {z}, z ∈ d.E₂ → z⁻¹ * d.t * z * d.t ∈ d.F := fun hz => h.U_crossed_mem_F (hU hz)
  have hcomm_eq : ∀ {z₁ z₂ w₁ w₂ : G}, z₁ ∈ d.E₂ → z₂ ∈ d.E₂ → w₁ ∈ d.E₂ → w₂ ∈ d.E₂ →
      z₁⁻¹ * d.t * z₁ * d.t = w₁⁻¹ * d.t * w₁ * d.t →
      z₂⁻¹ * d.t * z₂ * d.t = w₂⁻¹ * d.t * w₂ * d.t → ⁅z₁, z₂⁆ = ⁅w₁, w₂⁆ := by
    intro z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂ h1 h2
    have hk₁ := h.eq_mul_of_crossed_eq_E₂ hw₁ hz₁ h1.symm
    have hk₂ := h.eq_mul_of_crossed_eq_E₂ hw₂ hz₂ h2.symm
    obtain ⟨k₁, hk₁', rfl⟩ : ∃ k ∈ d.F, z₁ = w₁ * k := ⟨_, hk₁, by group⟩
    obtain ⟨k₂, hk₂', rfl⟩ : ∃ k ∈ d.F, z₂ = w₂ * k := ⟨_, hk₂, by group⟩
    have z1 : ∀ {a b : G}, a ∈ d.F → b ∈ d.U → ⁅a, b⁆ = 1 := fun ha hb => by
      rw [commutatorElement_def, ← h.U_comm_F hb ha]
      group
    have z2 : ∀ {a b : G}, a ∈ d.U → b ∈ d.F → ⁅a, b⁆ = 1 := fun ha hb => by
      rw [commutatorElement_def, h.U_comm_F ha hb]
      group
    rw [h.U_comm_mul_left (hU hw₁) (h.F_le_U hk₁') (mul_mem (hU hw₂) (h.F_le_U hk₂')),
      h.U_comm_mul_right (hU hw₁) (hU hw₂) (h.F_le_U hk₂'),
      z2 (hU hw₁) hk₂', z1 hk₁' (mul_mem (hU hw₂) (h.F_le_U hk₂'))]
    simp
  have hmulcr : ∀ {a b}, a ∈ d.F → b ∈ d.F →
      (s a * s b)⁻¹ * d.t * (s a * s b) * d.t = (s (a * b))⁻¹ * d.t * s (a * b) * d.t := by
    intro a b ha hb
    rw [crossed_mul h.t_mul_t (h.U_comm_F (hU (hsE b hb)) (hcr (hsE a ha))).symm, hscr a ha,
      hscr b hb, hscr _ (mul_mem ha hb)]
  have c1 : ∀ a ∈ d.F, ∀ b ∈ d.F, ⁅s a, s b⁆ ∈ d.F := fun a ha b hb =>
    h.commutator_U_mem_F (hU (hsE a ha)) (hU (hsE b hb))
  have c2 : ∀ a ∈ d.F, ∀ b ∈ d.F, ∀ c ∈ d.F, ⁅s (a * b), s c⁆ = ⁅s a, s c⁆ * ⁅s b, s c⁆ := by
    intro a ha b hb c hc
    rw [hcomm_eq (hsE _ (mul_mem ha hb)) (hsE c hc) (mul_mem (hsE a ha) (hsE b hb)) (hsE c hc)
      (hmulcr ha hb).symm rfl, h.U_comm_mul_left (hU (hsE a ha)) (hU (hsE b hb))
      (hU (hsE c hc))]
  have c3 : ∀ a ∈ d.F, ∀ b ∈ d.F, ∀ c ∈ d.F, ⁅s a, s (b * c)⁆ = ⁅s a, s b⁆ * ⁅s a, s c⁆ := by
    intro a ha b hb c hc
    rw [hcomm_eq (hsE a ha) (hsE _ (mul_mem hb hc)) (hsE a ha) (mul_mem (hsE b hb) (hsE c hc))
      rfl (hmulcr hb hc).symm, h.U_comm_mul_right (hU (hsE a ha)) (hU (hsE b hb))
      (hU (hsE c hc))]
  have c4 : ∀ a ∈ d.F, ⁅s a, s a⁆ = 1 := fun a _ => commutatorElement_self _
  have c5 : ∀ l ∈ d.Lev, ∀ a ∈ d.F, ∀ b ∈ d.F,
      ⁅s (l * a * l⁻¹), s (l * b * l⁻¹)⁆ = l * ⁅s a, s b⁆ * l⁻¹ := by
    intro l hl a ha b hb
    have hlt := h.Lev_comm_t hl
    have hlN := (h.le_normalizer_E₂).1 hl
    have hla : l * a * l⁻¹ ∈ d.F := Lev_conj_mem_F hl ha
    have hlb : l * b * l⁻¹ ∈ d.F := Lev_conj_mem_F hl hb
    have hsa : l * s a * l⁻¹ ∈ d.E₂ := (mem_normalizer_iff.1 hlN _).1 (hsE a ha)
    have hsb : l * s b * l⁻¹ ∈ d.E₂ := (mem_normalizer_iff.1 hlN _).1 (hsE b hb)
    rw [hcomm_eq (hsE _ hla) (hsE _ hlb) hsa hsb
      (by rw [hscr _ hla, crossed_conj hlt, hscr a ha])
      (by rw [hscr _ hlb, crossed_conj hlt, hscr b hb])]
    simp only [commutatorElement_def]
    group
  have hβ := hom_wedge_F (d := d) (fun a b => ⁅s a, s b⁆) c1 c2 c3 c4 c5
  have hxy : ⁅x, y⁆ = 1 := by
    rw [hcomm_eq hx hy (hsE _ (hcr hx)) (hsE _ (hcr hy)) (hscr _ (hcr hx)).symm
      (hscr _ (hcr hy)).symm]
    exact hβ _ (hcr hx) _ (hcr hy)
  rw [commutatorElement_def] at hxy
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hxy, one_mul]

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
