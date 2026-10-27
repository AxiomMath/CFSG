module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9AEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Pure

variable {G : Type} [Group G]

theorem late_klein_trichE {z t : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z)
    {a ε₁ ε₂ : G} (ha : a = z ∨ a = t ∨ a = z * t)
    (h₁ : ε₁ = 1 ∨ ε₁ = z ∨ ε₁ = t ∨ ε₁ = z * t) (h₂ : ε₂ = 1 ∨ ε₂ = z ∨ ε₂ = t ∨ ε₂ = z * t)
    (h₂1 : ε₂ ≠ 1) (h₂a : ε₂ ≠ a) (h₁1 : ε₁ ≠ 1) (h₁a : ε₁ ≠ a) :
    ε₁ = ε₂ ∨ ε₁ = ε₂ * a := by
  have hzzt : z * (z * t) = t := by rw [← mul_assoc, hz2, one_mul]
  have htzt : t * (z * t) = z := by rw [hzt, ← mul_assoc, ht2, one_mul]
  have hztz : (z * t) * z = t := by rw [hzt, mul_assoc, hz2, mul_one]
  have hztt : (z * t) * t = z := by rw [mul_assoc, ht2, mul_one]
  rcases ha with ha | ha | ha <;> rcases h₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ <;> subst ha h₁ h₂ <;>
    first
    | exact absurd rfl h₂1
    | exact absurd rfl h₁1
    | exact absurd rfl h₂a
    | exact absurd rfl h₁a
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact Or.inr hzt
    | exact Or.inr hztz.symm
    | exact Or.inr hztt.symm
    | exact Or.inr hzzt.symm
    | exact Or.inr htzt.symm

end Pure

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20G.late_S_act_z (d : Std20G K K' J S R R' W V z t) {g : G}
    (hg : g ∈ (S : Subgroup G)) : g * z * g⁻¹ = z := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hg)
  rw [h]
  group

theorem Std20G.late_S_act_t (d : Std20G K K' J S R R' W V z t) {g : G}
    (hg : g ∈ (S : Subgroup G)) : g * t * g⁻¹ = t ∨ g * t * g⁻¹ = z * t := by
  have hW : g * t * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hg) t).mp d.late_t_mem_W
  have h2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [d.viol.hzJ.sq]; group
  rcases d.late_inv_W _ hW h2 with h | h | h | h
  · exfalso
    apply d.viol.hzJ.ne_one
    have : g * t * g⁻¹ = 1 := h
    simpa using this
  · exfalso
    apply d.late_ne_inv
    have h1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [h1, h]
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [d.late_S_act_z hg]
      _ = z := by group
  · exact Or.inl h
  · exact Or.inr h

theorem Std20G.late_members_of_inv (d : Std20G K K' J S R R' W V z t) {m e : G}
    (hme : m * z * m⁻¹ = e) {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K)
    (hLe : IsUniqueInvolution L e) : L = conjSub m K ∨ L = conjSub m K' := by
  have hL₂ : conjSub m⁻¹ L ∈ CoreAssembly.conjClass K := d.hyp.conjInvariant m⁻¹ L hL
  have hinv : m⁻¹ * e * m⁻¹⁻¹ = z := by rw [← hme]; group
  have hL₂e : IsUniqueInvolution (conjSub m⁻¹ L) z := hinv ▸ hLe.conj m⁻¹
  have hmem : conjSub m⁻¹ L ∈ twinSet (CoreAssembly.conjClass K) K :=
    ⟨hL₂, z, d.viol.hzK, hL₂e⟩
  rw [d.twins] at hmem
  have hLe' : L = conjSub m (conjSub m⁻¹ L) := (conjSub_conjSub_inv m L).symm
  rcases hmem with h | h
  · left
    rw [hLe', h]
  · right
    rw [hLe', h]

theorem Std20G.late_member_data (d : Std20G K K' J S R R' W V z t) (m : G) :
    conjSub m K ∈ CoreAssembly.conjClass K ∧ conjSub m K' ∈ CoreAssembly.conjClass K ∧
      conjSub m K ≠ conjSub m K' ∧ IsUniqueInvolution (conjSub m K) (m * z * m⁻¹) ∧
      IsUniqueInvolution (conjSub m K') (m * z * m⁻¹) :=
  ⟨d.hyp.conjInvariant m K d.late_mem_K, d.hyp.conjInvariant m K' d.late_mem_K',
    fun h => d.ne (conjSub_injective m h).symm, d.viol.hzK.conj m, d.late_hzK'.conj m⟩

theorem Std20G.late_two_lines (d : Std20G K K' J S R R' W V z t)
    (hzt : z * t = t * z) {a₀ α b₁ b₂ : G}
    (ha₀ : a₀ ≠ 1) (ha₀2 : a₀ * a₀ = 1) (hα : α ∈ W) (hb₁ : b₁ ∈ W) (hb₂ : b₂ ∈ W)
    (hαa : α * α = a₀) (hb₁a : b₁ * b₁ = a₀) (hb₂a : b₂ * b₂ = a₀)
    (hne : Subgroup.zpowers b₁ ≠ Subgroup.zpowers b₂) :
    Subgroup.zpowers α = Subgroup.zpowers b₁ ∨ Subgroup.zpowers α = Subgroup.zpowers b₂ := by
  have hWc := d.late_hWc
  have ha₀W : a₀ ∈ W := hb₁a ▸ W.mul_mem hb₁ hb₁
  have ha₀' : a₀ = z ∨ a₀ = t ∨ a₀ = z * t := by
    rcases d.late_inv_W a₀ ha₀W ha₀2 with h | h | h | h
    · exact absurd h ha₀
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hinv : ∀ {b : G}, b * b = a₀ → b⁻¹ = b * a₀ := by
    intro b hb
    have h4 : b * b * (b * b) = 1 := by rw [hb, ha₀2]
    calc b⁻¹ = b⁻¹ * (b * b * (b * b)) := by rw [h4, mul_one]
      _ = b * (b * b) := by group
      _ = b * a₀ := by rw [hb]
  have hzp : ∀ {b : G}, b * b = a₀ → Subgroup.zpowers (b * a₀) = Subgroup.zpowers b := by
    intro b hb
    rw [← hinv hb, Subgroup.zpowers_inv]
  have hε : ∀ {w w' : G}, w ∈ W → w' ∈ W → w * w = a₀ → w' * w' = a₀ →
      (w * w'⁻¹ = 1 ∨ w * w'⁻¹ = z ∨ w * w'⁻¹ = t ∨ w * w'⁻¹ = z * t) := by
    intro w w' hw hw' h h'
    refine d.late_inv_W _ (W.mul_mem hw (W.inv_mem hw')) ?_
    have hc : w'⁻¹ * w = w * w'⁻¹ := hWc _ (W.inv_mem hw') _ hw
    calc w * w'⁻¹ * (w * w'⁻¹) = w * (w'⁻¹ * w) * w'⁻¹ := by group
      _ = w * (w * w'⁻¹) * w'⁻¹ := by rw [hc]
      _ = (w * w) * (w' * w')⁻¹ := by group
      _ = 1 := by rw [h, h']; exact mul_inv_cancel a₀
  have e₁ := hε hα hb₁ hαa hb₁a
  have e₂ := hε hb₂ hb₁ hb₂a hb₁a
  by_cases h₁1 : α * b₁⁻¹ = 1
  · left
    have : α = b₁ := by
      calc α = α * b₁⁻¹ * b₁ := by group
        _ = b₁ := by rw [h₁1, one_mul]
    rw [this]
  by_cases h₁a : α * b₁⁻¹ = a₀
  · left
    have : α = b₁ * a₀ := by
      calc α = α * b₁⁻¹ * b₁ := by group
        _ = a₀ * b₁ := by rw [h₁a]
        _ = b₁ * a₀ := hWc a₀ ha₀W b₁ hb₁
    rw [this, hzp hb₁a]
  have h₂1 : b₂ * b₁⁻¹ ≠ 1 := fun h => hne (by
    have : b₂ = b₁ := by
      calc b₂ = b₂ * b₁⁻¹ * b₁ := by group
        _ = b₁ := by rw [h, one_mul]
    rw [this])
  have h₂a : b₂ * b₁⁻¹ ≠ a₀ := fun h => hne (by
    have : b₂ = b₁ * a₀ := by
      calc b₂ = b₂ * b₁⁻¹ * b₁ := by group
        _ = a₀ * b₁ := by rw [h]
        _ = b₁ * a₀ := hWc a₀ ha₀W b₁ hb₁
    rw [this, hzp hb₁a])
  right
  rcases late_klein_trichE d.viol.hzK.sq d.viol.hzJ.sq hzt ha₀' e₁ e₂ h₂1 h₂a h₁1 h₁a
    with h | h
  · have : α = b₂ := mul_right_cancel h
    rw [this]
  · have : α = b₂ * a₀ := by
      calc α = α * b₁⁻¹ * b₁ := by group
        _ = (b₂ * b₁⁻¹ * a₀) * b₁ := by rw [h]
        _ = b₂ * (b₁⁻¹ * a₀) * b₁ := by group
        _ = b₂ * (a₀ * b₁⁻¹) * b₁ := by rw [hWc _ (W.inv_mem hb₁) _ ha₀W]
        _ = b₂ * a₀ := by group
    rw [this, hzp hb₂a]

theorem Std20G.late_swap_J (d : Std20G K K' J S R R' W V z t) {σ ρ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσt : σ * t * σ⁻¹ = t) (hρ : ρ ∈ R)
    (hσJ : conjSub σ (conjSub ρ J) = conjSub ρ J) : False := by
  have hρS : ρ ∈ (S : Subgroup G) := d.hRS hρ
  have hρK : ρ ∈ K := d.hR.1 hρ
  have hσz := d.late_S_act_z hσ
  have hσ₂S : ρ⁻¹ * σ * ρ ∈ (S : Subgroup G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hρS) hσ) hρS
  have hfix : ∀ y : G, (y = t ∨ y = z * t) → σ * y * σ⁻¹ = y := by
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact hσt
    · rw [hy]
      calc σ * (z * t) * σ⁻¹ = (σ * z * σ⁻¹) * (σ * t * σ⁻¹) := by group
        _ = z * t := by rw [hσz, hσt]
  have hσ₂t : (ρ⁻¹ * σ * ρ) * t * (ρ⁻¹ * σ * ρ)⁻¹ = t := by
    have h := hfix _ (d.late_S_act_t hρS)
    calc (ρ⁻¹ * σ * ρ) * t * (ρ⁻¹ * σ * ρ)⁻¹
        = ρ⁻¹ * (σ * (ρ * t * ρ⁻¹) * σ⁻¹) * ρ := by group
      _ = ρ⁻¹ * (ρ * t * ρ⁻¹) * ρ := by rw [h]
      _ = t := by group
  have hσ₂J : conjSub (ρ⁻¹ * σ * ρ) J = J := by
    rw [conjSub_mul, conjSub_mul, hσJ, conjSub_inv_conjSub]
  have hX2 : IsPGroup 2 ↥(Subgroup.zpowers (ρ⁻¹ * σ * ρ)) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hσ₂S)
  have hcomm : (ρ⁻¹ * σ * ρ) * t = t * (ρ⁻¹ * σ * ρ) := by
    calc (ρ⁻¹ * σ * ρ) * t = ((ρ⁻¹ * σ * ρ) * t * (ρ⁻¹ * σ * ρ)⁻¹) * (ρ⁻¹ * σ * ρ) := by group
      _ = t * (ρ⁻¹ * σ * ρ) := by rw [hσ₂t]
  have hiff := d.late_98_iff d.late_JW d.late_hW hX2 (Subgroup.zpowers_le.mpr hσ₂S)
    (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left hcomm k).eq))
  have hJ : ∀ x ∈ Subgroup.zpowers (ρ⁻¹ * σ * ρ), conjSub x J = J := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr
      (mem_normalizer_iff_conjSub_eq.mpr hσ₂J)) hx)
  have hK₂ := hiff.mpr hJ (ρ⁻¹ * σ * ρ) (Subgroup.mem_zpowers _)
  have hσK₂ : conjSub σ K = K := by
    have h1 : σ = ρ * (ρ⁻¹ * σ * ρ) * ρ⁻¹ := by group
    have hρK' : conjSub ρ⁻¹ K = K := conjSub_eq_self_of_mem (Subgroup.inv_mem _ hρK)
    calc conjSub σ K = conjSub (ρ * (ρ⁻¹ * σ * ρ) * ρ⁻¹) K := by rw [← h1]
      _ = conjSub ρ (conjSub (ρ⁻¹ * σ * ρ) (conjSub ρ⁻¹ K)) := by
          rw [conjSub_mul, conjSub_mul]
      _ = K := by rw [hρK', hK₂, conjSub_eq_self_of_mem hρK]
  exact d.ne (hσK.symm.trans hσK₂)

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
