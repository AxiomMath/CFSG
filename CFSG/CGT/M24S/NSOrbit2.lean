module

public import CFSG.CGT.M24S.NSOrbit

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem disp_mul_right' {g y s : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hs : s ∈ T) (hT : y⁻¹ * g * y * g⁻¹ ∈ T) :
    disp c g (y * s) = tail (c.vec s) + disp c g y + blk (c.mat g) *ᵥ tail (c.vec s) := by
  have hc : g * s * g⁻¹ ∈ T := c.conj_mem hg.1 hs
  have e : (y * s)⁻¹ * g * (y * s) * g⁻¹ = s⁻¹ * (y⁻¹ * g * y * g⁻¹) * (g * s * g⁻¹) := by
    group
  rw [disp, e, c.vec_mul (T.mul_mem (T.inv_mem hs) hT) hc, c.vec_mul (T.inv_mem hs) hT,
    vec_inv c hs, GL4.tail_add, GL4.tail_add, tail_vec_conj c hg hs, disp]

theorem top_eq_zero_of_mem_T {s : G} (hs : s ∈ T) : top (c.mat s) = 0 := by
  rw [(c.mat_eq_one_iff (c.le hs)).2 hs, top_one]

theorem exists_over (v : Fin 3 → ZMod 2) : ∃ y : G, Over c v y := by
  by_cases hv : v = 0
  · refine ⟨1, c.E.one_mem, ?_, one_pow 2⟩
    rw [c.mat_one, top_one, hv]
  obtain ⟨x, hx, hxm⟩ := c.exists_mem_E v
  have hxv : top (c.mat x) = v := by rw [hxm, top_mk4]
  rcases c.sq_eq_one_or_eq_z hx with h | h
  · exact ⟨x, hx, hxv, h⟩
  obtain ⟨u, hu⟩ := exists_dotProduct_eq_one v hv
  obtain ⟨s, hs, hsv⟩ := c.exists_vec_eq (Fin.cons 0 u)
  have hsu : tail (c.vec s) = u := by rw [hsv, tail_cons_zero]
  refine ⟨x * s, c.E.mul_mem hx (c.T_le_E hs), ?_, ?_⟩
  · rw [top_mul_of_mem_E c hx (c.T_le_E hs), hxv, top_eq_zero_of_mem_T c hs, add_zero]
  · rw [sq_mul_of_dot_one c hx hs (by rw [hxv, hsu, dotProduct_comm]; exact hu), h, ← pow_two,
      c.z_sq]

theorem dot_disp_eq_zero {g : G} {v : Fin 3 → ZMod 2} {y : G}
    (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hv : vecMul v (blk (c.mat g)) = v)
    (hy : Over c v y) : v ⬝ᵥ disp c g y = 0 := by
  have hy' : Over c v (g * y * g⁻¹) :=
    ⟨c.conj_mem_E hg hy.1, top_conj_eq c hg hy.1 hy.2.1 hv,
      by rw [conj_pow, hy.2.2, mul_one, mul_inv_cancel]⟩
  obtain ⟨s, -, hys, hvs⟩ := exists_mul_of_over c hy hy'
  have e : y⁻¹ * g * y * g⁻¹ = s := by
    rw [show y⁻¹ * g * y * g⁻¹ = y⁻¹ * (g * y * g⁻¹) by group, hys, inv_mul_cancel_left]
  rw [disp, e]
  exact hvs

theorem det_blk_ne_zero {g : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) :
    (blk (c.mat g)).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (blk_mul_inv c hg)
  rw [det_mul, h, zero_mul, det_one] at h1
  exact zero_ne_one h1

@[expose] def StabV₀ (g : G) : Prop :=
  g ∈ H ⊓ Subgroup.centralizer ({t} : Set G) ∧ vecMul v₀ (blk (c.mat g)) = v₀

theorem stab_mul {g₁ g₂ : G} (h₁ : StabV₀ c g₁) (h₂ : StabV₀ c g₂) : StabV₀ c (g₁ * g₂) :=
  ⟨mul_mem h₁.1 h₂.1, by rw [blk_mul_of_mem c h₁.1 h₂.1.1, ← vecMul_vecMul, h₁.2, h₂.2]⟩

theorem mem_T_of_stab {g y : G} (hg : StabV₀ c g) (hy : Over c v₀ y) :
    y⁻¹ * g * y * g⁻¹ ∈ T :=
  mem_T_of_fix c hg.1 hy.1 (by rw [hy.2.1]; exact hg.2)

theorem disp_mul_stab {g₁ g₂ y : G} (h₁ : StabV₀ c g₁) (h₂ : StabV₀ c g₂) (hy : Over c v₀ y) :
    disp c (g₁ * g₂) y = disp c g₁ y + blk (c.mat g₁) *ᵥ disp c g₂ y :=
  disp_mul c h₁.1 (mem_T_of_stab c h₁ hy) (mem_T_of_stab c h₂ hy)

theorem stab_one : StabV₀ c 1 :=
  ⟨one_mem _, by rw [c.mat_one, blk_one, vecMul_one]⟩

theorem exists_fixed_over_v₀ (hF : Fixes c v₀) :
    ∃ e : G, Over c v₀ e ∧ ∀ g : G, StabV₀ c g → disp c g e = 0 := by
  obtain ⟨e₀, he₀⟩ := exists_over c v₀
  obtain ⟨ω, hω, hωB⟩ := c.exists_mem_cent ω₀ det_ω₀
  obtain ⟨τ, hτ, hτB⟩ := c.exists_mem_cent τ₀ det_τ₀
  have sω : StabV₀ c ω := ⟨hω, by rw [hωB]; exact vecMul_v₀_ω₀⟩
  have sτ : StabV₀ c τ := ⟨hτ, by rw [hτB]; exact vecMul_v₀_τ₀⟩
  have hE : ∀ g, StabV₀ c g → blk (c.mat g) = 1 → disp c g e₀ = 0 := fun g hg h1 =>
    disp_of_mem_E c (mem_E_of_blk_eq_one c hg.1 h1) he₀.1
  have hblk : ∀ {g₁ g₂ : G}, StabV₀ c g₁ → StabV₀ c g₂ →
      blk (c.mat (g₁ * g₂)) = blk (c.mat g₁) * blk (c.mat g₂) := fun h₁ h₂ =>
    blk_mul_of_mem c h₁.1 h₂.1.1
  have r1 : disp c ω e₀ + ω₀ *ᵥ disp c ω e₀ + ω₀ *ᵥ (ω₀ *ᵥ disp c ω e₀) = 0 := by
    have h := hE _ (stab_mul c sω (stab_mul c sω sω))
      (by rw [hblk sω (stab_mul c sω sω), hblk sω sω, hωB, ← mul_assoc, ω₀_cube])
    rwa [disp_mul_stab c sω (stab_mul c sω sω) he₀, disp_mul_stab c sω sω he₀, hωB, mulVec_add,
      ← add_assoc] at h
  have r2 : disp c τ e₀ + τ₀ *ᵥ disp c τ e₀ = 0 := by
    have h := hE _ (stab_mul c sτ sτ) (by rw [hblk sτ sτ, hτB, τ₀_sq])
    rwa [disp_mul_stab c sτ sτ he₀, hτB] at h
  have sτω := stab_mul c sτ sω
  have hd : disp c (τ * ω) e₀ = disp c τ e₀ + τ₀ *ᵥ disp c ω e₀ := by
    rw [disp_mul_stab c sτ sω he₀, hτB]
  have r3 : (disp c τ e₀ + τ₀ *ᵥ disp c ω e₀) +
      (τ₀ * ω₀) *ᵥ (disp c τ e₀ + τ₀ *ᵥ disp c ω e₀) = 0 := by
    have h := hE _ (stab_mul c sτω sτω) (by rw [hblk sτω sτω, hblk sτ sω, hτB, hωB, τ₀ω₀_sq])
    rwa [disp_mul_stab c sτω sτω he₀, hblk sτ sω, hτB, hωB, hd] at h
  obtain ⟨u, hu0, hau, hbu⟩ := cocycleSol_of _ _ (dot_disp_eq_zero c hω sω.2 he₀)
    (dot_disp_eq_zero c hτ sτ.2 he₀) r1 r2 r3
  obtain ⟨s, hs, hsv⟩ := c.exists_vec_eq (Fin.cons 0 u)
  have hsu : tail (c.vec s) = u := by rw [hsv, tail_cons_zero]
  have he : Over c v₀ (e₀ * s) :=
    ⟨c.E.mul_mem he₀.1 (c.T_le_E hs), by
      rw [top_mul_of_mem_E c he₀.1 (c.T_le_E hs), he₀.2.1, top_eq_zero_of_mem_T c hs, add_zero],
      by rw [sq_mul_of_dot_zero c he₀.1 hs (by rw [he₀.2.1, hsu]; exact hu0), he₀.2.2]⟩
  refine ⟨e₀ * s, he, ?_⟩
  have hZ : ∀ {g₁ g₂ : G}, StabV₀ c g₁ → disp c g₁ (e₀ * s) = 0 → StabV₀ c g₂ →
      disp c g₂ (e₀ * s) = 0 → disp c (g₁ * g₂) (e₀ * s) = 0 := fun h₁ d₁ h₂ d₂ => by
    rw [disp_mul_stab c h₁ h₂ he, d₁, d₂, mulVec_zero, add_zero]
  have dω : disp c ω (e₀ * s) = 0 := by
    rw [disp_mul_right' c hω hs (mem_T_of_stab c sω he₀), hsu, hau, hωB, ← add_assoc,
      vec_add_self, zero_add, vec_add_self]
  have dτ : disp c τ (e₀ * s) = 0 := by
    rw [disp_mul_right' c hτ hs (mem_T_of_stab c sτ he₀), hsu, hbu, hτB, ← add_assoc,
      vec_add_self, zero_add, vec_add_self]
  have d1 : disp c 1 (e₀ * s) = 0 := disp_of_mem_E c c.E.one_mem he.1
  have key : ∀ (g r : G) (cc : Fin 3 → ZMod 2), StabV₀ c g → v₀ ⬝ᵥ cc = 0 → StabV₀ c r →
      disp c r (e₀ * s) = 0 → blk (c.mat g) = lv cc v₀ * blk (c.mat r) →
      disp c g (e₀ * s) = 0 := by
    intro g r cc hg hcc hr dr hB
    have hg' : StabV₀ c (g * r⁻¹) := by
      refine ⟨mul_mem hg.1 (inv_mem hr.1), ?_⟩
      rw [blk_mul_of_mem c hg.1 (H.inv_mem hr.1.1), hB, mul_assoc, blk_mul_inv c hr.1,
        mul_one, vecMul_lv_self hcc]
    have hB' : blk (c.mat (g * r⁻¹)) = lv cc v₀ := by
      rw [blk_mul_of_mem c hg.1 (H.inv_mem hr.1.1), hB, mul_assoc, blk_mul_inv c hr.1,
        mul_one]
    have h := hZ hg' (hF _ hg'.1 cc hcc hB' _ he) hr dr
    rwa [inv_mul_cancel_right] at h
  intro g hg
  obtain ⟨cc, hcc, hR⟩ := stab_decomp _ hg.2 (det_blk_ne_zero c hg.1)
  have sωω := stab_mul c sω sω
  rcases hR with h | h | h | h | h | h
  · exact key g 1 cc hg hcc (stab_one c) d1 (by rw [h, c.mat_one, blk_one, mul_one])
  · exact key g ω cc hg hcc sω dω (by rw [h, hωB])
  · exact key g (ω * ω) cc hg hcc sωω (hZ sω dω sω dω) (by rw [h, hblk sω sω, hωB])
  · exact key g τ cc hg hcc sτ dτ (by rw [h, hτB])
  · exact key g (ω * τ) cc hg hcc (stab_mul c sω sτ) (hZ sω dω sτ dτ)
      (by rw [h, hblk sω sτ, hωB, hτB])
  · exact key g (ω * ω * τ) cc hg hcc (stab_mul c sωω sτ) (hZ sωω (hZ sω dω sω dω) sτ dτ)
      (by rw [h, hblk sωω sτ, hblk sω sω, hωB, hτB])

end CFSG.CGT.M24S.NSB
