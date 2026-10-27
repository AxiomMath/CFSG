module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ECtx

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

private theorem isLong_titsZ_aux : IsLong titsZ := ⟨1, one_mem _, by group⟩

private theorem titsZ_ne_one_aux {zp y0 : Equiv.Perm (Fin 1755)} (hF6 : F6Facts zp y0) :
    titsZ ≠ 1 := by
  intro h
  apply hF6.prod_not_long
  rw [h, one_mul]
  exact hF6.zp_long

private theorem zp_ne_one_aux {zp y0 : Equiv.Perm (Fin 1755)} (hF6 : F6Facts zp y0) :
    zp ≠ 1 := by
  intro h
  apply hF6.prod_not_long
  rw [h, mul_one]
  exact isLong_titsZ_aux

private theorem inA_mem_Am {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) : inA a ∈ Am :=
  Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, ha⟩

private theorem inA_inj {a b : Equiv.Perm (Fin 1755)} (h : inA a = inA b) : a = b := by
  simpa [inA] using h

private theorem inA_eq_one {a : Equiv.Perm (Fin 1755)} (h : inA a = 1) : a = 1 := by
  simpa [inA] using congrArg Prod.snd h

private theorem model_I1 (a b : Equiv.Perm (Fin 1755)) :
    tauH * inA a * tauH * (tauH * inA b) = tauH * inA (a * b) := by
  simp [tauH, inA]

private theorem model_I2 (a b : Equiv.Perm (Fin 1755)) :
    tauH * (tauH * inA a) * (tauH * inA b) = tauH * inA (a * b) := by
  simp [tauH, inA]

private theorem model_I3 (a b : Equiv.Perm (Fin 1755)) :
    (tauH * inA a) * (tauH * inA b) = inA (a * b) := by
  simp [tauH, inA]

private theorem model_I4 (x a : Equiv.Perm (Fin 1755)) :
    inA x * (tauH * inA a) * (inA x)⁻¹ = tauH * inA (x * a * x⁻¹) := by
  simp [tauH, inA]

private theorem conj_commute_aux {G : Type} [Group G] (g : G) {P Q : G} (h : Commute P Q) :
    Commute (g⁻¹ * P * g) (g⁻¹ * Q * g) := by
  show (g⁻¹ * P * g) * (g⁻¹ * Q * g) = (g⁻¹ * Q * g) * (g⁻¹ * P * g)
  calc (g⁻¹ * P * g) * (g⁻¹ * Q * g) = g⁻¹ * (P * Q) * g := by group
    _ = g⁻¹ * (Q * P) * g := by rw [h.eq]
    _ = (g⁻¹ * Q * g) * (g⁻¹ * P * g) := by group

private theorem conj_commute_t_aux {G : Type} [Group G] {g t R P : G} (hg : g * t * g⁻¹ = R)
    (h : Commute P R) : Commute (g⁻¹ * P * g) t := by
  have ht : g⁻¹ * R * g = t := by rw [← hg]; group
  have := conj_commute_aux g h
  rwa [ht] at this

private theorem eq_of_conj_eq_aux {G : Type} [Group G] {g t R P : G} (hg : g * t * g⁻¹ = R)
    (h : g⁻¹ * P * g = t) : P = R := by
  subst hg
  calc P = g * (g⁻¹ * P * g) * g⁻¹ := by group
    _ = g * t * g⁻¹ := by rw [h]

theorem Ctx.exists_swap {G : Type} [Group G] (c : Ctx G) {zp y0 : Equiv.Perm (Fin 1755)}
    (hF6 : F6Facts zp y0) :
    ∃ (z z' y₁ v : G) (hz : z ∈ centralizer ({c.t} : Set G))
      (hz' : z' ∈ centralizer ({c.t} : Set G)) (hy : y₁ ∈ centralizer ({c.t} : Set G)),
      c.Φ ⟨z, hz⟩ = inA titsZ ∧ c.Φ ⟨z', hz'⟩ = inA zp ∧ c.Φ ⟨y₁, hy⟩ = inA y0 ∧
      v * c.t * v⁻¹ = c.t * z ∧ v * (c.t * z) * v⁻¹ = c.t ∧ v * (c.t * z') * v⁻¹ = c.t * z' := by
  obtain ⟨tC, htC, htΦ⟩ : ∃ u : ↥(centralizer ({c.t} : Set G)), (u : G) = c.t ∧ c.Φ u = tauH :=
    ⟨⟨c.t, mem_centralizer_singleton_iff.2 rfl⟩, rfl, c.map_t⟩
  obtain ⟨z₀, hz₀⟩ := c.surj (inA titsZ) (inA_mem_Am hF6.z_mem)
  obtain ⟨z'₀, hz'₀⟩ := c.surj (inA zp) (inA_mem_Am hF6.zp_mem)
  obtain ⟨y₀, hy₀⟩ := c.surj (inA y0) (inA_mem_Am hF6.y0_mem)
  have hΦQ : c.Φ (tC * z₀) = tauH * inA titsZ := by rw [map_mul, htΦ, hz₀]
  have hΦR : c.Φ (tC * z'₀) = tauH * inA zp := by rw [map_mul, htΦ, hz'₀]
  have hzt : Commute (z₀ : G) c.t := mem_centralizer_singleton_iff.1 z₀.2
  have hz't : Commute (z'₀ : G) c.t := mem_centralizer_singleton_iff.1 z'₀.2
  have hzz' : Commute (z₀ : G) z'₀ := by
    have h : z₀ * z'₀ = z'₀ * z₀ :=
      c.inj (by rw [map_mul, map_mul, hz₀, hz'₀]; simp [inA, hF6.zp_comm])
    exact congrArg Subtype.val h
  have hPQ : Commute c.t (c.t * z₀) := (Commute.refl c.t).mul_right hzt.symm
  have hPR : Commute c.t (c.t * z'₀) := (Commute.refl c.t).mul_right hz't.symm
  have hQR : Commute (c.t * z₀) (c.t * z'₀) := hPR.mul_left (hzt.mul_right hzz')
  have hQconj : ∃ k : G, k * c.t * k⁻¹ = c.t * z₀ := by
    have := (c.I2 (tC * z₀)).2 (Or.inr ⟨titsZ, isLong_titsZ_aux, hΦQ⟩)
    simpa [htC] using this
  have hRconj : ∃ k : G, k * c.t * k⁻¹ = c.t * z'₀ := by
    have := (c.I2 (tC * z'₀)).2 (Or.inr ⟨zp, hF6.zp_long, hΦR⟩)
    simpa [htC] using this
  have hnot : ¬ ∃ k : G, k * c.t * k⁻¹ = (c.t * z'₀) * c.t * (c.t * z₀) := by
    rintro hk
    have hk' : ∃ k : G, k * c.t * k⁻¹ = (((tC * z'₀) * tC * (tC * z₀) :
        ↥(centralizer ({c.t} : Set G))) : G) := by simpa [htC] using hk
    rcases (c.I2 _).1 hk' with h | ⟨l, hl, h⟩
    · simp only [map_mul, htΦ, hz₀, hz'₀, model_I1] at h
      have h1 : inA (zp * titsZ) = 1 := mul_left_cancel (h.trans (mul_one tauH).symm)
      have h2 : zp * titsZ = 1 := inA_eq_one h1
      exact hF6.zp_ne (mul_right_cancel (h2.trans hF6.z_sq.symm))
    · simp only [map_mul, htΦ, hz₀, hz'₀, model_I1] at h
      have h1 : zp * titsZ = l := inA_inj (mul_left_cancel h)
      apply hF6.prod_not_long
      rw [hF6.zp_comm, h1]
      exact hl
  obtain ⟨g, hg⟩ := hRconj
  obtain ⟨Y', hY'⟩ : ∃ u : ↥(centralizer ({c.t} : Set G)), (u : G) = g⁻¹ * c.t * g :=
    ⟨⟨_, mem_centralizer_singleton_iff.2 (conj_commute_t_aux hg hPR).eq⟩, rfl⟩
  obtain ⟨W', hW'⟩ : ∃ u : ↥(centralizer ({c.t} : Set G)), (u : G) = g⁻¹ * (c.t * z₀) * g :=
    ⟨⟨_, mem_centralizer_singleton_iff.2 (conj_commute_t_aux hg hQR).eq⟩, rfl⟩
  have hYconj : ∃ k : G, k * c.t * k⁻¹ = (Y' : G) := ⟨g⁻¹, by rw [hY', inv_inv]⟩
  have hWconj : ∃ k : G, k * c.t * k⁻¹ = (W' : G) := by
    obtain ⟨k, hk⟩ := hQconj
    exact ⟨g⁻¹ * k, by rw [hW', ← hk]; group⟩
  obtain ⟨a, ha, haΦ⟩ : ∃ a, IsLong a ∧ c.Φ Y' = tauH * inA a := by
    rcases (c.I2 Y').1 hYconj with h | h
    · exfalso
      have h1 : Y' = tC := c.inj (h.trans htΦ.symm)
      have h2 : g⁻¹ * c.t * g = c.t := by rw [← hY', h1, htC]
      have h3 : c.t = c.t * z'₀ := eq_of_conj_eq_aux hg h2
      have h4 : (z'₀ : G) = 1 := by simpa using h3.symm
      have h5 : z'₀ = 1 := Subtype.ext h4
      rw [h5, map_one] at hz'₀
      exact zp_ne_one_aux hF6 (inA_eq_one hz'₀.symm)
    · exact h
  obtain ⟨b, hb, hbΦ⟩ : ∃ b, IsLong b ∧ c.Φ W' = tauH * inA b := by
    rcases (c.I2 W').1 hWconj with h | h
    · exfalso
      have h1 : W' = tC := c.inj (h.trans htΦ.symm)
      have h2 : g⁻¹ * (c.t * z₀) * g = c.t := by rw [← hW', h1, htC]
      have h3 : c.t * z₀ = c.t * z'₀ := eq_of_conj_eq_aux hg h2
      have h4 : (z₀ : G) = z'₀ := mul_left_cancel h3
      have h5 : z₀ = z'₀ := Subtype.ext h4
      rw [h5] at hz₀
      exact hF6.zp_ne (inA_inj (hz'₀.symm.trans hz₀))
    · exact h
  have hYW : Y' * W' = W' * Y' := by
    apply Subtype.ext
    simpa [hY', hW'] using (conj_commute_aux g hPQ).eq
  have hab : a ≠ b := by
    rintro rfl
    have h1 : Y' = W' := c.inj (haΦ.trans hbΦ.symm)
    have h2 : g⁻¹ * c.t * g = g⁻¹ * (c.t * z₀) * g := by rw [← hY', ← hW', h1]
    have h3 : (z₀ : G) = 1 := by simpa using h2.symm
    have h4 : z₀ = 1 := Subtype.ext h3
    rw [h4, map_one] at hz₀
    exact titsZ_ne_one_aux hF6 (inA_eq_one hz₀.symm)
  have hcomm : a * b = b * a := by
    have := congrArg c.Φ hYW
    rw [map_mul, map_mul, haΦ, hbΦ, model_I3, model_I3] at this
    exact inA_inj this
  have hnotlong : ¬ IsLong (a * b) := by
    intro hlong
    have hx₀Φ : c.Φ (tC * Y' * W') = tauH * inA (a * b) := by
      rw [map_mul, map_mul, htΦ, haΦ, hbΦ, model_I2]
    obtain ⟨h, hh⟩ := (c.I2 (tC * Y' * W')).2 (Or.inr ⟨a * b, hlong, hx₀Φ⟩)
    apply hnot
    refine ⟨g * h, ?_⟩
    have hh' : h * c.t * h⁻¹ = c.t * (g⁻¹ * c.t * g) * (g⁻¹ * (c.t * z₀) * g) := by
      rw [hh]; simp [htC, hY', hW']
    calc (g * h) * c.t * (g * h)⁻¹ = g * (h * c.t * h⁻¹) * g⁻¹ := by group
      _ = g * (c.t * (g⁻¹ * c.t * g) * (g⁻¹ * (c.t * z₀) * g)) * g⁻¹ := by rw [hh']
      _ = (g * c.t * g⁻¹) * c.t * (c.t * z₀) := by group
      _ = (c.t * z'₀) * c.t * (c.t * z₀) := by rw [hg]
  obtain ⟨xh, hxh, hxa, hxb⟩ := hF6.swap a b ha hb hab hcomm hnotlong
  obtain ⟨x, hx⟩ := c.surj (inA xh) (inA_mem_Am hxh)
  have hxY : x * Y' * x⁻¹ = W' := by
    apply c.inj
    rw [map_mul, map_mul, map_inv, hx, haΦ, hbΦ, model_I4, hxa]
  have hxW : x * W' * x⁻¹ = Y' := by
    apply c.inj
    rw [map_mul, map_mul, map_inv, hx, haΦ, hbΦ, model_I4, hxb]
  obtain ⟨xg, hxg⟩ : ∃ u : G, u = (x : G) := ⟨_, rfl⟩
  have hxY' : xg * (g⁻¹ * c.t * g) * xg⁻¹ = g⁻¹ * (c.t * z₀) * g := by
    rw [hxg]; simpa [hY', hW'] using congrArg Subtype.val hxY
  have hxW' : xg * (g⁻¹ * (c.t * z₀) * g) * xg⁻¹ = g⁻¹ * c.t * g := by
    rw [hxg]; simpa [hY', hW'] using congrArg Subtype.val hxW
  have hxt : xg * c.t * xg⁻¹ = c.t := by
    rw [hxg]; exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 x.2)
  refine ⟨z₀, z'₀, y₀, g * xg * g⁻¹, z₀.2, z'₀.2, y₀.2, hz₀, hz'₀, hy₀, ?_, ?_, ?_⟩
  · calc g * xg * g⁻¹ * c.t * (g * xg * g⁻¹)⁻¹
        = g * (xg * (g⁻¹ * c.t * g) * xg⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * (c.t * z₀) * g) * g⁻¹ := by rw [hxY']
      _ = c.t * z₀ := by group
  · calc g * xg * g⁻¹ * (c.t * z₀) * (g * xg * g⁻¹)⁻¹
        = g * (xg * (g⁻¹ * (c.t * z₀) * g) * xg⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * c.t * g) * g⁻¹ := by rw [hxW']
      _ = c.t := by group
  · calc g * xg * g⁻¹ * (c.t * z'₀) * (g * xg * g⁻¹)⁻¹
        = g * xg * g⁻¹ * (g * c.t * g⁻¹) * (g * xg * g⁻¹)⁻¹ := by rw [hg]
      _ = g * (xg * c.t * xg⁻¹) * g⁻¹ := by group
      _ = g * c.t * g⁻¹ := by rw [hxt]
      _ = c.t * z'₀ := hg

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
