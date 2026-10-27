module

public import CFSG.CGT.Stroth77.Stroth34T201

public section

namespace CFSG.CGT.Stroth77

open Stroth34T201

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem t201_thetaT_of_rel34i {e : G} (he : Rel34i dD e (2 ^ (m + 1)))
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (x : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT heN x = (1 + 2 ^ (m + 1) : ℤ) • x := by
  have hc : dD.thetaT heN (Torus.ofInt _ ![1, 0, 0]) = Torus.ofInt _ ![1, 0, 0] := by
    rw [dD.thetaT_apply, ← dD.t201_c_eq, he.c_conj, dD.t201_c_eq, dD.crdT_ofT]
  have ha : dD.thetaT heN (Torus.ofInt _ ![0, 1, 0]) =
      (1 + 2 ^ (m + 1) : ℤ) • Torus.ofInt _ ![0, 1, 0] := by
    rw [dD.thetaT_apply, ← dD.t201_a_eq, he.a_conj, dD.t201_a_mul_pow_eq, dD.crdT_ofT]
    push_cast; rfl
  have hb : dD.thetaT heN (Torus.ofInt _ ![0, 0, 1]) =
      (1 + 2 ^ (m + 1) : ℤ) • Torus.ofInt _ ![0, 0, 1] := by
    rw [dD.thetaT_apply, ← dD.t201_b_eq, he.b_conj, dD.t201_b_mul_pow_eq, dD.crdT_ofT]
    push_cast; rfl
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  have hx : Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] =
      a • Torus.ofInt _ ![1, 0, 0] + b • Torus.ofInt _ ![0, 1, 0] +
        c • Torus.ofInt _ ![0, 0, 1] := by
    rw [t201_zsmul_vec, t201_zsmul_vec, t201_zsmul_vec, t201_add_vec, t201_add_vec]
    congr 1; funext i; fin_cases i <;> simp
  rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hc, ha, hb]
  simp only [t201_zsmul_vec, t201_add_vec, smul_add, t201_vec_eq_iff]
  refine ⟨⟨2 * a, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t201_not_mem_of_rel34i {e : G} (he : Rel34i dD e (2 ^ (m + 1)))
    (heN : e ∈ Subgroup.normalizer (D : Set G)) : e ∉ D := by
  intro heD
  have h1 := t201_thetaT_of_rel34i he heN (Torus.ofInt _ ![0, 1, 0])
  rw [dD.thetaT_of_mem heN heD, t201_zsmul_vec, t201_vec_eq_iff] at h1
  obtain ⟨-, h2, -⟩ := h1
  exact not_dvd_one_add_sub_one (by simpa using h2.neg_right)

theorem u_inv_mul_mul_eq_of_rel34i {e : G} (he : Rel34i dD e (2 ^ (m + 1))) :
    dD.u⁻¹ * e * dD.u = e := by
  have hcomm : dD.u * e = e * dD.u := by
    have := congrArg (e * ·) he.u_conj
    simpa [mul_assoc] using this
  rw [mul_assoc, ← hcomm]; group

theorem false_of_conj_u_inv (hm : 1 ≤ m) {e δ : G} (he : Rel34i dD e (2 ^ (m + 1)))
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (hδ : δ ∈ D)
    (hg : dD.u⁻¹ * (e * δ) * dD.u = (e * δ)⁻¹) : False := by
  have hue : dD.u⁻¹ * e * dD.u = e := u_inv_mul_mul_eq_of_rel34i he
  have hδu : dD.u⁻¹ * δ * dD.u ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.u_mem δ).mp hδ
  have key : (dD.c : G)⁻¹ * (e⁻¹ * (dD.u⁻¹ * δ * dD.u) * e) = δ⁻¹ := by
    have h1 : e * (dD.u⁻¹ * δ * dD.u) = δ⁻¹ * e⁻¹ := by
      rw [← mul_inv_rev, ← hg]
      calc e * (dD.u⁻¹ * δ * dD.u) = (dD.u⁻¹ * e * dD.u) * (dD.u⁻¹ * δ * dD.u) := by rw [hue]
        _ = dD.u⁻¹ * (e * δ) * dD.u := by group
    rw [← he.e_sq]
    calc e * e * (e⁻¹ * (dD.u⁻¹ * δ * dD.u) * e) = e * (dD.u⁻¹ * δ * dD.u) * e := by group
      _ = δ⁻¹ := by rw [h1]; group
  have hcD : (dD.c : G)⁻¹ ∈ D := inv_mem dD.c.2
  have hconj : e⁻¹ * (dD.u⁻¹ * δ * dD.u) * e ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp heN _).mp hδu
  have hcrd := congrArg (crdT dD.e) key
  rw [crdT_mul dD.e hcD hconj, crdT_inv dD.e dD.c.2, crdT_inv dD.e hδ, ← dD.thetaT_crdT heN hδu,
    t201_thetaT_of_rel34i he heN, crdT_conj dD.e dD.u_mem dD.u_conj hδ] at hcrd
  obtain ⟨x₀, x₁, x₂, hx⟩ := t201_exists_vec (crdT dD.e δ)
  rw [hx, t201_φu_vec, show crdT dD.e (dD.c : G) = Torus.ofInt _ ![1, 0, 0] by
    rw [dD.t201_c_eq, dD.crdT_ofT], t201_neg_vec, t201_zsmul_vec, t201_add_vec, t201_neg_vec,
    t201_vec_eq_iff] at hcrd
  obtain ⟨⟨w, hw⟩, -, -⟩ := hcrd
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have : (1 : ℤ) = 2 * (2 ^ j * w + x₀ + 2 ^ (j + 1) * x₀) := by
    linear_combination hw
  omega

theorem t201_R1_eq_of_rel34i (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e : G}
    (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1))) :
    hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e := by
  have heN := hS.R_le_normalizer heR
  have heR1 : e ∈ hS.R1 dD.uv dD.t := by
    refine ⟨heR, ?_, ?_⟩
    · rw [he.uv_conj, mul_inv_cancel_right]
      exact pow_mem (mul_mem (mul_mem dD.c.2 dD.a.2) dD.b.2) 2
    · rw [he.t_conj, mul_inv_cancel_right]
      exact inv_mem (pow_mem dD.a.2 2)
  have hue : dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D := by
    rw [u_inv_mul_mul_eq_of_rel34i he, mul_inv_cancel]; exact one_mem D
  have heD := t201_not_mem_of_rel34i he heN
  obtain ⟨d₀, hd₀, y, p, hn₀⟩ := h.exists_normal201 hS hm hfus heR1 hue
  have hp : (4 : ℤ) ∣ 2 * p - 2 := by
    rcases Int.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩
    · have h1 := hn₀.mem_of_dvd h ⟨q, by rw [hq]; ring⟩
      have h2 : e ∈ D := by simpa using mul_mem h1 (inv_mem hd₀)
      exact absurd h2 heD
    · exact ⟨q, by rw [hq]; ring⟩
  obtain ⟨d₁, hd₁, hn⟩ := hn₀.renorm hp
  have hcls : ∀ {g : G} {y' p' : ℤ}, Normal201 hS dD g y' (2 * p') →
      g ∈ D ∨ g * (e * d₀ * d₁)⁻¹ ∈ D := by
    intro g y' p' hg
    rcases Int.even_or_odd p' with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact Or.inl (hg.mem_of_dvd h ⟨q, by rw [hq]; ring⟩)
    · exact Or.inr (hg.mul_inv_mem h hn ⟨q, by rw [hq]; ring⟩)
  have hB1 : ∀ f ∈ hS.R1 dD.uv dD.t, dD.u⁻¹ * f * dD.u * f⁻¹ ∈ D := by
    intro f hf
    by_contra huf
    obtain ⟨hg, hθ⟩ := h.t201_comm_u_scalar hS hm hf huf
    obtain ⟨d, hd, p', hgn⟩ := h.t201_normal_of_scalar hS hm hfus hg hθ
    rcases hcls hgn with h1 | h1
    · exact not_dvd_one_add_sub_one (hgn.scalar_dvd_of_mem h1)
    ·
      set g := f⁻¹ * (dD.u⁻¹ * f * dD.u) with hgdef
      have hδ : e⁻¹ * g ∈ D := by
        have h2 : e⁻¹ * g = (e⁻¹ * (g * d * (e * d₀ * d₁)⁻¹) * e) * (d₀ * d₁ * d⁻¹) := by
          group
        rw [h2]
        exact mul_mem ((Subgroup.mem_normalizer_iff''.mp heN _).mp h1)
          (mul_mem (mul_mem hd₀ hd₁) (inv_mem hd))
      have hgu : dD.u⁻¹ * (e * (e⁻¹ * g)) * dD.u = (e * (e⁻¹ * g))⁻¹ := by
        rw [mul_inv_cancel_left, hgdef]
        have hu2 : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
        calc dD.u⁻¹ * (f⁻¹ * (dD.u⁻¹ * f * dD.u)) * dD.u
            = (dD.u⁻¹ * f⁻¹ * dD.u) * (dD.u⁻¹ * dD.u⁻¹ * f * (dD.u * dD.u)) := by group
          _ = (dD.u⁻¹ * f⁻¹ * dD.u) * f := by rw [hu2, dD.u_sq]; group
          _ = (f⁻¹ * (dD.u⁻¹ * f * dD.u))⁻¹ := by group
      exact false_of_conj_u_inv hm he heN hδ hgu
  refine le_antisymm (fun f hf => ?_) (sup_le (t201_D_le_R1 hS)
    ((Subgroup.zpowers_le).mpr heR1))
  obtain ⟨d, hd, y', p', hfn⟩ := h.exists_normal201 hS hm hfus hf (hB1 f hf)
  rcases hcls hfn with h1 | h1
  · have : f = f * d * d⁻¹ := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_left (inv_mem hd))
  · have : f = f * d * (e * d₀ * d₁)⁻¹ * e * (d₀ * d₁ * d⁻¹) := by group
    rw [this]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)))
      (Subgroup.mem_sup_left (mul_mem (mul_mem hd₀ hd₁) (inv_mem hd)))

end StrothFrame.IsD

end CFSG.CGT.Stroth77
