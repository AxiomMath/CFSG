module

public import CFSG.CGT.Stroth77.Stroth34Frame

public section

namespace CFSG.CGT.Stroth77

section Coord

variable {G : Type*} [Group G] {D : Subgroup G} {k : Fin 3 → ℕ} (eD : Additive D ≃+ Torus k)

noncomputable def crdT (g : G) : Torus k := by
  classical
  exact if h : g ∈ D then eD (Additive.ofMul ⟨g, h⟩) else 0

theorem crdT_of_mem {g : G} (h : g ∈ D) : crdT eD g = eD (Additive.ofMul ⟨g, h⟩) := by
  rw [crdT, dif_pos h]

theorem crdT_mul {g h : G} (hg : g ∈ D) (hh : h ∈ D) :
    crdT eD (g * h) = crdT eD g + crdT eD h := by
  rw [crdT_of_mem eD (mul_mem hg hh), crdT_of_mem eD hg, crdT_of_mem eD hh, ← map_add]
  rfl

theorem crdT_inj {g h : G} (hg : g ∈ D) (hh : h ∈ D) (he : crdT eD g = crdT eD h) : g = h := by
  rw [crdT_of_mem eD hg, crdT_of_mem eD hh] at he
  exact congrArg Subtype.val (Additive.ofMul.injective (eD.injective he))

theorem crdT_one : crdT eD (1 : G) = 0 := by
  rw [crdT_of_mem eD (one_mem D)]
  exact map_zero eD

theorem crdT_inv {g : G} (hg : g ∈ D) : crdT eD g⁻¹ = -crdT eD g := by
  have h := crdT_mul eD hg (inv_mem hg)
  rw [mul_inv_cancel, crdT_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem exists_crdT_eq (δ : Torus k) : ∃ d ∈ D, crdT eD d = δ :=
  ⟨_, (Additive.toMul (eD.symm δ)).2, by
    rw [crdT_of_mem eD (Additive.toMul (eD.symm δ)).2]
    simp⟩

theorem crdT_conj {x : G} (hx : x ∈ Subgroup.normalizer (D : Set G)) {φ : Torus k →+ Torus k}
    (hφ : ∀ y : D, eD (Additive.ofMul (conjBy hx y)) = φ (eD (Additive.ofMul y)))
    {g : G} (hg : g ∈ D) : crdT eD (x⁻¹ * g * x) = φ (crdT eD g) := by
  rw [crdT_of_mem eD hg, crdT_of_mem eD ((Subgroup.mem_normalizer_iff''.mp hx g).mp hg)]
  exact hφ ⟨g, hg⟩

theorem crdT_conj_mul {x e d : G} (hx : x ∈ Subgroup.normalizer (D : Set G)) (hx2 : x * x = 1)
    {φ : Torus k →+ Torus k}
    (hφ : ∀ y : D, eD (Additive.ofMul (conjBy hx y)) = φ (eD (Additive.ofMul y)))
    (hr : e⁻¹ * x * e * x⁻¹ ∈ D) (hd : d ∈ D) :
    (e * d)⁻¹ * x * (e * d) * x⁻¹ ∈ D ∧
      crdT eD ((e * d)⁻¹ * x * (e * d) * x⁻¹) =
        crdT eD (e⁻¹ * x * e * x⁻¹) - crdT eD d + φ (crdT eD d) := by
  have hxd : x⁻¹ * d * x ∈ D := (Subgroup.mem_normalizer_iff''.mp hx d).mp hd
  rw [conj_mul_mul_inv_eq hx2]
  refine ⟨mul_mem (mul_mem (inv_mem hd) hr) hxd, ?_⟩
  rw [crdT_mul eD (mul_mem (inv_mem hd) hr) hxd, crdT_mul eD (inv_mem hd) hr,
    crdT_inv eD hd, crdT_conj eD hx hφ hd]
  abel

theorem cocycle_uv_t {uv t : G} (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hc : uv * t = t * uv)
    (huvN : uv ∈ Subgroup.normalizer (D : Set G)) (htN : t ∈ Subgroup.normalizer (D : Set G))
    {φuv φt : Torus k →+ Torus k}
    (huvc : ∀ x : D, eD (Additive.ofMul (conjBy huvN x)) = φuv (eD (Additive.ofMul x)))
    (htc : ∀ x : D, eD (Additive.ofMul (conjBy htN x)) = φt (eD (Additive.ofMul x)))
    {e : G} (huv : e⁻¹ * uv * e * uv⁻¹ ∈ D) (ht : e⁻¹ * t * e * t⁻¹ ∈ D) :
    crdT eD (e⁻¹ * uv * e * uv⁻¹) + φuv (crdT eD (e⁻¹ * uv * e * uv⁻¹)) = 0 ∧
      crdT eD (e⁻¹ * t * e * t⁻¹) + φt (crdT eD (e⁻¹ * t * e * t⁻¹)) = 0 ∧
      crdT eD (e⁻¹ * uv * e * uv⁻¹) + φuv (crdT eD (e⁻¹ * t * e * t⁻¹)) =
        crdT eD (e⁻¹ * t * e * t⁻¹) + φt (crdT eD (e⁻¹ * uv * e * uv⁻¹)) := by
  have cuv := fun {g : G} (hg : g ∈ D) => crdT_conj eD huvN huvc hg
  have ct := fun {g : G} (hg : g ∈ D) => crdT_conj eD htN htc hg
  have nuv := fun {g : G} (hg : g ∈ D) => (Subgroup.mem_normalizer_iff''.mp huvN g).mp hg
  have nt := fun {g : G} (hg : g ∈ D) => (Subgroup.mem_normalizer_iff''.mp htN g).mp hg
  have iuv : uv⁻¹ = uv := inv_eq_of_mul_eq_one_right huv2
  have it : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have suv : ∀ y, uv * (uv * y) = y := fun y => by rw [← mul_assoc, huv2, one_mul]
  have st : ∀ y, t * (t * y) = y := fun y => by rw [← mul_assoc, ht2, one_mul]
  have c1 : ∀ y, uv * (t * y) = t * (uv * y) := fun y => by rw [← mul_assoc, hc, mul_assoc]
  have ga : (e⁻¹ * uv * e * uv⁻¹) * (uv⁻¹ * (e⁻¹ * uv * e * uv⁻¹) * uv) = 1 := by
    rw [iuv]
    simp only [mul_assoc, suv, mul_inv_cancel_left, inv_mul_cancel_left, huv2]
  have gb : (e⁻¹ * t * e * t⁻¹) * (t⁻¹ * (e⁻¹ * t * e * t⁻¹) * t) = 1 := by
    rw [it]
    simp only [mul_assoc, st, mul_inv_cancel_left, inv_mul_cancel_left, ht2]
  have gc : (e⁻¹ * uv * e * uv⁻¹) * (uv⁻¹ * (e⁻¹ * t * e * t⁻¹) * uv) =
      (e⁻¹ * t * e * t⁻¹) * (t⁻¹ * (e⁻¹ * uv * e * uv⁻¹) * t) := by
    rw [iuv, it]
    simp only [mul_assoc, suv, st, mul_inv_cancel_left, inv_mul_cancel_left, c1, hc]
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (crdT eD) ga
    rwa [crdT_mul eD huv (nuv huv), crdT_one, cuv huv] at h
  · have h := congrArg (crdT eD) gb
    rwa [crdT_mul eD ht (nt ht), crdT_one, ct ht] at h
  · have h := congrArg (crdT eD) gc
    rwa [crdT_mul eD huv (nuv ht), crdT_mul eD ht (nt huv), cuv ht, ct huv] at h

end Coord

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem rho_stable_crd (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e d₀ : G}
    (he : e ∈ hS.R) (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D)
    (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) (hd₀ : d₀ ∈ D) (hp : hS.proj dD.ρ e = e * d₀) :
    τ.action.φρ (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
        τ.action.φuv (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))) =
      crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) - crdT dD.e d₀ + τ.action.φuv (crdT dD.e d₀) ∧
    τ.action.φρ (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) =
      crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) - crdT dD.e d₀ + τ.action.φt (crdT dD.e d₀) := by
  obtain ⟨tw1, tw2⟩ := h.rho_twist hS he huv ht hp
  have huvi : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  have hrt' : dD.uv⁻¹ * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp dD.uv_mem _).mp ht
  have huvt : e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ =
      (e⁻¹ * dD.uv * e * dD.uv⁻¹) * (dD.uv⁻¹ * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv) := by
    rw [huvi]
    have hs : ∀ y, dD.uv * (dD.uv * y) = y := fun y => by rw [← mul_assoc, dD.uv_sq, one_mul]
    simp only [mul_inv_rev, mul_assoc, hs, inv_mul_cancel_left, mul_inv_cancel_left]
    rw [huvi]
  have hmem : e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ ∈ D := by
    rw [huvt]; exact mul_mem huv hrt'
  have cρ := fun {g : G} (hg : g ∈ D) => crdT_conj dD.e dD.ρ_mem dD.ρ_conj hg
  have cuv := fun {g : G} (hg : g ∈ D) => crdT_conj dD.e dD.uv_mem dD.uv_conj hg
  obtain ⟨-, m1⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hd₀
  obtain ⟨-, m2⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hd₀
  constructor
  · rw [← m1, tw1, cρ hmem, huvt, crdT_mul dD.e huv hrt', cuv ht]
  · rw [← m2, tw2, cρ huv]

theorem crd_x1 (h : F.IsD D dD) :
    crdT dD.e (((F.dA.a : F.A) : G) ^ 2) + crdT dD.e (((F.dA.a : F.A) : G) ^ 2) = 0 ∧
      crdT dD.e (((F.dA.a : F.A) : G) ^ 2) ≠ 0 ∧
      τ.action.φρ (τ.action.φρ (crdT dD.e (((F.dA.a : F.A) : G) ^ 2))) =
        crdT dD.e (((F.dA.a : F.A) : G) ^ 2) +
          τ.action.φρ (crdT dD.e (((F.dA.a : F.A) : G) ^ 2)) ∧
      ∀ g ∈ D, (crdT dD.e g = 0 ∨ crdT dD.e g = crdT dD.e (((F.dA.a : F.A) : G) ^ 2) ∨
        crdT dD.e g = τ.action.φρ (crdT dD.e (((F.dA.a : F.A) : G) ^ 2)) ∨
        crdT dD.e g = crdT dD.e (((F.dA.a : F.A) : G) ^ 2) +
          τ.action.φρ (crdT dD.e (((F.dA.a : F.A) : G) ^ 2))) → g ∈ F.E := by
  have hx₁ : ((F.dA.a : F.A) : G) ^ 2 = F.dA.ofTorus (2 • Torus.a) := by
    rw [F.dA.ofTorus_nsmul]; rfl
  have hy₁ : ((F.dA.b : F.A) : G) ^ 2 = F.dA.ofTorus (2 • Torus.b) := by
    rw [F.dA.ofTorus_nsmul]; rfl
  have hxD : ((F.dA.a : F.A) : G) ^ 2 ∈ D := h.A_le (F.A.pow_mem F.dA.a.2 2)
  have hyD : ((F.dA.b : F.A) : G) ^ 2 ∈ D := h.A_le (F.A.pow_mem F.dA.b.2 2)
  have hxx : ((F.dA.a : F.A) : G) ^ 2 * ((F.dA.a : F.A) : G) ^ 2 = 1 := by
    rw [hx₁, ← F.dA.ofTorus_add,
      show (2 • Torus.a + 2 • Torus.a : Torus (StrothTypeIndex.t100 1).k) = 0 by decide,
      F.dA.ofTorus_zero]
  have hx1 : ((F.dA.a : F.A) : G) ^ 2 ≠ 1 := by
    rw [hx₁, ← F.dA.ofTorus_zero]
    exact fun he => (show (2 • Torus.a : Torus (StrothTypeIndex.t100 1).k) ≠ 0 by decide)
      (F.dA.ofTorus_injective he)
  have hρx : F.dA.ρ⁻¹ * ((F.dA.a : F.A) : G) ^ 2 * F.dA.ρ = ((F.dA.b : F.A) : G) ^ 2 := by
    rw [hx₁, hy₁, F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj]
    congr 1
    decide
  have hρy : F.dA.ρ⁻¹ * ((F.dA.b : F.A) : G) ^ 2 * F.dA.ρ =
      ((F.dA.a : F.A) : G) ^ 2 * ((F.dA.b : F.A) : G) ^ 2 := by
    rw [hx₁, hy₁, F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj, ← F.dA.ofTorus_add]
    congr 1
    decide
  have cρ := fun {x : G} (hx : x ∈ D) => crdT_conj dD.e dD.ρ_mem dD.ρ_conj hx
  rw [h.ρ_eq] at cρ
  have e1 := cρ hxD
  have e2 := cρ hyD
  rw [hρx] at e1
  rw [hρy, crdT_mul dD.e hxD hyD] at e2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← crdT_mul dD.e hxD hxD, hxx, crdT_one]
  · exact fun h0 => hx1 (crdT_inj dD.e hxD (one_mem D) (h0.trans (crdT_one dD.e).symm))
  · rw [← e1, ← e2]
  · rintro g hg (h0 | h' | h' | h')
    · rw [crdT_inj dD.e hg (one_mem D) (h0.trans (crdT_one dD.e).symm)]
      exact one_mem _
    · rw [crdT_inj dD.e hg hxD h']
      exact F.a_sq_mem_E
    · rw [← e1] at h'
      rw [crdT_inj dD.e hg hyD h']
      exact F.b_sq_mem_E
    · rw [← e1, ← crdT_mul dD.e hxD hyD] at h'
      rw [crdT_inj dD.e hg (mul_mem hxD hyD) h']
      exact mul_mem F.a_sq_mem_E F.b_sq_mem_E

end StrothFrame.IsD

end CFSG.CGT.Stroth77
