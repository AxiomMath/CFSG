module

public import CFSG.CGT.Stroth77.StrothFrameNE
public import CFSG.CGT.Stroth77.Section33
public import CFSG.GroupTheory.FixedCosetCommutator

public section

namespace CFSG.CGT.Stroth77

section Torus

variable (s : ℕ)

theorem rho_gens_t101 (x y z : ℤ) :
    (StrothTypeIndex.t101 s).action.φρ
        (x • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + z • gen _ 2) =
      (x - 2 * z) • gen (StrothTypeIndex.t101 s).k 0 + (-z) • gen _ 1 + (y - z) • gen _ 2 := by
  have h0 : (StrothTypeIndex.t101 s).action.φρ (gen _ 0) =
      (1 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 := Type101.rho_c s
  have h1 : (StrothTypeIndex.t101 s).action.φρ (gen _ 1) =
      (1 : ℤ) • gen (StrothTypeIndex.t101 s).k 2 := Type101.rho_a s
  have h2 : (StrothTypeIndex.t101 s).action.φρ (gen _ 2) =
      (-2 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (-1 : ℤ) • gen _ 1 + (-1 : ℤ) • gen _ 2 :=
    Type101.rho_b s
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
  module

abbrev aInv101 : Torus (StrothTypeIndex.t101 s).k :=
  (0 : ℤ) • gen _ 0 + (2 ^ (s + 1) : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2

abbrev cInv101 : Torus (StrothTypeIndex.t101 s).k :=
  (2 ^ s : ℤ) • gen _ 0 + (0 : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2

omit s in
private theorem gens_add101 {k : Fin 3 → ℕ} (p q r p' q' r' : ℤ) :
    (p • gen k 0 + q • gen k 1 + r • gen k 2) + (p' • gen k 0 + q' • gen k 1 + r' • gen k 2) =
      (p + p') • gen k 0 + (q + q') • gen k 1 + (r + r') • gen k 2 := by
  module

omit s in
private theorem gens_zero101 {k : Fin 3 → ℕ} :
    (0 : Torus k) = (0 : ℤ) • gen k 0 + (0 : ℤ) • gen k 1 + (0 : ℤ) • gen k 2 := by
  simp

theorem sigma_cocycle_t101 :
    aInv101 s + (StrothTypeIndex.t101 s).action.φt (aInv101 s) = 0 ∧
      aInv101 s + (StrothTypeIndex.t101 s).action.φuv (cInv101 s) =
        cInv101 s + (StrothTypeIndex.t101 s).action.φu (aInv101 s) ∧
      aInv101 s + (StrothTypeIndex.t101 s).action.φt (cInv101 s) =
        cInv101 s + (StrothTypeIndex.t101 s).action.φu (aInv101 s) +
          (StrothTypeIndex.t101 s).action.φu
            ((StrothTypeIndex.t101 s).action.φuv (aInv101 s)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [aInv101, t_gens_t101, gens_add101]
    rw [gens_zero101]
    apply zsmul_gens_eq_of_dvd
    · exact ⟨0, by ring⟩
    · rw [k_one_t101]; exact ⟨-2 ^ s, by ring⟩
    · exact ⟨0, by ring⟩
  · simp only [aInv101, cInv101, uv_gens_t101, u_gens_t101, gens_add101]
    apply zsmul_gens_eq_of_dvd
    · rw [k_zero_t101]; exact ⟨2, by ring⟩
    · exact ⟨0, by ring⟩
    · rw [k_two_t101]; exact ⟨1, by ring⟩
  · simp only [aInv101, cInv101, uv_gens_t101, u_gens_t101, t_gens_t101, gens_add101]
    apply zsmul_gens_eq_of_dvd
    · rw [k_zero_t101]; exact ⟨2, by ring⟩
    · rw [k_one_t101]; exact ⟨2 ^ s, by ring⟩
    · rw [k_two_t101]; exact ⟨1, by ring⟩

omit s in
private theorem pow_dvd_of_pow_succ_dvd_neg_double101 {n : ℕ} {x : ℤ}
    (h : (2 : ℤ) ^ (n + 1) ∣ 0 - (x + x)) : (2 : ℤ) ^ n ∣ x := by
  obtain ⟨q, hq⟩ := h
  refine ⟨-q, mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_⟩
  rw [pow_succ] at hq
  linear_combination (-1 : ℤ) * hq

theorem aInv_eq_of_rho_t101 {v : Torus (StrothTypeIndex.t101 s).k} (h2 : v + v = 0)
    (hρ : (StrothTypeIndex.t101 s).action.φρ ((StrothTypeIndex.t101 s).action.φρ v) =
      v + (StrothTypeIndex.t101 s).action.φρ v) (hv : v ≠ 0) :
    aInv101 s = v ∨ aInv101 s = (StrothTypeIndex.t101 s).action.φρ v ∨
      aInv101 s = v + (StrothTypeIndex.t101 s).action.φρ v := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [gens_add101, gens_zero101] at h2
  obtain ⟨hx, hy, hz⟩ := zsmul_gens_dvd_of_eq h2
  rw [k_zero_t101] at hx
  rw [k_one_t101] at hy
  rw [k_two_t101] at hz
  obtain ⟨α, rfl⟩ := pow_dvd_of_pow_succ_dvd_neg_double101 hx
  obtain ⟨β, rfl⟩ := pow_dvd_of_pow_succ_dvd_neg_double101 hy
  obtain ⟨γ, rfl⟩ := pow_dvd_of_pow_succ_dvd_neg_double101 hz
  simp only [rho_gens_t101, gens_add101] at hρ ⊢
  obtain ⟨h0, -, -⟩ := zsmul_gens_dvd_of_eq hρ
  rw [k_zero_t101] at h0
  obtain ⟨α', rfl⟩ : (2 : ℤ) ∣ α := by
    obtain ⟨q, hq⟩ := h0
    refine ⟨q - 2 * (β - γ), mul_left_cancel₀ (pow_ne_zero s (two_ne_zero (α := ℤ))) ?_⟩
    rw [pow_succ] at hq
    linear_combination hq
  rcases Int.even_or_odd β with ⟨β', rfl⟩ | ⟨β', rfl⟩ <;>
    rcases Int.even_or_odd γ with ⟨γ', rfl⟩ | ⟨γ', rfl⟩
  · exact absurd (by
      rw [gens_zero101]
      apply zsmul_gens_eq_of_dvd
      · rw [k_zero_t101]; exact ⟨-α', by ring⟩
      · rw [k_one_t101]; exact ⟨-β', by ring⟩
      · rw [k_two_t101]; exact ⟨-γ', by ring⟩) hv
  · right; right
    apply zsmul_gens_eq_of_dvd
    · rw [k_zero_t101]; exact ⟨2 * α' - 4 * γ' - 2, by ring⟩
    · rw [k_one_t101]; exact ⟨β' - γ' - 1, by ring⟩
    · rw [k_two_t101]; exact ⟨β', by ring⟩
  · left
    apply zsmul_gens_eq_of_dvd
    · rw [k_zero_t101]; exact ⟨α', by ring⟩
    · rw [k_one_t101]; exact ⟨β', by ring⟩
    · rw [k_two_t101]; exact ⟨γ', by ring⟩
  · right; left
    apply zsmul_gens_eq_of_dvd
    · rw [k_zero_t101]; exact ⟨α' - 4 * γ' - 2, by ring⟩
    · rw [k_one_t101]; exact ⟨-γ' - 1, by ring⟩
    · rw [k_two_t101]; exact ⟨β' - γ', by ring⟩

end Torus

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_closure_of_conj_mem {s : Set G} {g : G}
    (hs : ∀ x ∈ s, g⁻¹ * x * g ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  have key : ∀ x ∈ Subgroup.closure s, g⁻¹ * x * g ∈ Subgroup.closure s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hs y hy
    | one => simp
    | mul y z _ _ hy hz =>
      have := mul_mem hy hz
      convert this using 1
      group
    | inv y _ hy =>
      have := inv_mem hy
      convert this using 1
      group
  have hinj : Function.Injective (fun x : Subgroup.closure s =>
      (⟨g⁻¹ * x * g, key x x.2⟩ : Subgroup.closure s)) := by
    intro x y hxy
    have h' : g⁻¹ * (x : G) * g = g⁻¹ * y * g := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h')
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  refine ⟨fun hy => key y hy, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨g⁻¹ * y * g, hy⟩
  have h' : g⁻¹ * (x : G) * g = g⁻¹ * y * g := congrArg Subtype.val hx
  have hxy : (x : G) = y := by simpa using h'
  exact hxy ▸ x.2

end General

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem a_sq_mul_a_sq : ((F.dA.a : F.A) : G) ^ 2 * ((F.dA.a : F.A) : G) ^ 2 = 1 := by
  rw [show ((F.dA.a : F.A) : G) ^ 2 = F.dA.ofTorus (2 • Torus.a) by rw [F.dA.ofTorus_nsmul]; rfl,
    ← F.dA.ofTorus_add,
    show (2 • Torus.a + 2 • Torus.a : Torus (StrothTypeIndex.t100 1).k) = 0 by decide,
    F.dA.ofTorus_zero]

theorem b_sq_mul_b_sq : ((F.dA.b : F.A) : G) ^ 2 * ((F.dA.b : F.A) : G) ^ 2 = 1 := by
  rw [show ((F.dA.b : F.A) : G) ^ 2 = F.dA.ofTorus (2 • Torus.b) by rw [F.dA.ofTorus_nsmul]; rfl,
    ← F.dA.ofTorus_add,
    show (2 • Torus.b + 2 • Torus.b : Torus (StrothTypeIndex.t100 1).k) = 0 by decide,
    F.dA.ofTorus_zero]

end StrothFrame

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {s : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t101 s)}

theorem mem_E_of_crd_t101 (h : F.IsD D dD) {g : G} (hg : g ∈ D)
    (hc : crd101 dD.e g = aInv101 s) : g ∈ F.E := by
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
  have cρ := fun {x : G} (hx : x ∈ D) => crd101_conj dD.e dD.ρ_mem dD.ρ_conj hx
  rw [h.ρ_eq] at cρ
  have e1 := cρ hxD
  have e2 := cρ hyD
  rw [hρx] at e1
  rw [hρy, crd101_mul dD.e hxD hyD] at e2
  have h2 : crd101 dD.e (((F.dA.a : F.A) : G) ^ 2) +
      crd101 dD.e (((F.dA.a : F.A) : G) ^ 2) = 0 := by
    rw [← crd101_mul dD.e hxD hxD, hxx, crd101_one]
  have hv : crd101 dD.e (((F.dA.a : F.A) : G) ^ 2) ≠ 0 := fun h0 =>
    hx1 (crd101_inj dD.e hxD (one_mem D) (h0.trans (crd101_one dD.e).symm))
  have hρ2 := aInv_eq_of_rho_t101 s h2 (by rw [← e1, ← e2]) hv
  rw [← e1] at hρ2
  rcases hρ2 with h' | h' | h'
  · rw [crd101_inj dD.e hg hxD (hc.trans h')]
    exact F.a_sq_mem_E
  · rw [crd101_inj dD.e hg hyD (hc.trans h')]
    exact F.b_sq_mem_E
  · rw [← crd101_mul dD.e hxD hyD] at h'
    rw [crd101_inj dD.e hg (mul_mem hxD hyD) (hc.trans h')]
    exact mul_mem F.a_sq_mem_E F.b_sq_mem_E

theorem mem_of_conj_eq_aInv_t101 (h : F.IsD D dD) {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgC : g ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (huv : g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ D)
    (hcuv : crd101 dD.e (g⁻¹ * dD.uv * g * dD.uv⁻¹) = aInv101 s)
    (ht : g⁻¹ * dD.t * g * dD.t⁻¹ ∈ D)
    (hct : crd101 dD.e (g⁻¹ * dD.t * g * dD.t⁻¹) = aInv101 s) : g ∈ D := by
  rw [h.uv_eq] at huv hcuv
  rw [h.t_eq] at ht hct
  have hfix : ∀ y : G, y * y = 1 → y ∈ F.A → g⁻¹ * y * g = y := fun y hyy hyA => by
    have hc := Subgroup.mem_centralizer_iff.mp hgC y
      (mem_omegaIn_one_of_mul_self (h.A_le hyA) hyy)
    rw [mul_assoc, hc]; group
  refine h.mem_of_mem_normalizer_E hgS hgC ?_
  rw [F.E_eq]
  refine mem_normalizer_closure_of_conj_mem ?_
  rw [← F.E_eq]
  rintro y (rfl | rfl | rfl | rfl)
  · rw [hfix _ F.a_sq_mul_a_sq (F.A.pow_mem F.dA.a.2 2)]; exact F.a_sq_mem_E
  · rw [hfix _ F.b_sq_mul_b_sq (F.A.pow_mem F.dA.b.2 2)]; exact F.b_sq_mem_E
  · have hw := h.mem_E_of_crd_t101 huv hcuv
    have e : g⁻¹ * F.dA.uv * g = (g⁻¹ * F.dA.uv * g * F.dA.uv⁻¹) * F.dA.uv := by group
    rw [e]; exact mul_mem hw F.uv_mem_E
  · have hw := h.mem_E_of_crd_t101 ht hct
    have e : g⁻¹ * F.dA.t * g = (g⁻¹ * F.dA.t * g * F.dA.t⁻¹) * F.dA.t := by group
    rw [e]; exact mul_mem hw F.t_mem_E

theorem stroth_3_3 (h : F.IsD D dD) (hs : 1 ≤ s) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D := by
  set R : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
    Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) with hR
  have hcomm : ∀ x y : D, x * y = y * x := fun x y => dD.isMulCommutative.is_comm.comm x y
  have hDR : D ≤ R := fun x hx => Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h.le_S hx,
    Subgroup.le_normalizer hx⟩, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hcomm ⟨y, omegaIn_le 1 D hy⟩ ⟨x, hx⟩)⟩
  refine le_antisymm ?_ hDR
  by_contra hRD
  have hlt : D < R := lt_of_le_not_ge hDR hRD
  have hRS : R ≤ (F.S : Subgroup G) := fun x hx =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hRN : R ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have hRC : R ≤ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp hx).2
  have hgen : ∀ x ∈ ({dD.uv, dD.t, dD.u} : Set G), x ∈ (F.S : Subgroup G) ∧
      x ∈ Subgroup.normalizer (D : Set G) ∧ x * x = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨h.uv_eq ▸ F.uv_mem_S, dD.uv_mem, dD.uv_sq⟩
    · exact ⟨h.t_eq ▸ F.t_mem_S, dD.t_mem, dD.t_sq⟩
    · exact ⟨h.u_eq ▸ F.u_mem_S, dD.u_mem, dD.u_sq⟩
  have hPS : Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ≤ (F.S : Subgroup G) :=
    (Subgroup.closure_le _).mpr fun x hx => (hgen x hx).1
  have hPQ : Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx =>
      mem_normalizer_inf_centralizer_omegaIn (hgen x hx).1 (hgen x hx).2.1 (hgen x hx).2.2
  have hPK : Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ≤
      Subgroup.normalizer (D : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => (hgen x hx).2.1
  obtain ⟨e, heR, heD, he⟩ := CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup
    (F.S.isPGroup'.to_le hPS) (F.S.isPGroup'.to_le hRS) hlt hRN hPQ hPK
  have hr : ∀ x ∈ ({dD.uv, dD.t, dD.u} : Set G), e⁻¹ * x * e * x⁻¹ ∈ D := fun x hx => by
    have h' := (Subgroup.mem_normalizer_iff''.mp (hRN heR) _).mp
      (he x (Subgroup.subset_closure hx))
    rw [commutatorElement_def] at h'
    convert h' using 1
    group
  have hruv := hr dD.uv (by simp)
  have hrt := hr dD.t (by simp)
  have hru := hr dD.u (by simp)
  obtain ⟨-, hIu, -, -⟩ := cocycle101 dD.e dD.uv_sq dD.t_sq dD.u_sq dD.uv_comm_u dD.t_u
    dD.uv_mem dD.t_mem dD.u_mem dD.uv_conj dD.t_conj dD.u_conj hruv hrt hru
  obtain ⟨δ₁, hδ₁⟩ := exists_u_class_t101 s _ hIu
  obtain ⟨d₁, hd₁, hcd₁⟩ := exists_crd101_eq dD.e δ₁
  obtain ⟨huv₁, cuv₁⟩ := crd101_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj hruv hd₁
  obtain ⟨ht₁, ct₁⟩ := crd101_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj hrt hd₁
  obtain ⟨hu₁, cu₁⟩ := crd101_conj_mul dD.e dD.u_mem dD.u_sq dD.u_conj hru hd₁
  have he₁R : e * d₁ ∈ R := mul_mem heR (hDR hd₁)
  obtain ⟨hIt, -, hIII, hIV⟩ := cocycle101 dD.e dD.uv_sq dD.t_sq dD.u_sq dD.uv_comm_u dD.t_u
    dD.uv_mem dD.t_mem dD.u_mem dD.uv_conj dD.t_conj dD.u_conj huv₁ ht₁ hu₁
  have hback : ∀ d₂ : G, e * d₁ * d₂ ∈ D → d₂ ∈ D → False := by
    intro d₂ h₂ hd₂
    apply heD
    have h₃ := mul_mem (mul_mem h₂ (inv_mem hd₂)) (inv_mem hd₁)
    simpa only [mul_inv_cancel_right] using h₃
  rcases hδ₁ with hδ₁ | hδ₁
  ·
    have hu0 : crd101 dD.e ((e * d₁)⁻¹ * dD.u * (e * d₁) * dD.u⁻¹) = 0 := by
      rw [cu₁, hcd₁, hδ₁]
      abel
    rw [hu0, map_zero, add_zero, zero_add] at hIII hIV
    obtain ⟨δ₂, -, hδuv, hδt⟩ := exists_coboundary_t101 s hs _ _ hIt hIII.symm hIV
    obtain ⟨d₂, hd₂, hcd₂⟩ := exists_crd101_eq dD.e δ₂
    obtain ⟨huv₂, cuv₂⟩ := crd101_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv₁ hd₂
    obtain ⟨ht₂, ct₂⟩ := crd101_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht₁ hd₂
    have he₂R : e * d₁ * d₂ ∈ R := mul_mem he₁R (hDR hd₂)
    refine hback d₂ (h.mem_of_commute (hRS he₂R) (hRC he₂R) ?_ ?_) hd₂
    · rw [← h.uv_eq]
      refine mul_comm_of_crd101_eq_zero dD.e huv₂ ?_
      rw [cuv₂, hcd₂, hδuv]
      abel
    · rw [← h.t_eq]
      refine mul_comm_of_crd101_eq_zero dD.e ht₂ ?_
      rw [ct₂, hcd₂, hδt]
      abel
  ·
    have hu1 : crd101 dD.e ((e * d₁)⁻¹ * dD.u * (e * d₁) * dD.u⁻¹) = cInv101 s := by
      rw [cu₁, hcd₁, hδ₁, cInv101]
      simp only [zero_smul, add_zero]
      abel
    obtain ⟨σ1, σ3, σ4⟩ := sigma_cocycle_t101 s
    rw [hu1] at hIII hIV
    set ruv := crd101 dD.e ((e * d₁)⁻¹ * dD.uv * (e * d₁) * dD.uv⁻¹) with hruv'
    set rt := crd101 dD.e ((e * d₁)⁻¹ * dD.t * (e * d₁) * dD.t⁻¹) with hrt'
    have h2' : rt - aInv101 s + (StrothTypeIndex.t101 s).action.φt (rt - aInv101 s) = 0 := by
      rw [map_sub, show rt - aInv101 s + ((StrothTypeIndex.t101 s).action.φt rt -
          (StrothTypeIndex.t101 s).action.φt (aInv101 s)) =
          (rt + (StrothTypeIndex.t101 s).action.φt rt) -
            (aInv101 s + (StrothTypeIndex.t101 s).action.φt (aInv101 s)) by abel, hIt, σ1,
        sub_zero]
    have h5' : (StrothTypeIndex.t101 s).action.φu (ruv - aInv101 s) = ruv - aInv101 s := by
      rw [map_sub, ← sub_eq_zero, show (StrothTypeIndex.t101 s).action.φu ruv -
          (StrothTypeIndex.t101 s).action.φu (aInv101 s) - (ruv - aInv101 s) =
          (cInv101 s + (StrothTypeIndex.t101 s).action.φu ruv -
            (ruv + (StrothTypeIndex.t101 s).action.φuv (cInv101 s))) -
          (cInv101 s + (StrothTypeIndex.t101 s).action.φu (aInv101 s) -
            (aInv101 s + (StrothTypeIndex.t101 s).action.φuv (cInv101 s))) by abel,
        hIII, σ3, sub_self, sub_self, sub_zero]
    have h6' : rt - aInv101 s = (StrothTypeIndex.t101 s).action.φu (ruv - aInv101 s) +
        (StrothTypeIndex.t101 s).action.φu
          ((StrothTypeIndex.t101 s).action.φuv (rt - aInv101 s)) := by
      rw [map_sub, map_sub, map_sub, ← sub_eq_zero, show rt - aInv101 s -
          ((StrothTypeIndex.t101 s).action.φu ruv -
            (StrothTypeIndex.t101 s).action.φu (aInv101 s) +
          ((StrothTypeIndex.t101 s).action.φu ((StrothTypeIndex.t101 s).action.φuv rt) -
            (StrothTypeIndex.t101 s).action.φu
              ((StrothTypeIndex.t101 s).action.φuv (aInv101 s)))) =
          (rt + (StrothTypeIndex.t101 s).action.φt (cInv101 s) -
            (cInv101 s + (StrothTypeIndex.t101 s).action.φu ruv +
              (StrothTypeIndex.t101 s).action.φu ((StrothTypeIndex.t101 s).action.φuv rt))) -
          (aInv101 s + (StrothTypeIndex.t101 s).action.φt (cInv101 s) -
            (cInv101 s + (StrothTypeIndex.t101 s).action.φu (aInv101 s) +
              (StrothTypeIndex.t101 s).action.φu
                ((StrothTypeIndex.t101 s).action.φuv (aInv101 s)))) by abel,
        hIV, σ4, sub_self, sub_self, sub_zero]
    obtain ⟨δ₂, -, hδuv, hδt⟩ := exists_coboundary_t101 s hs _ _ h2' h5' h6'
    obtain ⟨d₂, hd₂, hcd₂⟩ := exists_crd101_eq dD.e δ₂
    obtain ⟨huv₂, cuv₂⟩ := crd101_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv₁ hd₂
    obtain ⟨ht₂, ct₂⟩ := crd101_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht₁ hd₂
    have he₂R : e * d₁ * d₂ ∈ R := mul_mem he₁R (hDR hd₂)
    refine hback d₂ (h.mem_of_conj_eq_aInv_t101 (hRS he₂R) (hRC he₂R) huv₂ ?_ ht₂ ?_) hd₂
    · rw [cuv₂, hcd₂, ← hruv', ← sub_sub_cancel ruv (aInv101 s), hδuv]
      abel
    · rw [ct₂, hcd₂, ← hrt', ← sub_sub_cancel rt (aInv101 s), hδt]
      abel

end StrothFrame.IsD

end CFSG.CGT.Stroth77
