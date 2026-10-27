module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Dihedral

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace A7Data

variable {t : X} {L : Subgroup X} (A : A7Data t L)

omit [Finite X] in
theorem eq_T_of_le {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : A.T ≤ Q)
    (hQt : Q ≤ centralizer ({t} : Set X)) : Q = A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf (centralizer ({t} : Set X))) :=
    hQ.comap_of_injective _ (subtype_injective _)
  have hsyl : (A.syl : Subgroup _) ≤ Q.subgroupOf (centralizer ({t} : Set X)) := by
    intro c hc
    exact hTQ ⟨c, hc, rfl⟩
  have heq := A.syl.is_maximal' hQ' hsyl
  refine le_antisymm (fun q hq => ?_) hTQ
  have : (⟨q, hQt hq⟩ : centralizer ({t} : Set X)) ∈
      Q.subgroupOf (centralizer ({t} : Set X)) := hq
  rw [heq] at this
  exact ⟨_, this, rfl⟩

omit [Finite X] in
theorem mem_T_of_commute {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : A.T ≤ Q) {g : X}
    (hg : g ∈ Q) (hgt : g * t = t * g) : g ∈ A.T := by
  have hle : A.T ⊔ zpowers g ≤ centralizer ({t} : Set X) :=
    sup_le A.T_le_centralizer (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hgt))
  have h := A.eq_T_of_le (hQ.to_le (sup_le hTQ (zpowers_le.mpr hg))) le_sup_left hle
  rw [← h]
  exact mem_sup_right (mem_zpowers g)

omit [Finite X] in
theorem eq_of_commutator_of_coords {z : X} (hz : z ∈ A.T)
    (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4) (hφz : φ ⟨z, hz⟩ = (r 2, 1))
    (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) {g : X} (hg : g ∈ A.T)
    (hgc : ∀ h ∈ A.T, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = z * t) :
    g = 1 ∨ g = z ∨ g = t ∨ g = z * t := by
  have hφzt : φ ⟨z * t, mul_mem hz A.t_mem_T⟩ = (r 2, r 2) := by
    have : (⟨z * t, mul_mem hz A.t_mem_T⟩ : A.T) = ⟨z, hz⟩ * ⟨t, A.t_mem_T⟩ := rfl
    rw [this, map_mul, hφz, hφt]
    rfl
  have key : ∀ q, φ ⟨g, hg⟩ * q * (φ ⟨g, hg⟩)⁻¹ * q⁻¹ = 1 ∨
      φ ⟨g, hg⟩ * q * (φ ⟨g, hg⟩)⁻¹ * q⁻¹ = (r 2, r 2) := by
    intro q
    obtain ⟨h, rfl⟩ := φ.surjective q
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hφzt, ← map_one φ]
    rcases hgc h h.2 with h1 | h1
    · exact Or.inl (congrArg φ (Subtype.ext h1))
    · exact Or.inr (congrArg φ (Subtype.ext h1))
  have hv : ∀ {y : X} (hy : y ∈ A.T) (p : DihedralGroup 4 × DihedralGroup 4),
      φ ⟨y, hy⟩ = p → φ ⟨g, hg⟩ = p → g = y := by
    intro y hy p h1 h2
    exact congrArg Subtype.val (φ.injective (h2.trans h1.symm))
  rcases dd_eq_of_commutator _ key with h | h | h | h
  · exact Or.inl (hv (one_mem _) 1 (map_one φ) h)
  · exact Or.inr (Or.inl (hv hz _ hφz h))
  · exact Or.inr (Or.inr (Or.inl (hv A.t_mem_T _ hφt h)))
  · exact Or.inr (Or.inr (Or.inr (hv (mul_mem hz A.t_mem_T) _ hφzt h)))

omit [Finite X] in
theorem eq_of_central_of_coords {z : X} (hz : z ∈ A.T)
    (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4) (hφz : φ ⟨z, hz⟩ = (r 2, 1))
    (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) {g : X} (hg : g ∈ A.T)
    (hgc : ∀ h ∈ A.T, g * h = h * g) : g = 1 ∨ g = z ∨ g = t ∨ g = z * t :=
  A.eq_of_commutator_of_coords hz φ hφz hφt hg fun h hh => Or.inl (by
    rw [hgc h hh, mul_inv_cancel_right, mul_inv_cancel])

omit [Finite X] in
theorem z_ne_one_of_coords {z : X} (hz : z ∈ A.T)
    (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4) (hφz : φ ⟨z, hz⟩ = (r 2, 1)) : z ≠ 1 := by
  rintro rfl
  have : φ ⟨1, hz⟩ = 1 := map_one φ
  rw [hφz] at this
  exact absurd this (by decide)

omit [Finite X] in
theorem commute_z_t {z : X} (hz : z ∈ A.T) : z * t = t * z := A.commute_t hz

omit [Finite X] in
theorem conj_t_eq_z {z : X} (hz : z ∈ A.T) (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4)
    (hφz : φ ⟨z, hz⟩ = (r 2, 1)) (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) {w : X}
    (hw : w ∈ normalizer (A.T : Set X)) (hwt : w * t ≠ t * w) :
    w * t * w⁻¹ = z ∧ w * z * w⁻¹ = t := by
  have hzt := A.conj_zt_eq hz φ hφz hφt hw
  have hz1 := A.z_ne_one_of_coords hz φ hφz
  have hgT : w * t * w⁻¹ ∈ A.T := A.conj_mem_T hw A.t_mem_T
  have hgc : ∀ h ∈ A.T, w * t * w⁻¹ * h = h * (w * t * w⁻¹) := by
    intro h hh
    have h1 := A.commute_t (A.conj_inv_mem_T hw hh)
    calc w * t * w⁻¹ * h = w * (t * (w⁻¹ * h * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * h * w) * t) * w⁻¹ := by rw [h1]
      _ = h * (w * t * w⁻¹) := by group
  have hwz : w * z * w⁻¹ = (w * (z * t) * w⁻¹) * (w * t * w⁻¹)⁻¹ := by group
  rcases A.eq_of_central_of_coords hz φ hφz hφt hgT hgc with h | h | h | h
  · exact absurd h (A.conj_t_ne_one w)
  · refine ⟨h, ?_⟩
    rw [hwz, hzt, h, A.commute_z_t hz, mul_inv_cancel_right]
  · exfalso
    apply hwt
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [h]
  · exfalso
    rw [h, hzt, mul_inv_cancel] at hwz
    exact hz1 (by
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = 1 := by rw [hwz]; group)

theorem T_le_normalizer_R : A.T ≤ normalizer (A.R : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact A.conj_mem_R hg
  · intro hh
    have := A.conj_mem_R (inv_mem hg) hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem conj_mem_map {w : X} (hw : w ∈ normalizer (A.T : Set X)) {g b : X} (hg : g ∈ A.T)
    (hb : b ∈ A.R.map (MulAut.conj w).toMonoidHom) :
    g * b * g⁻¹ ∈ A.R.map (MulAut.conj w).toMonoidHom := by
  obtain ⟨r, hr, rfl⟩ := hb
  refine ⟨(w⁻¹ * g * w) * r * (w⁻¹ * g * w)⁻¹, A.conj_mem_R (A.conj_inv_mem_T hw hg) hr, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

omit [Finite X] in
theorem map_conj_le_T {w : X} (hw : w ∈ normalizer (A.T : Set X)) :
    A.R.map (MulAut.conj w).toMonoidHom ≤ A.T := by
  rintro _ ⟨r, hr, rfl⟩
  exact A.conj_mem_T hw hr.1

theorem inf_conj_eq_bot {z : X} (hz : z ∈ A.R) (eR : A.R ≃* DihedralGroup 4)
    (heRz : eR ⟨z, hz⟩ = r 2) {w : X} (hw : w ∈ normalizer (A.T : Set X))
    (hwt : w * t * w⁻¹ = z) : A.R ⊓ A.R.map (MulAut.conj w).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyR, hyB⟩ := mem_inf.mp hy
  rw [mem_bot]
  by_contra hy1
  have hzB : z ∈ A.R.map (MulAut.conj w).toMonoidHom := by
    have hne : eR ⟨y, hyR⟩ ≠ 1 := by
      intro h
      exact hy1 (congrArg Subtype.val (eR.injective (h.trans (map_one eR).symm)))
    rcases eq_r_two_or_exists_commutator _ hne with h | ⟨d, hd⟩
    · have : y = z := congrArg Subtype.val (eR.injective (h.trans heRz.symm))
      rw [← this]
      exact hyB
    · obtain ⟨h₀, rfl⟩ := eR.surjective d
      have hyz : y * h₀ * y⁻¹ * h₀⁻¹ = z := by
        have : (⟨y, hyR⟩ : A.R) * h₀ * (⟨y, hyR⟩ : A.R)⁻¹ * h₀⁻¹ = ⟨z, hz⟩ :=
          eR.injective (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hd, heRz])
        exact congrArg Subtype.val this
      rw [← hyz, mul_assoc y, mul_assoc y]
      exact mul_mem hyB (A.conj_mem_map hw h₀.2.1 (inv_mem hyB))
  obtain ⟨r, hr, hrz⟩ := hzB
  have hrt : r = t := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hrz
    calc r = w⁻¹ * (w * r * w⁻¹) * w := by group
      _ = t := by rw [hrz, ← hwt]; group
  exact A.t_not_mem_L (hrt ▸ hr.2)

theorem commute_and_exists_mul_eq {B : Subgroup X} (hBT : B ≤ A.T) (hRB : A.R ⊓ B = ⊥)
    (hBn : ∀ g ∈ A.T, ∀ b ∈ B, g * b * g⁻¹ ∈ B) (hcardB : Nat.card B = 8)
    (hcardT : Nat.card A.T = 64) :
    (∀ r ∈ A.R, ∀ b ∈ B, r * b = b * r) ∧ ∀ h ∈ A.T, ∃ r ∈ A.R, ∃ b ∈ B, h = r * b := by
  have hcomm : ∀ r ∈ A.R, ∀ b ∈ B, r * b = b * r := by
    intro r hr b hb
    have h1 : r * (b * r⁻¹ * b⁻¹) ∈ A.R := mul_mem hr (A.conj_mem_R (hBT hb) (inv_mem hr))
    have h2 : (r * b * r⁻¹) * b⁻¹ ∈ B := mul_mem (hBn r hr.1 b hb) (inv_mem hb)
    have h1' : r * b * r⁻¹ * b⁻¹ ∈ A.R := by
      rw [show r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) by group]
      exact h1
    have h3 : r * b * r⁻¹ * b⁻¹ ∈ A.R ⊓ B := Subgroup.mem_inf.mpr ⟨h1', h2⟩
    rw [hRB, mem_bot] at h3
    calc r * b = r * b * r⁻¹ * b⁻¹ * (b * r) := by group
      _ = b * r := by rw [h3, one_mul]
  refine ⟨hcomm, fun h hh => ?_⟩
  have hN : B ≤ normalizer (A.R : Set X) := hBT.trans A.T_le_normalizer_R
  have hsup : A.R ⊔ B = A.T := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hBT) ?_
    rw [card_sup_eq_mul_of_le_normalizer hN hRB, A.card_R, hcardB, hcardT]
  have hh' : h ∈ (A.R : Set X) * (B : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hN, hsup]
    exact hh
  obtain ⟨r, hr, b, hb, rfl⟩ := hh'
  exact ⟨r, hr, b, hb, rfl⟩

omit [Finite X] in
theorem eq_of_mul_eq {B : Subgroup X} (hRB : A.R ⊓ B = ⊥) {r r' b b' : X} (hr : r ∈ A.R)
    (hr' : r' ∈ A.R) (hb : b ∈ B) (hb' : b' ∈ B) (h : r * b = r' * b') : r = r' ∧ b = b' := by
  have h1 : r'⁻¹ * r = b' * b⁻¹ := by
    calc r'⁻¹ * r = r'⁻¹ * (r * b) * b⁻¹ := by group
      _ = b' * b⁻¹ := by rw [h]; group
  have h2 : r'⁻¹ * r ∈ A.R ⊓ B :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hr') hr, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [hRB, mem_bot] at h2
  have hrr : r = r' := by
    calc r = r' * (r'⁻¹ * r) := by group
      _ = r' := by rw [h2, mul_one]
  refine ⟨hrr, ?_⟩
  rw [hrr] at h
  exact mul_left_cancel h

theorem exists_swap {z : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = a0 ^ 2) {w : X}
    (hw : w ∈ normalizer (A.T : Set X)) (hwT : w ∉ A.T)
    (hwp : IsPGroup 2 (A.T ⊔ zpowers w : Subgroup X)) (hwt : w * t * w⁻¹ = z)
    (hwz : w * z * w⁻¹ = t) (hRB : A.R ⊓ A.R.map (MulAut.conj w).toMonoidHom = ⊥)
    (hcomm : ∀ r ∈ A.R, ∀ b ∈ A.R.map (MulAut.conj w).toMonoidHom, r * b = b * r)
    (hdec : ∀ h ∈ A.T, ∃ r ∈ A.R, ∃ b ∈ A.R.map (MulAut.conj w).toMonoidHom, h = r * b) :
    ∃ u : X, u ^ 2 = 1 ∧ u ∈ normalizer (A.T : Set X) ∧ u ∉ A.T ∧
      IsPGroup 2 (A.T ⊔ zpowers u : Subgroup X) ∧
      (∀ r ∈ A.R, u * r * u⁻¹ ∈ A.R.map (MulAut.conj w).toMonoidHom) ∧
      (∀ b ∈ A.R.map (MulAut.conj w).toMonoidHom, u * b * u⁻¹ ∈ A.R) ∧
      u * z * u⁻¹ = t ∧ u * t * u⁻¹ = z := by
  set B := A.R.map (MulAut.conj w).toMonoidHom with hB
  have hw2 : w ^ 2 ∈ A.T := by
    refine A.mem_T_of_commute hwp le_sup_left (pow_mem (mem_sup_right (mem_zpowers w)) 2) ?_
    have : w ^ 2 * t * (w ^ 2)⁻¹ = t := by
      calc w ^ 2 * t * (w ^ 2)⁻¹ = w * (w * t * w⁻¹) * w⁻¹ := by rw [pow_two]; group
        _ = t := by rw [hwt, hwz]
    calc w ^ 2 * t = w ^ 2 * t * (w ^ 2)⁻¹ * w ^ 2 := by group
      _ = t * w ^ 2 := by rw [this]
  obtain ⟨x₁, hx₁, x₂, hx₂, hw2eq⟩ := hdec _ hw2
  have hwx₁ : w * x₁ * w⁻¹ ∈ B := ⟨x₁, hx₁, rfl⟩
  have hwB : ∀ b ∈ B, w * b * w⁻¹ ∈ A.R := by
    rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show w * (w * r * w⁻¹) * w⁻¹ = w ^ 2 * r * (w ^ 2)⁻¹ by rw [pow_two]; group]
    exact A.conj_mem_R hw2 hr
  have hwx₂ : w * x₂ * w⁻¹ ∈ A.R := hwB x₂ hx₂
  have hfix : (w * x₂ * w⁻¹) * (w * x₁ * w⁻¹) = x₁ * x₂ := by
    calc (w * x₂ * w⁻¹) * (w * x₁ * w⁻¹) = (w * x₁ * w⁻¹) * (w * x₂ * w⁻¹) :=
          hcomm _ hwx₂ _ hwx₁
      _ = w * (x₁ * x₂) * w⁻¹ := by group
      _ = x₁ * x₂ := by rw [← hw2eq, pow_two]; group
  obtain ⟨h₁, h₂⟩ := A.eq_of_mul_eq hRB hwx₂ hx₁ hwx₁ hx₂ hfix
  set u := x₁⁻¹ * w with hu
  have hx₁T : x₁ ∈ A.T := hx₁.1
  have huN : u ∈ normalizer (A.T : Set X) :=
    mul_mem (inv_mem (le_normalizer hx₁T)) hw
  have hzc : x₁ * z = z * x₁ := (A.commute_z hz hψz hx₁).symm
  refine ⟨u, ?_, huN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc u ^ 2 = x₁⁻¹ * (w * x₁⁻¹ * w⁻¹) * (w * w) := by rw [hu, pow_two]; group
      _ = x₁⁻¹ * x₂⁻¹ * (x₁ * x₂) := by
          rw [show w * x₁⁻¹ * w⁻¹ = (w * x₁ * w⁻¹)⁻¹ by group, h₂, ← pow_two, hw2eq]
      _ = 1 := by rw [hcomm x₁ hx₁ x₂ hx₂]; group
  · intro huT
    exact hwT (by
      have := mul_mem hx₁T huT
      rwa [hu, mul_inv_cancel_left] at this)
  · refine hwp.to_le (sup_le le_sup_left (zpowers_le.mpr ?_))
    exact mul_mem (mem_sup_left (inv_mem hx₁T)) (mem_sup_right (mem_zpowers w))
  · intro r hr
    have hm : w * r * w⁻¹ ∈ B := ⟨r, hr, rfl⟩
    rw [show u * r * u⁻¹ = x₁⁻¹ * (w * r * w⁻¹) * x₁⁻¹⁻¹ by rw [hu]; group]
    exact A.conj_mem_map hw (inv_mem hx₁T) hm
  · intro b hb
    rw [show u * b * u⁻¹ = x₁⁻¹ * (w * b * w⁻¹) * x₁⁻¹⁻¹ by rw [hu]; group]
    exact A.conj_mem_R (inv_mem hx₁T) (hwB b hb)
  · rw [show u * z * u⁻¹ = x₁⁻¹ * (w * z * w⁻¹) * x₁ by rw [hu]; group, hwz, mul_assoc,
      ← A.commute_t hx₁T, inv_mul_cancel_left]
  · rw [show u * t * u⁻¹ = x₁⁻¹ * (w * t * w⁻¹) * x₁ by rw [hu]; group, hwt, mul_assoc,
      ← hzc, inv_mul_cancel_left]

end A7Data

end CFSG.ComponentClassification.HSFLit
