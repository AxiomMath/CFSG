module

public import CFSG.GH74.GLS.LU.Local.Torus3

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open CFSG.Semidihedral.MatrixCoverData (slConjugation)
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

theorem two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have := Fintype.ofFinite F
  refine Ring.two_ne_zero ?_
  intro h2
  have h := (FiniteField.even_card_iff_char_two (F := F)).mp h2
  rw [← Nat.card_eq_fintype_card] at h
  have := Nat.odd_iff.mp hodd
  omega

@[expose] def sl2NegOne (F : Type) [Field F] : SL(2, F) :=
  ⟨-1, by simp [Matrix.det_fin_two]⟩

theorem sl2NegOne_coe (F : Type) [Field F] :
    ((sl2NegOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := rfl

theorem sl2NegOne_ne_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : sl2NegOne F ≠ 1 := by
  intro h
  have := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [sl2NegOne_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq] at this
  apply h2
  linear_combination -this

theorem sl2NegOne_mem_center {F : Type} [Field F] : sl2NegOne F ∈ Subgroup.center SL(2, F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, sl2NegOne_coe]
  simp

variable {G : Type} [Group G] [Finite G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
  {p f : ℕ} {ε : ℤ}

omit [Finite G] in
theorem iso_negOne_eq_z {q : ℕ} (hc : LUComps G q z K₁ K₂) (hz2 : z * z = 1) {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (e : SL(2, F) ≃* ↥K₁) : ((e (sl2NegOne F) : ↥K₁) : G) = z := by
  have h1 : ((e (sl2NegOne F) : ↥K₁) : G) ∈ (center ↥K₁).map K₁.subtype :=
    ⟨e (sl2NegOne F), (mem_center_equiv_iff e (a := sl2NegOne F)).mpr sl2NegOne_mem_center, rfl⟩
  rw [hc.cen₁] at h1
  rcases eq_one_or_eq_of_mem_zpowers hz2 h1 with h | h
  · exfalso
    apply sl2NegOne_ne_one h2
    apply e.injective
    apply Subtype.ext
    simpa using h
  · exact h

omit [Finite G] in
theorem exists_anti_K₁ {q : ℕ} (hc : LUComps G q z K₁ K₂) (hz2 : z * z = 1) (hq : Odd q) (hq3 : 3 < q)
    {s : G} (hs2 : s * s = 1) (hsn : s ∈ normalizer (K₁ : Set G)) (hnc : ∃ k ∈ K₁, s * k ≠ k * s)
    (hab : ∀ a ∈ K₁, ∀ b ∈ K₁, a * s = s * a → b * s = s * b → a * b = b * a) :
    ∃ w ∈ K₁, s * w * s⁻¹ = w * z := by
  obtain ⟨F, hF, hFin, hFq, -⟩ := hc.sl₁
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hc.sl₁ F hFq
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hq
  have h3' : 3 < Nat.card F := by rw [hFq]; exact hq3
  have hh2 := two_ne_zero_of_odd_card hodd
  have hαsq : actAut e s hsn * actAut e s hsn = 1 := by
    have h := (actHom e).map_mul ⟨s, hsn⟩ ⟨s, hsn⟩
    have h1 : (⟨s, hsn⟩ * ⟨s, hsn⟩ : ↥(normalizer (K₁ : Set G))) = 1 := Subtype.ext hs2
    rw [h1, map_one] at h
    exact h.symm
  have hαne : actAut e s hsn ≠ 1 := by
    intro h
    obtain ⟨k, hk, hkc⟩ := hnc
    exact hkc ((actAut_eq_one_iff e hsn).mp h k hk)
  have hfix : ∀ a b : SL(2, F), actAut e s hsn a = a → actAut e s hsn b = b → a * b = b * a := by
    intro a b ha hb
    have h1 := (actAut_fixed_iff e hsn a).mp ha
    have h2 := (actAut_fixed_iff e hsn b).mp hb
    have := hab _ (e a).2 _ (e b).2 h1 h2
    apply e.injective
    apply Subtype.ext
    simpa using this
  obtain ⟨G₁, hG₁, ⟨c₁, hc₁⟩, hn₁⟩ := sl2_aut_matrix_form_of_involution hodd h3' _ hαsq hαne hfix
  obtain ⟨w, hw⟩ := exists_anti_fixed hh2 G₁ ⟨c₁, hc₁⟩ hn₁
  have hαw : actAut e s hsn w = w * sl2NegOne F := by
    apply Subtype.ext
    rw [hG₁, slConjugation_coe, hw, Matrix.SpecialLinearGroup.coe_mul, sl2NegOne_coe]
    simp
  refine ⟨(e w : G), (e w).2, ?_⟩
  have h1 := congrArg (fun M : SL(2, F) => ((e M : ↥K₁) : G)) hαw
  simp only [coe_actAut, map_mul, Subgroup.coe_mul] at h1
  rw [h1, iso_negOne_eq_z hc hz2 hh2 e]

theorem exists_v_w (X : LUCtx G p f z S K₁ K₂ t u ε) {h₀ : G} (hh₀ : h₀⁻¹ * z * h₀ = u) :
    ∃ v ∈ cj K₁ h₀, ∃ w ∈ K₁, z * v * z⁻¹ = v * u ∧ u * w * u⁻¹ = w * z := by
  have hc := X.comps
  have hs := X.syl
  have hq := X.odd_q
  have hq3 : 3 < p ^ f := lt_of_lt_of_le (by norm_num) X.hq
  have hz2 : z * z = 1 := hs.z_sq
  have hu2 : u * u = 1 := hs.u_sq
  have ho2 : ∀ w : G, w * w = 1 → w ≠ 1 → ∃ n : ℕ, orderOf w = 2 ^ n := by
    intro w hw hw1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨1, ?_⟩
    have : w ^ 2 = 1 := by rw [pow_two]; exact hw
    simpa using orderOf_eq_prime this hw1
  have hunc := u_not_cent hc hs hq (Or.inl rfl)
  obtain ⟨w, hwK, hw⟩ := exists_anti_K₁ hc hz2 hq hq3 hu2 hs.u_norm hunc
    (cenAb_C hc hs (Or.inl rfl) hs.u_mem_Cz (ho2 u hu2 (u_ne_one hs)) hs.u_norm hunc)
  have hzcC : h₀ * z * h₀⁻¹ ∈ Cz z := mem_centralizer_singleton_iff.mpr (conj_comm_z hh₀ hs.zu_comm)
  have hzc2 : (h₀ * z * h₀⁻¹) * (h₀ * z * h₀⁻¹) = 1 := by rw [conj_mul_mul, hz2]; group
  have hzcz : (h₀ * z * h₀⁻¹) ∉ zpowers z := conj_z_not_mem_zpowers hs hh₀
  have hzcn : (h₀ * z * h₀⁻¹) ∈ normalizer (K₁ : Set G) :=
    (mem_normalizer_cj_iff K₁ h₀ z).mp (z_norm_L X hh₀)
  have hnc := invol_nontriv hc hs hq (Or.inl rfl) hzcC hzc2 hzcz
  have hzc1 : h₀ * z * h₀⁻¹ ≠ 1 := fun h => hzcz (h ▸ one_mem _)
  obtain ⟨v₁, hv₁K, hv₁⟩ := exists_anti_K₁ hc hz2 hq hq3 hzc2 hzcn hnc
    (cenAb_C hc hs (Or.inl rfl) hzcC (ho2 _ hzc2 hzc1) hzcn hnc)
  refine ⟨h₀⁻¹ * v₁ * h₀, ?_, w, hwK, ?_, hw⟩
  · rw [mem_cj]
    have : h₀ * (h₀⁻¹ * v₁ * h₀) * h₀⁻¹ = v₁ := by group
    rw [this]; exact hv₁K
  · calc z * (h₀⁻¹ * v₁ * h₀) * z⁻¹
        = h₀⁻¹ * ((h₀ * z * h₀⁻¹) * v₁ * (h₀ * z * h₀⁻¹)⁻¹) * h₀ := by group
      _ = h₀⁻¹ * (v₁ * z) * h₀ := by rw [hv₁]
      _ = (h₀⁻¹ * v₁ * h₀) * (h₀⁻¹ * z * h₀) := by group
      _ = (h₀⁻¹ * v₁ * h₀) * u := by rw [hh₀]

omit [Finite G] in
theorem h_conj {q : ℕ} (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {v w : G}
    (hwK : w ∈ K₁) (hv : z * v * z⁻¹ = v * u) (hw : u * w * u⁻¹ = w * z) :
    (v * w)⁻¹ * z * (v * w) = u ∧ v⁻¹ * z * v = z * u := by
  have hz2 : z * z = 1 := hs.z_sq
  have hzu : z * u = u * z := hs.zu_comm
  have hwz : w * z = z * w := hc.cz₁ hwK
  have e0 : z * v = v * u * z := by
    calc z * v = (z * v * z⁻¹) * z := by group
      _ = v * u * z := by rw [hv]
  have e1 : v⁻¹ * z * v = u * z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by group
      _ = v⁻¹ * (v * u * z) := by rw [e0]
      _ = u * z := by group
  have e0' : u * w = w * z * u := by
    calc u * w = (u * w * u⁻¹) * u := by group
      _ = w * z * u := by rw [hw]
  have e2 : w⁻¹ * u * w = z * u := by
    calc w⁻¹ * u * w = w⁻¹ * (u * w) := by group
      _ = w⁻¹ * (w * z * u) := by rw [e0']
      _ = z * u := by group
  have e3 : w⁻¹ * z * w = z := by
    calc w⁻¹ * z * w = w⁻¹ * (z * w) := by group
      _ = w⁻¹ * (w * z) := by rw [hwz]
      _ = z := by group
  refine ⟨?_, by rw [e1, ← hzu]⟩
  calc (v * w)⁻¹ * z * (v * w) = w⁻¹ * (v⁻¹ * z * v) * w := by group
    _ = w⁻¹ * (u * z) * w := by rw [e1]
    _ = (w⁻¹ * u * w) * (w⁻¹ * z * w) := by group
    _ = (z * u) * z := by rw [e2, e3]
    _ = (u * z) * z := by rw [hzu]
    _ = u * (z * z) := by group
    _ = u := by rw [hz2, mul_one]

theorem cj_eq_or {q : ℕ} (hc : LUComps G q z K₁ K₂) {h₀ h : G} (hh₀ : h₀⁻¹ * z * h₀ = u)
    (hh : h⁻¹ * z * h = u) : cj K₁ h = cj K₁ h₀ ∨ cj K₁ h = cj K₂ h₀ := by
  set c : G := h * h₀⁻¹ with hcdef
  have hz₀ : h₀ * u * h₀⁻¹ = z := by rw [← hh₀]; group
  have hz₁ : h * u * h⁻¹ = z := by rw [← hh]; group
  have hcC : c ∈ Cz z := by
    refine mem_centralizer_singleton_iff.mpr ?_
    calc c * z = (h * h₀⁻¹) * (h₀ * u * h₀⁻¹) := by rw [hcdef, hz₀]
      _ = (h * u * h⁻¹) * (h * h₀⁻¹) := by group
      _ = z * c := by rw [hz₁]
  have hcinv : c⁻¹ ∈ Cz z := (Cz z).inv_mem hcC
  have hmem : ∀ (K : Subgroup G) (y : G),
      y ∈ K.map (MulAut.conj c⁻¹).toMonoidHom ↔ c * y * c⁻¹ ∈ K := by
    intro K y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : c * ((MulAut.conj c⁻¹).toMonoidHom k) * c⁻¹ = k := by
        show c * (c⁻¹ * k * c⁻¹⁻¹) * c⁻¹ = k
        group
      rw [this]; exact hk
    · intro hy
      refine ⟨c * y * c⁻¹, hy, ?_⟩
      show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y
      group
  have hh' : h = c * h₀ := by rw [hcdef]; group
  have hcj : cj K₁ h = cj (K₁.map (MulAut.conj c⁻¹).toMonoidHom) h₀ := by
    ext x
    rw [mem_cj, mem_cj, hmem, hh']
    have : c * (h₀ * x * h₀⁻¹) * c⁻¹ = c * h₀ * x * (c * h₀)⁻¹ := by group
    rw [this]
  rcases comp_conj_mem hc (Or.inl rfl) hcinv with e | e
  · left; rw [hcj, e]
  · right; rw [hcj, e]

end CFSG.GH74.GLS.LU.Local
