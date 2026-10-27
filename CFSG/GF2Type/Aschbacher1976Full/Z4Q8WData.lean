module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Struct
public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Wreath

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem int_dvd_of_odd_mul {α b : ℤ} (hα : Odd α) (h : (4 : ℤ) ∣ α * b) : (4 : ℤ) ∣ b := by
  obtain ⟨m, rfl⟩ := hα
  obtain ⟨q, hq⟩ := h
  exact ⟨(2 * m + 1) * q - b * (m ^ 2 + m), by linear_combination (2 * m + 1) * hq⟩

theorem comm_sup_of {K Y : Subgroup G}
    (hK : ∀ c ∈ K, ∀ c' ∈ K, c * c' = c' * c) (hY : ∀ d ∈ Y, ∀ d' ∈ Y, d * d' = d' * d)
    (hKY : ∀ c ∈ K, ∀ d ∈ Y, c * d = d * c) :
    ∀ a ∈ K ⊔ Y, ∀ b ∈ K ⊔ Y, a * b = b * a := by
  intro a ha b hb
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_iff' hKY).mp ha
  obtain ⟨c', hc', d', hd', rfl⟩ := (mem_sup_iff' hKY).mp hb
  calc c * d * (c' * d') = c * (d * c') * d' := by group
    _ = c * (c' * d) * d' := by rw [hKY c' hc' d hd]
    _ = (c * c') * (d * d') := by group
    _ = (c' * c) * (d' * d) := by rw [hK c hc c' hc', hY d hd d' hd']
    _ = c' * (c * d') * d := by group
    _ = c' * (d' * c) * d := by rw [hKY c hc d' hd']
    _ = c' * d' * (c * d) := by group

theorem indep_k_y {k y : G} (hk4 : orderOf k = 4) (hy4 : orderOf y = 4)
    (hKY : Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥) {i j : ℤ} (h : k ^ i * y ^ j = 1) :
    (4 : ℤ) ∣ i ∧ (4 : ℤ) ∣ j := by
  have hi : k ^ i = (y ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hmemK : k ^ i ∈ Subgroup.zpowers k := Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) i
  have hmemY : k ^ i ∈ Subgroup.zpowers y := by
    rw [hi]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j)
  have hbot : k ^ i = 1 := by
    have : k ^ i ∈ Subgroup.zpowers k ⊓ Subgroup.zpowers y := Subgroup.mem_inf.mpr ⟨hmemK, hmemY⟩
    rw [hKY, Subgroup.mem_bot] at this
    exact this
  have hj : y ^ j = 1 := by
    rw [hbot] at hi
    exact inv_eq_one.mp hi.symm
  constructor
  · have := (orderOf_dvd_iff_zpow_eq_one (x := k)).mpr hbot
    rw [hk4] at this
    exact_mod_cast this
  · have := (orderOf_dvd_iff_zpow_eq_one (x := y)).mpr hj
    rw [hy4] at this
    exact_mod_cast this

theorem conj_sq_eq {z y s : G} {T A : Subgroup G} (hsT : s ∈ T) (hsA : s ∉ A)
    (hA_sub : ∀ g ∈ T, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAinv : ∀ x ∈ A, x ^ 2 = 1 → x = 1 ∨ x = z ∨ x = y ^ 2 ∨ x = z * y ^ 2)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hy2A : y ^ 2 ∈ A)
    (hzT : ∀ g ∈ T, z * g = g * z) (hFT : Fz z ≤ T)
    (hFnc : ∃ f ∈ Fz z, f * y ^ 2 ≠ y ^ 2 * f)
    (hcoset : ∀ x ∈ T, x ∉ A → s⁻¹ * x ∈ A) (hy4 : y ^ 4 = 1) (hy2ne1 : y ^ 2 ≠ 1)
    (htz : y ^ 2 ≠ z) : s * y ^ 2 * s⁻¹ = z * y ^ 2 := by
  have hconj : s * y ^ 2 * s⁻¹ ∈ A := hA_sub s hsT _ hy2A
  have hsq : (s * y ^ 2 * s⁻¹) ^ 2 = 1 := by
    calc (s * y ^ 2 * s⁻¹) ^ 2 = s * (y ^ 2) ^ 2 * s⁻¹ := conj_pow
      _ = s * y ^ 4 * s⁻¹ := by rw [← pow_mul]
      _ = 1 := by rw [hy4]; group
  rcases hAinv _ hconj hsq with h1 | h1 | h1 | h1
  · exfalso
    apply hy2ne1
    calc y ^ 2 = s⁻¹ * (s * y ^ 2 * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  · exfalso
    apply htz
    calc y ^ 2 = s⁻¹ * (s * y ^ 2 * s⁻¹) * s := by group
      _ = s⁻¹ * z * s := by rw [h1]
      _ = z := by rw [mul_assoc, hzT s hsT, inv_mul_cancel_left]
  · exfalso
    obtain ⟨f, hfF, hf⟩ := hFnc
    have hfT : f ∈ T := hFT hfF
    have hst : s * y ^ 2 = y ^ 2 * s := by
      calc s * y ^ 2 = (s * y ^ 2 * s⁻¹) * s := by group
        _ = y ^ 2 * s := by rw [h1]
    by_cases hfA : f ∈ A
    · exact hf (hAcomm f hfA _ hy2A)
    · apply hf
      have ha : s⁻¹ * f ∈ A := hcoset f hfT hfA
      have hf_eq : f = s * (s⁻¹ * f) := by group
      calc f * y ^ 2 = s * (s⁻¹ * f) * y ^ 2 := by rw [← hf_eq]
        _ = s * ((s⁻¹ * f) * y ^ 2) := by group
        _ = s * (y ^ 2 * (s⁻¹ * f)) := by rw [hAcomm _ ha _ hy2A]
        _ = (s * y ^ 2) * (s⁻¹ * f) := by group
        _ = (y ^ 2 * s) * (s⁻¹ * f) := by rw [hst]
        _ = y ^ 2 * (s * (s⁻¹ * f)) := by group
        _ = y ^ 2 * f := by rw [← hf_eq]
  · exact h1

theorem coords_indep {z k y v : G} (hky : k * y = y * k) (hk4 : orderOf k = 4)
    (hy4 : orderOf y = 4) (hk2 : k ^ 2 = z) (hKY : Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥)
    (hvK : v ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y) (hv2 : v ^ 2 = z * y ^ 2) :
    ∃ α β : ℤ, Odd α ∧ Odd β ∧ v = k ^ α * y ^ β ∧
      ∀ i j : ℤ, y ^ i * v ^ j = 1 → (4 : ℤ) ∣ i ∧ (4 : ℤ) ∣ j := by
  have hkyC : Commute k y := hky
  have hcomm : ∀ a b : ℤ, k ^ a * y ^ b = y ^ b * k ^ a := fun a b =>
    (hkyC.zpow_zpow a b).eq
  have hcomm' : ∀ c ∈ Subgroup.zpowers k, ∀ d ∈ Subgroup.zpowers y, c * d = d * c := by
    intro c hc d hd
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact hcomm a b
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_iff' hcomm').mp hvK
  obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨β, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hsq : (k ^ α * y ^ β) ^ 2 = k ^ (2 * α) * y ^ (2 * β) := by
    rw [sq]
    calc k ^ α * y ^ β * (k ^ α * y ^ β) = k ^ α * (y ^ β * k ^ α) * y ^ β := by group
      _ = k ^ α * (k ^ α * y ^ β) * y ^ β := by rw [hcomm α β]
      _ = k ^ (2 * α) * y ^ (2 * β) := by
        rw [show (2 : ℤ) * α = α + α by ring, show (2 : ℤ) * β = β + β by ring, zpow_add,
          zpow_add]
        group
  have hcancel : k ^ (2 * α - 2) * y ^ (2 * β - 2) = 1 := by
    have e : k ^ (2 * α) * y ^ (2 * β) = k ^ (2 : ℤ) * y ^ (2 : ℤ) := by
      rw [← hsq, hv2, ← hk2]
      simp
    have hc1 : Commute (k ^ (2 : ℤ)) (y ^ (2 * β)) := hkyC.zpow_zpow 2 (2 * β)
    have hc2 : Commute (k ^ (2 : ℤ)) (y ^ (2 : ℤ)) := hkyC.zpow_zpow 2 2
    rw [zpow_sub, zpow_sub]
    calc k ^ (2 * α) * (k ^ (2 : ℤ))⁻¹ * (y ^ (2 * β) * (y ^ (2 : ℤ))⁻¹)
        = k ^ (2 * α) * ((k ^ (2 : ℤ))⁻¹ * y ^ (2 * β)) * (y ^ (2 : ℤ))⁻¹ := by group
      _ = k ^ (2 * α) * (y ^ (2 * β) * (k ^ (2 : ℤ))⁻¹) * (y ^ (2 : ℤ))⁻¹ := by
          rw [hc1.inv_left.eq]
      _ = (k ^ (2 * α) * y ^ (2 * β)) * ((k ^ (2 : ℤ))⁻¹ * (y ^ (2 : ℤ))⁻¹) := by group
      _ = (k ^ (2 : ℤ) * y ^ (2 : ℤ)) * ((k ^ (2 : ℤ))⁻¹ * (y ^ (2 : ℤ))⁻¹) := by rw [e]
      _ = (y ^ (2 : ℤ) * k ^ (2 : ℤ)) * ((k ^ (2 : ℤ))⁻¹ * (y ^ (2 : ℤ))⁻¹) := by rw [hc2.eq]
      _ = 1 := by group
  obtain ⟨h4a, h4b⟩ := indep_k_y hk4 hy4 hKY hcancel
  have hoddα : Odd α := Int.odd_iff.mpr (by omega)
  have hoddβ : Odd β := Int.odd_iff.mpr (by omega)
  refine ⟨α, β, hoddα, hoddβ, rfl, ?_⟩
  intro i j hij
  have e2 : y ^ i * (k ^ α * y ^ β) ^ j = k ^ (α * j) * y ^ (i + β * j) := by
    rw [((show Commute (k ^ α) (y ^ β) from hkyC.zpow_zpow α β)).mul_zpow j]
    rw [← zpow_mul, ← zpow_mul, zpow_add]
    calc y ^ i * (k ^ (α * j) * y ^ (β * j)) = (y ^ i * k ^ (α * j)) * y ^ (β * j) := by group
      _ = (k ^ (α * j) * y ^ i) * y ^ (β * j) := by rw [← hcomm (α * j) i]
      _ = k ^ (α * j) * (y ^ i * y ^ (β * j)) := by group
  rw [e2] at hij
  obtain ⟨h1, h2⟩ := indep_k_y hk4 hy4 hKY hij
  have hj4 : (4 : ℤ) ∣ j := int_dvd_of_odd_mul hoddα h1
  refine ⟨?_, hj4⟩
  exact (dvd_add_left (dvd_mul_of_dvd_right hj4 β)).mp h2

theorem wdata_exists {z : G} {k y s : G} {T : Subgroup G} (hky : k * y = y * k)
    (hk4 : orderOf k = 4) (hy4 : orderOf y = 4) (hk2 : k ^ 2 = z)
    (hKY : Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥)
    (hsT : s ∈ T) (hyT : y ∈ T) (hsA : s ∉ Subgroup.zpowers k ⊔ Subgroup.zpowers y)
    (hs2A : s ^ 2 ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y)
    (hst : s * y ^ 2 * s⁻¹ = z * y ^ 2)
    (hsub : ∀ g ∈ T, ∀ a ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y,
      g * a * g⁻¹ ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y) :
    ∃ s' : G, s' ∈ T ∧ WData y (s * y * s⁻¹) s' := by
  set A : Subgroup G := Subgroup.zpowers k ⊔ Subgroup.zpowers y with hAdef
  have hkyC : Commute k y := hky
  have hyA : y ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    refine comm_sup_of ?_ ?_ ?_
    · intro c hc c' hc'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
      exact ((Commute.zpow_zpow_self k i j)).eq
    · intro d hd d' hd'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd'
      exact ((Commute.zpow_zpow_self y i j)).eq
    · intro c hc d hd
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      exact ((hkyC.zpow_zpow i j)).eq
  set v : G := s * y * s⁻¹ with hvdef
  have hvA : v ∈ A := hsub s hsT y hyA
  have hvT : v ∈ T := by
    rw [hvdef]
    exact T.mul_mem (T.mul_mem hsT hyT) (T.inv_mem hsT)
  have hv2 : v ^ 2 = z * y ^ 2 := by
    rw [hvdef, conj_pow, hst]
  have hv4ord : orderOf v = 4 := by
    rw [hvdef, ← hy4]
    exact orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective y
  have hv4 : v ^ 4 = 1 := by
    rw [← hv4ord]
    exact pow_orderOf_eq_one v
  obtain ⟨α, β, hoα, hoβ, hveq, hind_yv⟩ := coords_indep hky hk4 hy4 hk2 hKY hvA hv2
  have hyv : Commute y v := hcommA y hyA v hvA
  have hY_V : Subgroup.zpowers y ⊓ Subgroup.zpowers v = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    obtain ⟨hwY, hwV⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwY
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwV
    have h1 : y ^ i * v ^ (-j) = 1 := by
      rw [zpow_neg, ← hj]
      group
    obtain ⟨hi4, -⟩ := hind_yv i (-j) h1
    have : y ^ i = 1 := (orderOf_dvd_iff_zpow_eq_one (x := y)).mp (by rw [hy4]; exact_mod_cast hi4)
    exact this
  have hVcard : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers v) = 16 :=
    card_A hyv.eq hy4 hv4ord hY_V
  have hAcard : Nat.card ↥A = 16 := card_A hky hk4 hy4 hKY
  have hAeq : Subgroup.zpowers y ⊔ Subgroup.zpowers v = A := by
    have hle : Subgroup.zpowers y ⊔ Subgroup.zpowers v ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr hyA) (Subgroup.zpowers_le.mpr hvA)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard, hVcard])
  have hYV_comm : ∀ c ∈ Subgroup.zpowers y, ∀ d ∈ Subgroup.zpowers v, c * d = d * c := by
    intro c hc d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact (hyv.zpow_zpow i j).eq
  have hs2' : s ^ 2 ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers v := by
    rw [hAeq]
    exact hs2A
  obtain ⟨c, hc, d, hd, hcd⟩ := (mem_sup_iff' hYV_comm).mp hs2'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hs2y : s ^ 2 * y = y * s ^ 2 := hcommA (s ^ 2) hs2A y hyA
  have hsvs : s * v * s⁻¹ = y := by
    calc s * v * s⁻¹ = s ^ 2 * y * (s ^ 2)⁻¹ := by rw [hvdef]; simp only [sq]; group
      _ = y * s ^ 2 * (s ^ 2)⁻¹ := by rw [hs2y]
      _ = y := by group
  have hfix : s * (y ^ i * v ^ j) * s⁻¹ = y ^ i * v ^ j := by
    rw [← hcd]
    group
  have hconjiv : s * (y ^ i * v ^ j) * s⁻¹ = v ^ i * y ^ j := by
    have h1 : s * y ^ i * s⁻¹ = v ^ i := by
      rw [← conj_zpow, hvdef]
    have h2 : s * v ^ j * s⁻¹ = y ^ j := by
      rw [← conj_zpow, hsvs]
    calc s * (y ^ i * v ^ j) * s⁻¹ = (s * y ^ i * s⁻¹) * (s * v ^ j * s⁻¹) := by group
      _ = v ^ i * y ^ j := by rw [h1, h2]
  have hfix2 : v ^ i * y ^ j = y ^ i * v ^ j := hconjiv.symm.trans hfix
  have hyvij : y ^ (i - j) = v ^ (i - j) := by
    have hyj : y ^ j * v ^ i = y ^ i * v ^ j := (hyv.zpow_zpow j i).eq.trans hfix2
    have e1 : y ^ i = y ^ j * v ^ i * (v ^ j)⁻¹ := by
      rw [hyj]
      group
    calc y ^ (i - j) = y ^ i * (y ^ j)⁻¹ := by rw [zpow_sub]
      _ = (y ^ j * v ^ i * (v ^ j)⁻¹) * (y ^ j)⁻¹ := by rw [← e1]
      _ = y ^ j * v ^ (i - j) * (y ^ j)⁻¹ := by rw [zpow_sub]; group
      _ = v ^ (i - j) := by rw [(hyv.zpow_zpow j (i - j)).eq]; group
  have hyij1 : y ^ (i - j) = 1 := by
    have hmem : y ^ (i - j) ∈ Subgroup.zpowers y ⊓ Subgroup.zpowers v := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) _, ?_⟩
      rw [hyvij]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _
    rw [hY_V, Subgroup.mem_bot] at hmem
    exact hmem
  have hvij1 : v ^ (i - j) = 1 := by rw [← hyvij, hyij1]
  have hdvd_ij : (4 : ℤ) ∣ i - j := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := y)).mpr hyij1
    rw [hy4] at this
    exact_mod_cast this
  have hvj_eq : v ^ i = v ^ j := by
    have e : v ^ i = v ^ j * v ^ (i - j) := by
      rw [← zpow_add]
      congr 1
      ring
    rw [e, hvij1, mul_one]
  have hs2eq : s ^ 2 = (y * v) ^ i := by
    rw [hcd, ← hvj_eq, hyv.mul_zpow]
  have hsv_inv : s⁻¹ * y * s = v := by
    calc s⁻¹ * y * s = s⁻¹ * (s * v * s⁻¹) * s := by rw [hsvs]
      _ = v := by group
  have hyss : y ^ (-i) * s = s * v ^ (-i) := by
    have hc1 : (s⁻¹ * y * s⁻¹⁻¹) ^ (-i) = s⁻¹ * y ^ (-i) * s⁻¹⁻¹ := conj_zpow
    simp only [inv_inv] at hc1
    rw [hsv_inv] at hc1
    calc y ^ (-i) * s = s * (s⁻¹ * y ^ (-i) * s) := by group
      _ = s * v ^ (-i) := by rw [← hc1]
  have hs2' : (s * y ^ (-i)) ^ 2 = 1 := by
    rw [sq]
    calc s * y ^ (-i) * (s * y ^ (-i)) = s * (y ^ (-i) * s) * y ^ (-i) := by group
      _ = s * (s * v ^ (-i)) * y ^ (-i) := by rw [hyss]
      _ = s ^ 2 * v ^ (-i) * y ^ (-i) := by rw [sq]; group
      _ = (y * v) ^ i * v ^ (-i) * y ^ (-i) := by rw [hs2eq]
      _ = y ^ i * v ^ i * v ^ (-i) * y ^ (-i) := by rw [hyv.mul_zpow]
      _ = 1 := by group
  have hyc : y ^ (-i) * v = v * y ^ (-i) := (hyv.zpow_left (-i)).eq
  have hsu' : s * y ^ (-i) * y * (s * y ^ (-i))⁻¹ = v := by
    calc s * y ^ (-i) * y * (s * y ^ (-i))⁻¹ = s * y * s⁻¹ := by group
      _ = v := hvdef.symm
  have hsv' : s * y ^ (-i) * v * (s * y ^ (-i))⁻¹ = y := by
    calc s * y ^ (-i) * v * (s * y ^ (-i))⁻¹ = s * ((y ^ (-i) * v) * y ^ i) * s⁻¹ := by group
      _ = s * ((v * y ^ (-i)) * y ^ i) * s⁻¹ := by rw [hyc]
      _ = s * v * s⁻¹ := by group
      _ = y := hsvs
  have hind : ∀ a b : ℕ, y ^ a * v ^ b = 1 → 4 ∣ a ∧ 4 ∣ b := by
    intro a b hab
    have h' : y ^ (a : ℤ) * v ^ (b : ℤ) = 1 := by
      simpa only [zpow_natCast] using hab
    obtain ⟨h1, h2⟩ := hind_yv a b h'
    exact ⟨Int.natCast_dvd_natCast.mp h1, Int.natCast_dvd_natCast.mp h2⟩
  have hsnot : ∀ a b : ℕ, s * y ^ (-i) ≠ y ^ a * v ^ b := by
    intro a b h
    apply hsA
    have hs_eq : s = y ^ a * v ^ b * y ^ i := by
      rw [← h]
      group
    rw [hs_eq]
    refine A.mul_mem (A.mul_mem (A.pow_mem hyA a) (A.pow_mem hvA b)) (A.zpow_mem hyA i)
  refine ⟨s * y ^ (-i), T.mul_mem hsT (T.zpow_mem hyT _), ?_⟩
  refine ⟨?_, hv4, hyv, hs2', hsu', hsv', hind, hsnot⟩
  exact pow_orderOf_eq_one y |> fun h => by rw [hy4] at h; exact h

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
