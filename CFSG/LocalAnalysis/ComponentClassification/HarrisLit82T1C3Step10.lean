module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step9

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L S : Subgroup G} {p f : ℕ}

theorem exists_conj_normalizes {M T : Subgroup G} (hT : IsSylowOf 2 T M) {c : G}
    (hc : M.map (MulAut.conj c).toMonoidHom = M) :
    ∃ k ∈ M, (∀ t ∈ T, (k⁻¹ * c) * t * (k⁻¹ * c)⁻¹ ∈ T) ∧
      ∀ t ∈ T, (k⁻¹ * c)⁻¹ * t * (k⁻¹ * c) ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowOf 2 (T.map (MulAut.conj c).toMonoidHom) M := by
    have h1 := IsSylowOf.map (MulAut.conj c).toMonoidHom hT
    rwa [hc] at h1
  obtain ⟨k, hkM, hk⟩ := hT.exists_mem_conj hT'
  refine ⟨k, hkM, fun t ht => ?_, fun t ht => ?_⟩
  · have h1 := (hk (c * t * c⁻¹)).mp ⟨t, ht, by simp [MulAut.conj_apply]⟩
    rwa [show k⁻¹ * (c * t * c⁻¹) * k = (k⁻¹ * c) * t * (k⁻¹ * c)⁻¹ by group] at h1
  · have h1 : k * t * k⁻¹ ∈ T.map (MulAut.conj c).toMonoidHom :=
      (hk _).mpr (by rwa [show k⁻¹ * (k * t * k⁻¹) * k = t by group])
    obtain ⟨y, hy, hyt⟩ := h1
    have hyt' : c * y * c⁻¹ = k * t * k⁻¹ := by simpa [MulAut.conj_apply] using hyt
    rwa [show (k⁻¹ * c)⁻¹ * t * (k⁻¹ * c) = c⁻¹ * (k * t * k⁻¹) * c by group, ← hyt',
      show c⁻¹ * (c * y * c⁻¹) * c = y by group]

omit [Finite G] in
theorem map_conj_centralizer_inf (a b c : G) :
    (centralizer ({a} : Set G) ⊓ centralizer {b}).map (MulAut.conj c).toMonoidHom =
      centralizer {c * a * c⁻¹} ⊓ centralizer {c * b * c⁻¹} := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective, map_centralizer_singleton_mulEquiv,
    map_centralizer_singleton_mulEquiv, MulAut.conj_apply, MulAut.conj_apply]

omit [Finite G] in
theorem conj_eq_of_commute {k x : G} (h : k * x = x * k) : k⁻¹ * x * k = x := by
  rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

omit [Finite G] in
theorem commute_mul' {k a b : G} (ha : k * a = a * k) (hb : k * b = b * k) :
    k * (a * b) = (a * b) * k :=
  (Commute.mul_right (a := k) (b := a) (c := b) ha hb).eq

namespace Step6

variable (d : Step6 z L S)

section Certified


theorem exists_pi (hI : C3Inputs) (h : C3Config G z L p f)
    (hS : IsSylowOf 2 S (centralizer {z})) :
    ∃ π : G, π * d.z₁ * π⁻¹ = z ∧ (∀ t ∈ S ⊓ centralizer {d.z₁},
      π * t * π⁻¹ ∈ S ⊓ centralizer {d.z₁}) ∧
      ∀ t ∈ S ⊓ centralizer {d.z₁}, t⁻¹ * (π * t * π⁻¹) ∈ L := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := S ⊓ centralizer {d.z₁} with hTdef
  set M := centralizer ({z} : Set G) ⊓ centralizer {d.z₁} with hMdef
  have hT : IsSylowOf 2 T M := d.hT
  have hTS : T ≤ S := inf_le_left
  have hSH : S ≤ centralizer {z} := hS.le
  have hTH : T ≤ centralizer {z} := hTS.trans hSH
  have hTp : IsPGroup 2 T := hS.isPGroup.to_le hTS
  have hz₁H : d.z₁ ∈ centralizer ({z} : Set G) := h.hL.1 d.hz₁L
  have hc : z * d.z₁ = d.z₁ * z := (mem_centralizer_singleton_iff.mp hz₁H).symm
  have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
  have hz₁z₁ : d.z₁ * d.z₁ = 1 := by rw [← sq, ← d.hz₁, pow_orderOf_eq_one]
  have hne : d.z₁ ≠ z := fun he => d.hz₁Z (by
    have h1 : (⟨d.z₁, d.hz₁L⟩ : ↥L) = ⟨z, h.hzL⟩ := Subtype.ext he
    rw [h1]
    exact mk_mem_center_of_mem_center (mem_center_of_le_centralizer h.hL.1 h.hzL))
  have hzz₁ : orderOf (z * d.z₁) = 2 := orderOf_mul_of_commute h.hz d.hz₁ hc hne
  have hzz₁L : z * d.z₁ ∈ L := mul_mem h.hzL d.hz₁L
  have hzz₁Z : (QuotientGroup.mk (⟨z * d.z₁, hzz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    intro hcen
    apply d.hz₁Z
    have h1 : (QuotientGroup.mk (⟨d.z₁, d.hz₁L⟩ : ↥L) : Bar L) =
        (QuotientGroup.mk ⟨z, h.hzL⟩)⁻¹ * QuotientGroup.mk ⟨z * d.z₁, hzz₁L⟩ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp
    rw [h1]
    exact mul_mem (inv_mem (mk_mem_center_of_mem_center
      (mem_center_of_le_centralizer h.hL.1 h.hzL))) hcen
  obtain ⟨a, haL, ha⟩ := spinSeven_conj_of_involution h.h5 h.hcov d.hz₁L hzz₁L d.hz₁ hzz₁
    d.hz₁Z hzz₁Z
  have haH : a ∈ centralizer ({z} : Set G) := h.hL.1 haL
  have haz : a * z * a⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp haH, mul_inv_cancel_right]
  have hMz : ∀ {c : G}, c * z * c⁻¹ = z → c * d.z₁ * c⁻¹ = z * d.z₁ →
      M.map (MulAut.conj c).toMonoidHom = M := by
    intro c h1 h2
    rw [hMdef, map_conj_centralizer_inf, h1, h2, T23.centralizer_inf_mul]
  obtain ⟨k₁, hk₁M, hn₁, hn₂⟩ := exists_conj_normalizes hT (hMz haz ha)
  set n := k₁⁻¹ * a with hn
  have hk₁H : k₁ ∈ centralizer ({z} : Set G) := (mem_inf.mp hk₁M).1
  have hnH : n ∈ centralizer ({z} : Set G) := mul_mem (inv_mem hk₁H) haH
  have hk₁z₁ : k₁ * d.z₁ = d.z₁ * k₁ := mem_centralizer_singleton_iff.mp (mem_inf.mp hk₁M).2
  have hk₁z : k₁ * z = z * k₁ := mem_centralizer_singleton_iff.mp hk₁H
  have hnz : n * z * n⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp hnH, mul_inv_cancel_right]
  have hnz₁ : n * d.z₁ * n⁻¹ = z * d.z₁ := by
    calc n * d.z₁ * n⁻¹ = k₁⁻¹ * (a * d.z₁ * a⁻¹) * k₁ := by rw [hn]; group
      _ = k₁⁻¹ * (z * d.z₁) * k₁ := by rw [ha]
      _ = z * d.z₁ := conj_eq_of_commute (commute_mul' hk₁z hk₁z₁)
  have hπz : (a * d.b) * z * (a * d.b)⁻¹ = d.z₁ := by
    calc (a * d.b) * z * (a * d.b)⁻¹ = a * (d.b * z * d.b⁻¹) * a⁻¹ := by group
      _ = (a * z * a⁻¹) * (a * d.z₁ * a⁻¹) := by rw [d.hbz]; group
      _ = d.z₁ := by rw [haz, ha, ← mul_assoc, hzz, one_mul]
  have hπz₁ : (a * d.b) * d.z₁ * (a * d.b)⁻¹ = z * d.z₁ := by
    calc (a * d.b) * d.z₁ * (a * d.b)⁻¹ = a * (d.b * d.z₁ * d.b⁻¹) * a⁻¹ := by group
      _ = z * d.z₁ := by rw [d.hbz₁, ha]
  have hMπ : M.map (MulAut.conj (a * d.b)).toMonoidHom = M := by
    rw [hMdef, map_conj_centralizer_inf, hπz, hπz₁, hc, T23.centralizer_inf_mul, inf_comm]
  obtain ⟨k₂, hk₂M, hπ₁, hπ₂⟩ := exists_conj_normalizes hT hMπ
  set π := k₂⁻¹ * (a * d.b) with hπ
  have hk₂z₁ : k₂ * d.z₁ = d.z₁ * k₂ := mem_centralizer_singleton_iff.mp (mem_inf.mp hk₂M).2
  have hk₂z : k₂ * z = z * k₂ := mem_centralizer_singleton_iff.mp (mem_inf.mp hk₂M).1
  have hπz' : π * z * π⁻¹ = d.z₁ := by
    calc π * z * π⁻¹ = k₂⁻¹ * ((a * d.b) * z * (a * d.b)⁻¹) * k₂ := by rw [hπ]; group
      _ = d.z₁ := by rw [hπz]; exact conj_eq_of_commute hk₂z₁
  have hπz₁' : π * d.z₁ * π⁻¹ = z * d.z₁ := by
    calc π * d.z₁ * π⁻¹ = k₂⁻¹ * ((a * d.b) * d.z₁ * (a * d.b)⁻¹) * k₂ := by rw [hπ]; group
      _ = z * d.z₁ := by rw [hπz₁]; exact conj_eq_of_commute (commute_mul' hk₂z hk₂z₁)
  have hK1 : ∀ k ∈ centralizer ({z} : Set G), (∀ t ∈ T, k * t * k⁻¹ ∈ T) →
      ∀ t ∈ T, t⁻¹ * (k * t * k⁻¹) ∈ L := fun k hk hkT t ht =>
    h.inv_mul_conj_mem hI hTH hTp ht hk (hkT t ht)
  have hcl := h.closure_inf_eq hI d.hz₁L d.hz₁ d.hz₁Z hT
  have hK4 : ∀ l ∈ T ⊓ L, π * l * π⁻¹ ∈ L := by
    have hle : closure {x | x ∈ T ⊓ L ∧ x * x = 1} ≤
        (L.map (MulAut.conj π⁻¹).toMonoidHom) := by
      rw [closure_le]
      rintro x ⟨hxTL, hx2⟩
      obtain ⟨hxT, hxL⟩ := mem_inf.mp hxTL
      have hπx : π * x * π⁻¹ ∈ L := by
        by_cases hx1 : x = 1
        · rw [hx1, mul_one, mul_inv_cancel]
          exact one_mem L
        · have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
          obtain ⟨g, hg⟩ := (h.conj_iff hI (hTH hxT)).mpr ⟨hxL, hxo⟩
          have hπxT : π * x * π⁻¹ ∈ T := hπ₁ x hxT
          exact ((h.conj_iff hI (hTH hπxT)).mp ⟨π * g, by rw [← hg]; group⟩).1
      rw [SetLike.mem_coe, mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
      exact hπx
    intro l hl
    have h0 : l ∈ closure {x | x ∈ T ⊓ L ∧ x * x = 1} := by rw [hcl]; exact hl
    have h1 := hle h0
    rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at h1
    exact h1
  have hn₁' : ∀ t ∈ T, n * t * n⁻¹ ∈ T := hn₁
  have hn₂' : ∀ t ∈ T, n⁻¹ * t * n⁻¹⁻¹ ∈ T := fun t ht => by
    rw [inv_inv]
    exact hn₂ t ht
  have hnz' : n⁻¹ * z * n = z := by
    calc n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [hnz]
      _ = z := by group
  have hnz₁' : n⁻¹ * d.z₁ * n = z * d.z₁ := by
    have h1 : d.z₁ = z * (n * d.z₁ * n⁻¹) := by rw [hnz₁, ← mul_assoc, hzz, one_mul]
    calc n⁻¹ * d.z₁ * n = n⁻¹ * (z * (n * d.z₁ * n⁻¹)) * n := by rw [← h1]
      _ = (n⁻¹ * z * n) * d.z₁ := by group
      _ = z * d.z₁ := by rw [hnz']
  have hz₁zz₁ : d.z₁ * (z * d.z₁) = z := by
    rw [← mul_assoc, ← hc, mul_assoc, hz₁z₁, mul_one]
  set w := n * π * n⁻¹ * π with hw
  have hwz : w * z * w⁻¹ = z := by
    calc w * z * w⁻¹ = n * (π * (n⁻¹ * (π * z * π⁻¹) * n) * π⁻¹) * n⁻¹ := by rw [hw]; group
      _ = n * (π * (z * d.z₁) * π⁻¹) * n⁻¹ := by rw [hπz', hnz₁']
      _ = n * ((π * z * π⁻¹) * (π * d.z₁ * π⁻¹)) * n⁻¹ := by group
      _ = z := by rw [hπz', hπz₁', hz₁zz₁, hnz]
  have hwH : w ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w * z = w * z * w⁻¹ * w := by group
      _ = z * w := by rw [hwz]
  have hwT : ∀ t ∈ T, w * t * w⁻¹ ∈ T := by
    intro t ht
    rw [show w * t * w⁻¹ = n * (π * (n⁻¹ * (π * t * π⁻¹) * n⁻¹⁻¹) * π⁻¹) * n⁻¹ by rw [hw]; group]
    exact hn₁' _ (hπ₁ _ (hn₂' _ (hπ₁ t ht)))
  refine ⟨π * π, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · calc π * π * d.z₁ * (π * π)⁻¹ = π * (π * d.z₁ * π⁻¹) * π⁻¹ := by group
      _ = π * (z * d.z₁) * π⁻¹ := by rw [hπz₁']
      _ = (π * z * π⁻¹) * (π * d.z₁ * π⁻¹) := by group
      _ = z := by rw [hπz', hπz₁', hz₁zz₁]
  · rw [show π * π * t * (π * π)⁻¹ = π * (π * t * π⁻¹) * π⁻¹ by group]
    exact hπ₁ _ (hπ₁ t ht)
  · set a₁ := π * t * π⁻¹ with ha₁
    have ha₁T : a₁ ∈ T := hπ₁ t ht
    set a₂ := n⁻¹ * a₁ * n⁻¹⁻¹ with ha₂
    have ha₂T : a₂ ∈ T := hn₂' a₁ ha₁T
    have hR₁ : a₁⁻¹ * a₂ ∈ L := hK1 n⁻¹ (inv_mem hnH) hn₂' a₁ ha₁T
    have hR₂ : (π * a₁ * π⁻¹)⁻¹ * (π * a₂ * π⁻¹) ∈ L := by
      rw [show (π * a₁ * π⁻¹)⁻¹ * (π * a₂ * π⁻¹) = π * (a₁⁻¹ * a₂) * π⁻¹ by group]
      exact hK4 _ (mem_inf.mpr ⟨mul_mem (inv_mem ha₁T) ha₂T, hR₁⟩)
    set a₃ := π * a₂ * π⁻¹ with ha₃
    have ha₃T : a₃ ∈ T := hπ₁ a₂ ha₂T
    have hR₃ : a₃⁻¹ * (n * a₃ * n⁻¹) ∈ L := hK1 n hnH hn₁' a₃ ha₃T
    have hR₄ : t⁻¹ * (w * t * w⁻¹) ∈ L := hK1 w hwH hwT t ht
    have hwt : w * t * w⁻¹ = n * a₃ * n⁻¹ := by
      rw [hw, ha₃, ha₂, ha₁]
      group
    rw [hwt] at hR₄
    have h1 := mul_mem (mul_mem hR₄ (inv_mem hR₃)) (inv_mem hR₂)
    rwa [show t⁻¹ * (n * a₃ * n⁻¹) * (a₃⁻¹ * (n * a₃ * n⁻¹))⁻¹ *
      ((π * a₁ * π⁻¹)⁻¹ * a₃)⁻¹ = t⁻¹ * (π * a₁ * π⁻¹) by group,
      show π * a₁ * π⁻¹ = π * π * t * (π * π)⁻¹ by rw [ha₁]; group] at h1

end Certified

end Step6

end CFSG.ComponentClassification.HarrisLit.T1
