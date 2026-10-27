module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Abs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement Pointwise

section Alg

variable {K : Type} [Group K]

theorem zpow_cube_eq_one {c : K} (hc : c ^ 3 = 1) (k : ℤ) : (c ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

theorem eq_one_of_mul_self_of_pow_three {u : K} (h2 : u * u = 1) (h3 : u ^ 3 = 1) : u = 1 := by
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem abs_c {a c : K} (ha : a ^ 3 = 1) (hc : c ^ 3 = 1) (hac : a * c = c * a) (k : ℤ)
    (h : (a * c ^ k) * (a * c ^ k) = 1) : a * c ^ k = 1 := by
  have hcomm : Commute a (c ^ k) := (show Commute a c from hac).zpow_right k
  have h3 : (a * c ^ k) ^ 3 = 1 := by
    rw [hcomm.mul_pow, ha, zpow_cube_eq_one hc, one_mul]
  exact eq_one_of_mul_self_of_pow_three h h3

theorem abs_cx {a c x : K} (hx2 : x * x = 1) (hxc : x * c * x = c⁻¹) (ha : a ^ 3 = 1)
    (hc : c ^ 3 = 1) (hax : a * x = x * a) (hac : a * c = c * a) (k : ℤ)
    (h2 : (a * (c ^ k * x)) * (a * (c ^ k * x)) = 1) (h3 : ⁅a * (c ^ k * x), c⁆ = 1) :
    c = 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hcx : x * c * x⁻¹ = c⁻¹ := by rw [hxi]; exact hxc
  have hxk : x * c ^ k * x = c ^ (-k) := by
    have h := map_zpow (MulAut.conj x) c k
    simp only [MulAut.conj_apply] at h
    rw [hcx, inv_zpow', zpow_neg] at h
    rw [← hxi] at h ⊢
    simpa [hxi] using h
  have hack : Commute a (c ^ k) := (show Commute a c from hac).zpow_right k
  have hcomm : Commute a (c ^ k * x) := hack.mul_right (show Commute a x from hax)
  have hu2 : (c ^ k * x) * (c ^ k * x) = 1 := by
    calc (c ^ k * x) * (c ^ k * x) = c ^ k * (x * c ^ k * x) := by group
      _ = 1 := by rw [hxk]; group
  have haa : a * a = 1 := by
    have : (a * (c ^ k * x)) * (a * (c ^ k * x)) = a * a * ((c ^ k * x) * (c ^ k * x)) := by
      calc (a * (c ^ k * x)) * (a * (c ^ k * x)) = a * ((c ^ k * x) * a) * (c ^ k * x) := by group
        _ = a * (a * (c ^ k * x)) * (c ^ k * x) := by rw [hcomm.eq]
        _ = _ := by group
    rw [this, hu2, mul_one] at h2
    exact h2
  have ha1 : a = 1 := eq_one_of_mul_self_of_pow_three haa ha
  subst ha1
  have h3' : (c ^ k * x) * c * (c ^ k * x)⁻¹ * c⁻¹ = 1 := by simpa [commutatorElement_def] using h3
  have h4 : c ^ (-2 : ℤ) = 1 := by
    calc c ^ (-2 : ℤ) = (c ^ k * x) * c * (c ^ k * x)⁻¹ * c⁻¹ := by
          have : (c ^ k * x) * c * (c ^ k * x)⁻¹ * c⁻¹ =
              c ^ k * (x * c * x⁻¹) * (c ^ k)⁻¹ * c⁻¹ := by group
          rw [this, hcx]; group
      _ = 1 := h3'
  have hcc : c * c = 1 := by
    have h5 : c ^ (-2 : ℤ) = (c * c)⁻¹ := by group
    rw [h5] at h4
    exact inv_eq_one.mp h4
  exact eq_one_of_mul_self_of_pow_three hcc hc

end Alg

section One

variable {H : Type} [Group H]

theorem conj_c_eq_inv' {x y : H} (hx2 : x * x = 1) (hy2 : y * y = 1) :
    x * (x * y) * x = (x * y)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have := conj_c_eq_inv hx2 hy2
  rwa [hxi] at this

theorem commute_of_mem_closure_pair {t x y : H} (hx : t * x = x * t) (hy : t * y = y * t) {w : H}
    (hw : w ∈ Subgroup.closure {x, y}) : t * w = w * t := by
  have hle : Subgroup.closure ({x, y} : Set H) ≤ Subgroup.centralizer ({t} : Set H) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff] at hz; subst hz; exact hy
  exact Subgroup.mem_centralizer_iff.mp (hle hw) t (Set.mem_singleton t)

theorem mem_normalizer_closure_pair {t x y : H} (hx : t * x = x * t) (hy : t * y = y * t) :
    t ∈ Subgroup.normalizer ((Subgroup.closure {x, y} : Subgroup H) : Set H) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ?_
  have e1 : ∀ w ∈ Subgroup.closure ({x, y} : Set H), t * w * t⁻¹ = w := fun w hw => by
    rw [commute_of_mem_closure_pair hx hy hw, mul_inv_cancel_right]
  constructor
  · intro hh; rw [e1 h hh]; exact hh
  · intro hh
    have e2 := e1 _ hh
    have e3 : t * h * t⁻¹ = h := by
      apply (MulAut.conj t).injective
      simpa [MulAut.conj_apply] using e2
    rwa [e3] at hh

theorem hasInvolMod_of_commute {t x y : H} (hx : t * x = x * t) (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1) : HasInvolMod H t := by
  refine ⟨x, not_mem_pCore_two_of_inverts hx2 (conj_c_eq_inv' hx2 hy2) hxy3 hxy1,
    by rw [hx2]; exact one_mem _, ?_⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have : ⁅x, t⁆ = 1 := by
    rw [commutatorElement_def, show x * t = t * x from hx.symm]
    group
  rw [this]; exact one_mem _

theorem not_hasInvolMod_c_one {T : Subgroup H} {x y : H}
    (hgen : (⊤ : Subgroup H) ≤ CFSG.pCore 2 H ⊔ (T ⊔ Subgroup.closure {x, y}))
    (hTx : ∀ t ∈ T, t * x = x * t) (hTy : ∀ t ∈ T, t * y = y * t) (hT3 : ∀ t ∈ T, t ^ 3 = 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1) :
    ¬ HasInvolMod H (x * y) := by
  rintro ⟨u, huO, hu2, hcomm⟩
  haveI : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  set O : Subgroup H := CFSG.pCore 2 H with hO
  set cl : Subgroup H := Subgroup.closure {x, y} with hcl
  have hTN : T ≤ Subgroup.normalizer (cl : Set H) := fun t ht =>
    mem_normalizer_closure_pair (hTx t ht) (hTy t ht)
  have hu : u ∈ (↑(O ⊔ (T ⊔ cl)) : Set H) := hgen (Subgroup.mem_top u)
  rw [Subgroup.normal_mul, Subgroup.coe_mul_of_left_le_normalizer_right T cl hTN] at hu
  obtain ⟨r, hr, v, hv, rfl⟩ := hu
  obtain ⟨t, ht, w, hw, rfl⟩ := hv
  obtain ⟨k, hk⟩ := mem_closure_pair_cases hx2 hy2 hw
  set q : H →* H ⧸ O := QuotientGroup.mk' O with hq
  have hq1 : ∀ g, q g = 1 ↔ g ∈ O := fun g => QuotientGroup.eq_one_iff g
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxc : q x * q (x * y) * q x = (q (x * y))⁻¹ := by
    rw [← map_mul, ← map_mul, ← map_inv, conj_c_eq_inv' hx2 hy2]
  have hqx2 : q x * q x = 1 := by rw [← map_mul, hx2, map_one]
  have hqc3 : (q (x * y)) ^ 3 = 1 := by rw [← map_pow, hxy3, map_one]
  have hqt3 : (q t) ^ 3 = 1 := by rw [← map_pow, hT3 t ht, map_one]
  have hqtx : q t * q x = q x * q t := by rw [← map_mul, ← map_mul, hTx t ht]
  have hqty : q t * q y = q y * q t := by rw [← map_mul, ← map_mul, hTy t ht]
  have hqtc : q t * q (x * y) = q (x * y) * q t := by
    rw [map_mul, ← mul_assoc, hqtx, mul_assoc, hqty, ← mul_assoc]
  have hqr : q r = 1 := (hq1 r).2 hr
  have hqu2 : q (r * (t * w)) * q (r * (t * w)) = 1 := by
    rw [← map_mul]; exact (hq1 _).2 hu2
  have hqcomm : ⁅q (r * (t * w)), q (x * y)⁆ = 1 := by
    rw [← map_commutatorElement]; exact (hq1 _).2 hcomm
  have hqu : q (r * (t * w)) = q t * q w := by rw [map_mul, hqr, one_mul, map_mul]
  rw [hqu] at hqu2 hqcomm
  have hc1 : q (x * y) ≠ 1 := fun h =>
    not_mem_pCore_two_of_pow_three hxy3 hxy1 ((hq1 _).1 h)
  rcases hk with hw' | hw'
  · rw [hw', map_zpow] at hqu2
    have := abs_c hqt3 hqc3 hqtc k hqu2
    apply huO
    refine (hq1 _).1 ?_
    rw [hqu, hw', map_zpow]; exact this
  · rw [hw', map_mul, map_zpow] at hqu2 hqcomm
    exact hc1 (abs_cx hqx2 hxc hqt3 hqc3 hqtx hqtc k hqu2 hqcomm)

end One

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
