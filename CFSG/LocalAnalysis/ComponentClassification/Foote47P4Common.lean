module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Ft
import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools2

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

omit [Finite G] in
theorem T_le_S (d : P4Data L M T S P t z w) : T ≤ S := d.c.hT ▸ inf_le_left

omit [Finite G] in
theorem P_le_S (d : P4Data L M T S P t z w) : P ≤ S := d.c.hP ▸ inf_le_left

omit [Finite G] in
theorem z_comm (d : P4Data L M T S P t z w) {s : G} (hs : s ∈ S) : s * z = z * s :=
  mem_centralizer_singleton_iff.mp (d.c.hSz.le hs)

omit [Finite G] in
theorem t_comm (d : P4Data L M T S P t z w) {s : G} (hs : s ∈ P) : s * t = t * s := by
  rw [d.c.hP] at hs
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2

omit [Finite G] in
theorem t_mem_P (d : P4Data L M T S P t z w) : t ∈ P := by
  rw [d.c.hP]
  exact mem_inf.mpr ⟨d.T_le_S d.c.htT, mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G] in
theorem z_mem_P (d : P4Data L M T S P t z w) : z ∈ P := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  rw [d.c.hP]
  exact mem_inf.mpr ⟨d.T_le_S hd.hzT, mem_centralizer_singleton_iff.mpr (hd.hzc t d.c.htT).symm⟩

omit [Finite G] in
theorem w_mem_P (d : P4Data L M T S P t z w) : w ∈ P := by
  rw [d.c.hP]
  exact mem_inf.mpr ⟨d.hwS, mem_centralizer_singleton_iff.mpr (d.hwc t (d.T_le_S d.c.htT)).symm⟩

omit [Finite G] in
theorem isConj_t_tz (d : P4Data L M T S P t z w) : IsConj t (t * z) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  obtain ⟨n, -, -, hn⟩ := hd.hn
  exact isConj_iff.mpr ⟨n, hn⟩

omit [Finite G] in
theorem isConj_tw_tzw (d : P4Data L M T S P t z w) : IsConj (t * w) (t * z * w) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  obtain ⟨n, hnT, -, hn⟩ := hd.hn
  have hnw : n * w * n⁻¹ = w := by
    rw [d.hwc n (d.T_le_S hnT), mul_inv_cancel_right]
  refine isConj_iff.mpr ⟨n, ?_⟩
  calc n * (t * w) * n⁻¹ = (n * t * n⁻¹) * (n * w * n⁻¹) := by group
    _ = t * z * w := by rw [hn, hnw]

omit [Finite G] in
theorem not_isConj_t (d : P4Data L M T S P t z w) :
    ¬ IsConj t z ∧ ¬ IsConj t w ∧ ¬ IsConj t (z * w) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  refine ⟨d.ht2c z (d.T_le_S hd.hzT) fun s hs => d.z_comm hs, d.ht2c w d.hwS d.hwc,
    d.ht2c (z * w) (mul_mem (d.T_le_S hd.hzT) d.hwS) fun s hs => ?_⟩
  rw [← mul_assoc, d.z_comm hs, mul_assoc, d.hwc s hs, mul_assoc]

theorem P_inf_coreActionKernel (d : P4Data L M T S P t z w) :
    P ⊓ coreActionKernel (footeF L z) = T ⊓ centralizer ({t} : Set G) := by
  refine (d.c.hQX.eq_of_le (le_inf d.Q_le_P (le_trans ?_ (d.c.hQX.le.trans inf_le_right)))
    (fun x hx => ?_) (d.c.hPsyl.isPGroup.to_le inf_le_left))
  · exact le_rfl
  · obtain ⟨hxP, hxK⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨d.c.hSz.le (d.P_le_S hxP), d.c.hPsyl.le hxP⟩, hxK⟩

end P4Data

structure Valid (P : Subgroup G) (t z w g : G) : Prop where
  hx : g⁻¹ * t * g ∈ P
  hxt : g⁻¹ * t * g ≠ t
  hxtz : g⁻¹ * t * g ≠ t * z
  hz : g * z * g⁻¹ ∈ P
  ht : g * t * g⁻¹ ∈ P
  hw : g * w * g⁻¹ ∈ P

theorem exists_valid_of_isConj_mem {P : Subgroup G} {t z w : G}
    (hP : IsSylowOf 2 P (centralizer ({t} : Set G)))
    (htP : t ∈ P) (hzP : z ∈ P) (hwP : w ∈ P)
    (hzC : ∀ x ∈ P, x * z = z * x) (hwC : ∀ x ∈ P, x * w = w * x)
    (hx : ∃ x ∈ P, IsConj t x ∧ x ≠ t ∧ x ≠ t * z) :
    ∃ g : G, Valid P t z w g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxP, htx, hxt, hxtz⟩ := hx
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp htx
  set V := zpowers z ⊔ zpowers t ⊔ zpowers w ⊔ zpowers x with hV
  have hVP : V ≤ P := sup_le (sup_le (sup_le (zpowers_le.mpr hzP)
    (zpowers_le.mpr htP)) (zpowers_le.mpr hwP)) (zpowers_le.mpr hxP)
  have hVx : V ≤ centralizer ({x} : Set G) := by
    have hzx : z ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hzC x hxP).symm
    have htx' : t ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hP.le hxP)).symm
    have hwx : w ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hwC x hxP).symm
    exact sup_le (sup_le (sup_le (zpowers_le.mpr hzx) (zpowers_le.mpr htx'))
      (zpowers_le.mpr hwx)) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hPx : IsSylowOf 2 (conjugate P g₀⁻¹) (centralizer ({x} : Set G)) := by
    have h1 := isSylowOf_conjugate hP g₀⁻¹
    have h2 : conjugate (centralizer ({t} : Set G)) g₀⁻¹ = centralizer ({x} : Set G) := by
      ext y
      rw [mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hg₀]
      constructor
      · intro h3
        calc y * (g₀ * t * g₀⁻¹) = g₀ * ((g₀⁻¹ * y * g₀⁻¹⁻¹) * t) * g₀⁻¹ := by group
          _ = g₀ * (t * (g₀⁻¹ * y * g₀⁻¹⁻¹)) * g₀⁻¹ := by rw [h3]
          _ = g₀ * t * g₀⁻¹ * y := by group
      · intro h3
        calc g₀⁻¹ * y * g₀⁻¹⁻¹ * t = g₀⁻¹ * (y * (g₀ * t * g₀⁻¹)) * g₀ := by group
          _ = g₀⁻¹ * (g₀ * t * g₀⁻¹ * y) * g₀ := by rw [h3]
          _ = t * (g₀⁻¹ * y * g₀⁻¹⁻¹) := by group
    rwa [h2] at h1
  obtain ⟨k, hkx, hk⟩ := exists_conj_le_of_isSylowOf hPx hVx (hP.isPGroup.to_le hVP)
  refine ⟨g₀⁻¹ * k⁻¹, ?_⟩
  have hkxc : k * x = x * k := mem_centralizer_singleton_iff.mp hkx
  have hgt : (g₀⁻¹ * k⁻¹)⁻¹ * t * (g₀⁻¹ * k⁻¹) = x := by
    calc (g₀⁻¹ * k⁻¹)⁻¹ * t * (g₀⁻¹ * k⁻¹) = k * (g₀ * t * g₀⁻¹) * k⁻¹ := by group
      _ = x := by rw [hg₀, hkxc, mul_inv_cancel_right]
  have hgV : ∀ v ∈ V, (g₀⁻¹ * k⁻¹) * v * (g₀⁻¹ * k⁻¹)⁻¹ ∈ P := by
    intro v hv
    have h1 := hk v hv
    rw [mem_conjugate_iff, inv_inv] at h1
    convert h1 using 1
    group
  refine ⟨hgt ▸ hxP, hgt ▸ hxt, hgt ▸ hxtz, hgV z ?_, hgV t ?_, hgV w ?_⟩
  · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers z)))
  · exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers t)))
  · exact mem_sup_left (mem_sup_right (mem_zpowers w))

theorem exists_valid_of_isSimpleGroup [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {P : Subgroup G} {t z w : G}
    (ht : orderOf t = 2)
    (hP : IsSylowOf 2 P (centralizer ({t} : Set G)))
    (htP : t ∈ P) (hzP : z ∈ P) (hwP : w ∈ P)
    (hzC : ∀ x ∈ P, x * z = z * x) (hwC : ∀ x ∈ P, x * w = w * x) :
    ∃ g : G, Valid P t z w g := by
  obtain ⟨x, hxP, htx, hxt, hxtz⟩ := Foote5.exists_conj_mem_ne hnab ht hP (t * z)
  exact exists_valid_of_isConj_mem hP htP hzP hwP hzC hwC ⟨x, hxP, htx, hxt, hxtz⟩

omit [Finite G] in
theorem exists_noncommuting_of_isConj_mul {t z : G}
    (h : IsConj t (t * z)) (hz1 : z ≠ 1) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  refine ⟨g, t, fun hgt => hz1 (mul_left_cancel (a := t) ?_)⟩
  rw [mul_one, ← hg, hgt, mul_inv_cancel_right]

omit [Finite G] in
theorem TwoData.conj_inv_of_conj {T : Subgroup G} {t z : G} {Q₀ : Subgroup G}
    (d : TwoData T t z Q₀) {n : G} (hnT : n ∈ T) (hn : n * t * n⁻¹ = t * z) :
    n⁻¹ * t * n = t * z := by
  have hnz : n⁻¹ * z * n = z := by rw [mul_assoc, ← d.hzc n hnT, inv_mul_cancel_left]
  have hz2 : z * z = 1 := by rw [← sq, ← d.hz]; exact pow_orderOf_eq_one z
  have h2 : n⁻¹ * (t * z) * n = t := by rw [← hn]; group
  have h3 : (n⁻¹ * t * n) * z = t := by
    calc (n⁻¹ * t * n) * z = (n⁻¹ * t * n) * (n⁻¹ * z * n) := by rw [hnz]
      _ = n⁻¹ * (t * z) * n := by group
      _ = t := h2
  calc n⁻¹ * t * n = (n⁻¹ * t * n) * z * z := by rw [mul_assoc (n⁻¹ * t * n) z z, hz2, mul_one]
    _ = t * z := by rw [h3]

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

theorem exists_valid (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    ∃ g : G, Valid P t z w g := by
  haveI : IsSimpleGroup G := h.simple
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have hz1 : z ≠ 1 := by
    intro hz1
    have hzo := hd.hz
    rw [hz1, orderOf_one] at hzo
    omega
  exact exists_valid_of_isSimpleGroup
    (exists_noncommuting_of_isConj_mul d.isConj_t_tz hz1)
    d.c.hv.ht d.c.hPsyl d.t_mem_P d.z_mem_P d.w_mem_P
    (fun x hx => d.z_comm (d.P_le_S hx)) (fun x hx => d.hwc x (d.P_le_S hx))

omit [Finite G] in
theorem Valid.not_mem_centralizer_of_twoData {T P F : Subgroup G} {t z w g : G}
    {Q₀ : Subgroup G} (d : TwoData T t z Q₀) (ht : orderOf t = 2) (htT : t ∈ T)
    (hTK : T ≤ coreActionKernel F)
    (hPK : P ⊓ coreActionKernel F = T ⊓ centralizer ({t} : Set G))
    (hCN : centralizer ({z} : Set G) ≤ normalizer (F : Set G))
    (htz : ¬ IsConj t z) (hg : Valid P t z w g) :
    g ∉ centralizer ({z} : Set G) := by
  intro hgz
  have htt : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have htK : t ∈ coreActionKernel F := hTK htT
  have hgK : g⁻¹ ∈ normalizer (F : Set G) := hCN (inv_mem hgz)
  have hxK : g⁻¹ * t * g ∈ coreActionKernel F := by
    have h1 := FooteLit.conj_mem_coreActionKernel hgK htK
    rwa [inv_inv] at h1
  have hxQ : g⁻¹ * t * g ∈ T ⊓ centralizer ({t} : Set G) := by
    rw [← hPK]
    exact mem_inf.mpr ⟨hg.hx, hxK⟩
  have hxo : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, ht]
  rcases d.inv_cases htt hxQ hxo with h1 | h1 | h1
  · exact htz (h1 ▸ isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)
  · exact hg.hxt h1
  · exact hg.hxtz h1

theorem Valid.not_mem_centralizer (h : FooteSec4 G L) (d : P4Data L M T S P t z w) {g : G}
    (hg : Valid P t z w g) : g ∉ centralizer ({z} : Set G) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have dz := zData_of h d.c.hv.hM d.c.hTsyl hd.hz hd.hzT hd.hzc
  exact Valid.not_mem_centralizer_of_twoData (F := footeF L z) hd d.c.hv.ht d.c.htT
    dz.hTKle d.P_inf_coreActionKernel (dz.centralizer_le_normalizer h) (d.not_isConj_t).1 hg

omit [Finite G] in
theorem conj_inv_of_conj (d : P4Data L M T S P t z w) {n : G} (hnT : n ∈ T)
    (hn : n * t * n⁻¹ = t * z) : n⁻¹ * t * n = t * z := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  exact hd.conj_inv_of_conj hnT hn

omit [Finite G] in
theorem conj_mem_P_of_conj (d : P4Data L M T S P t z w) {n : G} (hnT : n ∈ T)
    (hn : n * t * n⁻¹ = t * z) {y : G} (hy : y ∈ P) : n * y * n⁻¹ ∈ P := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have hnS := d.T_le_S hnT
  have hn' := d.conj_inv_of_conj hnT hn
  have hyt := d.t_comm hy
  have hyz := d.z_comm (d.P_le_S hy)
  rw [d.c.hP]
  refine mem_inf.mpr ⟨mul_mem (mul_mem hnS (d.P_le_S hy)) (inv_mem hnS), ?_⟩
  rw [mem_centralizer_singleton_iff]
  have h1 : n⁻¹ * t * n * y = y * (n⁻¹ * t * n) := by
    rw [hn']
    calc t * z * y = t * (z * y) := mul_assoc _ _ _
      _ = t * (y * z) := by rw [← hyz]
      _ = (t * y) * z := (mul_assoc _ _ _).symm
      _ = (y * t) * z := by rw [← hyt]
      _ = y * (t * z) := mul_assoc _ _ _
  calc n * y * n⁻¹ * t = n * (y * (n⁻¹ * t * n)) * n⁻¹ := by group
    _ = n * (n⁻¹ * t * n * y) * n⁻¹ := by rw [h1]
    _ = t * (n * y * n⁻¹) := by group

omit [Finite G] in
theorem Valid.tstar_ne_of_twoData {T P F : Subgroup G} {t z w g : G} {Q₀ : Subgroup G}
    (d : TwoData T t z Q₀) (ht : orderOf t = 2) (htT : t ∈ T) (htP : t ∈ P)
    (hQK : T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel F)
    (hPK : P ⊓ coreActionKernel F = T ⊓ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (F : Set G))
    (htz : ¬ IsConj t z) (hg : Valid P t z w g) :
    g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ ≠ t * z := by
  have htt : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  constructor
  · intro h1
    apply hg.hxt
    calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h1]
      _ = t := by group
  · intro h1
    obtain ⟨n, hnT, -, hn⟩ := d.hn
    have htzConj : IsConj t (t * z) := isConj_iff.mpr ⟨n, hn⟩
    have hn' := d.conj_inv_of_conj hnT hn
    have hnz : n⁻¹ * z * n = z := by rw [mul_assoc, ← d.hzc n hnT, inv_mul_cancel_left]
    have hz2 : z * z = 1 := by rw [← sq, ← d.hz]; exact pow_orderOf_eq_one z
    set c := n⁻¹ * g with hc
    have hct : c * t = t * c := by
      have h3 : c * t * c⁻¹ = t := by
        calc c * t * c⁻¹ = n⁻¹ * (g * t * g⁻¹) * n := by rw [hc]; group
          _ = (n⁻¹ * t * n) * (n⁻¹ * z * n) := by rw [h1]; group
          _ = t := by rw [hn', hnz, mul_assoc, hz2, mul_one]
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [h3]
    have hx : g⁻¹ * t * g = t * (c⁻¹ * z * c) := by
      have hg' : g = n * c := by rw [hc]; group
      rw [hg']
      calc (n * c)⁻¹ * t * (n * c) = c⁻¹ * (n⁻¹ * t * n) * c := by group
        _ = (c⁻¹ * t * c) * (c⁻¹ * z * c) := by rw [hn']; group
        _ = t * (c⁻¹ * z * c) := by rw [mul_assoc c⁻¹ t c, ← hct, inv_mul_cancel_left]
    have hzc : c⁻¹ * z * c ∈ P := by
      have h4 : c⁻¹ * z * c = t * (g⁻¹ * t * g) := by rw [hx, ← mul_assoc t t, htt, one_mul]
      rw [h4]
      exact mul_mem htP hg.hx
    have hctN : c⁻¹ ∈ normalizer (F : Set G) :=
      hCN (inv_mem (mem_centralizer_singleton_iff.mpr hct))
    have hzF : c⁻¹ * z * c ∈ coreActionKernel F := by
      have h5 := FooteLit.conj_mem_coreActionKernel hctN
        (hQK (mem_inf.mpr ⟨d.hzT, mem_centralizer_singleton_iff.mpr (d.hzc t htT).symm⟩))
      rwa [inv_inv] at h5
    have hzQ : c⁻¹ * z * c ∈ T ⊓ centralizer ({t} : Set G) := by
      rw [← hPK]
      exact mem_inf.mpr ⟨hzc, hzF⟩
    have hzo : orderOf (c⁻¹ * z * c) = 2 := by
      rw [show c⁻¹ * z * c = MulAut.conj c⁻¹ z by rw [MulAut.conj_apply, inv_inv],
        MulEquiv.orderOf_eq, d.hz]
    have hzz : IsConj z (c⁻¹ * z * c) := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩
    rcases d.inv_cases htt hzQ hzo with h6 | h6 | h6
    · apply hg.hxtz
      rw [hx, h6]
    · exact htz (h6 ▸ hzz).symm
    · exact htz (htzConj.trans (h6 ▸ hzz).symm)

theorem Valid.tstar_ne (h : FooteSec4 G L) (d : P4Data L M T S P t z w) {g : G}
    (hg : Valid P t z w g) : g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ ≠ t * z := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  exact Valid.tstar_ne_of_twoData (F := footeF L t) hd d.c.hv.ht d.c.htT d.t_mem_P
    d.Q_le d.c.hQP (d.centralizer_le_normalizer_t h) (d.not_isConj_t).1 hg

omit [Finite G] in
theorem Valid.mul_inv (d : P4Data L M T S P t z w) {g n : G} (hg : Valid P t z w g)
    (hnT : n ∈ T) (hn : n * t * n⁻¹ = t * z) :
    Valid P t z w (g * n⁻¹) ∧
      (g * n⁻¹) * t * (g * n⁻¹)⁻¹ = (g * t * g⁻¹) * (g * z * g⁻¹) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have hnS := d.T_le_S hnT
  have hn' := d.conj_inv_of_conj hnT hn
  have hnz : n⁻¹ * z * n = z := by rw [mul_assoc, ← hd.hzc n hnT, inv_mul_cancel_left]
  have hnw : n⁻¹ * w * n = w := by rw [mul_assoc, ← d.hwc n hnS, inv_mul_cancel_left]
  have hz2 : z * z = 1 := by rw [← sq, ← hd.hz]; exact pow_orderOf_eq_one z
  have hx : (g * n⁻¹)⁻¹ * t * (g * n⁻¹) = n * (g⁻¹ * t * g) * n⁻¹ := by group
  have hgt : (g * n⁻¹) * t * (g * n⁻¹)⁻¹ = (g * t * g⁻¹) * (g * z * g⁻¹) := by
    calc (g * n⁻¹) * t * (g * n⁻¹)⁻¹ = g * (n⁻¹ * t * n) * g⁻¹ := by group
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by rw [hn']; group
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hgt⟩
  · rw [hx]
    exact d.conj_mem_P_of_conj hnT hn hg.hx
  · rw [hx]
    intro h1
    apply hg.hxtz
    calc g⁻¹ * t * g = n⁻¹ * (n * (g⁻¹ * t * g) * n⁻¹) * n := by group
      _ = t * z := by rw [h1, hn']
  · rw [hx]
    intro h1
    apply hg.hxt
    calc g⁻¹ * t * g = n⁻¹ * (n * (g⁻¹ * t * g) * n⁻¹) * n := by group
      _ = (n⁻¹ * t * n) * (n⁻¹ * z * n) := by rw [h1]; group
      _ = t := by rw [hn', hnz, mul_assoc, hz2, mul_one]
  · rw [show (g * n⁻¹) * z * (g * n⁻¹)⁻¹ = g * (n⁻¹ * z * n) * g⁻¹ by group, hnz]
    exact hg.hz
  · rw [hgt]
    exact mul_mem hg.ht hg.hz
  · rw [show (g * n⁻¹) * w * (g * n⁻¹)⁻¹ = g * (n⁻¹ * w * n) * g⁻¹ by group, hnw]
    exact hg.hw

end P4Data

end CFSG.ComponentClassification.Foote47
