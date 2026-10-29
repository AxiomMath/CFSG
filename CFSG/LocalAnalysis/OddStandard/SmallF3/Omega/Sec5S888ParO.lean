module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParC

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma s888_mem_conjugate_iff {Y : Type*} [Group Y] {A : Subgroup Y} {g x : Y} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma s888_conj_mem_iff {Y : Type*} [Group Y] {A : Subgroup Y} {g x : Y}
    (h : CFSG.conjugate A g = A) : g⁻¹ * x * g ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    rw [← h] at hx
    have h' := s888_mem_conjugate_iff.mp hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h'
  · intro hx
    rw [← h]
    exact s888_mem_conjugate_iff.mpr (by
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group])

private lemma s888_mem_twoCoreIn_iff [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {u : G} :
    u ∈ twoCoreIn (K i) ↔ u ∈ K i ∧ u ^ 4 = 1 := by
  rw [twoCoreIn_eq_inf hq i]
  exact mem_inf_K_iff hq i

private lemma s888_not_parNt_apply {g : G} {i : Fin 4} (h : ¬ ParNt K z g i) {q : G}
    (hq : q ∈ twoCoreIn (K i)) :
    g⁻¹ * q * g = q ∨ g⁻¹ * q * g = q * z := by
  by_contra hc
  push Not at hc
  exact h ⟨q, hq, hc.1, hc.2⟩

private lemma s888_inv_conj_z {g : G} (hgz : g * z = z * g) : g⁻¹ * z * g = z := by
  calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
    _ = g⁻¹ * (g * z) := by rw [← hgz]
    _ = z := by group

private lemma s888_conj_inj {k x y : G} (h : k * x * k⁻¹ = k * y * k⁻¹) : x = y := by
  have h' : k * x = k * y := by
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = (k * y * k⁻¹) * k := by rw [h]
      _ = k * y := by group
  exact mul_left_cancel h'

private lemma s888_cancel_conj {k a b : G} (hzk : z * k = k * z) (hz2 : z * z = 1)
    (h : k * a * k⁻¹ = k * b * k⁻¹ ∨ k * a * k⁻¹ = (k * b * k⁻¹) * z) :
    a = b ∨ a = b * z := by
  rcases h with h | h
  · exact Or.inl (s888_conj_inj h)
  · right
    have hzkinv : z * k⁻¹ = k⁻¹ * z := by
      have hc : Commute z k := (commute_iff_eq z k).mpr hzk
      exact hc.inv_right.eq
    have hkb : (k * b * k⁻¹) * z = k * (b * z) * k⁻¹ := by
      calc (k * b * k⁻¹) * z = k * b * (k⁻¹ * z) := by group
        _ = k * b * (z * k⁻¹) := by rw [← hzkinv]
        _ = k * (b * z) * k⁻¹ := by group
    exact s888_conj_inj (h.trans hkb)

private lemma s888_commute_z_mul {a b : G} (ha : z * a = a * z) (hb : z * b = b * z) :
    z * (a * b) = (a * b) * z := by
  calc z * (a * b) = (z * a) * b := by rw [mul_assoc]
    _ = (a * z) * b := by rw [ha]
    _ = a * (z * b) := by rw [mul_assoc]
    _ = a * (b * z) := by rw [hb]
    _ = (a * b) * z := by rw [mul_assoc]

private lemma s888_commute_z_inv {a : G} (ha : z * a = a * z) : z * a⁻¹ = a⁻¹ * z := by
  have hc : Commute z a := (commute_iff_eq z a).mpr ha
  exact hc.inv_right.eq

private lemma s888_conj_mul_z_cancel {u X : G} (hz2 : z * z = 1) (hzu : z * u = u * z) :
    u * (X * z) * u⁻¹ * z = u * X * u⁻¹ := by
  have hzu' : z * u⁻¹ = u⁻¹ * z := s888_commute_z_inv hzu
  calc u * (X * z) * u⁻¹ * z = u * X * (z * u⁻¹) * z := by group
    _ = u * X * (u⁻¹ * z) * z := by rw [hzu']
    _ = u * X * u⁻¹ * (z * z) := by group
    _ = u * X * u⁻¹ := by rw [hz2, mul_one]

private lemma s888_not_nt_not_out [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {g : G}
    (hgz : g * z = z * g) (hgK : CFSG.conjugate (K i) g = K i)
    (hNT : ¬ ParNt K z g i) :
    ∀ k ∈ K i, g⁻¹ * k * g * k⁻¹ ∈ twoCoreIn (K i) := by
  intro k hk
  set k' : G := g⁻¹ * k * g with hk'_def
  set y : G := k⁻¹ * k' with hy_def
  have hk'K : k' ∈ K i := by rw [hk'_def]; exact (s888_conj_mem_iff hgK).mpr hk
  have hyK : y ∈ K i := by rw [hy_def]; exact (K i).mul_mem ((K i).inv_mem hk) hk'K
  have hky' : g⁻¹ * k * g = k * y := by rw [← hk'_def, hy_def]; group
  have hzk : z * k = k * z := hq.z_comm hk
  have hz2 : z * z = 1 := hq.z_sq
  have hy_mod : ∀ q ∈ K i, q ^ 4 = 1 → y * q * y⁻¹ = q ∨ y * q * y⁻¹ = q * z := by
    intro q hqK hq4
    have hqmem : q ∈ twoCoreIn (K i) := (s888_mem_twoCoreIn_iff hq i).mpr ⟨hqK, hq4⟩
    have hq1 : g⁻¹ * q * g = q ∨ g⁻¹ * q * g = q * z := s888_not_parNt_apply hNT hqmem
    have hkqK : k * q * k⁻¹ ∈ K i :=
      (K i).mul_mem ((K i).mul_mem hk hqK) ((K i).inv_mem hk)
    have hkq4 : (k * q * k⁻¹) ^ 4 = 1 := by rw [conj_pow, hq4]; simp
    have hq2 : g⁻¹ * (k * q * k⁻¹) * g = k * q * k⁻¹ ∨
        g⁻¹ * (k * q * k⁻¹) * g = (k * q * k⁻¹) * z :=
      s888_not_parNt_apply hNT ((s888_mem_twoCoreIn_iff hq i).mpr ⟨hkqK, hkq4⟩)
    have hbase : g⁻¹ * (k * q * k⁻¹) * g =
        (g⁻¹ * k * g) * (g⁻¹ * q * g) * (g⁻¹ * k * g)⁻¹ := by group
    rcases hq1 with hq1 | hq1
    · have hL : g⁻¹ * (k * q * k⁻¹) * g = k * (y * q * y⁻¹) * k⁻¹ := by
        calc g⁻¹ * (k * q * k⁻¹) * g =
            (g⁻¹ * k * g) * (g⁻¹ * q * g) * (g⁻¹ * k * g)⁻¹ := hbase
          _ = (k * y) * q * (k * y)⁻¹ := by rw [hky', hq1]
          _ = k * (y * q * y⁻¹) * k⁻¹ := by group
      have hstep : k * (y * q * y⁻¹) * k⁻¹ = k * q * k⁻¹ ∨
          k * (y * q * y⁻¹) * k⁻¹ = (k * q * k⁻¹) * z := by
        rcases hq2 with h | h
        · exact Or.inl (by rw [← hL]; exact h)
        · exact Or.inr (by rw [← hL]; exact h)
      exact s888_cancel_conj hzk hz2 hstep
    · have hzky : z * (k * y) = (k * y) * z :=
        s888_commute_z_mul hzk (hq.z_comm hyK)
      have hzkyinv : z * (k * y)⁻¹ = (k * y)⁻¹ * z := s888_commute_z_inv hzky
      have hL : g⁻¹ * (k * q * k⁻¹) * g = (k * (y * q * y⁻¹) * k⁻¹) * z := by
        calc g⁻¹ * (k * q * k⁻¹) * g =
            (g⁻¹ * k * g) * (g⁻¹ * q * g) * (g⁻¹ * k * g)⁻¹ := hbase
          _ = (k * y) * (q * z) * (k * y)⁻¹ := by rw [hky', hq1]
          _ = ((k * y) * q * (k * y)⁻¹) * z := by
              calc (k * y) * (q * z) * (k * y)⁻¹ =
                  (k * y) * q * (z * (k * y)⁻¹) := by group
                _ = (k * y) * q * ((k * y)⁻¹ * z) := by rw [hzkyinv]
                _ = ((k * y) * q * (k * y)⁻¹) * z := by group
          _ = (k * (y * q * y⁻¹) * k⁻¹) * z := by group
      have hstep : k * (y * q * y⁻¹) * k⁻¹ = k * q * k⁻¹ ∨
          k * (y * q * y⁻¹) * k⁻¹ = (k * q * k⁻¹) * z := by
        rcases hq2 with h | h
        · right
          have h' : (k * (y * q * y⁻¹) * k⁻¹) * z = k * q * k⁻¹ := by
            rw [← hL]; exact h
          have := congrArg (· * z) h'
          simpa [mul_assoc, hz2] using this
        · left
          have h' : (k * (y * q * y⁻¹) * k⁻¹) * z = (k * q * k⁻¹) * z := by
            rw [← hL]; exact h
          exact mul_right_cancel h'
      exact s888_cancel_conj hzk hz2 hstep
  have hy4 : y ^ 4 = 1 := par_pow4_of_conj_mod hq i hyK hy_mod
  have hmem : g⁻¹ * k * g * k⁻¹ ∈ K i := by
    have e : g⁻¹ * k * g * k⁻¹ = k * y * k⁻¹ := by rw [hky']
    rw [e]
    exact (K i).mul_mem ((K i).mul_mem hk hyK) ((K i).inv_mem hk)
  have h4 : (g⁻¹ * k * g * k⁻¹) ^ 4 = 1 := by
    have e : g⁻¹ * k * g * k⁻¹ = k * y * k⁻¹ := by rw [hky']
    rw [e, conj_pow, hy4]
    simp
  exact (s888_mem_twoCoreIn_iff hq i).mpr ⟨hmem, h4⟩

private lemma s888_not_out_not_nt [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {g : G}
    (hgz : g * z = z * g) (hgK : CFSG.conjugate (K i) g = K i)
    (hg2 : ∀ q ∈ K i, q ^ 4 = 1 →
      (g * g)⁻¹ * q * (g * g) = q ∨ (g * g)⁻¹ * q * (g * g) = q * z)
    (hOUT : ∀ k ∈ K i, g⁻¹ * k * g * k⁻¹ ∈ twoCoreIn (K i)) :
    ¬ ParNt K z g i := by
  rintro ⟨q, hqmem, hqne1, hqne2⟩
  have hqK : q ∈ K i := ((s888_mem_twoCoreIn_iff hq i).mp hqmem).1
  have hq4 : q ^ 4 = 1 := ((s888_mem_twoCoreIn_iff hq i).mp hqmem).2
  have hgz' : g⁻¹ * z * g = z := s888_inv_conj_z hgz
  rcases hq.sq_of_pow4 hqK hq4 with hsq | hsq
  · rcases hq.eq_of_sq hqK hsq with h1 | hz
    · exact hqne1 (by rw [h1]; simp)
    · exact hqne1 (by rw [hz, hgz'])
  · have hbK : g⁻¹ * q * g ∈ K i := (s888_conj_mem_iff hgK).mpr hqK
    have hb2 : (g⁻¹ * q * g) * (g⁻¹ * q * g) = z := by
      calc (g⁻¹ * q * g) * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g := by group
        _ = g⁻¹ * z * g := by rw [hsq]
        _ = z := hgz'
    obtain ⟨k, hk, hkcase⟩ := par_exists_conj_class hq i hqK hbK hsq hb2
    have hb_rel : g⁻¹ * q * g = k * q * k⁻¹ ∨
        g⁻¹ * q * g = (k * q * k⁻¹) * z := by
      rcases hkcase with hka | hka
      · exact Or.inl hka.symm
      · right
        have h' : (k * q * k⁻¹) * z = g⁻¹ * q * g := by
          rw [hka, mul_assoc, hq.z_sq, mul_one]
        exact h'.symm
    have hkkK : k * k ∈ K i := (K i).mul_mem hk hk
    set u : G := g⁻¹ * k * g * k⁻¹ with hu_def
    have hu : u ∈ twoCoreIn (K i) := by rw [hu_def]; exact hOUT k hk
    have huK : u ∈ K i := ((s888_mem_twoCoreIn_iff hq i).mp hu).1
    have hu4 : u ^ 4 = 1 := ((s888_mem_twoCoreIn_iff hq i).mp hu).2
    have hgk : g⁻¹ * k * g = u * k := by rw [hu_def]; group
    set X : G := (k * k) * q * (k * k)⁻¹ with hX_def
    have hXK : X ∈ K i := by
      rw [hX_def]
      exact (K i).mul_mem ((K i).mul_mem hkkK hqK) ((K i).inv_mem hkkK)
    have hX4 : X ^ 4 = 1 := by rw [hX_def, conj_pow, hq4]; simp
    have hz2 : z * z = 1 := hq.z_sq
    have hgbg : g⁻¹ * (g⁻¹ * q * g) * g = (g * g)⁻¹ * q * (g * g) := by group
    have hgbg_in : g⁻¹ * (g⁻¹ * q * g) * g = q ∨
        g⁻¹ * (g⁻¹ * q * g) * g = q * z := by
      rw [hgbg]; exact hg2 q hqK hq4
    have huX : u * X * u⁻¹ = X ∨ u * X * u⁻¹ = X * z :=
      par_conj_q8_mod hq i huK hXK hu4 hX4
    have hgbg_X : g⁻¹ * (g⁻¹ * q * g) * g = u * X * u⁻¹ := by
      rcases hb_rel with hb | hb
      · have hkb : k * (g⁻¹ * q * g) * k⁻¹ = X := by
          rw [hb, hX_def]; group
        calc g⁻¹ * (g⁻¹ * q * g) * g =
            (g⁻¹ * k * g) * (g⁻¹ * q * g) * (g⁻¹ * k * g)⁻¹ := by
              conv_lhs => rw [hb]
              group
          _ = (u * k) * (g⁻¹ * q * g) * (u * k)⁻¹ := by rw [hgk]
          _ = u * (k * (g⁻¹ * q * g) * k⁻¹) * u⁻¹ := by group
          _ = u * X * u⁻¹ := by rw [hkb]
      · have hzkinv : z * k⁻¹ = k⁻¹ * z := s888_commute_z_inv (hq.z_comm hk)
        have hkb : k * (g⁻¹ * q * g) * k⁻¹ = X * z := by
          rw [hb, hX_def]
          calc k * ((k * q * k⁻¹) * z) * k⁻¹ = k * (k * q * k⁻¹) * (z * k⁻¹) := by
                group
            _ = k * (k * q * k⁻¹) * (k⁻¹ * z) := by rw [hzkinv]
            _ = ((k * k) * q * (k * k)⁻¹) * z := by group
        calc g⁻¹ * (g⁻¹ * q * g) * g =
            (g⁻¹ * k * g) * (g⁻¹ * q * g) * (g⁻¹ * k * g)⁻¹ * (g⁻¹ * z * g) := by
              conv_lhs => rw [hb]
              group
          _ = (u * k) * (g⁻¹ * q * g) * (u * k)⁻¹ * z := by rw [hgk, hgz']
          _ = u * (k * (g⁻¹ * q * g) * k⁻¹) * u⁻¹ * z := by group
          _ = u * (X * z) * u⁻¹ * z := by rw [hkb]
          _ = u * X * u⁻¹ := s888_conj_mul_z_cancel hz2 (hq.z_comm huK)
    have hXin : X = q ∨ X = q * z := by
      rcases huX with huX | huX
      · rcases hgbg_in with h | h
        · left
          calc X = u * X * u⁻¹ := huX.symm
            _ = g⁻¹ * (g⁻¹ * q * g) * g := hgbg_X.symm
            _ = q := h
        · right
          calc X = u * X * u⁻¹ := huX.symm
            _ = g⁻¹ * (g⁻¹ * q * g) * g := hgbg_X.symm
            _ = q * z := h
      · rcases hgbg_in with h | h
        · right
          have h' : X * z = q := by
            calc X * z = u * X * u⁻¹ := huX.symm
              _ = g⁻¹ * (g⁻¹ * q * g) * g := hgbg_X.symm
              _ = q := h
          have := congrArg (· * z) h'
          simpa [mul_assoc, hz2] using this
        · left
          have h' : X * z = q * z := by
            calc X * z = u * X * u⁻¹ := huX.symm
              _ = g⁻¹ * (g⁻¹ * q * g) * g := hgbg_X.symm
              _ = q * z := h
          exact mul_right_cancel h'
    have hkk4 : (k * k) ^ 4 = 1 := by
      by_contra hne
      have hne' := par_conj_ne_of_not_q8 hq i hkkK hqK hsq hne
      rcases hXin with h | h
      · rw [hX_def] at h
        exact hne'.1 h
      · rw [hX_def] at h
        exact hne'.2 h
    have hk4 : k ^ 4 = 1 := by
      by_contra hne
      exact (par_sq_not_q8 hq i hk hne) hkk4
    have hd_in : k * q * k⁻¹ = q ∨ k * q * k⁻¹ = q * z :=
      par_conj_q8_mod hq i hk hqK hk4 hq4
    have hb_in : g⁻¹ * q * g = q ∨ g⁻¹ * q * g = q * z := by
      rcases hb_rel with hb | hb
      · rcases hd_in with h | h
        · left; rw [hb, h]
        · right; rw [hb, h]
      · rcases hd_in with h | h
        · right; rw [hb, h]
        · left
          rw [hb, h]
          calc (q * z) * z = q * (z * z) := by group
            _ = q := by rw [hq.z_sq, mul_one]
    rcases hb_in with h | h
    · exact hqne1 h
    · exact hqne2 h

theorem par_outer_iff [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {g : G}
    (hgz : g * z = z * g) (hgK : CFSG.conjugate (K i) g = K i)
    (hg2 : ∀ q ∈ K i, q ^ 4 = 1 →
      (g * g)⁻¹ * q * (g * g) = q ∨ (g * g)⁻¹ * q * (g * g) = q * z) :
    (∃ k ∈ K i, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn (K i)) ↔ ParNt K z g i := by
  constructor
  · intro hOUT
    by_contra hNT
    obtain ⟨k, hk, hne⟩ := hOUT
    exact hne (s888_not_nt_not_out hq i hgz hgK hNT k hk)
  · intro hNT
    by_contra hOUT
    push Not at hOUT
    exact s888_not_out_not_nt hq i hgz hgK hg2 hOUT hNT

end CFSG.OddStandard.SmallF3.Omega
