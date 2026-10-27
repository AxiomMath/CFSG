module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParS2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888M3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3a

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma s888parC_mem_conjugate_iff {A : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma s888parC_conj_mem {l : Fin 4} {g x : G} (hgK : CFSG.conjugate (K l) g = K l)
    (hx : x ∈ K l) : g⁻¹ * x * g ∈ K l := by
  have h : g⁻¹ * x * g ∈ CFSG.conjugate (K l) g := by
    rw [s888parC_mem_conjugate_iff]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  rwa [hgK] at h

private lemma s888parC_conj_mem' {l : Fin 4} {g x : G} (hgK : CFSG.conjugate (K l) g = K l)
    (hx : x ∈ K l) : g * x * g⁻¹ ∈ K l := by
  have h : x ∈ CFSG.conjugate (K l) g := by
    rw [hgK]
    exact hx
  exact s888parC_mem_conjugate_iff.mp h

private lemma s888parC_mem_core [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {q : G} :
    q ∈ twoCoreIn (K i) ↔ q ∈ K i ∧ q ^ 4 = 1 := by
  rw [twoCoreIn_eq_inf hq i, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, Sec5B517Q8.pow_four hq h1⟩
  · rintro ⟨h2, h4⟩
    exact ⟨Sec5B517Q8.mem_of_mem hq h2 h4, h2⟩

private lemma s888parC_conj_pow4 {g x : G} (hx : x ^ 4 = 1) : (g⁻¹ * x * g) ^ 4 = 1 := by
  have h := conj_pow (a := g⁻¹) (b := x) (i := 4)
  simp only [inv_inv] at h
  rw [h, hx]
  group

private lemma s888parC_conj_z (hq : Sec5B517Quad K z) {j : Fin 4} {r : G} (hr : r ∈ K j) :
    r⁻¹ * z * r = z := by
  have h : z * r = r * z := hq.z_comm hr
  calc r⁻¹ * z * r = r⁻¹ * (z * r) := by rw [mul_assoc]
    _ = r⁻¹ * (r * z) := by rw [h]
    _ = z := by group

theorem par_exists_corr (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a b w : G}
    (ha : a ∈ K i) (hb : b ∈ K j) (ha2 : a * a = z) (hb2 : b * b = z)
    (hwa : w⁻¹ * a * w = a ∨ w⁻¹ * a * w = a * z)
    (hwb : w⁻¹ * b * w = b ∨ w⁻¹ * b * w = b * z) :
    ∃ r ∈ K i, r ^ 4 = 1 ∧ (w * r)⁻¹ * (a * b) * (w * r) = a * b := by
  have hzsq : z * z = 1 := hq.z_sq
  have ha4 : a ^ 4 = 1 := by
    have h : a ^ 4 = (a * a) * (a * a) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [h, ha2, hzsq]
  have ha1 : a ≠ 1 := fun h => hq.z_ne (by rw [h, one_mul] at ha2; exact ha2.symm)
  have haz : a ≠ z := fun h => hq.z_ne (by rw [h] at ha2; exact ha2.symm.trans hzsq)
  have hexp : ∀ r : G, (w * r)⁻¹ * (a * b) * (w * r) =
      r⁻¹ * ((w⁻¹ * a * w) * (w⁻¹ * b * w)) * r := fun r => by group
  have hzb : z * b = b * z := hq.z_comm hb
  obtain ⟨r, hrK, hr4, hra⟩ := Sec5B517Quad.exists_inverting hq ha ha4 ha1 haz
  have hzr : r⁻¹ * z * r = z := s888parC_conj_z hq hrK
  have hXz : (r⁻¹ * a * r) * z = a := by
    calc (r⁻¹ * a * r) * z = (r⁻¹ * a * r) * (r⁻¹ * z * r) := by rw [hzr]
      _ = r⁻¹ * (a * z) * r := by group
      _ = a := by rw [← hra]; group
  have hrinv : r⁻¹ * a * r = a * z := by
    calc r⁻¹ * a * r = (r⁻¹ * a * r) * (z * z) := by rw [hzsq, mul_one]
      _ = ((r⁻¹ * a * r) * z) * z := by rw [mul_assoc (r⁻¹ * a * r) z z]
      _ = a * z := by rw [hXz]
  have hrb : r⁻¹ * b * r = b := by
    have h := hq.comm i j hij r hrK b hb
    calc r⁻¹ * b * r = r⁻¹ * (b * r) := by rw [mul_assoc]
      _ = r⁻¹ * (r * b) := by rw [h]
      _ = b := by group
  rcases hwa with hwa | hwa <;> rcases hwb with hwb | hwb
  · refine ⟨1, one_mem _, one_pow 4, ?_⟩
    rw [hexp, hwa, hwb]
    simp
  · refine ⟨r, hrK, hr4, ?_⟩
    rw [hexp, hwa, hwb]
    calc r⁻¹ * (a * (b * z)) * r = (r⁻¹ * a * r) * (r⁻¹ * b * r) * (r⁻¹ * z * r) := by group
      _ = (a * z) * b * z := by rw [hrinv, hrb, hzr]
      _ = a * (z * b) * z := by group
      _ = a * (b * z) * z := by rw [hzb]
      _ = a * b * (z * z) := by group
      _ = a * b := by rw [hzsq, mul_one]
  · refine ⟨r, hrK, hr4, ?_⟩
    rw [hexp, hwa, hwb]
    calc r⁻¹ * ((a * z) * b) * r = (r⁻¹ * a * r) * (r⁻¹ * z * r) * (r⁻¹ * b * r) := by group
      _ = (a * z) * z * b := by rw [hrinv, hrb, hzr]
      _ = a * (z * z) * b := by group
      _ = a * b := by rw [hzsq, mul_one]
  · refine ⟨1, one_mem _, one_pow 4, ?_⟩
    rw [hexp, hwa, hwb]
    simp only [inv_one, one_mul, mul_one]
    calc (a * z) * (b * z) = a * (z * b) * z := by group
      _ = a * (b * z) * z := by rw [hzb]
      _ = a * b * (z * z) := by group
      _ = a * b := by rw [hzsq, mul_one]

@[expose] def ParNt (K : Fin 4 → Subgroup G) (z g : G) (i : Fin 4) : Prop :=
  ∃ q ∈ twoCoreIn (K i), g⁻¹ * q * g ≠ q ∧ g⁻¹ * q * g ≠ q * z

theorem par_nt_corr_iff [Finite G] (hq : Sec5B517Quad K z) {j : Fin 4} {r g : G} (hr : r ∈ K j)
    (hr4 : r ^ 4 = 1) (hgK : ∀ l, CFSG.conjugate (K l) g = K l) (i : Fin 4) :
    ParNt K z (g * r) i ↔ ParNt K z g i := by
  unfold ParNt
  have hz2 : z * z = 1 := hq.z_sq
  have hconj : ∀ q : G, (g * r)⁻¹ * q * (g * r) = r⁻¹ * (g⁻¹ * q * g) * r := fun q => by group
  by_cases hji : j = i
  · subst hji
    have hr4' : (r⁻¹) ^ 4 = 1 := by rw [inv_pow, hr4, inv_one]
    have hzr : r⁻¹ * z * r = z := s888parC_conj_z hq hr
    have hrq : ∀ x ∈ K j, x ^ 4 = 1 → r⁻¹ * x * r = x ∨ r⁻¹ * x * r = x * z := by
      intro x hx hx4
      have h := par_conj_q8_mod hq j ((K j).inv_mem hr) hx hr4' hx4
      simpa using h
    constructor
    · rintro ⟨q, hqc, h1, h2⟩
      obtain ⟨hqK, hq4⟩ := (s888parC_mem_core hq j).mp hqc
      have hnot : ¬ (g⁻¹ * q * g = q ∨ g⁻¹ * q * g = q * z) := by
        intro hd
        rcases hd with hd | hd
        · rcases hrq q hqK hq4 with h3 | h3
          · exact h1 (by rw [hconj, hd]; exact h3)
          · exact h2 (by rw [hconj, hd]; exact h3)
        · have e : r⁻¹ * (q * z) * r = (r⁻¹ * q * r) * z := by
            calc r⁻¹ * (q * z) * r = (r⁻¹ * q * r) * (r⁻¹ * z * r) := by group
              _ = (r⁻¹ * q * r) * z := by rw [hzr]
          rcases hrq q hqK hq4 with h3 | h3
          · exact h2 (by rw [hconj, hd, e, h3])
          · refine h1 ?_
            rw [hconj, hd, e, h3]
            calc q * z * z = q * (z * z) := by rw [mul_assoc]
              _ = q := by rw [hz2, mul_one]
      exact ⟨q, hqc, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
    · rintro ⟨q, hqc, h1, h2⟩
      obtain ⟨hqK, hq4⟩ := (s888parC_mem_core hq j).mp hqc
      have hq'K : g⁻¹ * q * g ∈ K j := s888parC_conj_mem (hgK j) hqK
      have hq'4 : (g⁻¹ * q * g) ^ 4 = 1 := s888parC_conj_pow4 hq4
      refine ⟨q, hqc, ?_⟩
      rw [hconj]
      rcases hrq _ hq'K hq'4 with hu | hu
      · rw [hu]
        exact ⟨h1, h2⟩
      · rw [hu]
        refine ⟨fun h => h2 ?_, fun h => h1 ?_⟩
        · calc g⁻¹ * q * g = g⁻¹ * q * g * (z * z) := by rw [hz2, mul_one]
            _ = (g⁻¹ * q * g * z) * z := (mul_assoc _ _ _).symm
            _ = q * z := by rw [h]
        · exact mul_right_cancel h
  · have hcomm : ∀ x ∈ K i, r⁻¹ * x * r = x := by
      intro x hx
      have h := hq.comm j i hji r hr x hx
      calc r⁻¹ * x * r = r⁻¹ * (x * r) := by rw [mul_assoc]
        _ = r⁻¹ * (r * x) := by rw [h]
        _ = x := by group
    have key : ∀ q ∈ twoCoreIn (K i), (g * r)⁻¹ * q * (g * r) = g⁻¹ * q * g := by
      intro q hqc
      obtain ⟨hqK, -⟩ := (s888parC_mem_core hq i).mp hqc
      rw [hconj]
      exact hcomm _ (s888parC_conj_mem (hgK i) hqK)
    constructor
    · rintro ⟨q, hqc, h1, h2⟩
      exact ⟨q, hqc, by rwa [key q hqc] at h1, by rwa [key q hqc] at h2⟩
    · rintro ⟨q, hqc, h1, h2⟩
      exact ⟨q, hqc, by rwa [key q hqc], by rwa [key q hqc]⟩

theorem par_conj_mul (hq : Sec5B517Quad K z) {j : Fin 4} {r g : G} (hr : r ∈ K j)
    (hgK : ∀ l, CFSG.conjugate (K l) g = K l) (l : Fin 4) :
    CFSG.conjugate (K l) (g * r) = K l := by
  have hcomm : l ≠ j → ∀ x ∈ K l, r * x * r⁻¹ = x := by
    intro hlj x hx
    have h := hq.comm j l hlj.symm r hr x hx
    calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [h]
      _ = x := by group
  have hr1 : ∀ x : G, r * x * r⁻¹ ∈ K l ↔ x ∈ K l := by
    intro x
    by_cases hlj : l = j
    · subst hlj
      constructor
      · intro hx
        have h := (K l).mul_mem ((K l).mul_mem ((K l).inv_mem hr) hx) hr
        have e : r⁻¹ * (r * x * r⁻¹) * r = x := by group
        rwa [e] at h
      · intro hx
        exact (K l).mul_mem ((K l).mul_mem hr hx) ((K l).inv_mem hr)
    · constructor
      · intro hx
        have h := hq.comm j l (Ne.symm hlj) r⁻¹ ((K j).inv_mem hr) _ hx
        have e1 : r⁻¹ * (r * x * r⁻¹) = x * r⁻¹ := by group
        rw [e1] at h
        have h2 : x = r * x * r⁻¹ := mul_right_cancel h
        rwa [← h2] at hx
      · intro hx
        rw [hcomm hlj x hx]
        exact hx
  ext x
  rw [s888parC_mem_conjugate_iff]
  have e : (g * r) * x * (g * r)⁻¹ = g * (r * x * r⁻¹) * g⁻¹ := by group
  rw [e]
  constructor
  · intro hx
    have h1 := s888parC_conj_mem (hgK l) hx
    have e2 : g⁻¹ * (g * (r * x * r⁻¹) * g⁻¹) * g = r * x * r⁻¹ := by group
    rw [e2] at h1
    exact (hr1 x).mp h1
  · intro hx
    exact s888parC_conj_mem' (hgK l) ((hr1 x).mpr hx)

end CFSG.OddStandard.SmallF3.Omega
