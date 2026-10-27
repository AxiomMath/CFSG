module

public import CFSG.GH74.GLS.Stage4.T2FourBuild
public import CFSG.GH74.GLS.Stage4.T2NegDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.T2

section Index

theorem t2N_relIndex_two {G : Type} [Group G] {A H : Subgroup G} {t : G} (htH : t ∈ H)
    (htA : t ∉ A) (htt : t * t = 1) (hform : ∀ x ∈ H, x ∈ A ∨ ∃ y ∈ A, x = y * t) :
    A.relIndex H = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, htH, fun b hb => ?_⟩
  rcases hform b hb with hbA | ⟨y, hyA, rfl⟩
  · refine Or.inr ⟨hbA, fun hbt => htA ?_⟩
    have := A.mul_mem (A.inv_mem hbA) hbt
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, fun hyt => htA ?_⟩
    · rwa [mul_assoc, htt, mul_one]
    · have := A.mul_mem (A.inv_mem hyA) hyt
      rwa [inv_mul_cancel_left] at this

end Index

section Cent

theorem t2N_param {F : Type} [Field F] {a b c d e f g h : F} (hY : ¬ (b = 0 ∧ c = 0 ∧ a = d))
    (h1 : f * c = b * g) (h2 : b * (e - h) = f * (a - d)) (h3 : c * (e - h) = g * (a - d)) :
    ∃ r : F, f = r * b ∧ g = r * c ∧ e - h = r * (a - d) := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · have hda : a - d ≠ 0 := fun h0 => hY ⟨hb, hc, sub_eq_zero.1 h0⟩
      refine ⟨(e - h) / (a - d), ?_, ?_, ?_⟩
      · have h0 : f * (a - d) = 0 := by rw [← h2, hb, zero_mul]
        have hf : f = 0 := (mul_eq_zero.1 h0).resolve_right hda
        rw [hf, hb, mul_zero]
      · have h0 : g * (a - d) = 0 := by rw [← h3, hc, zero_mul]
        have hg : g = 0 := (mul_eq_zero.1 h0).resolve_right hda
        rw [hg, hc, mul_zero]
      · field_simp
    · refine ⟨g / c, ?_, ?_, ?_⟩
      · have h0 : f * c = 0 := by rw [h1, hb, zero_mul]
        have hf : f = 0 := (mul_eq_zero.1 h0).resolve_right hc
        rw [hf, hb, mul_zero]
      · field_simp
      · field_simp
        linear_combination h3
  · refine ⟨f / b, ?_, ?_, ?_⟩
    · field_simp
    · field_simp
      linear_combination (-1 : F) * h1
    · field_simp
      linear_combination h2

theorem t2N_comm_of_nonscalar {F : Type} [Field F] {Y B C : Matrix (Fin 2) (Fin 2) F}
    (hY : ∀ s : F, Y ≠ s • (1 : Matrix (Fin 2) (Fin 2) F))
    (hB : B * Y = Y * B) (hC : C * Y = Y * C) : B * C = C * B := by
  have hY' : ¬ (Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1) := by
    rintro ⟨hb, hc, had⟩
    apply hY (Y 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  have hB00 := congrFun (congrFun hB 0) 0
  have hB01 := congrFun (congrFun hB 0) 1
  have hB10 := congrFun (congrFun hB 1) 0
  have hC00 := congrFun (congrFun hC 0) 0
  have hC01 := congrFun (congrFun hC 0) 1
  have hC10 := congrFun (congrFun hC 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hB00 hB01 hB10 hC00 hC01 hC10
  obtain ⟨r, hr1, hr2, hr3⟩ := t2N_param (a := Y 0 0) (b := Y 0 1) (c := Y 1 0) (d := Y 1 1)
    (e := B 0 0) (f := B 0 1) (g := B 1 0) (h := B 1 1) hY' (by linear_combination hB00)
    (by linear_combination hB01) (by linear_combination (-1 : F) * hB10)
  obtain ⟨r', hr1', hr2', hr3'⟩ := t2N_param (a := Y 0 0) (b := Y 0 1) (c := Y 1 0) (d := Y 1 1)
    (e := C 0 0) (f := C 0 1) (g := C 1 0) (h := C 1 1) hY' (by linear_combination hC00)
    (by linear_combination hC01) (by linear_combination (-1 : F) * hC10)
  have k1 : B 0 1 * C 1 0 = C 0 1 * B 1 0 := by rw [hr1, hr2', hr1', hr2]; ring
  have k2 : C 0 1 * (B 0 0 - B 1 1) = B 0 1 * (C 0 0 - C 1 1) := by
    rw [hr3, hr1', hr1, hr3']; ring
  have k3 : B 1 0 * (C 0 0 - C 1 1) = C 1 0 * (B 0 0 - B 1 1) := by
    rw [hr2, hr3', hr2', hr3]; ring
  have k4 : B 1 0 * C 0 1 = C 1 0 * B 0 1 := by rw [hr2, hr1', hr2', hr1]; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination k1
  · linear_combination k2
  · linear_combination k3
  · linear_combination k4

theorem t2N_nonscalar {F : Type} [Field F] {Y : SL2 F} (hYY : Y * Y ≠ 1) :
    ∀ s : F, (Y : Matrix (Fin 2) (Fin 2) F) ≠ s • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro s hs
  apply hYY
  have hdet : s * s = 1 := by
    have h := Y.2
    rw [hs, Matrix.det_smul, Matrix.det_one] at h
    simpa [sq] using h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hs, smul_mul_smul_comm, mul_one, hdet, one_smul]
  rfl

theorem t2N_slConj_eq {F : Type} [Field F] {Y D : SL2 F} {g : GL (Fin 2) F} (hYY : Y * Y ≠ 1)
    (hYg : (Y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F))
    (hDY : D * Y = Y * D) : slConj g D = D := by
  have hDY' : (D : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) =
      (Y : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) hDY
    simpa using this
  have key := t2N_comm_of_nonscalar (t2N_nonscalar hYY) hDY' hYg.symm
  have hgg : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by simp
  apply Subtype.ext
  rw [coe_slConj, ← key, Matrix.mul_assoc, hgg, Matrix.mul_one]

theorem t2N_cent {G : Type} [Group G] {z t : G} {K : Subgroup G} {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (hz : orderOf z = 2) (hzK : z ∈ K) (htt : t * t = 1) (e : ↥K ≃* SL2 F)
    (g : GL (Fin 2) F) (hact : ActsAsConj t K e g) {Hd : Subgroup G}
    (hiff : ∀ x ∈ K, x ∈ Hd ↔ x * t = t * x) {y : G} (hyK : y ∈ K) (hyHd : y ∈ Hd)
    (hyy : y * y ≠ 1) {d : G} (hdK : d ∈ K) (hdy : d * y = y * d) : d ∈ Hd := by
  obtain ⟨φ, hinj, hrange, -, hτ, -⟩ := exists_coords0 h2 hz hzK htt e g hact
  obtain ⟨Y, rfl⟩ : y ∈ φ.range := hrange ▸ hyK
  obtain ⟨D, rfl⟩ : d ∈ φ.range := hrange ▸ hdK
  have hYt : φ Y * t = t * φ Y := (hiff _ hyK).1 hyHd
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hYg1 : slConj g Y = Y := by
    apply hinj
    rw [← hτ Y, ← hYt, mul_inv_cancel_right]
  have hYg : (Y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) := by
    have h3 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) hYg1
    simp only [coe_slConj] at h3
    have hgg : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        1 := by simp
    calc (Y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)
        = ((g : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (g : Matrix (Fin 2) (Fin 2) F) := by
          rw [h3]
      _ = (g : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) := by
          rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hYY : Y * Y ≠ 1 := fun h => hyy (by rw [← map_mul, h, map_one])
  have hDY : D * Y = Y * D := hinj (by rw [map_mul, map_mul]; exact hdy)
  have hDg := t2N_slConj_eq hYY hYg hDY
  have hDt : φ D * t = t * φ D := by
    have h4 := hτ D
    rw [hDg, hti] at h4
    calc φ D * t = (t * φ D * t) * t := by rw [h4]
      _ = t * φ D := by rw [mul_assoc, htt, mul_one]
  exact (hiff _ hdK).2 hDt

end Cent

section Assembly

theorem ch6NegCfg_of_rem {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hq : q % 4 = 1) :
    ∃ (H : Subgroup G) (w₁ w₂ : G),
      Ch6NegCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z t K₁ K₂ H w₁ w₂ := by
  have := hSet.finite₁
  have := hSet.finite₂
  have h5 : 5 ≤ q := hSet.five
  have hzord : orderOf z = 2 := hSet.central.1
  have hzz : z * z = 1 := t2C_zz hSet
  have htt : t * t = 1 := hRem.sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; omega
  have h3₂ : 3 < Nat.card F₂ := by rw [hSet.card₂]; omega
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card hodd₁
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card hodd₂
  have hq1 : (q : ℤ) ≡ 1 [ZMOD 4] := by unfold Int.ModEq; omega
  have hd : ((q + 1 : ℕ) : ℤ) = q + 1 := by push_cast; ring
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  obtain ⟨Hd₁, w₁, hHd₁K, hcyc₁, hcard₁, hiff₁, hw₁K, hw₁sq, hw₁t, hw₁inv⟩ :=
    t2B_factor hodd₁ h3₁ hzord hSet.z_mem₁ htt e₁ g₁ hns₁ hact₁ 1 (Or.inl rfl)
      (by rw [hSet.card₁]; exact hq1) (q + 1) (by rw [hSet.card₁]; exact hd)
  obtain ⟨Hd₂, w₂, hHd₂K, hcyc₂, hcard₂, hiff₂, hw₂K, hw₂sq, hw₂t, hw₂inv⟩ :=
    t2B_factor hodd₂ h3₂ hzord hSet.z_mem₂ htt e₂ g₂ hns₂ hact₂ 1 (Or.inl rfl)
      (by rw [hSet.card₂]; exact hq1) (q + 1) (by rw [hSet.card₂]; exact hd)
  have htK := t2B_t_notin hSet hRem
  have hHd₁c := t2B_cyclic_comm Hd₁ hcyc₁
  have hHd₂c := t2B_cyclic_comm Hd₂ hcyc₂
  have hHd₁₂ : ∀ x ∈ Hd₁, ∀ y ∈ Hd₂, x * y = y * x := fun x hx y hy =>
    hSet.comm x (hHd₁K hx) y (hHd₂K hy)
  have hHd₁t : ∀ x ∈ Hd₁, x * t = t * x := fun x hx => (hiff₁ x (hHd₁K hx)).1 hx
  have hHd₂t : ∀ x ∈ Hd₂, x * t = t * x := fun x hx => (hiff₂ x (hHd₂K hx)).1 hx
  have hAc : ∀ x ∈ Hd₁ ⊔ Hd₂, ∀ y ∈ Hd₁ ⊔ Hd₂, x * y = y * x :=
    t2B_sup_comm hHd₁c hHd₂c hHd₁₂
  have hAt : ∀ x ∈ Hd₁ ⊔ Hd₂, x * t = t * x := by
    have : Hd₁ ⊔ Hd₂ ≤ centralizer ({t} : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hHd₁t x hx))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hHd₂t x hx))
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  have hZc : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self t m n).eq
  have hAZ : ∀ x ∈ Hd₁ ⊔ Hd₂, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hxt : Commute x t := hAt x hx
    exact (hxt.zpow_right n).eq
  set H : Subgroup G := (Hd₁ ⊔ Hd₂) ⊔ Subgroup.zpowers t with hHdef
  have hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := t2B_sup_comm hAc hZc hAZ
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHd₁H : Hd₁ ≤ H := le_sup_left.trans le_sup_left
  have hHd₂H : Hd₂ ≤ H := le_sup_right.trans le_sup_left
  have hzH : z ∈ H :=
    hHd₁H ((hiff₁ z hSet.z_mem₁).2 hRem.comm_z.symm)
  have hform : ∀ x ∈ H, ∃ h₁ ∈ Hd₁, ∃ h₂ ∈ Hd₂, x = h₁ * h₂ ∨ x = h₁ * h₂ * t := by
    intro x hx
    obtain ⟨p, hp, s, hs, rfl⟩ := (mem_sup_iff_of_comm hAZ x).1 hx
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (mem_sup_iff_of_comm hHd₁₂ p).1 hp
    rcases t2C_zpowers_cases htt hs with rfl | rfl
    · exact ⟨h₁, hh₁, h₂, hh₂, Or.inl (mul_one _)⟩
    · exact ⟨h₁, hh₁, h₂, hh₂, Or.inr rfl⟩
  have hHK₁ : H ⊓ K₁ = Hd₁ :=
    le_antisymm (fun x hx => (hiff₁ x hx.2).2 (hHc x hx.1 t htH))
      (fun x hx => ⟨hHd₁H hx, hHd₁K hx⟩)
  have hHK₂ : H ⊓ K₂ = Hd₂ :=
    le_antisymm (fun x hx => (hiff₂ x hx.2).2 (hHc x hx.1 t htH))
      (fun x hx => ⟨hHd₂H hx, hHd₂K hx⟩)
  have hw₁t' : t * w₁ * t = w₁⁻¹ := by rw [hti] at hw₁t; exact hw₁t
  have hw₂t' : t * w₂ * t = w₂⁻¹ := by rw [hti] at hw₂t; exact hw₂t
  have hw₁z : w₁ * z = z * w₁ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_left hw₁K))
  have hw₂z : w₂ * z = z * w₂ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_right hw₂K))
  have hw₁tz : w₁ * t * w₁⁻¹ = t * z := by
    have h1 : w₁ * t = t * w₁⁻¹ := by
      calc w₁ * t = (t * t) * w₁ * t := by rw [htt, one_mul]
        _ = t * (t * w₁ * t) := by group
        _ = t * w₁⁻¹ := by rw [hw₁t']
    calc w₁ * t * w₁⁻¹ = t * (w₁⁻¹ * w₁⁻¹) := by rw [h1]; group
      _ = t * (w₁ * w₁)⁻¹ := by group
      _ = t * z := by rw [hw₁sq]; rw [inv_eq_of_mul_eq_one_right hzz]
  have hw₂tz : w₂ * t * w₂⁻¹ = t * z := by
    have h1 : w₂ * t = t * w₂⁻¹ := by
      calc w₂ * t = (t * t) * w₂ * t := by rw [htt, one_mul]
        _ = t * (t * w₂ * t) := by group
        _ = t * w₂⁻¹ := by rw [hw₂t']
    calc w₂ * t * w₂⁻¹ = t * (w₂⁻¹ * w₂⁻¹) := by rw [h1]; group
      _ = t * (w₂ * w₂)⁻¹ := by group
      _ = t * z := by rw [hw₂sq]; rw [inv_eq_of_mul_eq_one_right hzz]
  have hc₁₁ : ∀ x ∈ Hd₁, w₁ * x * w₁⁻¹ = x⁻¹ := hw₁inv
  have hc₂₂ : ∀ x ∈ Hd₂, w₂ * x * w₂⁻¹ = x⁻¹ := hw₂inv
  have hc₁₂ : ∀ y ∈ Hd₂, w₁ * y * w₁⁻¹ = y := by
    intro y hy
    rw [hSet.comm w₁ hw₁K y (hHd₂K hy)]; group
  have hc₂₁ : ∀ x ∈ Hd₁, w₂ * x * w₂⁻¹ = x := by
    intro x hx
    rw [(hSet.comm x (hHd₁K hx) w₂ hw₂K).symm]; group
  have hinv2 : ∀ h₁ ∈ Hd₁, ∀ h₂ ∈ Hd₂, (h₁ * h₂)⁻¹ = h₁⁻¹ * h₂⁻¹ := by
    intro h₁ hh₁ h₂ hh₂
    have := hHd₁₂ h₁⁻¹ (Hd₁.inv_mem hh₁) h₂⁻¹ (Hd₂.inv_mem hh₂)
    calc (h₁ * h₂)⁻¹ = h₂⁻¹ * h₁⁻¹ := by group
      _ = h₁⁻¹ * h₂⁻¹ := this.symm
  have hinv3 : ∀ h₁ ∈ Hd₁, ∀ h₂ ∈ Hd₂, (h₁ * h₂ * t)⁻¹ = h₁⁻¹ * h₂⁻¹ * t := by
    intro h₁ hh₁ h₂ hh₂
    have hp : (h₁ * h₂)⁻¹ ∈ Hd₁ ⊔ Hd₂ :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₁) (Subgroup.mem_sup_right hh₂))
    have := hAt _ hp
    calc (h₁ * h₂ * t)⁻¹ = t⁻¹ * (h₁ * h₂)⁻¹ := by group
      _ = t * (h₁ * h₂)⁻¹ := by rw [hti]
      _ = (h₁ * h₂)⁻¹ * t := this.symm
      _ = h₁⁻¹ * h₂⁻¹ * t := by rw [hinv2 h₁ hh₁ h₂ hh₂]
  have hw₀inv : ∀ x ∈ H, (w₁ * w₂) * x * (w₁ * w₂)⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have e1 : (w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹ = h₁⁻¹ := by
      calc (w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * h₁ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * h₁ * w₁⁻¹ := by rw [hc₂₁ h₁ hh₁]
        _ = h₁⁻¹ := hc₁₁ h₁ hh₁
    have e2 : (w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹ = h₂⁻¹ := by
      calc (w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * h₂ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * h₂⁻¹ * w₁⁻¹ := by rw [hc₂₂ h₂ hh₂]
        _ = h₂⁻¹ := hc₁₂ h₂⁻¹ (Hd₂.inv_mem hh₂)
    have e3 : (w₁ * w₂) * t * (w₁ * w₂)⁻¹ = t := by
      calc (w₁ * w₂) * t * (w₁ * w₂)⁻¹ = w₁ * (w₂ * t * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (t * z) * w₁⁻¹ := by rw [hw₂tz]
        _ = (w₁ * t * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = (t * z) * z := by
            rw [hw₁tz, show w₁ * z * w₁⁻¹ = z by rw [hw₁z]; group]
        _ = t := by rw [mul_assoc, hzz, mul_one]
    rcases hxe with rfl | rfl
    · rw [hinv2 h₁ hh₁ h₂ hh₂]
      calc (w₁ * w₂) * (h₁ * h₂) * (w₁ * w₂)⁻¹
          = ((w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹) := by group
        _ = h₁⁻¹ * h₂⁻¹ := by rw [e1, e2]
    · rw [hinv3 h₁ hh₁ h₂ hh₂]
      calc (w₁ * w₂) * (h₁ * h₂ * t) * (w₁ * w₂)⁻¹
          = ((w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹) *
              ((w₁ * w₂) * t * (w₁ * w₂)⁻¹) := by group
        _ = h₁⁻¹ * h₂⁻¹ * t := by rw [e1, e2, e3]
  have hw₁norm : ∀ x ∈ H, w₁ * x * w₁⁻¹ ∈ H := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hH1 : h₁⁻¹ ∈ H := H.inv_mem (hHd₁H hh₁)
    have hH2 : h₂ ∈ H := hHd₂H hh₂
    rcases hxe with rfl | rfl
    · have : w₁ * (h₁ * h₂) * w₁⁻¹ = h₁⁻¹ * h₂ := by
        calc w₁ * (h₁ * h₂) * w₁⁻¹ = (w₁ * h₁ * w₁⁻¹) * (w₁ * h₂ * w₁⁻¹) := by group
          _ = h₁⁻¹ * h₂ := by rw [hc₁₁ h₁ hh₁, hc₁₂ h₂ hh₂]
      rw [this]; exact H.mul_mem hH1 hH2
    · have : w₁ * (h₁ * h₂ * t) * w₁⁻¹ = h₁⁻¹ * h₂ * (t * z) := by
        calc w₁ * (h₁ * h₂ * t) * w₁⁻¹
            = (w₁ * h₁ * w₁⁻¹) * (w₁ * h₂ * w₁⁻¹) * (w₁ * t * w₁⁻¹) := by group
          _ = h₁⁻¹ * h₂ * (t * z) := by rw [hc₁₁ h₁ hh₁, hc₁₂ h₂ hh₂, hw₁tz]
      rw [this]; exact H.mul_mem (H.mul_mem hH1 hH2) (H.mul_mem htH hzH)
  have hw₂norm : ∀ x ∈ H, w₂ * x * w₂⁻¹ ∈ H := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hH1 : h₁ ∈ H := hHd₁H hh₁
    have hH2 : h₂⁻¹ ∈ H := H.inv_mem (hHd₂H hh₂)
    rcases hxe with rfl | rfl
    · have : w₂ * (h₁ * h₂) * w₂⁻¹ = h₁ * h₂⁻¹ := by
        calc w₂ * (h₁ * h₂) * w₂⁻¹ = (w₂ * h₁ * w₂⁻¹) * (w₂ * h₂ * w₂⁻¹) := by group
          _ = h₁ * h₂⁻¹ := by rw [hc₂₁ h₁ hh₁, hc₂₂ h₂ hh₂]
      rw [this]; exact H.mul_mem hH1 hH2
    · have : w₂ * (h₁ * h₂ * t) * w₂⁻¹ = h₁ * h₂⁻¹ * (t * z) := by
        calc w₂ * (h₁ * h₂ * t) * w₂⁻¹
            = (w₂ * h₁ * w₂⁻¹) * (w₂ * h₂ * w₂⁻¹) * (w₂ * t * w₂⁻¹) := by group
          _ = h₁ * h₂⁻¹ * (t * z) := by rw [hc₂₁ h₁ hh₁, hc₂₂ h₂ hh₂, hw₂tz]
      rw [this]; exact H.mul_mem (H.mul_mem hH1 hH2) (H.mul_mem htH hzH)
  have hw₀notin : w₁ * w₂ ∉ H := by
    refine t2C_w0_not_mem (K := K₁) hHc hw₀inv ?_ ?_
    · rw [hHK₁]; exact hcyc₁
    · rw [hHK₁, hcard₁]; omega
  have hKC : K₁ ⊔ K₂ ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := hSet.le_residual
  have htC : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hRem.gen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHle : H ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    sup_le (sup_le (hHd₁K.trans (le_sup_left.trans hKC)) (hHd₂K.trans (le_sup_right.trans hKC)))
      (Subgroup.zpowers_le.2 htC)
  have hC₁le : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ centralizer ({z} : Set G) :=
    Subgroup.map_subtype_le _
  have hformA : ∀ x ∈ H, x ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) ∨ ∃ y ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂), x = y * t := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hp : h₁ * h₂ ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) := by
      rw [hHK₁, hHK₂]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₁) (Subgroup.mem_sup_right hh₂)
    rcases hxe with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr ⟨h₁ * h₂, hp, rfl⟩
  refine ⟨H, w₁, w₂, ?_⟩
  refine
    { zz := hzz, z_ne := t2C_z_ne hSet, uu := htt,
      u_ne := fun h1 => htK (h1 ▸ (K₁ ⊔ K₂).one_mem),
      zu_ne := fun h1 => htK (h1 ▸ Subgroup.mem_sup_left hSet.z_mem₁),
      zu_comm := hRem.comm_z.symm, K_comm := hSet.comm, K_inter := hSet.inter_eq.le,
      C_comm := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hC₁le hx),
      K_le_C := hKC,
      C_norm₁ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).1 c hc,
      C_norm₂ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).2 c hc,
      C_idx := hSet.index_two, H_comm := hHc, z_mem_H := hzH, u_mem_H := htH,
      H_le_C := hHle, H_not_le_K := fun hle => htK (hle htH),
      H₁_iff := ?_, H₂_iff := ?_, w₁_mem := hw₁K, w₂_mem := hw₂K, w₁_sq := hw₁sq,
      w₂_sq := hw₂sq, w₁_u := hw₁tz, w₂_u := hw₂tz, w₁_normH := hw₁norm,
      w₂_normH := hw₂norm, w₀_inv := hw₀inv, w₀_not_mem := hw₀notin,
      H₁_cyc := ?_, H₂_cyc := ?_, H₁_card := ?_, H₂_card := ?_, H_idx := ?_,
      H₁_cent := fun y hy hyy d hd hdy => hHd₁H
        (t2N_cent h2₁ hzord hSet.z_mem₁ htt e₁ g₁ hact₁ hiff₁ hy.2 (hHK₁ ▸ hy) hyy hd hdy),
      H₂_cent := fun y hy hyy d hd hdy => hHd₂H
        (t2N_cent h2₂ hzord hSet.z_mem₂ htt e₂ g₂ hact₂ hiff₂ hy.2 (hHK₂ ▸ hy) hyy hd hdy) }
  · intro x hx
    exact ⟨fun hxH => hHc x hxH t htH, fun hxt => hHd₁H ((hiff₁ x hx).2 hxt)⟩
  · intro x hx
    exact ⟨fun hxH => hHc x hxH t htH, fun hxt => hHd₂H ((hiff₂ x hx).2 hxt)⟩
  · rw [hHK₁]; exact hcyc₁
  · rw [hHK₂]; exact hcyc₂
  · rw [hHK₁, hcard₁]
  · rw [hHK₂, hcard₂]
  · have hAle : (H ⊓ K₁) ⊔ (H ⊓ K₂) ≤ K₁ ⊔ K₂ := sup_le_sup inf_le_right inf_le_right
    exact t2N_relIndex_two htH (fun h => htK (hAle h)) htt hformA

end Assembly

theorem ch6T2NegCfgMod_one : Ch6T2NegCfgMod 1 := by
  intro G _ _ Gs _ q z K₁ K₂ F₁ F₂ _ _ t hSet hRem hq
  obtain ⟨H, w₁, w₂, hCfg⟩ := ch6NegCfg_of_rem hSet hRem hq
  exact ⟨t, H, w₁, w₂, hCfg⟩

end CFSG.GH74.GLS.Stage4.Rest
