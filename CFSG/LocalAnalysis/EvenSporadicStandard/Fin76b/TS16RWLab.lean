module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

theorem eT_lt : eT < 32 := by decide

theorem eT_ne : eT ≠ 0 := by decide

theorem eT_sq : mulE0 eT eT = 0 := by decide +kernel

theorem eCenter : ∀ a < 32, (∀ b < 32, mulE0 a b = mulE0 b a) → a = 0 ∨ a = eT := by
  decide +kernel

theorem redP_facts : ∀ i < 8, ∀ k < 32, (redP i k).1 < 8 ∧ (redP i k).2 < 32 ∧ ixP i k < 128 ∧
    decD (ixP i k) = (redP i k).1 ∧ ixP i k % 32 = (redP i k).2 ∧
    ((i, k) = redP i k ∨ redP i k = (dMul i 2, mulE0 k eT)) := by
  decide +kernel

theorem lab_inj_fact : ∀ a < 128, ∀ b < 128,
    ((decD a, a % 32) = (decD b, b % 32) ∨
      (decD b, b % 32) = (dMul (decD a) 2, mulE0 (a % 32) eT)) → a = b := by
  decide +kernel

theorem ixP_decD : ∀ c < 128, (decD c < 8 ∧ c % 32 < 32) ∧ ixP (decD c) (c % 32) = c := by
  decide +kernel

theorem mulC_eq_ixP (a b : ℕ) : mulC a b = ixP (dMul (decD a) (decD b)) (mulE0 (a % 32) (b % 32)) :=
  rfl

theorem dMul_lt : ∀ i < 8, ∀ j < 8, dMul i j < 8 := by decide +kernel

section Lab

variable {Γ : Type*} [Group Γ]

structure DECtx (D E : Subgroup Γ) (eD : D ≃* DihedralGroup 4) (t : Γ) (eltE : ℕ → Γ) : Prop where
  L : ELabelling E t mulE0 eT eltE
  tD : t ∈ D
  comm : ∀ s ∈ D, ∀ e ∈ E, s * e = e * s

@[expose] noncomputable def valDE {D : Subgroup Γ} (eD : D ≃* DihedralGroup 4) (eltE : ℕ → Γ)
    (p : ℕ × ℕ) : Γ := sElt eD p.1 * eltE p.2

@[expose] noncomputable def labD {D : Subgroup Γ} (eD : D ≃* DihedralGroup 4) (eltE : ℕ → Γ)
    (c : ℕ) : Γ := sElt eD (decD c) * eltE (c % 32)

variable {D E : Subgroup Γ} {eD : D ≃* DihedralGroup 4} {t : Γ} {eltE : ℕ → Γ}

namespace DECtx

variable (h : DECtx D E eD t eltE)

include h

theorem t_sq : t * t = 1 := by
  rw [← h.L.at_tI, ← h.L.mul eT eT_lt eT eT_lt, eT_sq, h.L.one]

theorem t_mem_E : t ∈ E := h.L.at_tI ▸ h.L.mem eT eT_lt

theorem t_eq : t = sElt eD 2 := by
  have htE : t ∈ E := h.t_mem_E
  have hcen : ∀ x : DihedralGroup 4, x * eD ⟨t, h.tD⟩ = eD ⟨t, h.tD⟩ * x := by
    intro x
    have h1 : eD.symm x * (⟨t, h.tD⟩ : D) = ⟨t, h.tD⟩ * eD.symm x :=
      Subtype.ext (h.comm _ (eD.symm x).2 t htE)
    have h2 := congrArg eD h1
    simpa [map_mul] using h2
  have hsq : eD ⟨t, h.tD⟩ * eD ⟨t, h.tD⟩ = 1 := by
    rw [← map_mul, ← map_one eD]
    congr 1
    exact Subtype.ext h.t_sq
  have hne : eD ⟨t, h.tD⟩ ≠ 1 := by
    intro h1
    have : (⟨t, h.tD⟩ : D) = 1 := by
      apply eD.injective
      rw [h1, map_one]
    have h3 : t = 1 := congrArg Subtype.val this
    apply eT_ne
    apply h.L.inj eT eT_lt 0 (by norm_num)
    rw [h.L.at_tI, h.L.one, h3]
  have hd := dih_central _ hcen hsq hne
  unfold sElt
  rw [← hd]
  simp

theorem comm_elt (i : ℕ) {k : ℕ} (hk : k < 32) : eltE k * sElt eD i = sElt eD i * eltE k :=
  (h.comm _ (sElt_mem eD i) _ (h.L.mem k hk)).symm

theorem val_mul {i k j l : ℕ} (hi : i < 8) (hk : k < 32) (hj : j < 8) (hl : l < 32) :
    valDE eD eltE (i, k) * valDE eD eltE (j, l) = valDE eD eltE (dMul i j, mulE0 k l) := by
  simp only [valDE]
  rw [← sElt_mul eD hi hj, h.L.mul k hk l hl]
  calc sElt eD i * eltE k * (sElt eD j * eltE l)
      = sElt eD i * (eltE k * sElt eD j) * eltE l := by group
    _ = sElt eD i * (sElt eD j * eltE k) * eltE l := by rw [h.comm_elt j hk]
    _ = sElt eD i * sElt eD j * (eltE k * eltE l) := by group

theorem val_peq {x y : ℕ × ℕ} (hx1 : x.1 < 8) (hx2 : x.2 < 32) (hxy : UPeq mulE0 eT x y) :
    valDE eD eltE x = valDE eD eltE y := by
  obtain ⟨i, k⟩ := x
  simp only at hx1 hx2
  rcases hxy with rfl | hy
  · rfl
  · rw [hy]
    simp only [valDE]
    have htEq := h.t_eq
    have htt := h.t_sq
    have htk : t * eltE k = eltE k * t := by
      have := h.comm_elt 2 hx2
      rw [← htEq] at this
      exact this.symm
    rw [← sElt_mul eD hx1 (by norm_num : 2 < 8), h.L.mul k hx2 eT eT_lt, h.L.at_tI, ← htEq]
    calc sElt eD i * eltE k = sElt eD i * eltE k * (t * t) := by rw [htt, mul_one]
      _ = sElt eD i * (eltE k * t) * t := by group
      _ = sElt eD i * (t * eltE k) * t := by rw [htk]
      _ = sElt eD i * t * (eltE k * t) := by group

theorem val_fib {x y : ℕ × ℕ} (hx1 : x.1 < 8) (hx2 : x.2 < 32) (hy1 : y.1 < 8) (hy2 : y.2 < 32)
    (hxy : valDE eD eltE x = valDE eD eltE y) : UPeq mulE0 eT x y := by
  obtain ⟨i, k⟩ := x
  obtain ⟨j, l⟩ := y
  simp only [valDE] at hxy
  simp only at hx1 hx2 hy1 hy2
  have htEq := h.t_eq
  have hz : (sElt eD j)⁻¹ * sElt eD i = eltE l * (eltE k)⁻¹ := by
    calc (sElt eD j)⁻¹ * sElt eD i
        = (sElt eD j)⁻¹ * (sElt eD i * eltE k) * (eltE k)⁻¹ := by group
      _ = (sElt eD j)⁻¹ * (sElt eD j * eltE l) * (eltE k)⁻¹ := by rw [hxy]
      _ = eltE l * (eltE k)⁻¹ := by group
  have hzS : (sElt eD j)⁻¹ * sElt eD i ∈ D :=
    mul_mem (inv_mem (sElt_mem eD j)) (sElt_mem eD i)
  have hzE : (sElt eD j)⁻¹ * sElt eD i ∈ E :=
    hz ▸ mul_mem (h.L.mem l hy2) (inv_mem (h.L.mem k hx2))
  obtain ⟨c, hc32, hcz⟩ := h.L.surj _ hzE
  have hcent : ∀ b < 32, mulE0 c b = mulE0 b c := by
    intro b hb
    apply h.L.inj _ (h.L.lt c hc32 b hb) _ (h.L.lt b hb c hc32)
    rw [h.L.mul c hc32 b hb, h.L.mul b hb c hc32, hcz]
    exact h.comm _ hzS (eltE b) (h.L.mem b hb)
  rcases eCenter c hc32 hcent with h0 | hI
  · have hz1 : (sElt eD j)⁻¹ * sElt eD i = 1 := by rw [← hcz, h0, h.L.one]
    have h1 : sElt eD j = sElt eD i := inv_mul_eq_one.1 hz1
    have h2 : eltE l * (eltE k)⁻¹ = 1 := hz ▸ hz1
    have h3 : eltE l = eltE k := mul_inv_eq_one.1 h2
    have hij : i = j := sElt_inj eD hx1 hy1 h1.symm
    have hlk : l = k := h.L.inj l hy2 k hx2 h3
    subst hij
    subst hlk
    exact Or.inl rfl
  · have hzt : (sElt eD j)⁻¹ * sElt eD i = t := by rw [← hcz, hI, h.L.at_tI]
    have hit : sElt eD i = sElt eD (dMul j 2) := by
      rw [← sElt_mul eD hy1 (by norm_num : 2 < 8), ← htEq, ← hzt]
      group
    have hi2 : i = dMul j 2 :=
      sElt_inj eD hx1 (dih_mul j hy1 2 (by norm_num)).1 hit
    have hlt' : eltE l = t * eltE k := by
      have : eltE l * (eltE k)⁻¹ = t := hz ▸ hzt
      rw [← this]
      group
    have htk : t * eltE k = eltE k * t := by
      have := h.comm_elt 2 hx2
      rw [← htEq] at this
      exact this.symm
    have hl2 : l = mulE0 k eT := by
      apply h.L.inj l hy2 _ (h.L.lt k hx2 eT eT_lt)
      rw [h.L.mul k hx2 eT eT_lt, h.L.at_tI, hlt', htk]
    right
    simp only
    rw [hi2, dMul_dMul_two j hy1, hl2]

theorem lab_ixP {i k : ℕ} (hi : i < 8) (hk : k < 32) :
    labD eD eltE (ixP i k) = sElt eD i * eltE k := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := redP_facts i hi k hk
  have e : labD eD eltE (ixP i k) = valDE eD eltE (redP i k) := by
    simp only [labD, valDE]
    rw [h4, h5]
  rw [e]
  exact (h.val_peq (x := (i, k)) hi hk h6).symm

theorem lab_mem (c : ℕ) (hc : c < 128) : labD eD eltE c ∈ D ⊔ E :=
  Subgroup.mul_mem_sup (sElt_mem eD _) (h.L.mem _ (Nat.mod_lt _ (by norm_num)))

theorem lab_zero : labD eD eltE 0 = 1 := by
  have e : labD eD eltE 0 = sElt eD 0 * eltE 0 := rfl
  rw [e, sElt_zero, h.L.one, mul_one]

theorem lab_tC : labD eD eltE tC = t := by
  have e : labD eD eltE tC = sElt eD 0 * eltE eT := rfl
  rw [e, sElt_zero, h.L.at_tI, one_mul]

theorem tabLab : TabLab (D ⊔ E) (labD eD eltE) where
  mem c hc := h.lab_mem c hc
  surj w hw := by
    have hB : E ≤ Subgroup.centralizer (D : Set Γ) := fun e he =>
      Subgroup.mem_centralizer_iff.2 fun s hs => h.comm s hs e he
    obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hB hw
    obtain ⟨i, hi, hsi⟩ := dih_surj (eD ⟨s, hs⟩)
    obtain ⟨k, hk, hek⟩ := h.L.surj e he
    have hsE : s = sElt eD i := by
      unfold sElt
      rw [hsi]
      simp
    obtain ⟨-, -, hlt, -⟩ := redP_facts i hi k hk
    refine ⟨ixP i k, hlt, ?_⟩
    rw [h.lab_ixP hi hk, hsE, hek]
  inj a ha b hb hab := by
    obtain ⟨⟨ha1, ha2⟩, -⟩ := ixP_decD a ha
    obtain ⟨⟨hb1, hb2⟩, -⟩ := ixP_decD b hb
    apply lab_inj_fact a ha b hb
    exact h.val_fib ha1 ha2 hb1 hb2 hab
  mul a ha b hb := by
    obtain ⟨⟨ha1, ha2⟩, -⟩ := ixP_decD a ha
    obtain ⟨⟨hb1, hb2⟩, -⟩ := ixP_decD b hb
    have hm1 := dMul_lt _ ha1 _ hb1
    have hm2 := h.L.lt (a % 32) ha2 (b % 32) hb2
    rw [mulC_eq_ixP, h.lab_ixP hm1 hm2]
    exact (h.val_mul ha1 ha2 hb1 hb2).symm
  one := h.lab_zero

theorem act_lab (u : Γ) (f g : ℕ → ℕ) (hf : ∀ i < 8, f i < 8) (hg : ∀ k < 32, g k < 32)
    (hD : ∀ i < 8, u * sElt eD i * u⁻¹ = sElt eD (f i))
    (hE : ∀ k < 32, u * eltE k * u⁻¹ = eltE (g k)) {c : ℕ} (hc : c < 128) :
    u * labD eD eltE c * u⁻¹ = labD eD eltE (ixP (f (decD c)) (g (c % 32))) := by
  obtain ⟨⟨hc1, hc2⟩, -⟩ := ixP_decD c hc
  rw [h.lab_ixP (hf _ hc1) (hg _ hc2)]
  calc u * labD eD eltE c * u⁻¹
      = (u * sElt eD (decD c) * u⁻¹) * (u * eltE (c % 32) * u⁻¹) := by
        simp only [labD]
        group
    _ = sElt eD (f (decD c)) * eltE (g (c % 32)) := by rw [hD _ hc1, hE _ hc2]

end DECtx

theorem conj_sElt (u : Γ) (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hfm : ∀ i < 8, ∀ j < 8, f (dMul i j) = dMul (f i) (f j)) (hflt : ∀ i < 8, f i < 8)
    (h1 : u * sElt eD 1 * u⁻¹ = sElt eD (f 1)) (h4 : u * sElt eD 4 * u⁻¹ = sElt eD (f 4)) :
    ∀ i < 8, u * sElt eD i * u⁻¹ = sElt eD (f i) := by
  have step : ∀ i < 8, ∀ j < 8, u * sElt eD i * u⁻¹ = sElt eD (f i) →
      u * sElt eD j * u⁻¹ = sElt eD (f j) →
      u * sElt eD (dMul i j) * u⁻¹ = sElt eD (f (dMul i j)) := by
    intro i hi j hj hi' hj'
    rw [← sElt_mul eD hi hj, hfm i hi j hj, ← sElt_mul eD (hflt i hi) (hflt j hj), ← hi', ← hj']
    group
  have P0 : u * sElt eD 0 * u⁻¹ = sElt eD (f 0) := by
    rw [sElt_zero, hf0, sElt_zero]
    group
  have P2 : u * sElt eD 2 * u⁻¹ = sElt eD (f 2) := by
    have := step 1 (by norm_num) 1 (by norm_num) h1 h1
    rwa [show dMul 1 1 = 2 by decide] at this
  have P3 : u * sElt eD 3 * u⁻¹ = sElt eD (f 3) := by
    have := step 1 (by norm_num) 2 (by norm_num) h1 P2
    rwa [show dMul 1 2 = 3 by decide] at this
  have P5 : u * sElt eD 5 * u⁻¹ = sElt eD (f 5) := by
    have := step 3 (by norm_num) 4 (by norm_num) P3 h4
    rwa [show dMul 3 4 = 5 by decide] at this
  have P6 : u * sElt eD 6 * u⁻¹ = sElt eD (f 6) := by
    have := step 2 (by norm_num) 4 (by norm_num) P2 h4
    rwa [show dMul 2 4 = 6 by decide] at this
  have P7 : u * sElt eD 7 * u⁻¹ = sElt eD (f 7) := by
    have := step 1 (by norm_num) 4 (by norm_num) h1 h4
    rwa [show dMul 1 4 = 7 by decide] at this
  intro i hi
  interval_cases i
  · exact P0
  · exact h1
  · exact P2
  · exact P3
  · exact h4
  · exact P5
  · exact P6
  · exact P7

theorem sElt_three : sElt eD 3 = (sElt eD 1)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [sElt_mul eD (by norm_num) (by norm_num), show dMul 1 3 = 0 by decide, sElt_zero]

end Lab

end CFSG.EvenSporadicStandard.Fin76b.W16
