module

public import CFSG.CGT.Stroth77.Section43CoreIII
public import CFSG.CGT.Stroth77.Section44CoreII

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth44Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t201 m)) {e : G}

@[expose] def t201iiiAction (heuv : e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t) (heu : e⁻¹ * dD.u * e = dD.u)
    (hec : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hea : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (heb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) : dD.EAction e :=
  dD.t201EAction (torusDiag _ ![-1, -1, -1]) 0
    (dD.conj_ofTorus_of_gens
      (by rw [hec, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
      (by rw [hea, torusDiag_gen, ofTorus_zsmul, ← a_eq]; simp)
      (by rw [heb, torusDiag_gen, ofTorus_zsmul, ← b_eq]; simp))
    heuv het heu (by rw [he, ofTorus_zero])

end StrothWeakTypeData

namespace Stroth44Core

section CaseIII

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem t201_iii_φe (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (x : Fin 3 → ℤ) :
    hE.φe (Torus.ofInt _ x) = Torus.ofInt _ ![-x 0, -x 1, -x 2] := by
  rw [hφe, torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t201_iii_φe_z (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) :
    hE.φe (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1] := by
  rw [om201_apply, t201_iii_φe dD hE hφe, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨0, by ring⟩, ⟨1, by ring⟩, ⟨1, by ring⟩⟩

theorem not_two_pow_dvd_odd {j : ℕ} (hj : j ≠ 0) {x : ℤ} (hx : Odd x) : ¬ (2 : ℤ) ^ j ∣ x := by
  intro h
  obtain ⟨r, hr⟩ := hx
  have := dvd_trans (dvd_pow_self 2 hj) h
  omega

theorem t201_iii_faithful (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) :
    ∀ i j l, (∀ v, hE.φe v = (StrothTypeIndex.t201 m).action.d8Act i j l v) → False := by
  intro i j l h
  have h1 := h (Torus.ofInt _ ![0, 1, 0])
  rw [t201_iii_φe dD hE hφe] at h1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hP : (0 : ℤ) < 2 ^ k := by positivity
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at h1
  · rw [t201_ofInt_eq_iff] at h1
    obtain ⟨-, h0, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    have h4 : (4 : ℤ) ∣ _ := dvd_trans ⟨2 * 2 ^ k, by ring⟩ h0
    omega
  · rw [t201_φu, t201_ofInt_eq_iff] at h1
    obtain ⟨-, h0, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    exact not_two_pow_dvd_odd (by omega) ⟨0, by ring⟩ h0
  · rw [t201_φt, t201_ofInt_eq_iff] at h1
    obtain ⟨-, h0, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    have e : (4 : ℤ) * 0 + (2 ^ (k + 1 + 1) - 1) * 1 - (2 + 2 ^ (k + 1 + 1)) * 0 - -1 =
        4 * 2 ^ k := by ring
    rw [e, show (2 : ℤ) ^ (k + 1 + 2) = 8 * 2 ^ k by ring] at h0
    have h8 := Int.le_of_dvd (by positivity) h0
    linarith
  · rw [t201_φu, t201_φt, t201_ofInt_eq_iff] at h1
    obtain ⟨-, h0, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    exact not_two_pow_dvd_odd (by omega) ⟨-1 - 2 * 2 ^ k, by ring⟩ h0
  · rw [t201_φuv, t201_ofInt_eq_iff] at h1
    obtain ⟨h0, -, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    exact not_two_pow_dvd_odd (by omega) ⟨0, by ring⟩ h0
  · rw [t201_φu, t201_φuv, t201_ofInt_eq_iff] at h1
    obtain ⟨h0, -, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    exact not_two_pow_dvd_odd (by omega) ⟨0, by ring⟩ h0
  · rw [t201_φt, t201_φuv, t201_ofInt_eq_iff] at h1
    obtain ⟨h0, -, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    exact not_two_pow_dvd_odd (by omega) ⟨-1 + 2 * 2 ^ k, by ring⟩ h0
  · rw [t201_φu, t201_φt, t201_φuv, t201_ofInt_eq_iff] at h1
    obtain ⟨-, h0, -⟩ := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    exact not_two_pow_dvd_odd (by omega)
      ⟨-4 * 2 ^ k - 32 * (2 ^ k) ^ 2 - 32 * (2 ^ k) ^ 3, by ring⟩ h0

theorem t201_iii_h1 (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  hE.relIndex_S (t201_iii_faithful dD hE hm hφe)

theorem t201_iii_h2 (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) :
    e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  hE.e_not_mem (t201_iii_faithful dD hE hm hφe)

theorem t201_e_mem_CSc₁ (hm : 1 ≤ m)
    (hc₁ : hE.φe (om201 m ![1, 0, 0]) = om201 m ![1, 0, 0]) {y : G}
    (hyS : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hyc : y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y) :
    ∃ (v : Torus (StrothTypeIndex.t201 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k := by
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyc
    obtain ⟨rfl, rfl⟩ := t201_comm_c₁ dD hm hyc
    exact ⟨v, l, false, rfl⟩
  · simp only [bpow, ↓reduceIte] at hyc
    rw [c_pow_om, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
      mul_left_inj] at hyc
    obtain ⟨rfl, rfl⟩ := t201_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
    exact ⟨v, l, true, rfl⟩

theorem t201_iii_φe_c₁ (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) :
    hE.φe (om201 m ![1, 0, 0]) = om201 m ![1, 0, 0] := by
  rw [om201_apply, t201_iii_φe dD hE hφe, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨1, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t201_iii_hC15 (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (hve : hE.ve = 0) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ∈ D ⊔ Subgroup.zpowers dD.u ∨ y * e ∈ D ⊔ Subgroup.zpowers dD.u := by
  intro y hy hyc
  obtain ⟨v, l, k, rfl⟩ := t201_e_mem_CSc₁ dD hE hm (t201_iii_φe_c₁ dD hE hm hφe) hy hyc
  have hmem : dD.ofTorus v * dD.d8 false false l ∈ D ⊔ Subgroup.zpowers dD.u := by
    refine mul_mem (Subgroup.mem_sup_left (dD.ofTorus_mem v)) (Subgroup.mem_sup_right ?_)
    cases l
    · rw [dD.d8_fff]; exact one_mem _
    · rw [dD.d8_fft]; exact Subgroup.mem_zpowers _
  cases k
  · left
    simpa [bpow] using hmem
  · right
    simp only [bpow, ↓reduceIte]
    rw [mul_assoc, hE.mul_self, hve, dD.ofTorus_zero, mul_one]
    exact hmem

end CaseIII

section Du

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))

open StrothWeakTypeData

theorem t201_mem_Du {y : G} (hy : y ∈ D ⊔ Subgroup.zpowers dD.u) :
    ∃ (v : Torus (StrothTypeIndex.t201 m).k) (l : Bool),
      y = dD.ofTorus v * dD.d8 false false l := by
  have hle : Subgroup.zpowers dD.u ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.zpowers_le).2 dD.u_mem
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle, Set.mem_mul] at hy
  obtain ⟨x, hx, w, hw, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hu2 : dD.u ^ (2 : ℤ) = 1 := by rw [zpow_two, dD.u_sq]
  refine ⟨v, decide (n % 2 = 1), ?_⟩
  have hn : dD.u ^ n = dD.u ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul, hu2, one_zpow, mul_one]
  rw [hn]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp [dD.d8_fft, dD.d8_fff]

theorem t201_hC13 (hm : 1 ≤ m) : ∀ E : Subgroup G, E ≤ D ⊔ Subgroup.zpowers dD.u →
    (∀ y ∈ E, y * y = 1) → Nat.card E = 8 → (dD.c : G) ^ 2 ^ (m - 1) ∈ E := by
  classical
  intro E hE hinv hcard
  by_contra hc₁
  rw [c_pow_om] at hc₁
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have hD1 : ∀ d ∈ E, d ∈ D → ∃ a b c : Bool,
      d = dD.ofTorus (om201 m ![(a.toNat : ℤ), b.toNat, c.toNat]) := by
    intro d hd hdD
    obtain ⟨ε, hε, rfl⟩ := t201_eq_om_of_mul_self dD hm hdD (hinv d hd)
    refine ⟨decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1), ?_⟩
    congr 2
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  by_cases hD : ∃ e₀ ∈ E, e₀ ∉ D
  · obtain ⟨e₀, he₀, he₀D⟩ := hD
    obtain ⟨v₀, l₀, hv₀⟩ := t201_mem_Du dD (hE he₀)
    have hl₀ : l₀ = true := by
      cases l₀
      · exact absurd (by rw [hv₀, dD.d8_fff, mul_one]; exact dD.ofTorus_mem v₀) he₀D
      · rfl
    subst hl₀
    set δ : G := if dD.ofTorus (om201 m ![0, 1, 1]) ∈ E then dD.ofTorus (om201 m ![0, 1, 1])
      else dD.ofTorus (om201 m ![1, 1, 1]) with hδ
    have hfix : ∀ d ∈ E, d ∈ D → d = 1 ∨ d = δ := by
      intro d hd hdD
      obtain ⟨a, b, c, rfl⟩ := hD1 d hd hdD
      have hc := hcomm _ hd _ he₀
      rw [hv₀] at hc
      have hω := (dD.nf_commute_iff v₀ _ false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, t201_φu_om, om201_eq_iff hm] at hω
      have hbc : c = b := by
        have h1 := hω 1
        revert h1
        cases a <;> cases b <;> cases c <;> decide
      subst hbc
      have hprod : dD.ofTorus (om201 m ![1, 1, 1]) * dD.ofTorus (om201 m ![0, 1, 1]) =
          dD.ofTorus (om201 m ![1, 0, 0]) := by
        rw [← dD.ofTorus_add, om201_add, dD.ofTorus_inj.eq_iff, om201_eq_iff hm]
        decide
      cases a <;> cases c
      · left
        rw [show (om201 m ![((false : Bool).toNat : ℤ), (false : Bool).toNat,
          (false : Bool).toNat]) = om201 m 0 by congr 1; funext i; fin_cases i <;> rfl,
          show om201 m 0 = 0 by
            rw [om201, ← Torus.ofInt_zero]; congr 1; funext i; simp, dD.ofTorus_zero]
      · right
        simp only [hδ]
        rw [if_pos (by simpa using hd)]
        simp
      · exact absurd (by simpa using hd) hc₁
      · right
        simp only [hδ]
        rw [if_neg (fun h' => hc₁ (by rw [← hprod]; exact mul_mem (by simpa using hd) h'))]
        simp
    let f : Bool × Bool → G := fun w => (if w.1 then δ else 1) * (if w.2 then e₀ else 1)
    have hcov : ∀ y ∈ E, ∃ w, f w = y := by
      intro y hy
      by_cases hyD : y ∈ D
      · rcases hfix y hy hyD with h | h
        · exact ⟨(false, false), by simp [f, h]⟩
        · exact ⟨(true, false), by simp [f, h]⟩
      · obtain ⟨v, l, hv⟩ := t201_mem_Du dD (hE hy)
        have hl : l = true := by
          cases l
          · exact absurd (by rw [hv, dD.d8_fff, mul_one]; exact dD.ofTorus_mem v) hyD
          · rfl
        subst hl
        have hmem : y * e₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        rcases hfix (y * e₀⁻¹) (mul_mem hy (inv_mem he₀)) hmem with h | h
        · exact ⟨(false, true), by simp [f, mul_inv_eq_one.mp h]⟩
        · exact ⟨(true, true), by simp [f, mul_inv_eq_iff_eq_mul.mp h]⟩
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard] at hle
    have h4 : Nat.card (Bool × Bool) = 4 := by simp [Nat.card_eq_fintype_card]
    omega
  · push Not at hD
    let f : {w : Bool × Bool × Bool // w ≠ (true, false, false)} → G := fun w =>
      dD.ofTorus (om201 m ![(w.1.1.toNat : ℤ), w.1.2.1.toNat, w.1.2.2.toNat])
    have hcov : ∀ y ∈ E, ∃ w, f w = y := by
      intro y hy
      obtain ⟨a, b, c, hd⟩ := hD1 y hy (hD y hy)
      refine ⟨⟨(a, b, c), fun h => hc₁ ?_⟩, hd.symm⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [hd] at hy
      exact hy
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard] at hle
    have h7 : Nat.card {w : Bool × Bool × Bool // w ≠ (true, false, false)} = 7 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega

end Du

section CaseIIIF

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem om201_zero : om201 m 0 = 0 := by
  rw [om201, ← Torus.ofInt_zero]
  congr 1
  funext i
  simp

theorem za_om : (dD.a : G) ^ 2 ^ (m + 1) = dD.ofTorus (om201 m ![0, 1, 0]) := by
  rw [za_eq, om201_apply]
  congr 2
  funext i
  fin_cases i <;> simp

theorem zb_om : (dD.b : G) ^ 2 ^ (m + 1) = dD.ofTorus (om201 m ![0, 0, 1]) := by
  rw [zb_eq, om201_apply]
  congr 2
  funext i
  fin_cases i <;> simp

theorem om201_ne_one (hm : 1 ≤ m) {ε : Fin 3 → ℤ} (i : Fin 3) (hi : ¬ ε i ≡ 0 [ZMOD 2]) :
    dD.ofTorus (om201 m ε) ≠ 1 := by
  rw [← dD.ofTorus_zero, ← om201_zero, Ne, dD.ofTorus_inj.eq_iff, om201_eq_iff hm]
  exact fun h => hi (h i)

theorem om201_mul_self (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    dD.ofTorus (om201 m ε) * dD.ofTorus (om201 m ε) = 1 := by
  rw [← dD.ofTorus_add, om201_add, ← dD.ofTorus_zero, ← om201_zero, dD.ofTorus_inj.eq_iff,
    om201_eq_iff hm]
  intro i
  exact Int.modEq_zero_iff_dvd.mpr ⟨ε i, by simp only [Pi.add_apply]; ring⟩

theorem t201_iii_φe_om (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (ε : Fin 3 → ℤ) : hE.φe (om201 m ε) = om201 m ε := by
  have h : hE.φe (om201 m ε) = om201 m (-ε) := by
    rw [om201, om201, t201_iii_φe dD hE hφe]
    congr 1
    funext i
    fin_cases i <;> simp [neg_mul]
  rw [h, om201_eq_iff hm]
  intro i
  exact Int.modEq_iff_dvd.mpr ⟨ε i, by simp only [Pi.neg_apply]; ring⟩

theorem t201_iii_comm_mul_e (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (ε : Fin 3 → ℤ) {d : G} (hd : d ∈ D) :
    dD.ofTorus (om201 m ε) * (d * e) = d * e * dD.ofTorus (om201 m ε) := by
  rw [← mul_assoc, mem_comm dD (dD.ofTorus_mem _) hd, mul_assoc, mul_assoc d e,
    hE.e_mul_ofTorus, t201_iii_φe_om dD hE hm hφe]

theorem t201_iii_hF (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (hve : hE.ve = 0)
    (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) :
    Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv} ≤
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * dD.a * dD.b * e} ∧
      (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv},
        y * y = 1) ∧
      Nat.card (Subgroup.closure
        {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv}) = 8 := by
  have he : e * e = 1 := by rw [hE.mul_self, hve, dD.ofTorus_zero]
  have hza := om201_mul_self dD hm ![0, 1, 0]
  have hzb := om201_mul_self dD hm ![0, 0, 1]
  rw [← za_om] at hza
  rw [← zb_om] at hzb
  have hab : (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) =
      (dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) :=
    mem_comm dD (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _)
  have hauv : (dD.a : G) ^ 2 ^ (m + 1) * dD.uv = dD.uv * (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [za_om, dD.uv_mul_ofTorus, t201_φuv_om hm]
    exact congrArg (· * dD.uv) (congrArg dD.ofTorus ((om201_eq_iff hm _ _).mpr (by decide)))
  have hbuv : (dD.b : G) ^ 2 ^ (m + 1) * dD.uv = dD.uv * (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [zb_om, dD.uv_mul_ofTorus, t201_φuv_om hm]
    exact congrArg (· * dD.uv) (congrArg dD.ofTorus ((om201_eq_iff hm _ _).mpr (by decide)))
  have hD : ∀ (a : Bool) (x : G), x ∈ D → (if a = true then x else 1) ∈ D := by
    intro a x hx
    split
    · exact hx
    · exact one_mem _
  have hind : ∀ a b c : Bool, bpow ((dD.a : G) ^ 2 ^ (m + 1)) a *
      bpow ((dD.b : G) ^ 2 ^ (m + 1)) b * bpow dD.uv c = 1 →
        a = false ∧ b = false ∧ c = false := by
    intro a b c h
    cases c
    · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at h
      cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] at h
      · exact ⟨rfl, rfl, rfl⟩
      · exact absurd h (by rw [zb_om]; exact om201_ne_one dD hm 2 (by decide))
      · exact absurd h (by rw [za_om]; exact om201_ne_one dD hm 1 (by decide))
      · exact absurd h (by rw [z_om]; exact om201_ne_one dD hm 1 (by decide))
    · exfalso
      simp only [bpow, ↓reduceIte] at h
      apply uv_not_mem dD hm
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (mul_mem (hD a _ (D.pow_mem dD.a.2 _)) (hD b _ (D.pow_mem dD.b.2 _)))
  obtain ⟨hinv, hcard⟩ := Stroth43Core.closure_three_inv hza hzb dD.uv_sq hab hauv hbuv hind
  refine ⟨?_, hinv, hcard⟩
  have hd : (dD.c : G) ^ 2 ^ (m - 1) * dD.a * dD.b ∈ D :=
    mul_mem (mul_mem (D.pow_mem dD.c.2 _) dD.a.2) dD.b.2
  have hd_eq : (dD.c : G) ^ 2 ^ (m - 1) * dD.a * dD.b =
      dD.ofTorus (Torus.ofInt _ ![2 ^ (m - 1), 1, 1]) := by
    have ha := a_pow_eq dD 1
    have hb := b_pow_eq dD 1
    rw [pow_one] at ha hb
    rw [c_pow_eq, ha, hb, ofTorus_ofInt_mul, ofTorus_ofInt_mul]
    congr 2
    funext i
    fin_cases i <;> simp
  have hinv' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have heuv' : e * dD.uv = dD.ofTorus hE.wuv * dD.uv * e := by
    calc e * dD.uv = e⁻¹ * dD.uv * e * e := by
          rw [hinv', mul_assoc (e * dD.uv) e e, he, mul_one]
      _ = dD.ofTorus hE.wuv * dD.uv * e := by rw [hE.conj_uv]
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · rw [za_om]
    exact t201_iii_comm_mul_e dD hE hm hφe _ hd
  · rw [zb_om]
    exact t201_iii_comm_mul_e dD hE hm hφe _ hd
  · rw [hd_eq, ← mul_assoc, dD.uv_mul_ofTorus, mul_assoc (dD.ofTorus _) e dD.uv, heuv',
      ← mul_assoc, ← mul_assoc, ← dD.ofTorus_add, mul_left_inj, mul_left_inj,
      dD.ofTorus_inj.eq_iff, hwuv, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    simp only [Nat.add_sub_cancel, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨2, by ring⟩, ⟨-1 - 2 * 2 ^ k, by ring⟩, ⟨0, by ring⟩⟩

end CaseIIIF

section NF

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem t201_ofInt_mul (x y : Fin 3 → ℤ) (z : G) :
    dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus (Torus.ofInt _ y) * z) =
      dD.ofTorus (Torus.ofInt _ (x + y)) * z := by
  rw [← mul_assoc, ofTorus_ofInt_mul]

theorem t201_uv_mul_ofInt (x : Fin 3 → ℤ) (z : G) :
    dD.uv * (dD.ofTorus (Torus.ofInt _ x) * z) = dD.ofTorus (Torus.ofInt _
      ![-3 * x 0 + x 1 + x 2,
        -4 * x 0 + x 1 + (2 + 3 * 2 ^ (m + 1) + 2 ^ (m + 1) * 2 ^ (m + 1)) * x 2,
        -4 * x 0 + (2 + 2 ^ (m + 1)) * x 1 + x 2]) * (dD.uv * z) := by
  rw [dD.uv_mul_ofTorus_mul, t201_φuv]

theorem t201_uv_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.uv * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _
      ![-3 * x 0 + x 1 + x 2,
        -4 * x 0 + x 1 + (2 + 3 * 2 ^ (m + 1) + 2 ^ (m + 1) * 2 ^ (m + 1)) * x 2,
        -4 * x 0 + (2 + 2 ^ (m + 1)) * x 1 + x 2]) * dD.uv := by
  rw [dD.uv_mul_ofTorus, t201_φuv]

theorem t201_t_mul_ofInt (x : Fin 3 → ℤ) (z : G) :
    dD.t * (dD.ofTorus (Torus.ofInt _ x) * z) = dD.ofTorus (Torus.ofInt _
      ![x 0 - (1 + 2 ^ (m + 1)) * x 2,
        4 * x 0 + (2 ^ (m + 1) - 1) * x 1 - (2 + 2 ^ (m + 1)) * x 2,
        -(1 + 2 ^ (m + 1)) * x 2]) * (dD.t * z) := by
  rw [dD.t_mul_ofTorus_mul, t201_φt]

theorem t201_t_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.t * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _
      ![x 0 - (1 + 2 ^ (m + 1)) * x 2,
        4 * x 0 + (2 ^ (m + 1) - 1) * x 1 - (2 + 2 ^ (m + 1)) * x 2,
        -(1 + 2 ^ (m + 1)) * x 2]) * dD.t := by
  rw [dD.t_mul_ofTorus, t201_φt]

theorem t201_u_mul_ofInt (x : Fin 3 → ℤ) (z : G) :
    dD.u * (dD.ofTorus (Torus.ofInt _ x) * z) =
      dD.ofTorus (Torus.ofInt _ ![x 0, x 2, x 1]) * (dD.u * z) := by
  rw [dD.u_mul_ofTorus_mul, t201_φu]

theorem t201_u_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.u * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ ![x 0, x 2, x 1]) * dD.u := by
  rw [dD.u_mul_ofTorus, t201_φu]

theorem t201_ofInt_mul_eq {x y : Fin 3 → ℤ} (z : G) (h0 : (2 : ℤ) ^ m ∣ y 0 - x 0)
    (h1 : (2 : ℤ) ^ (m + 2) ∣ y 1 - x 1) (h2 : (2 : ℤ) ^ (m + 2) ∣ y 2 - x 2) :
    dD.ofTorus (Torus.ofInt _ x) * z = dD.ofTorus (Torus.ofInt _ y) * z := by
  rw [(t201_ofInt_eq_iff x y).mpr ⟨h0, h1, h2⟩]

theorem t201_ofInt_eq {x y : Fin 3 → ℤ} (h0 : (2 : ℤ) ^ m ∣ y 0 - x 0)
    (h1 : (2 : ℤ) ^ (m + 2) ∣ y 1 - x 1) (h2 : (2 : ℤ) ^ (m + 2) ∣ y 2 - x 2) :
    dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ y) := by
  rw [(t201_ofInt_eq_iff x y).mpr ⟨h0, h1, h2⟩]

theorem t201_eq_of_nf {A B : G}
    (h : dD.ofTorus (Torus.ofInt _ 0) * (A * 1) = dD.ofTorus (Torus.ofInt _ 0) * (B * 1)) :
    A = B := by
  simpa [Torus.ofInt_zero, dD.ofTorus_zero] using h

theorem t201_iii_φe' (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (x : Fin 3 → ℤ) :
    hE.φe (Torus.ofInt _ x) = Torus.ofInt _ (-x) := by
  rw [hφe, torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t201_iii_e_mul_self (hve : hE.ve = 0) : e * e = 1 := by
  rw [hE.mul_self, hve, dD.ofTorus_zero]

theorem t201_iii_e_inv (hve : hE.ve = 0) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (t201_iii_e_mul_self dD hE hve)

theorem t201_iii_e_mul_e (hve : hE.ve = 0) (z : G) : e * (e * z) = z := by
  rw [← mul_assoc, t201_iii_e_mul_self dD hE hve, one_mul]

theorem t201_iii_e_mul_ofInt (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (x : Fin 3 → ℤ) (z : G) :
    e * (dD.ofTorus (Torus.ofInt _ x) * z) = dD.ofTorus (Torus.ofInt _ (-x)) * (e * z) := by
  rw [← mul_assoc, hE.e_mul_ofTorus, t201_iii_φe' dD hE hφe, mul_assoc]

theorem t201_iii_e_mul_ofInt' (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (x : Fin 3 → ℤ) :
    e * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ (-x)) * e := by
  rw [hE.e_mul_ofTorus, t201_iii_φe' dD hE hφe]

theorem t201_iii_e_mul_uv (hve : hE.ve = 0) (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) (z : G) :
    e * (dD.uv * z) = dD.ofTorus (Torus.ofInt _ ![2, 2, 2]) * (dD.uv * (e * z)) := by
  have h := hE.conj_uv
  rw [t201_iii_e_inv dD hE hve, hwuv] at h
  calc e * (dD.uv * z) = e * dD.uv * e * (e * z) := by
        rw [mul_assoc (e * dD.uv) e, t201_iii_e_mul_e dD hE hve, mul_assoc]
    _ = _ := by rw [h, mul_assoc]

theorem t201_iii_e_mul_uv' (hve : hE.ve = 0) (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) :
    e * dD.uv = dD.ofTorus (Torus.ofInt _ ![2, 2, 2]) * (dD.uv * e) := by
  have h := t201_iii_e_mul_uv dD hE hve hwuv 1
  rwa [mul_one, mul_one] at h

theorem t201_iii_e_mul_t (hve : hE.ve = 0) (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0]) (z : G) :
    e * (dD.t * z) = dD.ofTorus (Torus.ofInt _ ![0, -2, 0]) * (dD.t * (e * z)) := by
  have h := hE.conj_t
  rw [t201_iii_e_inv dD hE hve, hwt] at h
  calc e * (dD.t * z) = e * dD.t * e * (e * z) := by
        rw [mul_assoc (e * dD.t) e, t201_iii_e_mul_e dD hE hve, mul_assoc]
    _ = _ := by rw [h, mul_assoc]

theorem t201_iii_e_mul_t' (hve : hE.ve = 0) (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0]) :
    e * dD.t = dD.ofTorus (Torus.ofInt _ ![0, -2, 0]) * (dD.t * e) := by
  have h := t201_iii_e_mul_t dD hE hve hwt 1
  rwa [mul_one, mul_one] at h

theorem t201_iii_e_mul_u (hve : hE.ve = 0) (z : G) : e * (dD.u * z) = dD.u * (e * z) := by
  have h := hE.conj_u
  rw [t201_iii_e_inv dD hE hve] at h
  calc e * (dD.u * z) = e * dD.u * e * (e * z) := by
        rw [mul_assoc (e * dD.u) e, t201_iii_e_mul_e dD hE hve, mul_assoc]
    _ = _ := by rw [h]

theorem t201_iii_e_mul_u' (hve : hE.ve = 0) : e * dD.u = dD.u * e := by
  have h := t201_iii_e_mul_u dD hE hve 1
  rwa [mul_one, mul_one] at h

end NF

set_option hygiene false in
local macro "t201_iii_rels" : tactic => `(tactic| (
  have r1 := t201_iii_e_mul_ofInt dD hE hφe
  have r1' := t201_iii_e_mul_ofInt' dD hE hφe
  have r2 := t201_iii_e_mul_uv dD hE hve hwuv
  have r2' := t201_iii_e_mul_uv' dD hE hve hwuv
  have r3 := t201_iii_e_mul_t dD hE hve hwt
  have r3' := t201_iii_e_mul_t' dD hE hve hwt
  have r4 := t201_iii_e_mul_u dD hE hve
  have r4' := t201_iii_e_mul_u' dD hE hve
  have r5 := t201_iii_e_mul_e dD hE hve
  have r6 := t201_iii_e_inv dD hE hve
  have r7 := t201_iii_e_mul_self dD hE hve))

set_option hygiene false in
local macro "t201_nf" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [mul_inv_rev, dD.uv_inv, dD.t_inv, dD.u_inv, ofTorus_ofInt_inv,
    mul_assoc, t201_ofInt_mul, ofTorus_ofInt_mul, t201_uv_mul_ofInt, t201_t_mul_ofInt,
    t201_u_mul_ofInt, t201_uv_mul_ofInt', t201_t_mul_ofInt', t201_u_mul_ofInt', dD.uv_mul_uv,
    dD.t_mul_t, dD.u_mul_u, dD.t_mul_uv, dD.u_mul_uv, dD.u_mul_t, dD.uv_sq, dD.t_sq, dD.u_sq,
    dD.uv_comm_t.symm, dD.uv_comm_u.symm, dD.u_mul_t_eq, one_mul, mul_one] $[$loc]?)

set_option hygiene false in
local macro "t201_iii_nf" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [mul_inv_rev, r6, dD.uv_inv, dD.t_inv, dD.u_inv, ofTorus_ofInt_inv,
    mul_assoc, t201_ofInt_mul, ofTorus_ofInt_mul, t201_uv_mul_ofInt, t201_t_mul_ofInt,
    t201_u_mul_ofInt, t201_uv_mul_ofInt', t201_t_mul_ofInt', t201_u_mul_ofInt', dD.uv_mul_uv,
    dD.t_mul_t, dD.u_mul_u, dD.t_mul_uv, dD.u_mul_uv, dD.u_mul_t, dD.uv_sq, dD.t_sq, dD.u_sq,
    dD.uv_comm_t.symm, dD.uv_comm_u.symm, dD.u_mul_t_eq, one_mul, mul_one, r1, r1', r2, r2', r3,
    r3', r4, r4', r5, r7] $[$loc]?)

local macro "t201_coord" : tactic => `(tactic| first
  | (refine t201_ofInt_mul_eq _ _ ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_succ, Nat.cast_pow, Nat.cast_ofNat])
  | (refine t201_ofInt_eq _ ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_succ, Nat.cast_pow, Nat.cast_ofNat]))

section CaseIIIC2

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem t201_iii_conj_te (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (hve : hE.ve = 0)
    (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0])
    (x : Fin 3 → ℤ)
    (h2 : dD.ofTorus (Torus.ofInt _ x) * (dD.t * e) *
      (dD.ofTorus (Torus.ofInt _ x) * (dD.t * e)) = 1) :
    (dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ m - 1]) * (dD.uv * e))⁻¹ *
        (dD.ofTorus (Torus.ofInt _ x) * (dD.t * e)) *
        (dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ m - 1]) * (dD.uv * e)) =
      dD.ofTorus (Torus.ofInt _ x) * (dD.t * e) * dD.ofTorus (om201 m ![0, 1, 1]) := by
  obtain ⟨x0, x1, x2, rfl⟩ : ∃ a b c : ℤ, x = ![a, b, c] :=
    ⟨x 0, x 1, x 2, by funext i; fin_cases i <;> rfl⟩
  t201_iii_rels
  t201_iii_nf at h2
  have hc := (ofTorus_ofInt_eq_one_iff dD _).mp h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  obtain ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := hc
  obtain ⟨r, rfl⟩ : ∃ r, x2 = 4 * 2 ^ k * r := by
    have e1 : x2 = 2 * 2 ^ k * (4 * c2 - c0) := by linear_combination hc2 - hc0
    have e2 : (4 * c2 - c0) * (1 + 2 * 2 ^ k) = 2 * c2 := by
      have h4P : (4 * 2 ^ k : ℤ) ≠ 0 := by positivity
      apply mul_left_cancel₀ h4P
      linear_combination hc2 - (2 + 4 * 2 ^ k) * e1
    exact ⟨c2 - 2 ^ k * (4 * c2 - c0), by linear_combination e1 + 2 * 2 ^ k * e2⟩
  obtain ⟨s, rfl⟩ : ∃ s, x1 = 2 * s + 1 := by
    refine ⟨2 * 2 ^ k * c1 + x0 + 2 ^ k * x1 - (2 + 4 * 2 ^ k) * 2 ^ k * r + 2 * 2 ^ k - 1, ?_⟩
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    linear_combination hc1
  obtain rfl : x0 = s + 1 - 2 * 2 ^ k * s - 3 * 2 ^ k + 2 * 2 ^ k * r + 4 * (2 ^ k) ^ 2 * r -
      2 * 2 ^ k * c1 := by
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination -hc1
  rw [om201_apply]
  apply t201_eq_of_nf dD
  t201_iii_nf
  t201_coord <;> (try simp only [Nat.add_sub_cancel])
  · exact ⟨6 + 4 * 2 ^ k + 2 * c1 + 2 * s - 4 * 2 ^ k * r, by ring⟩
  · exact ⟨3 - 7 * 2 ^ k + c1 + s + 4 * 2 ^ k * r + 4 * (2 ^ k) ^ 2 + 8 * (2 ^ k) ^ 2 * r +
      16 * (2 ^ k) ^ 3, by ring⟩
  · exact ⟨3 + 2 ^ k + c1 + 2 * s - 2 * 2 ^ k * r + 4 * (2 ^ k) ^ 2, by ring⟩

theorem t201_iii_conj_uvte (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (hve : hE.ve = 0) (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2])
    (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0]) (x : Fin 3 → ℤ)
    (h2 : dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.t * e)) *
      (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.t * e))) = 1) :
    (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * (dD.uv * e))⁻¹ *
        (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.t * e))) *
        (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * (dD.uv * e)) =
      dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.t * e)) * dD.ofTorus (om201 m ![0, 1, 1]) := by
  obtain ⟨x0, x1, x2, rfl⟩ : ∃ a b c : ℤ, x = ![a, b, c] :=
    ⟨x 0, x 1, x 2, by funext i; fin_cases i <;> rfl⟩
  t201_iii_rels
  t201_iii_nf at h2
  have hc := (ofTorus_ofInt_eq_one_iff dD _).mp h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  obtain ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := hc
  have h4P : (4 * 2 ^ k : ℤ) ≠ 0 := by positivity
  obtain ⟨r₀, rfl⟩ : ∃ r₀, x1 = 2 * 2 ^ k * r₀ :=
    ⟨c0 + 2 * x1 + 2 * x2 + 4 + 16 * 2 ^ k, by linear_combination hc0⟩
  obtain ⟨r, rfl⟩ : ∃ r, r₀ = 2 * r := by
    refine ⟨c1 - x2 - 8 * 2 ^ k * x2 - 8 * (2 ^ k) ^ 2 * x2 - 2 - 24 * 2 ^ k - 80 * (2 ^ k) ^ 2 -
      64 * (2 ^ k) ^ 3 + 2 ^ k * r₀, ?_⟩
    apply mul_left_cancel₀ h4P
    linear_combination hc1
  obtain ⟨s, rfl⟩ : ∃ s, x2 = 2 * s + 1 := by
    refine ⟨2 * 2 ^ k * c2 + x0 + 4 * 2 ^ k * x0 - 2 ^ k * x2 - 4 * (2 ^ k) ^ 2 * x2 -
      2 * 2 ^ k * r + 4 * (2 ^ k) ^ 2 * r + 16 * (2 ^ k) ^ 3 * r - 4 * 2 ^ k - 16 * (2 ^ k) ^ 2 -
      32 * (2 ^ k) ^ 3 - 1, ?_⟩
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    linear_combination hc2
  have hx0 : (1 + 4 * 2 ^ k) * x0 = 1 + s + 2 * 2 ^ k * s + 5 * 2 ^ k + 8 * (2 ^ k) ^ 2 * s +
      20 * (2 ^ k) ^ 2 + 2 * 2 ^ k * r - 4 * (2 ^ k) ^ 2 * r - 16 * (2 ^ k) ^ 3 * r +
      32 * (2 ^ k) ^ 3 - 2 * 2 ^ k * c2 := by
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination -hc2
  rw [om201_apply]
  apply t201_eq_of_nf dD
  t201_iii_nf
  t201_coord <;> (try simp only [Nat.add_sub_cancel])
  · exact ⟨4 - 32 * (2 ^ k) + 2 * c2 + 2 * s - 8 * (2 ^ k) * c2 + 12 * (2 ^ k) * r -
      16 * (2 ^ k) * s - 32 * (2 ^ k) ^ 2 + 32 * (2 ^ k) ^ 2 * c2 - 32 * (2 ^ k) ^ 2 * r +
      64 * (2 ^ k) ^ 2 * x0 - 192 * (2 ^ k) ^ 3 - 128 * (2 ^ k) ^ 3 * s - 512 * (2 ^ k) ^ 4 +
      256 * (2 ^ k) ^ 4 * r, by linear_combination (-2 + 8 * (2 ^ k) - 32 * (2 ^ k) ^ 2) * hx0⟩
  · exact ⟨7 + 11 * (2 ^ k) + c2 + 4 * s - 4 * (2 ^ k) * c2 + 6 * (2 ^ k) * r - 4 * (2 ^ k) * s +
      32 * (2 ^ k) ^ 2 + 16 * (2 ^ k) ^ 2 * c2 - 16 * (2 ^ k) ^ 2 * r + 32 * (2 ^ k) ^ 2 * x0 -
      64 * (2 ^ k) ^ 3 - 64 * (2 ^ k) ^ 3 * s - 256 * (2 ^ k) ^ 4 + 128 * (2 ^ k) ^ 4 * r, by
      linear_combination (-4 + 16 * (2 ^ k) - 64 * (2 ^ k) ^ 2) * hx0⟩
  · exact ⟨2 - 9 * (2 ^ k) + c2 + s - 4 * (2 ^ k) * c2 + 8 * (2 ^ k) * r - 8 * (2 ^ k) * s -
      16 * (2 ^ k) ^ 2 + 16 * (2 ^ k) ^ 2 * c2 - 16 * (2 ^ k) ^ 2 * r + 32 * (2 ^ k) ^ 2 * x0 -
      96 * (2 ^ k) ^ 3 - 64 * (2 ^ k) ^ 3 * s - 256 * (2 ^ k) ^ 4 + 128 * (2 ^ k) ^ 4 * r, by
      linear_combination (-4 + 16 * (2 ^ k) - 64 * (2 ^ k) ^ 2) * hx0⟩

theorem t201_iii_conj_e (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) {i j l : Bool}
    (hj : j = false) :
    ∃ q : Torus (StrothTypeIndex.t201 m).k,
      (StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe q) = q + om201 m ![0, 1, 1] := by
  subst hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [om201_apply]
  cases i <;> cases l
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 2 ^ (k + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_iii_φe' dD hE hφe, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.neg_apply, Nat.add_sub_cancel, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨1, by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1 + 1), 0], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_iii_φe' dD hE hφe, t201_φu, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.neg_apply, Nat.add_sub_cancel, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨1, by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 0], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_iii_φe' dD hE hφe, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.neg_apply, Nat.add_sub_cancel, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨1, by ring⟩, ⟨1, by ring⟩, ⟨1 + 2 ^ k, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), -2 ^ (k + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_iii_φe' dD hE hφe, t201_φu, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.neg_apply, Nat.add_sub_cancel, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨1 + 3 * 2 ^ k + 4 * (2 ^ k) ^ 2, by ring⟩, ⟨-2 ^ k, by ring⟩⟩

theorem t201_ofTorus_mul_uv_ne_one (hm : 1 ≤ m) (X : Fin 3 → ℤ) :
    dD.ofTorus (Torus.ofInt _ X) * dD.uv ≠ 1 := by
  intro h
  apply uv_not_mem dD hm
  rw [eq_inv_of_mul_eq_one_right h]
  exact inv_mem (dD.ofTorus_mem _)

theorem t201_iii_hC2 (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (hve : hE.ve = 0)
    (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0]) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e, y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  intro y hy hy2 hy1 hyz
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  have hP : ∀ g ∈ ({dD.uv, dD.t, dD.u} : Set G),
      g ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure hg))
  have heS : e ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hDS : ∀ d ∈ D, d ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
    fun d hd => Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hy2 hy1 hyz ⊢
    obtain ⟨q, hq, hq'⟩ := t201_hC2 dD hm _ (dD.nf_mem v i j l) hy2 hy1 hyz
    exact ⟨q, Subgroup.mem_sup_left hq, hq'⟩
  simp only [bpow, ↓reduceIte] at hy2 hy1 hyz ⊢
  rw [z_om]
  cases j
  · obtain ⟨q, hq⟩ := t201_iii_conj_e dD hE hm hφe (i := i) (l := l) rfl
    refine ⟨dD.ofTorus q, hDS _ (dD.ofTorus_mem q), ofTorus_conj_nfe dD hE hq ?_⟩
    rw [t201_iii_φe_z dD hE hm hφe, t201_d8Act_z hm]
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  cases i <;> cases l
  · have h2 : dD.ofTorus (Torus.ofInt _ x) * (dD.t * e) *
        (dD.ofTorus (Torus.ofInt _ x) * (dD.t * e)) = 1 := by
      simpa only [dD.d8_ftf, mul_assoc] using hy2
    refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ m - 1]) * (dD.uv * e),
      mul_mem (hDS _ (dD.ofTorus_mem _)) (mul_mem (hP _ (by simp)) heS), ?_⟩
    rw [dD.d8_ftf, mul_assoc (dD.ofTorus _) dD.t e]
    exact t201_iii_conj_te dD hE hm hφe hve hwuv hwt x h2
  · exfalso
    t201_iii_rels
    rw [dD.d8_ftt] at hy2
    t201_iii_nf at hy2
    exact t201_ofTorus_mul_uv_ne_one dD hm _ hy2
  · have h2 : dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.t * e)) *
        (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.t * e))) = 1 := by
      simpa only [dD.d8_ttf, mul_assoc] using hy2
    refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * (dD.uv * e),
      mul_mem (hDS _ (dD.ofTorus_mem _)) (mul_mem (hP _ (by simp)) heS), ?_⟩
    rw [dD.d8_ttf, mul_assoc (dD.ofTorus _) (dD.uv * dD.t) e, mul_assoc dD.uv dD.t e]
    exact t201_iii_conj_uvte dD hE hm hφe hve hwuv hwt x h2
  · exfalso
    t201_iii_rels
    rw [dD.d8_ttt] at hy2
    t201_iii_nf at hy2
    exact t201_ofTorus_mul_uv_ne_one dD hm _ hy2

end CaseIIIC2

section CaseC7

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))

open StrothWeakTypeData

theorem t201_cls_uv (hm : 1 ≤ m) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.uv * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) = 1) :
    ∃ q ∈ D, q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) * q = dD.uv ∨
      q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) * q =
        (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv := by
  obtain ⟨x0, x1, x2, rfl⟩ : ∃ a b c : ℤ, x = ![a, b, c] :=
    ⟨x 0, x 1, x 2, by funext i; fin_cases i <;> rfl⟩
  t201_nf at h
  have hc := (ofTorus_ofInt_eq_one_iff dD _).mp h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  obtain ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := hc
  have h4P : (4 * 2 ^ k : ℤ) ≠ 0 := by positivity
  obtain rfl : x1 = (3 + 4 * 2 ^ k) * x2 - 2 * c1 + 2 * c2 := by
    apply mul_left_cancel₀ h4P
    linear_combination hc2 - hc1
  obtain rfl : c0 = 2 * c1 - (3 + 4 * 2 ^ k) * x2 := by
    apply mul_left_cancel₀ h4P
    linear_combination hc2 - 2 * hc0
  obtain rfl : x0 = (2 + 5 * 2 ^ k + 4 * (2 ^ k) ^ 2) * x2 - (1 + 2 * 2 ^ k) * c1 + c2 := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    linear_combination -hc0
  obtain ⟨b, rfl | rfl⟩ := Int.even_or_odd' x2
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, -b * (1 - 2 * 2 ^ k),
      -((3 + 4 * 2 ^ k) * b - c1 + c2) * (1 - 6 * 2 ^ k)]), dD.ofTorus_mem _, Or.inl ?_⟩
    apply t201_eq_of_nf dD
    t201_nf
    t201_coord <;> (try simp only [Nat.add_sub_cancel])
    · exact ⟨-13 * b + 4 * c1 - 3 * c2 - 16 * (2 ^ k) * b, by ring⟩
    · exact ⟨-21 * (2 ^ k) * b + 7 * (2 ^ k) * c1 - 7 * (2 ^ k) * c2 - 64 * (2 ^ k) ^ 2 * b +
        12 * (2 ^ k) ^ 2 * c1 - 12 * (2 ^ k) ^ 2 * c2 - 48 * (2 ^ k) ^ 3 * b, by ring⟩
    · exact ⟨-(2 ^ k) * b, by ring⟩
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, -b * (1 - 2 * 2 ^ k),
      -((3 + 4 * 2 ^ k) * b + 1 + 2 * 2 ^ k - c1 + c2) * (1 - 6 * 2 ^ k)]), dD.ofTorus_mem _,
      Or.inr ?_⟩
    rw [x_eq, dD.d8_tff]
    apply t201_eq_of_nf dD
    t201_nf
    t201_coord <;> (try simp only [Nat.add_sub_cancel])
    · exact ⟨-4 - 8 * (2 ^ k) - 13 * b + 4 * c1 - 3 * c2 - 16 * (2 ^ k) * b, by ring⟩
    · exact ⟨-7 * (2 ^ k) - 21 * (2 ^ k) * b + 7 * (2 ^ k) * c1 - 7 * (2 ^ k) * c2 -
        26 * (2 ^ k) ^ 2 - 64 * (2 ^ k) ^ 2 * b + 12 * (2 ^ k) ^ 2 * c1 - 12 * (2 ^ k) ^ 2 * c2 -
        24 * (2 ^ k) ^ 3 - 48 * (2 ^ k) ^ 3 * b, by ring⟩
    · exact ⟨-(2 ^ k) * b, by ring⟩

theorem t201_cls_u (hm : 1 ≤ m) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.u * (dD.ofTorus (Torus.ofInt _ x) * dD.u) = 1) :
    ∃ q ∈ D, q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.u) * q = dD.u ∨
      q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.u) * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  obtain ⟨x0, x1, x2, rfl⟩ : ∃ a b c : ℤ, x = ![a, b, c] :=
    ⟨x 0, x 1, x 2, by funext i; fin_cases i <;> rfl⟩
  t201_nf at h
  have hc := (ofTorus_ofInt_eq_one_iff dD _).mp h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  obtain ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩, -⟩ := hc
  obtain rfl : x0 = 2 ^ k * c0 := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    linear_combination hc0
  obtain rfl : x2 = 8 * 2 ^ k * c1 - x1 := by linear_combination hc1
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' c0
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, x1, 0]), dD.ofTorus_mem _, Or.inl ?_⟩
    apply t201_eq_of_nf dD
    t201_nf
    t201_coord <;> (try simp only [Nat.add_sub_cancel])
    · exact ⟨-j, by ring⟩
    · exact ⟨0, by ring⟩
    · exact ⟨-c1, by ring⟩
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, x1, 0]), dD.ofTorus_mem _, Or.inr ?_⟩
    rw [c_pow_eq]
    apply t201_eq_of_nf dD
    t201_nf
    t201_coord <;> (try simp only [Nat.add_sub_cancel])
    · exact ⟨-j, by ring⟩
    · exact ⟨0, by ring⟩
    · exact ⟨-c1, by ring⟩

theorem t201_rho_conj_t (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.ρ * (dD.ofTorus v * dD.t) * dD.ρ⁻¹ =
      dD.ofTorus ((StrothTypeIndex.t201 m).action.φρ ((StrothTypeIndex.t201 m).action.φρ v)) *
        dD.uv := by
  have ht : dD.ρ * dD.t * dD.ρ⁻¹ = dD.uv := by rw [← dD.conj_rho_uv]; group
  calc dD.ρ * (dD.ofTorus v * dD.t) * dD.ρ⁻¹ =
      (dD.ρ * dD.ofTorus v * dD.ρ⁻¹) * (dD.ρ * dD.t * dD.ρ⁻¹) := by group
    _ = _ := by rw [dD.rho_mul_ofTorus_mul_rho_inv, ht]

theorem t201_u_conj_uvt (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.u⁻¹ * (dD.ofTorus v * (dD.uv * dD.t)) * dD.u =
      dD.ofTorus ((StrothTypeIndex.t201 m).action.φu v) * dD.t := by
  rw [dD.u_inv]
  simp only [mul_assoc, dD.u_mul_ofTorus_mul, dD.u_mul_uv, dD.u_mul_t, dD.uv_mul_uv, dD.u_sq,
    mul_one]

theorem t201_t_conj_uvu (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.t⁻¹ * (dD.ofTorus v * (dD.uv * dD.u)) * dD.t =
      dD.ofTorus ((StrothTypeIndex.t201 m).action.φt v) * dD.u := by
  have htu : dD.t * dD.u * dD.t = dD.uv * dD.u := by
    rw [dD.t_u, mul_assoc (dD.u * dD.uv) dD.t dD.t, dD.t_sq, mul_one, ← dD.uv_comm_u]
  rw [dD.t_inv]
  calc dD.t * (dD.ofTorus v * (dD.uv * dD.u)) * dD.t
      = dD.t * dD.ofTorus v * dD.uv * (dD.u * dD.t) := by group
    _ = dD.ofTorus ((StrothTypeIndex.t201 m).action.φt v) * (dD.t * dD.uv) * (dD.u * dD.t) := by
        rw [dD.t_mul_ofTorus]; group
    _ = dD.ofTorus ((StrothTypeIndex.t201 m).action.φt v) * dD.uv * (dD.t * dD.u * dD.t) := by
        rw [← dD.uv_comm_t]; group
    _ = _ := by rw [htu, ← mul_assoc, mul_assoc _ dD.uv dD.uv, dD.uv_sq, mul_one]

theorem t201_hC7 (hm : 1 ≤ m) : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y = 1 →
    y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨ IsConj y ((dD.a : G) ^ 2 ^ (m + 1)) ∨
      IsConj y dD.uv ∨ IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) ∨
      IsConj y dD.u ∨ IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) := by
  intro y hy hy2 hy1
  have hconj : ∀ {y z : G} (q : G), q⁻¹ * y * q = z → IsConj y z := fun q h =>
    isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact h⟩
  have hsq : ∀ {z : G} (g : G), z * z = 1 → g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    intro z g h
    calc _ = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [h]; group
  have huv : ∀ v, dD.ofTorus v * dD.uv * (dD.ofTorus v * dD.uv) = 1 →
      IsConj (dD.ofTorus v * dD.uv) dD.uv ∨
        IsConj (dD.ofTorus v * dD.uv) ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) := by
    intro v hv
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    obtain ⟨q, -, hq | hq⟩ := t201_cls_uv dD hm x hv
    · exact Or.inl (hconj q hq)
    · exact Or.inr (hconj q hq)
  have hu : ∀ v, dD.ofTorus v * dD.u * (dD.ofTorus v * dD.u) = 1 →
      IsConj (dD.ofTorus v * dD.u) dD.u ∨
        IsConj (dD.ofTorus v * dD.u) ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) := by
    intro v hv
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    obtain ⟨q, -, hq | hq⟩ := t201_cls_u dD hm x hv
    · exact Or.inl (hconj q hq)
    · exact Or.inr (hconj q hq)
  have ht : ∀ v, dD.ofTorus v * dD.t * (dD.ofTorus v * dD.t) = 1 →
      IsConj (dD.ofTorus v * dD.t) dD.uv ∨
        IsConj (dD.ofTorus v * dD.t) ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) := by
    intro v hv
    have hc := t201_rho_conj_t dD v
    have h2 := hsq dD.ρ⁻¹ hv
    rw [inv_inv, hc] at h2
    have hc' : IsConj (dD.ofTorus v * dD.t) _ := isConj_iff.mpr ⟨dD.ρ, hc⟩
    rcases huv _ h2 with h | h
    · exact Or.inl (hc'.trans h)
    · exact Or.inr (hc'.trans h)
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  cases i <;> cases j <;> cases l
  · rw [dD.d8_fff, mul_one] at hy2 hy1 ⊢
    rcases t201_h3 dD hm _ (dD.ofTorus_mem v) hy2 hy1 with ⟨p, -, hp⟩ | ⟨g, -, hg⟩
    · exact Or.inl (hconj p hp)
    · exact Or.inr (Or.inl (hconj g hg))
  · rw [dD.d8_fft] at hy2 ⊢
    rcases hu v hy2 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [dD.d8_ftf] at hy2 ⊢
    rcases ht v hy2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exfalso
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    rw [dD.d8_ftt] at hy2
    t201_nf at hy2
    exact t201_ofTorus_mul_uv_ne_one dD hm _ hy2
  · rw [dD.d8_tff] at hy2 ⊢
    rcases huv v hy2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [dD.d8_tft] at hy2 ⊢
    have hc := t201_t_conj_uvu dD v
    have h2 := hsq dD.t hy2
    rw [hc] at h2
    rcases hu _ h2 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((hconj dD.t hc).trans h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((hconj dD.t hc).trans h)))))
  · rw [dD.d8_ttf] at hy2 ⊢
    have hc := t201_u_conj_uvt dD v
    have h2 := hsq dD.u hy2
    rw [hc] at h2
    rcases ht _ h2 with h | h
    · exact Or.inr (Or.inr (Or.inl ((hconj dD.u hc).trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((hconj dD.u hc).trans h))))
  · exfalso
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    rw [dD.d8_ttt] at hy2
    t201_nf at hy2
    exact t201_ofTorus_mul_uv_ne_one dD hm _ hy2

end CaseC7

section CaseIIIH9

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem t201_iii_comm_u (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (v₀ : Torus (StrothTypeIndex.t201 m).k) (k : Bool) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus v₀ * dD.d8 false false true * bpow e k) =
      dD.ofTorus v₀ * dD.d8 false false true * bpow e k * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ^ (m + 2) ∣ x 1 - (if k then -1 else 1) * x 2 := by
  have hc := (t201_e_comm_iff dD hE v₀ _ true k).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  cases k
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [t201_φu, t201_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1
  · simp only [↓reduceIte] at hc ⊢
    rw [t201_iii_φe' dD hE hφe, t201_φu, t201_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1

theorem t201_iii_comm_e (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (v₀ w : Torus (StrothTypeIndex.t201 m).k)
    (h : dD.ofTorus w * (dD.ofTorus v₀ * dD.d8 false false false * bpow e true) =
      dD.ofTorus v₀ * dD.d8 false false false * bpow e true * dD.ofTorus w) :
    dD.ofTorus w * dD.ofTorus w = 1 := by
  have hc := (t201_e_comm_iff dD hE v₀ w false true).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  rw [t201_iii_φe' dD hE hφe] at hc
  have h2 : Torus.ofInt (StrothTypeIndex.t201 m).k (-x) + Torus.ofInt _ x = 0 := by
    rw [← Torus.ofInt_add, neg_add_cancel, Torus.ofInt_zero]
  rw [hc] at h2
  rw [← dD.ofTorus_add, h2, dD.ofTorus_zero]

theorem t201_iii_h9 (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  classical
  intro X hX hab hcard
  have hDcard : Nat.card D = 2 ^ (m + (m + 2) + (m + 2)) := dD.card
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  have hnf : ∀ y ∈ X, ∃ (v : Torus (StrothTypeIndex.t201 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k := by
    intro y hy
    obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp (hX hy)
    exact t201_e_mem_CSc₁ dD hE hm (t201_iii_φe_c₁ dD hE hm hφe) hyS
      (Subgroup.mem_centralizer_singleton_iff.mp hyC)
  let rep : Bool × Bool → G := fun lk =>
    if h : ∃ y ∈ X, ∃ v, y = dD.ofTorus v * dD.d8 false false lk.1 * bpow e lk.2 then h.choose
    else 1
  have hrep : ∀ y ∈ X, ∀ v l k, y = dD.ofTorus v * dD.d8 false false l * bpow e k →
      y * (rep (l, k))⁻¹ ∈ D := by
    intro y hy v l k hyv
    have h : ∃ y ∈ X, ∃ v, y = dD.ofTorus v * dD.d8 false false l * bpow e k := ⟨_, hy, v, hyv⟩
    simp only [rep, h, dite_true]
    obtain ⟨-, v', hv'⟩ := h.choose_spec
    rw [hv', hyv]
    exact nfe_mul_inv_mem dD v v' l k
  have hrepX : ∀ lk, rep lk ∈ X := by
    intro lk
    simp only [rep]
    split_ifs with h
    · exact h.choose_spec.1
    · exact X.one_mem
  by_cases hD : ∀ x ∈ X, x ∈ D
  · haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge hD hcard.ge
  exfalso
  push Not at hD
  obtain ⟨x₁, hx₁, hx₁D⟩ := hD
  have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  by_cases hA : ∃ x₀ ∈ X, ∃ v₀ k₀, x₀ = dD.ofTorus v₀ * dD.d8 false false true * bpow e k₀
  · obtain ⟨x₀, hx₀, v₀, k₀, rfl⟩ := hA
    set γ : ℤ := if k₀ then -1 else 1 with hγ
    have hle := card_le_of_cover dD rep hrepX
      (fun y hy => by
        obtain ⟨v, l, k, hyv⟩ := hnf y hy
        exact ⟨(l, k), hrep y hy v l k hyv⟩)
      (fun s : ZMod (2 ^ m) × ZMod (2 ^ (m + 2)) =>
        Torus.ofInt _ ![(s.1.val : ℤ), γ * (s.2.val : ℤ), (s.2.val : ℤ)])
      (by
        intro d hd hdD
        obtain ⟨w, rfl⟩ := dD.exists_ofTorus hdD
        obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
        have h1 := t201_iii_comm_u dD hE hφe v₀ k₀ x (hcomm _ hd _ hx₀)
        refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((x 2 : ℤ) : ZMod (2 ^ (m + 2)))), ?_⟩
        congr 1
        rw [t201_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        have e0 := dvd_sub_val (2 ^ m) (x 0)
        have e2 := dvd_sub_val (2 ^ (m + 2)) (x 2)
        push_cast at e0 e2
        refine ⟨e0, ?_, e2⟩
        have := dvd_sub (Dvd.dvd.mul_left e2 γ) h1
        convert this using 1
        ring)
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
      Nat.card_zmod, h2, show 2 * 2 * (2 ^ m * 2 ^ (m + 2)) = 2 ^ (m + m + 4) by ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  ·
    push Not at hA
    obtain ⟨v₁, l₁, k₁, rfl⟩ := hnf _ hx₁
    have hl₁ : l₁ = false := by
      cases l₁
      · rfl
      · exact absurd rfl (hA _ hx₁ v₁ k₁)
    subst hl₁
    have hk₁ : k₁ = true := by
      cases k₁
      · exact absurd (by simpa [bpow, dD.d8_fff] using dD.ofTorus_mem v₁) hx₁D
      · rfl
    subst hk₁
    have hle := card_le_of_cover dD (fun k : Bool => rep (false, k)) (fun k => hrepX _)
      (fun y hy => by
        obtain ⟨v, l, k, hyv⟩ := hnf y hy
        have hl : l = false := by
          cases l
          · rfl
          · exact absurd hyv (hA y hy v k)
        subst hl
        exact ⟨k, hrep y hy v false k hyv⟩)
      (fun b : Bool × Bool × Bool =>
        om201 m ![(b.1.toNat : ℤ), b.2.1.toNat, b.2.2.toNat])
      (by
        intro d hd hdD
        obtain ⟨w, rfl⟩ := dD.exists_ofTorus hdD
        have hww := t201_iii_comm_e dD hE hφe v₁ w (hcomm _ hd _ hx₁)
        obtain ⟨ε, hε, hεeq⟩ := t201_eq_om_of_mul_self dD hm hdD hww
        refine ⟨(decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1)), ?_⟩
        rw [hεeq]
        congr 2
        funext i
        fin_cases i <;> simp [bool_toNat_cast_eq (hε _)])
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_prod, h2] at hle
    have h7 : 2 ^ 7 ≤ 2 ^ (m + (m + 2) + (m + 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end CaseIIIH9

section CaseIIIC11

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem t201_iii_conj_c₁ (hm : 2 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1])
    (v : Torus (StrothTypeIndex.t201 m).k) (l : Bool) :
    (dD.ofTorus (Torus.ofInt _ ![-2 ^ (m - 2), 0, 0]))⁻¹ *
        (dD.ofTorus v * dD.d8 false false l * e) *
        dD.ofTorus (Torus.ofInt _ ![-2 ^ (m - 2), 0, 0]) =
      (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 false false l * e) := by
  have hm1 : 1 ≤ m := by omega
  have hw : (StrothTypeIndex.t201 m).action.d8Act false false l (hE.φe (om201 m ![1, 0, 0])) =
      om201 m ![1, 0, 0] := by
    rw [t201_iii_φe_c₁ dD hE hm1 hφe]
    cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t201_φu_om]
    rfl
  have hq : (StrothTypeIndex.t201 m).action.d8Act false false l
      (hE.φe (Torus.ofInt _ ![-2 ^ (m - 2), 0, 0])) =
        Torus.ofInt _ ![-2 ^ (m - 2), 0, 0] + om201 m ![1, 0, 0] := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [om201_apply, ← Torus.ofInt_add, t201_iii_φe' dD hE hφe]
    cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply] <;> (try rw [t201_φu]) <;>
    · congr 1
      funext i
      fin_cases i <;> simp [pow_succ] <;> ring
  rw [ofTorus_conj_nfe dD hE hq hw, c_pow_om]
  have h := (t201_e_comm_iff dD hE v (om201 m ![1, 0, 0]) l true).mpr (by simpa using hw)
  simpa [bpow] using h.symm

theorem t201_iii_hC11 (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (hve : hE.ve = 0)
    (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0]) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * e ∈ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
      (∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * y) ∨
        (∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e, q⁻¹ * y * q = e) ∨
        (∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * e) ∨
        (∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = dD.u * e) ∨
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u * e := by
  intro y _ hye hy2
  have hDS : ∀ d ∈ D, d ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
    fun d hd => Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)
  have hP : ∀ g ∈ ({dD.uv, dD.t, dD.u} : Set G),
      g ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure hg))
  obtain ⟨v, l, hv⟩ := t201_mem_Du dD hye
  obtain rfl : y = dD.ofTorus v * dD.d8 false false l * e := by
    rw [← hv, mul_assoc, t201_iii_e_mul_self dD hE hve, mul_one]
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    obtain ⟨x0, x1, x2, rfl⟩ : ∃ a b c : ℤ, x = ![a, b, c] :=
      ⟨x 0, x 1, x 2, by funext i; fin_cases i <;> rfl⟩
    t201_iii_rels
    cases l
    · rw [dD.d8_fff, mul_one]
      obtain ⟨b, rfl | rfl⟩ := Int.even_or_odd' x2
      · obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' x1
        · obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' x0
          · refine Or.inr (Or.inl ⟨dD.ofTorus (Torus.ofInt _ ![0, a, b]), hDS _ (dD.ofTorus_mem _),
              ?_⟩)
            apply t201_eq_of_nf dD
            t201_iii_nf
            t201_coord
            · exact ⟨-j, by ring⟩
            · exact ⟨0, by ring⟩
            · exact ⟨0, by ring⟩
          · refine Or.inr (Or.inr (Or.inl ⟨dD.ofTorus (Torus.ofInt _ ![0, a, b]),
              hDS _ (dD.ofTorus_mem _), ?_⟩))
            rw [c_pow_eq]
            apply t201_eq_of_nf dD
            t201_iii_nf
            t201_coord
            · exact ⟨-j, by ring⟩
            · exact ⟨0, by ring⟩
            · exact ⟨0, by ring⟩
        · refine Or.inl ⟨dD.uv * dD.ofTorus (Torus.ofInt _ ![-2 * x0 + a + b - 1,
            -2 * x0 + 15 * (2 * b) + 27, -2 * x0 + 3 * (2 * a + 1) + 3]),
            mul_mem (hP _ (by simp)) (hDS _ (dD.ofTorus_mem _)), ?_⟩
          rw [c_pow_eq]
          apply t201_eq_of_nf dD
          t201_iii_nf
          t201_coord
          · exact ⟨276 + 168 * a + 120 * b - 64 * x0, by ring⟩
          · exact ⟨1300 + 56 * a + 1292 * b - 60 * x0, by ring⟩
          · exact ⟨322 + 260 * a + 56 * b - 84 * x0, by ring⟩
      · refine Or.inl ⟨dD.t * dD.ofTorus (Torus.ofInt _
          ![-5 * b - 3, 2 * x0 + x1 - 3 * (2 * b + 1) - 3,
          -3 * (2 * b + 1)]), mul_mem (hP _ (by simp)) (hDS _ (dD.ofTorus_mem _)), ?_⟩
        rw [c_pow_eq]
        apply t201_eq_of_nf dD
        t201_iii_nf
        t201_coord
        · exact ⟨-60 - 120 * b, by ring⟩
        · exact ⟨-18 - 20 * b + 4 * x0 + 2 * x1, by ring⟩
        · exact ⟨-18 - 36 * b, by ring⟩
    · rw [dD.d8_fft] at hy2 ⊢
      t201_iii_nf at hy2
      have hc := (ofTorus_ofInt_eq_one_iff dD _).mp hy2
      simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
      obtain ⟨-, ⟨j, hj⟩, -⟩ := hc
      obtain rfl : x2 = x1 - 8 * j := by linear_combination -hj
      obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' x0
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨dD.ofTorus (Torus.ofInt _ ![0, x1, 0]),
          hDS _ (dD.ofTorus_mem _), ?_⟩)))
        apply t201_eq_of_nf dD
        t201_iii_nf
        t201_coord
        · exact ⟨-i, by ring⟩
        · exact ⟨0, by ring⟩
        · exact ⟨j, by ring⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨dD.ofTorus (Torus.ofInt _ ![0, x1, 0]),
          hDS _ (dD.ofTorus_mem _), ?_⟩)))
        rw [c_pow_eq]
        apply t201_eq_of_nf dD
        t201_iii_nf
        t201_coord
        · exact ⟨-i, by ring⟩
        · exact ⟨0, by ring⟩
        · exact ⟨j, by ring⟩
  · exact Or.inl ⟨_, hDS _ (dD.ofTorus_mem _), t201_iii_conj_c₁ dD hE hm2 hφe v l⟩

theorem t201_iii_hue (hm : 1 ≤ m) (hφe : hE.φe = torusDiag _ ![-1, -1, -1]) (hve : hE.ve = 0)
    (hwuv : hE.wuv = Torus.ofInt _ ![2, 2, 2]) (hwt : hE.wt = Torus.ofInt _ ![0, -2, 0]) :
    (∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (dD.u * e) * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u * e) ∨
      ∃ v ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        (∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * v * q = dD.uv) ∧ v * (dD.u * e) = dD.u * e * v ∧
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * (dD.u * e * v) * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u * e := by
  have hDS : ∀ d ∈ D, d ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
    fun d hd => Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)
  have hP : ∀ g ∈ ({dD.uv, dD.t, dD.u} : Set G),
      g ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure hg))
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    right
    t201_iii_rels
    refine ⟨dD.ofTorus (Torus.ofInt _ ![1, 2, 0]) * dD.uv,
      mul_mem (hDS _ (dD.ofTorus_mem _)) (hP _ (by simp)),
      ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, 1]), hDS _ (dD.ofTorus_mem _), ?_⟩, ?_,
      ⟨dD.uv * dD.t, mul_mem (hP _ (by simp)) (hP _ (by simp)), ?_⟩⟩
    · apply t201_eq_of_nf dD
      t201_nf
      t201_coord
      · exact ⟨-1, by ring⟩
      · exact ⟨-4, by ring⟩
      · exact ⟨0, by ring⟩
    · apply t201_eq_of_nf dD
      t201_iii_nf
      t201_coord
      · exact ⟨0, by ring⟩
      · exact ⟨0, by ring⟩
      · exact ⟨0, by ring⟩
    · rw [c_pow_eq]
      apply t201_eq_of_nf dD
      t201_iii_nf
      t201_coord
      · exact ⟨-3, by ring⟩
      · exact ⟨3, by ring⟩
      · exact ⟨-7, by ring⟩
  · left
    have h := t201_iii_conj_c₁ dD hE hm2 hφe 0 true
    rw [dD.ofTorus_zero, one_mul, dD.d8_fft] at h
    exact ⟨_, hDS _ (dD.ofTorus_mem _), by rw [h, mul_assoc]⟩

end CaseIIIC11

end Stroth44Core

end CFSG.CGT.Stroth77
