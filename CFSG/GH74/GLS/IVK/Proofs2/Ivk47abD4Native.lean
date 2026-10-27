module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2Native
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Normal
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Params

variable {K : Type} [Field K] [Finite K] {σ : K →+* K}

theorem sigma_cube {q : ℕ} (hK3 : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) (c : K) :
    σ (σ (σ c)) = c := by
  have : Fintype K := Fintype.ofFinite K
  have h : c ^ (q ^ 3) = c := by
    rw [← hK3, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  simp only [hσq, ← pow_mul]
  rw [show q * q * q = q ^ 3 by ring]
  exact h

theorem neg_one_ne_one_of_odd {q : ℕ} (hq : Odd q) (hK3 : Nat.card K = q ^ 3) :
    (-1 : Kˣ) ≠ 1 := by
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    exact hq.pow
  have hchar : ringChar K ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hodd
  intro h
  exact Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)

theorem range_twistedIncl_eq_graphFixed {q : ℕ} (hq : Odd q) (hq2 : 2 ≤ q)
    (hK3 : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    (twistedIncl σ).range = graphFixedRootGroup TwistTag.D4 K σ := by
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    exact hq.pow
  have hK2 : ringChar K ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hodd
  let σK : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have h1 := (odd_diagram_fixed_root_group_perfect TwistTag.D4 K hK2 σK).2.2
  rw [hσK] at h1
  have h2 := commutator_twistedFixedGroup_eq_map σ hq2 hK3 hσq
  have h3 : (twistedGroup σ).map (adjointGroup d4 K).subtype =
      graphFixedRootGroup TwistTag.D4 K σ := h2.symm.trans h1
  rw [← h3, twistedIncl, MonoidHom.range_comp, Subgroup.range_subtype]

omit [Finite K] in
theorem card_fixedField_eq {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK3 : Nat.card K = (ℓ ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (fixedField σ) = ℓ ^ f := by
  have h := card_orbitField_D4_orientation hℓ hf hK3 (r := 1) (Or.inl rfl) (σ := σ)
    (by simpa using hσq) ⟨1, by decide⟩
  have h1 : (TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 1 := by
    decide
  rw [h1, pow_one] at h
  rw [← h]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro c
  change σ c = c ↔ _
  rw [mem_orbitField, h1, pow_one]

end Params


section Native

structure D4Data (K : Type) [Field K] (σ : K →+* K) (q : ℕ) : Prop where
  odd : Odd q
  card : Nat.card K = q ^ 3
  frob : ∀ c, σ c = c ^ q

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ}

theorem D4Data.sigma3 (h : D4Data K σ q) : ∀ c, σ (σ (σ c)) = c := sigma_cube h.card h.frob

theorem D4Data.neg_one (h : D4Data K σ q) : (-1 : Kˣ) ≠ 1 := neg_one_ne_one_of_odd h.odd h.card

theorem D4Data.two_le (h : D4Data K σ q) : 2 ≤ q := by
  by_contra hq
  have hq1 : q = 1 := by
    have := h.odd.pos
    omega
  have h1 : Nat.card K = 1 := by rw [h.card, hq1]; norm_num
  have := Finite.one_lt_card (α := K)
  omega


theorem D4Data.range (h : D4Data K σ q) :
    (twistedIncl σ).range = graphFixedRootGroup TwistTag.D4 K σ :=
  range_twistedIncl_eq_graphFixed h.odd h.two_le h.card h.frob

theorem D4Data.hC₀ (h : D4Data K σ q) :
    graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range := h.range.ge

theorem D4Data.hgF (h : D4Data K σ q) (g : twistedGroup σ) :
    twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ := h.range ▸ ⟨g, rfl⟩

end Native

section Charts

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

abbrev τL : twistedGroup σ := slLong σ hσ (-1)

abbrev Yd : Type := ↥(Subgroup.centralizer ({τL hσ} : Set (twistedGroup σ)))

@[expose] def toTw : Yd hσ →* twistedGroup σ :=
  (Subgroup.centralizer ({τL hσ} : Set (twistedGroup σ))).subtype

theorem toTw_injective : Function.Injective (toTw hσ) := Subtype.val_injective

theorem slLong_mem_cent (A : SL(2, fixedField σ)) :
    slLong σ hσ A ∈ Subgroup.centralizer ({τL hσ} : Set (twistedGroup σ)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    ← neg_one_mul_comm_SL2]

theorem slB_mem_cent (B : SL(2, K)) :
    slB σ hσ B ∈ Subgroup.centralizer ({τL hσ} : Set (twistedGroup σ)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (slLong_comm_slB hσ (-1) B).symm

@[expose] def chartAd : SL(2, fixedField σ) →* Yd hσ :=
  (slLong σ hσ).codRestrict _ (slLong_mem_cent hσ)

@[expose] def chartBd : SL(2, K) →* Yd hσ :=
  (slB σ hσ).codRestrict _ (slB_mem_cent hσ)

theorem toTw_chartAd (A : SL(2, fixedField σ)) : toTw hσ (chartAd hσ A) = slLong σ hσ A := rfl

theorem toTw_chartBd (B : SL(2, K)) : toTw hσ (chartBd hσ B) = slB σ hσ B := rfl

theorem chartAd_injective : Function.Injective (chartAd hσ) := fun _ _ h =>
  slLong_injective hσ (congrArg (toTw hσ) h)

theorem chartBd_injective : Function.Injective (chartBd hσ) := fun _ _ h =>
  slB_injective hσ (congrArg (toTw hσ) h)

theorem chartBd_comm (B : SL(2, K)) (A : SL(2, fixedField σ)) :
    chartBd hσ B * chartAd hσ A = chartAd hσ A * chartBd hσ B :=
  toTw_injective hσ (by
    rw [map_mul, map_mul, toTw_chartBd, toTw_chartAd]
    exact (slLong_comm_slB hσ A B).symm)

@[expose] def zd : Yd hσ := ⟨τL hσ, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem toTw_zd : toTw hσ (zd hσ) = slLong σ hσ (-1) := rfl

theorem chartAd_neg_one : chartAd hσ (-1) = zd hσ := rfl

theorem chartBd_neg_one : chartBd hσ (-1) = zd hσ := Subtype.ext (slB_neg_one hσ)

theorem zd_mul_self : zd hσ * zd hσ = 1 :=
  toTw_injective hσ (by
    rw [map_mul, toTw_zd, ← map_mul, neg_one_mul_neg_one_SL2, map_one, map_one])

theorem zd_ne_one (hK : (-1 : Kˣ) ≠ 1) : zd hσ ≠ 1 := by
  intro h
  have h1 : slLong σ hσ (-1) = 1 := by
    have := congrArg (toTw hσ) h
    rwa [toTw_zd, map_one] at this
  have h' := twistedIncl_slLong_neg_one hσ
  rw [h1, map_one, ← rootDiagUnit_one] at h'
  exact aLongTD4_ne_one hK (rootDiagUnit_injective h'.symm)


theorem glConjSL_eq_conjSLAut {F : Type} [Field F] (D : GL (Fin 2) F) (A : SL(2, F)) :
    glConjSL D A = conjSLAut D A :=
  Subtype.ext (by rw [glConjSL_coe, conjSLAut_coe])

theorem det_diagGL {F : Type} [Field F] (s : Fˣ) :
    Matrix.GeneralLinearGroup.det (diagGL s) = s :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL, Matrix.det_fin_two_of])

theorem m0_sq : m0 hσ * m0 hσ = 1 := by
  have hc : slB σ hσ WSL * slLong σ hσ WSL = slLong σ hσ WSL * slB σ hσ WSL :=
    (slLong_comm_slB hσ WSL WSL).symm
  calc m0 hσ * m0 hσ
      = slLong σ hσ WSL * (slB σ hσ WSL * slLong σ hσ WSL) * slB σ hσ WSL := by
        simp only [m0]; group
    _ = slLong σ hσ WSL * (slLong σ hσ WSL * slB σ hσ WSL) * slB σ hσ WSL := by rw [hc]
    _ = slLong σ hσ (WSL * WSL) * slB σ hσ (WSL * WSL) := by
        simp only [map_mul]; group
    _ = slLong σ hσ (-1) * slB σ hσ (-1) := by
        simp only [WSL_mul_WSL, HSL_neg_one_eq_neg_one]
    _ = 1 := by rw [slB_neg_one hσ, ← map_mul, neg_one_mul_neg_one_SL2, map_one]

theorem m0_conj_slB (B : SL(2, K)) :
    m0 hσ * slB σ hσ B * (m0 hσ)⁻¹ = slB σ hσ (WSL * B * WSL⁻¹) := by
  have h1 : ∀ C : SL(2, K), slLong σ hσ WSL * slB σ hσ C * (slLong σ hσ WSL)⁻¹ = slB σ hσ C :=
    fun C => by rw [slLong_comm_slB hσ WSL C]; group
  calc m0 hσ * slB σ hσ B * (m0 hσ)⁻¹
      = slLong σ hσ WSL * (slB σ hσ WSL * slB σ hσ B * (slB σ hσ WSL)⁻¹) *
        (slLong σ hσ WSL)⁻¹ := by simp only [m0]; group
    _ = slLong σ hσ WSL * slB σ hσ (WSL * B * WSL⁻¹) * (slLong σ hσ WSL)⁻¹ := by
        simp only [map_mul, map_inv]
    _ = slB σ hσ (WSL * B * WSL⁻¹) := h1 _

theorem m0_conj_slLong (A : SL(2, fixedField σ)) :
    m0 hσ * slLong σ hσ A * (m0 hσ)⁻¹ = slLong σ hσ (WSL * A * WSL⁻¹) := by
  have h1 : slB σ hσ WSL * slLong σ hσ A * (slB σ hσ WSL)⁻¹ = slLong σ hσ A := by
    rw [← slLong_comm_slB hσ A WSL]; group
  calc m0 hσ * slLong σ hσ A * (m0 hσ)⁻¹
      = slLong σ hσ WSL * (slB σ hσ WSL * slLong σ hσ A * (slB σ hσ WSL)⁻¹) *
        (slLong σ hσ WSL)⁻¹ := by simp only [m0]; group
    _ = slLong σ hσ WSL * slLong σ hσ A * (slLong σ hσ WSL)⁻¹ := by rw [h1]
    _ = slLong σ hσ (WSL * A * WSL⁻¹) := by simp only [map_mul, map_inv]

@[expose] def xd (x₀ : twistedGroup σ) : twistedGroup σ := x₀ * m0 hσ

theorem xd_sq {x₀ : twistedGroup σ} (hx₀ : x₀ ∈ TK σ) : xd hσ x₀ * xd hσ x₀ = 1 := by
  have h := m0_inverts_td4 hσ hx₀
  calc xd hσ x₀ * xd hσ x₀
      = x₀ * (m0 hσ * x₀ * (m0 hσ)⁻¹) * (m0 hσ * m0 hσ) := by simp only [xd]; group
    _ = 1 := by rw [h, m0_sq]; group

theorem xd_conj_slB {x₀ : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hb : twistedIncl σ x₀ = rootDiagUnit d4 b) (B : SL(2, K)) :
    xd hσ x₀ * slB σ hσ B * (xd hσ x₀)⁻¹ = slB σ hσ (conjSLAut
      (diagGL (b (nd 1) * b (nd 2) * b (nd 3)) * Matrix.SpecialLinearGroup.toGL (WSL : SL(2, K)))
        B) := by
  obtain ⟨s, hs, hconj⟩ := torus_conj_slB hσ hb
  calc xd hσ x₀ * slB σ hσ B * (xd hσ x₀)⁻¹
      = x₀ * (m0 hσ * slB σ hσ B * (m0 hσ)⁻¹) * x₀⁻¹ := by simp only [xd]; group
    _ = x₀ * slB σ hσ (WSL * B * WSL⁻¹) * x₀⁻¹ := by rw [m0_conj_slB]
    _ = slB σ hσ (glConjSL (diagGL s) (WSL * B * WSL⁻¹)) := hconj _
    _ = _ := by
        rw [glConjSL_eq_conjSLAut, ← conjSLAut_toGL, ← conjSLAut_mul, hs]

theorem xd_conj_slLong {x₀ : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hb : twistedIncl σ x₀ = rootDiagUnit d4 b) :
    ∃ s : (fixedField σ)ˣ, ((s : fixedField σ) : K) = (b (nd 2) : K) ∧
      ∀ A : SL(2, fixedField σ), xd hσ x₀ * slLong σ hσ A * (xd hσ x₀)⁻¹ =
        slLong σ hσ (conjSLAut (diagGL s *
          Matrix.SpecialLinearGroup.toGL (WSL : SL(2, fixedField σ))) A) := by
  obtain ⟨s, hs, hconj⟩ := torus_conj_slLong hσ hb
  refine ⟨s, hs, fun A => ?_⟩
  calc xd hσ x₀ * slLong σ hσ A * (xd hσ x₀)⁻¹
      = x₀ * (m0 hσ * slLong σ hσ A * (m0 hσ)⁻¹) * x₀⁻¹ := by simp only [xd]; group
    _ = x₀ * slLong σ hσ (WSL * A * WSL⁻¹) * x₀⁻¹ := by rw [m0_conj_slLong]
    _ = slLong σ hσ (glConjSL (diagGL s) (WSL * A * WSL⁻¹)) := hconj _
    _ = _ := by
        rw [glConjSL_eq_conjSLAut, ← conjSLAut_toGL, ← conjSLAut_mul]


section Torus

variable [Finite K]

theorem exists_torus_gamma {q : ℕ} (h : D4Data K σ q) (γ : (fixedField σ)ˣ) :
    ∃ (x₀ : twistedGroup σ) (b : Fin d4.rank → Kˣ), twistedIncl σ x₀ = rootDiagUnit d4 b ∧
      b (nd 0) = 1 ∧ b (nd 1) = 1 ∧ b (nd 2) = Units.map (fixedField σ).subtype.toMonoidHom γ ∧
        b (nd 3) = 1 := by
  classical
  set γK : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom γ with hγK
  let l : Fin TwistTag.D4.tag.rank → Kˣ := Function.update (fun _ => 1) (nd 2) γK
  have hσγ : σ (γK : K) = γK := γ.val.2
  let σE : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hperm2 : TwistTag.D4.perm (nd 2) = nd 2 := by decide
  have hl : ∀ i, l (TwistTag.D4.perm i) = Units.map σE.toRingHom.toMonoidHom (l i) := by
    intro i
    by_cases hi : i = nd 2
    · subst hi
      rw [hperm2]
      show Function.update (fun _ => (1 : Kˣ)) (nd 2) γK (nd 2) =
        Units.map σE.toRingHom.toMonoidHom (Function.update (fun _ => (1 : Kˣ)) (nd 2) γK (nd 2))
      rw [Function.update_self]
      exact Units.ext hσγ.symm
    · have hi' : TwistTag.D4.perm i ≠ nd 2 := fun h =>
        hi (TwistTag.D4.perm.injective (h.trans hperm2.symm))
      show Function.update (fun _ => (1 : Kˣ)) (nd 2) γK (TwistTag.D4.perm i) =
        Units.map σE.toRingHom.toMonoidHom (Function.update (fun _ => (1 : Kˣ)) (nd 2) γK i)
      rw [Function.update_of_ne hi', Function.update_of_ne hi]
      simp
  have hmem := rootDiagUnit_mem_graphFixedRootGroup_triality σE h.sigma3
    (Or.inr ⟨q, h.odd, h.frob⟩) hl
  rw [hσE, ← h.range] at hmem
  obtain ⟨x₀, hx₀⟩ := hmem
  have h02 : (nd 0 : Fin d4.rank) ≠ nd 2 := by decide
  have h12 : (nd 1 : Fin d4.rank) ≠ nd 2 := by decide
  have h32 : (nd 3 : Fin d4.rank) ≠ nd 2 := by decide
  exact ⟨x₀, l, hx₀, Function.update_of_ne h02 _ _, Function.update_of_ne h12 _ _,
    Function.update_self _ _ _, Function.update_of_ne h32 _ _⟩


theorem torus_sq_decomp {t : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hb : twistedIncl σ t = rootDiagUnit d4 b) {u : (fixedField σ)ˣ}
    (hu : b (nd 2) = Units.map (fixedField σ).subtype.toMonoidHom u ^ 2) :
    ∃ s₀ : Kˣ, t = slB σ hσ (HSL s₀) * slLong σ hσ (HSL u) := by
  set uK : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom u with huK
  obtain ⟨s₀, hs₀⟩ := nuU_surjective hσ (b (nd 0) * uK)
  refine ⟨s₀, ?_⟩
  have hy : twistedIncl σ (slB σ hσ (HSL s₀) * slLong σ hσ (HSL u)) = rootDiagUnit d4
      (weylTuple tdNhat (tupS σ s₀) * fun j => uK ^ d4.cartan (nd 2) j) := by
    rw [map_mul, twistedIncl_slB_HSL hσ, twistedIncl_slLong_HSL hσ, ← rootDiagUnit_mul]
  have h0 : b (nd 0) =
      (weylTuple tdNhat (tupS σ s₀) * fun j => uK ^ d4.cartan (nd 2) j) (nd 0) := by
    rw [Pi.mul_apply, cB_zero, hs₀]
    show b (nd 0) = b (nd 0) * uK * uK ^ d4.cartan (nd 2) (nd 0)
    have : d4.cartan (nd 2) (nd 0) = -1 := by decide
    rw [this, zpow_neg, zpow_one, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : b (nd 2) =
      (weylTuple tdNhat (tupS σ s₀) * fun j => uK ^ d4.cartan (nd 2) j) (nd 2) := by
    rw [Pi.mul_apply, cB_two, one_mul, hu]
    show uK ^ 2 = uK ^ d4.cartan (nd 2) (nd 2)
    have : d4.cartan (nd 2) (nd 2) = 2 := by decide
    rw [this]
    rfl
  have key := tuple_eq_of_compat hb hy h0 h2
  apply twistedIncl_injective σ
  rw [hy, ← key, hb]


omit [Finite K] in
theorem exists_unit_of_compat {t : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hb : twistedIncl σ t = rootDiagUnit d4 b) :
    ∃ γ₁ : (fixedField σ)ˣ, Units.map (fixedField σ).subtype.toMonoidHom γ₁ = b (nd 2) := by
  have hfix : σ (b (nd 2) : K) = (b (nd 2) : K) := (torus_compat hb).2.2.2.symm
  have hne : (b (nd 2) : K) ≠ 0 := (b (nd 2)).ne_zero
  exact ⟨Units.mk0 ⟨(b (nd 2) : K), hfix⟩ (fun h => hne (congrArg Subtype.val h)), Units.ext rfl⟩

theorem torus_decomp {γ : (fixedField σ)ˣ} (hγ : ¬ IsSquare ((γ : fixedField σ)))
    {x₀ : twistedGroup σ} {l : Fin d4.rank → Kˣ} (hl : twistedIncl σ x₀ = rootDiagUnit d4 l)
    (hl2 : l (nd 2) = Units.map (fixedField σ).subtype.toMonoidHom γ)
    {t : twistedGroup σ} (ht : t ∈ TK σ) :
    ∃ (s₀ : Kˣ) (u : (fixedField σ)ˣ),
      t = slB σ hσ (HSL s₀) * slLong σ hσ (HSL u) ∨
        t = x₀ * (slB σ hσ (HSL s₀) * slLong σ hσ (HSL u)) := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨γ₁, hγ₁⟩ := exists_unit_of_compat hb
  by_cases hsq : IsSquare ((γ₁ : fixedField σ))
  · obtain ⟨u, hu⟩ := exists_unit_sq hsq
    have hu' : b (nd 2) = Units.map (fixedField σ).subtype.toMonoidHom u ^ 2 := by
      rw [← hγ₁, hu, map_pow]
    obtain ⟨s₀, hs₀⟩ := torus_sq_decomp hσ hb hu'
    exact ⟨s₀, u, Or.inl hs₀⟩
  · obtain ⟨v, hv0, hv⟩ := exists_mul_sq_of_not_isSquare hγ hsq
    have hv' : γ₁ = (Units.mk0 v hv0) ^ 2 * γ := Units.ext (by simpa [sq] using hv)
    have hb2 : b (nd 2) = Units.map (fixedField σ).subtype.toMonoidHom (Units.mk0 v hv0) ^ 2 *
        Units.map (fixedField σ).subtype.toMonoidHom γ := by
      rw [← hγ₁, hv', map_mul, map_pow]
    have hx₂ : twistedIncl σ (x₀⁻¹ * t) = rootDiagUnit d4 (l⁻¹ * b) := by
      rw [map_mul, map_inv, hl, hb, rootDiagUnit_inv, rootDiagUnit_mul]
    have hv2 : (l⁻¹ * b) (nd 2) =
        Units.map (fixedField σ).subtype.toMonoidHom (Units.mk0 v hv0) ^ 2 := by
      rw [Pi.mul_apply, Pi.inv_apply, hl2, hb2, mul_comm, mul_inv_cancel_right]
    obtain ⟨s₀, hs₀⟩ := torus_sq_decomp hσ hx₂ hv2
    refine ⟨s₀, Units.mk0 v hv0, Or.inr ?_⟩
    rw [← hs₀]
    group

end Torus




theorem chartBd_chartAd_inter (A : SL(2, K)) (B : SL(2, fixedField σ))
    (h : chartBd hσ A = chartAd hσ B) : chartBd hσ A = 1 ∨ chartBd hσ A = zd hσ := by
  have hB : B ∈ Subgroup.center SL(2, fixedField σ) := by
    rw [Subgroup.mem_center_iff]
    intro C
    apply slLong_injective hσ
    rw [map_mul, map_mul]
    have h1 : slB σ hσ A = slLong σ hσ B := congrArg (toTw hσ) h
    rw [← h1]
    exact slLong_comm_slB hσ C A
  rcases eq_one_or_neg_one_of_mem_center hB with rfl | rfl
  · left
    rw [h, map_one]
  · right
    rw [h, chartAd_neg_one]

theorem not_isSquare_of_fixedField (hσ : ∀ c, σ (σ (σ c)) = c) {γ : fixedField σ}
    (hγ : ¬ IsSquare γ) : ¬ IsSquare ((γ : fixedField σ) : K) := by
  rintro ⟨s, hs⟩
  have hγ0 : (γ : K) ≠ 0 := by
    intro h0
    apply hγ
    have : γ = 0 := Subtype.ext h0
    rw [this]
    exact IsSquare.zero
  have hσγ : σ (γ : K) = γ := γ.2
  have hss : σ s * σ s = (γ : K) := by rw [← map_mul, ← hs, hσγ]
  have hsss : σ (σ s) * σ (σ s) = (γ : K) := by rw [← map_mul, hss, hσγ]
  have hn : σ (s * σ s * σ (σ s)) = s * σ s * σ (σ s) := by
    simp only [map_mul, hσ]
    ring
  have hnn : (s * σ s * σ (σ s)) * (s * σ s * σ (σ s)) = (γ : K) * γ * γ := by
    calc (s * σ s * σ (σ s)) * (s * σ s * σ (σ s))
        = (s * s) * (σ s * σ s) * (σ (σ s) * σ (σ s)) := by ring
      _ = (γ : K) * γ * γ := by rw [← hs, hss, hsss]
  apply hγ
  refine ⟨(⟨s * σ s * σ (σ s), hn⟩ : fixedField σ) / γ, ?_⟩
  apply Subtype.ext
  push_cast
  field_simp
  linear_combination -hnn

section Assembly

variable [Finite K]

theorem exists_native_shape_d4 (hσ : ∀ c, σ (σ (σ c)) = c) {q : ℕ} (h : D4Data K σ q) :
    ∃ S : Shape (Yd hσ) K (fixedField σ), S.z = zd hσ := by
  classical
  have hK := h.neg_one
  have hC₀ := h.hC₀
  have hgF := h.hgF
  have hneg : (-1 : fixedField σ) ≠ 1 := fun h' => hK (Units.ext (by
    have := congrArg (fixedField σ).subtype h'
    simpa using this))
  have hcharF : ringChar (fixedField σ) ≠ 2 := by
    intro hc
    have := ringChar.of_eq hc
    exact hneg (CharTwo.neg_eq 1)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hcharF
  have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ IsSquare.zero)
  set γ : (fixedField σ)ˣ := Units.mk0 a ha0 with hγdef
  have hγ : ¬ IsSquare ((γ : fixedField σ)) := ha
  obtain ⟨x₀, l, hl, hl0, hl1, hl2, hl3⟩ := exists_torus_gamma h γ
  have hx₀TK : x₀ ∈ TK σ := ⟨l, hl⟩
  have hxS : xd hσ x₀ ∈ SProd σ hσ := mul_mem (SProd_mem_of_TK hσ hx₀TK)
    (mul_mem (slLong_mem_SProd hσ WSL) (slB_mem_SProd hσ WSL))
  have hxc : xd hσ x₀ ∈ Subgroup.centralizer ({τL hσ} : Set (twistedGroup σ)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (SProd_le_centralizer hσ hxS)
  let xY : Yd hσ := ⟨xd hσ x₀, hxc⟩
  have hxY : toTw hσ xY = xd hσ x₀ := rfl
  have hxY_sq : xY * xY = 1 :=
    toTw_injective hσ (by rw [map_mul, hxY, map_one]; exact xd_sq hσ hx₀TK)
  set g₁ : GL (Fin 2) K := diagGL (l (nd 1) * l (nd 2) * l (nd 3)) *
    Matrix.SpecialLinearGroup.toGL (WSL : SL(2, K)) with hg₁
  have hdet₁ : Matrix.GeneralLinearGroup.det g₁ =
      Units.map (fixedField σ).subtype.toMonoidHom γ := by
    rw [hg₁, map_mul, det_diagGL, det_toGL_one, mul_one, hl1, hl3, hl2, one_mul, mul_one]
  have hn₁ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₁ : Kˣ) : K) := by
    rw [hdet₁]
    exact not_isSquare_of_fixedField hσ hγ
  obtain ⟨s, hs, hact⟩ := xd_conj_slLong hσ hl
  set g₂ : GL (Fin 2) (fixedField σ) := diagGL s *
    Matrix.SpecialLinearGroup.toGL (WSL : SL(2, fixedField σ)) with hg₂
  have hn₂ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₂ : (fixedField σ)ˣ) :
      fixedField σ) := by
    have hsγ : s = γ := Units.ext (Subtype.ext (by rw [hs, hl2]; rfl))
    rw [hg₂, map_mul, det_diagGL, det_toGL_one, mul_one, hsγ]
    exact hγ
  have hgen : (chartBd hσ).range ⊔ (chartAd hσ).range ⊔ Subgroup.zpowers xY = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hSB : ∀ B, chartBd hσ B ∈
        (chartBd hσ).range ⊔ (chartAd hσ).range ⊔ Subgroup.zpowers xY :=
      fun B => Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨B, rfl⟩)
    have hSA : ∀ A, chartAd hσ A ∈
        (chartBd hσ).range ⊔ (chartAd hσ).range ⊔ Subgroup.zpowers xY :=
      fun A => Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨A, rfl⟩)
    have hSx : xY ∈ (chartBd hσ).range ⊔ (chartAd hσ).range ⊔ Subgroup.zpowers xY :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyS : (y : twistedGroup σ) ∈ SProd σ hσ :=
      mem_SProd_of_centralizes hσ hK hC₀ hgF (Subgroup.mem_centralizer_singleton_iff.1 y.2)
    obtain ⟨t, ht, A, B, hy⟩ := hyS
    obtain ⟨s₀, u, hdec⟩ := torus_decomp hσ hγ hl hl2 ht
    rcases hdec with hdec | hdec
    · have key : y = (chartBd hσ (HSL s₀) * chartAd hσ (HSL u)) * (chartAd hσ A * chartBd hσ B) :=
        toTw_injective hσ (by
          simp only [map_mul, toTw_chartAd, toTw_chartBd]
          show (y : twistedGroup σ) = _
          rw [hy, hdec]
          group)
      rw [key]
      exact mul_mem (mul_mem (hSB _) (hSA _)) (mul_mem (hSA _) (hSB _))
    · have key : y = xY * (chartAd hσ WSL * chartBd hσ WSL)⁻¹ *
          (chartBd hσ (HSL s₀) * chartAd hσ (HSL u)) * (chartAd hσ A * chartBd hσ B) :=
        toTw_injective hσ (by
          simp only [map_mul, map_inv, toTw_chartAd, toTw_chartBd, hxY]
          show (y : twistedGroup σ) = _
          rw [hy, hdec]
          simp only [xd, m0]
          group)
      rw [key]
      exact mul_mem (mul_mem (mul_mem hSx (inv_mem (mul_mem (hSA _) (hSB _))))
        (mul_mem (hSB _) (hSA _))) (mul_mem (hSA _) (hSB _))
  exact ⟨Shape.ofCharts (chartBd hσ) (chartAd hσ) (chartBd_injective hσ) (chartAd_injective hσ)
    (chartBd_comm hσ) (zd hσ) (chartBd_neg_one hσ) (chartAd_neg_one hσ) (zd_mul_self hσ)
    (zd_ne_one hσ hK) (chartBd_chartAd_inter hσ) xY hxY_sq hgen g₁ g₂ hn₁ hn₂
    (fun B => toTw_injective hσ (by
      rw [map_mul, map_mul, map_inv, hxY, toTw_chartBd, toTw_chartBd]
      have := xd_conj_slB hσ hl B
      rw [hg₁]
      exact this))
    (fun A => toTw_injective hσ (by
      rw [map_mul, map_mul, map_inv, hxY, toTw_chartAd, toTw_chartAd]
      exact hact A)), rfl⟩

end Assembly

end Charts

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
