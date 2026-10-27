module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TwE6Group
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TwF4Data
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcCentLocal

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross (mactC)

section TwE6Cent

variable (K : Type) [Field K] [Finite K] (σ : K →+* K)

@[expose] noncomputable def pi1 : ↥(N1 K σ) →* WeylGroup Tag.F4 :=
  (foldEquiv : ↥(relWeylTwist TwistTag.E6) ≃* WeylGroup Tag.F4).toMonoidHom.comp
    ((psi1 K σ).codRestrict (relWeylTwist TwistTag.E6) (psi1_mem K σ))

theorem pi1_eq (g : ↥(N1 K σ)) : pi1 K σ g = foldEquiv ⟨psi1 K σ g, psi1_mem K σ g⟩ := rfl

theorem pi1_eq_one_iff (g : ↥(N1 K σ)) : pi1 K σ g = 1 ↔ psi1 K σ g = 1 := by
  rw [pi1_eq]
  constructor
  · intro h
    have := (foldEquiv).injective (h.trans (map_one foldEquiv).symm)
    exact congrArg Subtype.val this
  · intro h
    have : (⟨psi1 K σ g, psi1_mem K σ g⟩ : ↥(relWeylTwist TwistTag.E6)) = 1 := Subtype.ext h
    rw [this, map_one]

theorem pi1_iota0 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (t : Fin 4 → ↥(Cq K q)) :
    pi1 K σ (iota0 K σ hq hσ t) = 1 :=
  (pi1_eq_one_iff K σ _).2 (psi1_iota0 K σ hq hσ t)

@[expose] noncomputable def Afold (w : WeylGroup Tag.F4) : Matrix (Fin 4) (Fin 4) ℤ :=
  latMat Tag.F4 w

theorem Afold_wordW (l : List (Fin Tag.F4.rank)) : Afold (wordW Tag.F4 l) = SM l :=
  latMat_wordW Tag.F4 l

theorem conj_iota0_pi1 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (g : ↥(N1 K σ))
    (t : Fin 4 → ↥(Cq K q)) :
    g * iota0 K σ hq hσ t * g⁻¹ =
      iota0 K σ hq hσ (mactC (Afold (pi1 K σ g)) t) := by
  rw [conj_iota0 K σ hq hσ g t, foldMat_of_mem (psi1_mem K σ g)]
  rfl

theorem exists_lift_What1_pi1 (Q : Subgroup (WeylGroup Tag.F4)) (hQ : IsPGroup 3 Q) :
    ∃ C : Subgroup ↥(N1 K σ), C ≤ What1 K σ ∧
      (∀ x ∈ C, ∀ y ∈ C, pi1 K σ x = pi1 K σ y → x = y) ∧
      (∀ q ∈ Q, ∃ c ∈ C, pi1 K σ c = q) ∧ ∀ c ∈ C, pi1 K σ c ∈ Q := by
  refine exists_lift_of_ker_two (pi1 K σ) (What1 K σ) (Z1 K σ) ?_ ?_ ?_ ?_ ?_ Q hQ ?_
  · intro z hz
    exact Z0_le_What Tag.E6 K hz
  · intro z hz
    apply jHom_injective K σ
    rw [map_pow, map_one]
    exact Z0_sq Tag.E6 K hz
  · intro x hx h
    exact psi1_of_What1_ker K σ hx ((pi1_eq_one_iff K σ x).1 h)
  · intro z hz
    rw [MonoidHom.mem_ker, pi1_eq_one_iff, ← psi1_eq]
    exact MonoidHom.mem_ker.1 (Z0_le_ker Tag.E6 K hz)
  · intro g hg z hz
    show jHom K σ (g * z * g⁻¹) ∈ Z0 Tag.E6 K
    rw [map_mul, map_mul, map_inv]
    exact Z0_conj_What Tag.E6 K hg hz
  · intro q hq
    obtain ⟨g, hg, hgw⟩ := exists_What1_lift K σ (foldEquiv.symm q).2
    refine ⟨g, hg, ?_⟩
    rw [pi1_eq]
    have : (⟨psi1 K σ g, psi1_mem K σ g⟩ : ↥(relWeylTwist TwistTag.E6)) = foldEquiv.symm q :=
      Subtype.ext hgw
    rw [this, MulEquiv.apply_symm_apply]

theorem exists_omega_Cq {q : ℕ} (hq : 1 < q) (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q - 1) :
    ∃ ω : ↥(Cq K q), orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : 3 ∣ Nat.card ↥(Cq K q) := by rwa [card_Cq K hq hK]
  exact exists_prime_orderOf_dvd_card' 3 this

theorem exists_dec_of_mem_G {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) {s gx : ↥(N1 K σ)}
    (hs : s ∈ torusT K σ hq hσ ⊔ What1 K σ) (hgx : gx ∈ What1 K σ)
    (h : pi1 K σ s = pi1 K σ gx) : ∃ t : Fin 4 → ↥(Cq K q), s = iota0 K σ hq hσ t * gx := by
  have h1 : s * gx⁻¹ ∈ torusT K σ hq hσ ⊔ What1 K σ :=
    mul_mem hs (inv_mem (Subgroup.mem_sup_right hgx))
  have h2 : psi1 K σ (s * gx⁻¹) = 1 := by
    rw [← pi1_eq_one_iff, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨t, ht⟩ := mem_torusT_of_mem_sup K σ hq hσ h1 h2
  exact ⟨t, by rw [show iota0 K σ hq hσ t = s * gx⁻¹ from ht]; group⟩

theorem exists_comm_torus_u {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q)
    {gx gy : ↥(N1 K σ)} (hx : gx ∈ What1 K σ) (hy : gy ∈ What1 K σ)
    (hcomm : pi1 K σ gy * pi1 K σ gx = pi1 K σ gx * pi1 K σ gy) :
    ∃ u : Fin 4 → ↥(Cq K q), u * u = 1 ∧
      gy * gx * gy⁻¹ = iota0 K σ hq hσ u * gx := by
  set z := gy * gx * gy⁻¹ * gx⁻¹ with hz
  have hzW : z ∈ What1 K σ := mul_mem (mul_mem (mul_mem hy hx) (inv_mem hy)) (inv_mem hx)
  have hz1 : pi1 K σ z = 1 := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hzZ : z ∈ Z1 K σ := psi1_of_What1_ker K σ hzW ((pi1_eq_one_iff K σ z).1 hz1)
  obtain ⟨u, hu⟩ := Z1_le_torusT K σ hq hσ hzZ
  refine ⟨u, ?_, ?_⟩
  · apply iota0_injective K σ hq hσ
    rw [map_mul, map_one, hu]
    have h2 : jHom K σ z ^ 2 = 1 := Z0_sq Tag.E6 K hzZ
    apply jHom_injective K σ
    rw [map_one, map_mul, ← sq]
    exact h2
  · rw [hu, hz]; group

theorem boundA_tw {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q - 1) (lx ly : List (Fin Tag.F4.rank)) (hx : wordW Tag.F4 lx ∈ QF4)
    (hy : wordW Tag.F4 ly ∈ QF4) (Φ Ψ : Matrix (Fin 4) (Fin 4) ℤ)
    (hid : 1 - SM ly = (1 - SM lx) * Φ + Ψ * (1 + SM lx + SM lx * SM lx))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((SM lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((SM lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW Tag.F4 lx, wordW Tag.F4 ly} :
      Set (WeylGroup Tag.F4))))
    (s : ↥(N1 K σ)) (hs : s ∈ torusT K σ hq hσ ⊔ What1 K σ)
    (hsx : pi1 K σ s = wordW Tag.F4 lx) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(N1 K σ))) := by
  obtain ⟨ω, hω⟩ := exists_omega_Cq K hq hK h3
  obtain ⟨C, hCW, hCinj, hCsurj, hCmem⟩ := exists_lift_What1_pi1 K σ QF4 QF4_pGroup
  obtain ⟨gx, hgxC, hgx⟩ := hCsurj _ hx
  obtain ⟨gy, hgyC, hgy⟩ := hCsurj _ hy
  have hcomm : gy * gx = gx * gy := hCinj _ (mul_mem hgyC hgxC) _ (mul_mem hgxC hgyC) (by
    rw [map_mul, map_mul, hgx, hgy]; exact QF4_comm _ hy _ hx)
  have hgx3 : gx ^ 3 = 1 := hCinj _ (pow_mem hgxC 3) _ (one_mem C) (by
    rw [map_pow, map_one, hgx]; exact QF4_cube _ hx)
  have hdec := exists_dec_of_mem_G K σ hq hσ hs (hCW hgxC) (hsx.trans hgx.symm)
  have hid' : 1 - Afold (wordW Tag.F4 ly) =
      (1 - Afold (wordW Tag.F4 lx)) * Φ + Ψ * (1 + Afold (wordW Tag.F4 lx) +
        Afold (wordW Tag.F4 lx) * Afold (wordW Tag.F4 lx)) := by
    simpa only [Afold_wordW] using hid
  exact caseA_loc (iota0 K σ hq hσ) (pi1 K σ) Afold (iota0_injective K σ hq hσ)
    (pi1_iota0 K σ hq hσ) (conj_iota0_pi1 K σ hq hσ) (wordW Tag.F4 lx) (wordW Tag.F4 ly) s gx gy
    hdec hsx hgx hgy hcomm hgx3 hs3 Φ Ψ hid' ω hω c₁ c₂ p₁ p₂
    (by simpa only [Afold_wordW] using hf₁) (by simpa only [Afold_wordW] using hf₂)
    h11 h12 h21 h22 hQ

theorem boundB_tw {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q - 1) (lx : List (Fin Tag.F4.rank)) (ys : Fin 4 → List (Fin Tag.F4.rank))
    (Θ Ξ : Matrix (Fin 4) (Fin 4) ℤ) (l₂ l₃ θ₂ θ₃ : Fin 4 → ℤ)
    (tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
      (1 - SM lx).mulVec d = (1 - SM (ys i)).mulVec
        (((a : ℕ) : ℤ) • ![0, 0, 1, 0] + ((b : ℕ) : ℤ) • ![0, 0, 0, 1]))
    (D1 : (1 - SM lx) * Θ + Matrix.vecMulVec ![0, 0, 1, 0] l₂ +
      Matrix.vecMulVec ![0, 0, 0, 1] l₃ = 1)
    (D2 : (1 - SM lx).mulVec θ₂ = (3 : ℤ) • ![0, 0, 1, 0])
    (D3 : (1 - SM lx).mulVec θ₃ = (3 : ℤ) • ![0, 0, 0, 1])
    (hΞ : (1 - SM lx) * Ξ = (3 : ℤ) • 1)
    (hXY : ∀ i : Fin 4, SM lx * SM (ys i) = SM (ys i) * SM lx)
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((SM lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((SM lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hW1 : SM (lx ++ lx ++ lx) = SM []) (hW2 : SM lx ≠ SM [])
    (hWy : ∀ i, SM (ys i ++ ys i ++ ys i) = SM [] ∧ SM (ys i) ≠ SM lx ∧ SM (ys i) ≠ SM [] ∧
      SM (ys i) ≠ SM (lx ++ lx) ∧ SM (lx ++ ys i) = SM (ys i ++ lx))
    (s : ↥(N1 K σ)) (hs : s ∈ torusT K σ hq hσ ⊔ What1 K σ)
    (hsx : pi1 K σ s = wordW Tag.F4 lx) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(N1 K σ))) := by
  obtain ⟨ω, hω⟩ := exists_omega_Cq K hq hK h3
  have hlift0 : ∀ w : WeylGroup Tag.F4, ∃ g ∈ What1 K σ, pi1 K σ g = w := fun w => by
    obtain ⟨g, hg, hgw⟩ := exists_What1_lift K σ (foldEquiv.symm w).2
    refine ⟨g, hg, ?_⟩
    rw [pi1_eq]
    have : (⟨psi1 K σ g, psi1_mem K σ g⟩ : ↥(relWeylTwist TwistTag.E6)) = foldEquiv.symm w :=
      Subtype.ext hgw
    rw [this, MulEquiv.apply_symm_apply]
  obtain ⟨gx, hgxW, hgx⟩ := hlift0 (wordW Tag.F4 lx)
  have hdec := exists_dec_of_mem_G K σ hq hσ hs hgxW (hsx.trans hgx.symm)
  have hlift : ∀ i, ∃ (gy : ↥(N1 K σ)) (u : Fin 4 → ↥(Cq K q)),
      pi1 K σ gy = wordW Tag.F4 (ys i) ∧ u * u = 1 ∧
        gy * gx * gy⁻¹ = iota0 K σ hq hσ u * gx := fun i => by
    obtain ⟨gy, hgyW, hgy⟩ := hlift0 (wordW Tag.F4 (ys i))
    obtain ⟨u, hu1, hu2⟩ := exists_comm_torus_u K σ hq hσ hgxW hgyW (by
      rw [hgx, hgy]; exact (wordW_comm_of lx (ys i) (hWy i).2.2.2.2).symm)
    exact ⟨gy, u, hgy, hu1, hu2⟩
  have hsolve := solve_int_fpf (SM lx) (fun i => SM (ys i)) hXY Θ _ _ l₂ l₃ θ₂ θ₃ D1 D2 D3 tab
  have hΞ' : (1 - Afold (wordW Tag.F4 lx)) * Ξ = (3 : ℤ) • 1 := by
    simpa only [Afold_wordW] using hΞ
  have hsolve' : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
      (1 - Afold (wordW Tag.F4 lx)).mulVec d =
        (1 - Afold (wordW Tag.F4 (ys i))).mulVec c := fun c => by
    simpa only [Afold_wordW] using hsolve c
  exact caseB_loc (iota0 K σ hq hσ) (pi1 K σ) Afold (iota0_injective K σ hq hσ)
    (pi1_iota0 K σ hq hσ) (conj_iota0_pi1 K σ hq hσ) (wordW Tag.F4 lx)
    (fun i => wordW Tag.F4 (ys i)) s gx hdec hsx hgx hlift Ξ hΞ' hsolve' ω hω c₁ c₂ p₁ p₂
    (by simpa only [Afold_wordW] using hf₁) (by simpa only [Afold_wordW] using hf₂)
    h11 h12 h21 h22
    (fun i => pair_nine lx (ys i) hW1 (hWy i).1 hW2 (hWy i).2.1 (hWy i).2.2.1 (hWy i).2.2.2.1
      (hWy i).2.2.2.2)

theorem exists_What1_pi1_lift (w : WeylGroup Tag.F4) : ∃ g ∈ What1 K σ, pi1 K σ g = w := by
  obtain ⟨g, hg, hgw⟩ := exists_What1_lift K σ (foldEquiv.symm w).2
  refine ⟨g, hg, ?_⟩
  rw [pi1_eq]
  have : (⟨psi1 K σ g, psi1_mem K σ g⟩ : ↥(relWeylTwist TwistTag.E6)) = foldEquiv.symm w :=
    Subtype.ext hgw
  rw [this, MulEquiv.apply_symm_apply]

@[expose] def BdTw {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (x : WeylGroup Tag.F4) : Prop :=
  ∀ s : ↥(N1 K σ), s ∈ torusT K σ hq hσ ⊔ What1 K σ → pi1 K σ s = x → s ^ 3 = 1 →
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(N1 K σ)))

theorem BdTw.inv {q : ℕ} {hq : 1 < q} {hσ : ∀ c, σ c = c ^ q} {x : WeylGroup Tag.F4}
    (h : BdTw K σ hq hσ x) : BdTw K σ hq hσ x⁻¹ := by
  intro s hs hsx hs3
  have h1 := h s⁻¹ (inv_mem hs) (by rw [map_inv, hsx, inv_inv]) (by rw [inv_pow, hs3, inv_one])
  have : Subgroup.centralizer ({s⁻¹} : Set ↥(N1 K σ)) = Subgroup.centralizer ({s} : Set _) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  rwa [this] at h1

section Instances

variable {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
  (h3 : 3 ∣ q - 1)

include hK h3 in
theorem twBd_a : BdTw K σ hq hσ wa := by
  intro s hs hsx hs3
  obtain ⟨hid, hf₁, hf₂⟩ := twA_a_data
  exact boundA_tw K σ hq hσ hK h3 laF lbF wa_mem_QF4 wb_mem_QF4 _ _ hid _ _ 1 3 hf₁ hf₂
    (by decide) (by decide) (by decide) (by decide) nine_dvd_QF4 s hs hsx hs3

include hK h3 in
theorem twBd_b : BdTw K σ hq hσ wb := by
  intro s hs hsx hs3
  obtain ⟨hid, hf₁, hf₂⟩ := twA_b_data
  refine boundA_tw K σ hq hσ hK h3 lbF laF wb_mem_QF4 wa_mem_QF4 _ _ hid _ _ 0 1 hf₁ hf₂
    (by decide) (by decide) (by decide) (by decide) ?_ s hs hsx hs3
  have : ({wordW Tag.F4 lbF, wordW Tag.F4 laF} : Set (WeylGroup Tag.F4)) = {wa, wb} := by
    rw [Set.pair_comm]; rfl
  rw [this]
  exact nine_dvd_QF4

include hK h3 in
theorem twBd_ab : BdTw K σ hq hσ (wa * wb) := by
  intro s hs hsx hs3
  obtain ⟨D1, D2, D3, hΞ, hXY, hf₁, hf₂⟩ := twB_ab_data
  obtain ⟨hW1, hW2, hWy⟩ := twYs_ab_W
  exact boundB_tw K σ hq hσ hK h3 lAB twYs_ab _ _ _ _ _ _ twB_ab_data_tab D1 D2 D3 hΞ hXY _ _ 1 3
    hf₁ hf₂ (by decide) (by decide) (by decide) (by decide) hW1 hW2 hWy s hs
    (by rw [hsx, lAB, wordW_append]; rfl)

include hK h3 in
theorem twBd_ab2 : BdTw K σ hq hσ (wa * wb * wb) := by
  intro s hs hsx hs3
  obtain ⟨D1, D2, D3, hΞ, hXY, hf₁, hf₂⟩ := twB_ab2_data
  obtain ⟨hW1, hW2, hWy⟩ := twYs_ab2_W
  exact boundB_tw K σ hq hσ hK h3 lAB2 twYs_ab2 _ _ _ _ _ _ twB_ab2_data_tab D1 D2 D3 hΞ hXY _ _ 1 3
    hf₁ hf₂ (by decide) (by decide) (by decide) (by decide) hW1 hW2 hWy s hs
    (by rw [hsx, lAB2, wordW_append, wordW_append]; rfl)

include hK h3 in
theorem twBd_of_QF4 {x : WeylGroup Tag.F4} (hx : x ∈ QF4) (hx1 : x ≠ 1) :
    BdTw K σ hq hσ x := by
  obtain ⟨i, j, rfl⟩ := mem_QF4 hx
  rw [pow_eq_pow_mod i wa_cube, pow_eq_pow_mod j wb_cube] at hx1 ⊢
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = a at hi hx1 ⊢
  generalize j % 3 = b at hj hx1 ⊢
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hx1
  · simpa using twBd_b K σ hq hσ hK h3
  · have := (twBd_b K σ hq hσ hK h3).inv
    rwa [inv_eq_sq_of_cube wb_cube, ← one_mul (wb ^ 2), ← pow_zero wa] at this
  · simpa using twBd_a K σ hq hσ hK h3
  · simpa using twBd_ab K σ hq hσ hK h3
  · have := twBd_ab2 K σ hq hσ hK h3
    simpa [pow_two, mul_assoc] using this
  · have := (twBd_a K σ hq hσ hK h3).inv
    rwa [inv_eq_sq_of_cube wa_cube, ← mul_one (wa ^ 2), ← pow_zero wb] at this
  · have := (twBd_ab2 K σ hq hσ hK h3).inv
    rwa [inv_wa_wb_wb] at this
  · have := (twBd_ab K σ hq hσ hK h3).inv
    rwa [inv_wa_wb] at this

end Instances

section Final

variable {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
  (h3 : 3 ∣ q - 1)

include hK h3 in
theorem eightyOne_dvd_centralizer_G (s : ↥(N1 K σ)) (hs : s ∈ torusT K σ hq hσ ⊔ What1 K σ)
    (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(N1 K σ))) := by
  by_cases hx : pi1 K σ s = 1
  ·
    obtain ⟨t, ht⟩ := mem_torusT_of_mem_sup K σ hq hσ hs ((pi1_eq_one_iff K σ s).1 hx)
    have hle : torusT K σ hq hσ ≤ Subgroup.centralizer ({s} : Set ↥(N1 K σ)) := by
      rintro _ ⟨u, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← ht, ← map_mul, ← map_mul, mul_comm]
    have h81 : 81 ∣ Nat.card (torusT K σ hq hσ) := by
      rw [card_torusT K σ hq hσ hK]
      have : (3 : ℕ) ^ 4 ∣ (q - 1) ^ 4 := pow_dvd_pow_of_dvd h3 4
      simpa using this
    exact h81.trans (Subgroup.card_dvd_of_le hle)
  · have hx3 : (pi1 K σ s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    obtain ⟨w, hw⟩ := exists_conj_mem_QF4 _ hx3
    obtain ⟨g, hgW, hgw⟩ := exists_What1_pi1_lift K σ w
    have hgG : g ∈ torusT K σ hq hσ ⊔ What1 K σ := Subgroup.mem_sup_right hgW
    have hconj : pi1 K σ (g * s * g⁻¹) = w * pi1 K σ s * w⁻¹ := by
      rw [map_mul, map_mul, map_inv, hgw]
    have hne : w * pi1 K σ s * w⁻¹ ≠ 1 := by
      intro h
      apply hx
      have h' := mul_inv_eq_one.1 h
      exact mul_left_cancel (h'.trans (mul_one w).symm)
    have hQ := twBd_of_QF4 K σ hq hσ hK h3 hw hne (g * s * g⁻¹)
      (mul_mem (mul_mem hgG hs) (inv_mem hgG)) hconj (by rw [conj_pow, hs3]; simp)
    rwa [card_centralizer_conj] at hQ

end Final

theorem exists_sylow_centralizer_kill_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq3 : (ℓ ^ f) % 3 = 1) :
    ∃ Q : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ),
      Nat.card Q = 3 ^ (Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ)).factorization 3 ∧
        ∀ s ∈ Q, s ^ 3 = 1 → s ≠ 1 →
          81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(graphFixedRootGroup TwistTag.E6 K σ))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have h3 : 3 ∣ ℓ ^ f - 1 := by omega
  obtain ⟨P, hP⟩ := exists_sylow_le_G K σ hℓ hf hK hσ hq3
  refine ⟨P, P.card_eq_multiplicity ▸ rfl, ?_⟩
  intro s hs hs3 hs1
  obtain ⟨s₀, hs₀G, rfl⟩ := hP hs
  have hs₀3 : s₀ ^ 3 = 1 := by
    apply Subgroup.inclusion_injective (graphFixedRootMonomial_le TwistTag.E6 K σ)
    rw [map_pow, hs3, map_one]
  have h81 := eightyOne_dvd_centralizer_G K σ hq hσ hK h3 s₀ hs₀G hs₀3
  have hle : (Subgroup.centralizer ({s₀} : Set ↥(N1 K σ))).map
      (Subgroup.inclusion (graphFixedRootMonomial_le TwistTag.E6 K σ)) ≤
      Subgroup.centralizer ({Subgroup.inclusion (graphFixedRootMonomial_le TwistTag.E6 K σ) s₀} :
        Set ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 hc)
  have hmap := Subgroup.card_map_of_injective
    (Subgroup.inclusion_injective (graphFixedRootMonomial_le TwistTag.E6 K σ))
    (K := Subgroup.centralizer ({s₀} : Set ↥(N1 K σ)))
  exact (hmap ▸ h81 : 81 ∣ Nat.card ↥((Subgroup.centralizer ({s₀} : Set ↥(N1 K σ))).map
    (Subgroup.inclusion (graphFixedRootMonomial_le TwistTag.E6 K σ)))).trans
    (Subgroup.card_dvd_of_le hle)

end TwE6Cent

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
