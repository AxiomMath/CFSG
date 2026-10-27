module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcCentGeneric
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4CentData
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcIntSolve

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.CentralCover

section W


@[expose] noncomputable abbrev SM (l : List (Fin Tag.F4.rank)) : Matrix (Fin 4) (Fin 4) ℤ :=
  (l.map (Smat Tag.F4)).prod

theorem wordW_nil : wordW Tag.F4 [] = 1 := by simp [wordW]

theorem wordW_cube_of (l : List (Fin Tag.F4.rank)) (h : SM (l ++ l ++ l) = SM []) :
    wordW Tag.F4 l ^ 3 = 1 := by
  have := wordW_eq_of_matrix Tag.F4 _ _ h
  rw [wordW_append, wordW_append, wordW_nil] at this
  simpa [pow_succ, mul_assoc] using this

theorem wordW_ne_one_of (l : List (Fin Tag.F4.rank)) (h : SM l ≠ SM []) :
    wordW Tag.F4 l ≠ 1 := fun h1 =>
  h (matrix_eq_of_wordW_eq Tag.F4 l [] (by rw [h1, wordW_nil]))

theorem wordW_comm_of (l l' : List (Fin Tag.F4.rank)) (h : SM (l ++ l') = SM (l' ++ l)) :
    wordW Tag.F4 l * wordW Tag.F4 l' = wordW Tag.F4 l' * wordW Tag.F4 l := by
  have := wordW_eq_of_matrix Tag.F4 _ _ h
  rwa [wordW_append, wordW_append] at this

theorem pair_nine (lx ly : List (Fin Tag.F4.rank)) (hx3 : SM (lx ++ lx ++ lx) = SM [])
    (hy3 : SM (ly ++ ly ++ ly) = SM []) (hx1 : SM lx ≠ SM []) (hyx : SM ly ≠ SM lx)
    (hy1 : SM ly ≠ SM []) (hyx2 : SM ly ≠ SM (lx ++ lx)) (hc : SM (lx ++ ly) = SM (ly ++ lx)) :
    9 ∣ Nat.card (Subgroup.closure ({wordW Tag.F4 lx, wordW Tag.F4 ly} :
      Set (WeylGroup Tag.F4))) := by
  refine nine_dvd_closure_pair _ _ (wordW_cube_of lx hx3) (wordW_ne_one_of lx hx1)
    (wordW_cube_of ly hy3) (wordW_comm_of lx ly hc) ?_
  intro hmem
  rcases zpow_mod_three_aux _ (wordW_cube_of lx hx3) (Subgroup.mem_zpowers_iff.1 hmem).choose with
    h | h | h
  all_goals
    have hspec := (Subgroup.mem_zpowers_iff.1 hmem).choose_spec
    rw [h] at hspec
  · exact hy1 (matrix_eq_of_wordW_eq Tag.F4 ly [] (by rw [← hspec, wordW_nil]))
  · exact hyx (matrix_eq_of_wordW_eq Tag.F4 ly lx hspec.symm)
  · exact hyx2 (matrix_eq_of_wordW_eq Tag.F4 ly (lx ++ lx)
      (by rw [wordW_append, ← hspec, sq]))

end W

section Core

variable (K : Type) [Field K] [Finite K]

theorem torusN_injective_F4 : Function.Injective (torusN Tag.F4 K) := by
  intro a b hab
  have h1 := congrArg (monoι Tag.F4 K) hab
  rw [monoι_torusN, monoι_torusN] at h1
  exact torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_F4 (Subtype.val_injective h1)

theorem exists_omega (h3 : 3 ∣ Nat.card K - 1) : ∃ ω : Kˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  exact exists_prime_orderOf_dvd_card' 3 this

theorem boundA_core (lx ly : List (Fin Tag.F4.rank)) (hx : wordW Tag.F4 lx ∈ QF4)
    (hy : wordW Tag.F4 ly ∈ QF4) (Φ Ψ : Matrix (Fin 4) (Fin 4) ℤ)
    (hid : 1 - RM ly = (1 - RM lx) * Φ + Ψ * (1 + RM lx + RM lx * RM lx))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((RM lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((RM lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW Tag.F4 lx, wordW Tag.F4 ly} :
      Set (WeylGroup Tag.F4))))
    (h3 : 3 ∣ Nat.card K - 1) (s : ↥(monomialSub Tag.F4 K))
    (hs : monomialSubHom (τ := Tag.F4) (K := K) s = wordW Tag.F4 lx) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨ω, hω⟩ := exists_omega K h3
  obtain ⟨R, hRW, hRinj, hRsurj, hRmem⟩ := exists_lift Tag.F4 K QF4 QF4_pGroup
  obtain ⟨gx, hgxR, hgx⟩ := hRsurj _ hx
  obtain ⟨gy, hgyR, hgy⟩ := hRsurj _ hy
  have hcomm : gy * gx = gx * gy := hRinj _ (mul_mem hgyR hgxR) _ (mul_mem hgxR hgyR) (by
    rw [map_mul, map_mul, hgx, hgy]; exact QF4_comm _ hy _ hx)
  have hgx3 : gx ^ 3 = 1 := hRinj _ (pow_mem hgxR 3) _ (one_mem R) (by
    rw [map_pow, map_one, hgx]; exact QF4_cube _ hx)
  exact caseA Tag.F4 K (torusN_injective_F4 K) lx ly s gx gy hs hgx hgy hcomm hgx3 hs3 Φ Ψ hid ω hω
    c₁ c₂ p₁ p₂ hf₁ hf₂ h11 h12 h21 h22 hQ

theorem nine_dvd_QF4 : 9 ∣ Nat.card (Subgroup.closure ({wa, wb} : Set (WeylGroup Tag.F4))) := by
  have h : Nat.card (Subgroup.closure ({wa, wb} : Set (WeylGroup Tag.F4))) = 9 := QF4_card
  rw [h]

theorem wa_mem_QF4 : wordW Tag.F4 laF ∈ QF4 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem wb_mem_QF4 : wordW Tag.F4 lbF ∈ QF4 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem boundA_a (h3 : 3 ∣ Nat.card K - 1) (s : ↥(monomialSub Tag.F4 K))
    (hs : monomialSubHom (τ := Tag.F4) (K := K) s = wordW Tag.F4 laF) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨hid, hf₁, hf₂⟩ := boundA_a_data
  exact boundA_core K laF lbF wa_mem_QF4 wb_mem_QF4 _ _ hid _ _ 1 3 hf₁ hf₂ (by decide)
    (by decide) (by decide) (by decide) nine_dvd_QF4
    h3 s hs hs3

theorem boundA_b (h3 : 3 ∣ Nat.card K - 1) (s : ↥(monomialSub Tag.F4 K))
    (hs : monomialSubHom (τ := Tag.F4) (K := K) s = wordW Tag.F4 lbF) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨hid, hf₁, hf₂⟩ := boundA_b_data
  refine boundA_core K lbF laF wb_mem_QF4 wa_mem_QF4 _ _ hid _ _ 0 1 hf₁ hf₂ (by decide)
    (by decide) (by decide) (by decide) ?_ h3 s hs hs3
  have : ({wordW Tag.F4 lbF, wordW Tag.F4 laF} : Set (WeylGroup Tag.F4)) = {wa, wb} := by
    rw [Set.pair_comm]; rfl
  rw [this]
  exact nine_dvd_QF4

theorem boundB_core (lx : List (Fin Tag.F4.rank)) (ys : Fin 4 → List (Fin Tag.F4.rank))
    (Θ Ξ : Matrix (Fin 4) (Fin 4) ℤ) (l₂ l₃ θ₂ θ₃ : Fin 4 → ℤ)
    (tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
      (1 - RM lx).mulVec d = (1 - RM (ys i)).mulVec
        (((a : ℕ) : ℤ) • ![0, 0, 1, 0] + ((b : ℕ) : ℤ) • ![0, 0, 0, 1]))
    (D1 : (1 - RM lx) * Θ + Matrix.vecMulVec ![0, 0, 1, 0] l₂ +
      Matrix.vecMulVec ![0, 0, 0, 1] l₃ = 1)
    (D2 : (1 - RM lx).mulVec θ₂ = (3 : ℤ) • ![0, 0, 1, 0])
    (D3 : (1 - RM lx).mulVec θ₃ = (3 : ℤ) • ![0, 0, 0, 1])
    (hΞ : (1 - RM lx) * Ξ = (3 : ℤ) • 1)
    (hXY : ∀ i : Fin 4, RM lx * RM (ys i) = RM (ys i) * RM lx)
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((RM lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((RM lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hW1 : SM (lx ++ lx ++ lx) = SM []) (hW2 : SM lx ≠ SM [])
    (hWy : ∀ i, SM (ys i ++ ys i ++ ys i) = SM [] ∧ SM (ys i) ≠ SM lx ∧ SM (ys i) ≠ SM [] ∧
      SM (ys i) ≠ SM (lx ++ lx) ∧ SM (lx ++ ys i) = SM (ys i ++ lx))
    (h3 : 3 ∣ Nat.card K - 1) (s : ↥(monomialSub Tag.F4 K))
    (hs : monomialSubHom (τ := Tag.F4) (K := K) s = wordW Tag.F4 lx) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨ω, hω⟩ := exists_omega K h3
  obtain ⟨gx, hgxW, hgx⟩ := What_surj Tag.F4 K (wordW Tag.F4 lx)
  have hsolve := solve_int_fpf (RM lx) (fun i => RM (ys i)) hXY Θ _ _ l₂ l₃ θ₂ θ₃ D1 D2 D3 tab
  exact caseB Tag.F4 K (torusN_injective_F4 K) lx ys s gx hs hgx hgxW
    (fun i => (wordW_comm_of lx (ys i) (hWy i).2.2.2.2).symm) Ξ hΞ hsolve ω hω c₁ c₂ p₁ p₂ hf₁ hf₂
    h11 h12 h21 h22
    (fun i => pair_nine lx (ys i) hW1 (hWy i).1 hW2 (hWy i).2.1 (hWy i).2.2.1 (hWy i).2.2.2.1
      (hWy i).2.2.2.2)


theorem ys_ab_W :
    SM (lAB ++ lAB ++ lAB) = SM [] ∧ SM lAB ≠ SM [] ∧ ∀ i : Fin 4,
      SM (ys_ab i ++ ys_ab i ++ ys_ab i) = SM [] ∧ SM (ys_ab i) ≠ SM lAB ∧
      SM (ys_ab i) ≠ SM [] ∧ SM (ys_ab i) ≠ SM (lAB ++ lAB) ∧
      SM (lAB ++ ys_ab i) = SM (ys_ab i ++ lAB) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel

theorem bound_ab (h3 : 3 ∣ Nat.card K - 1) (s : ↥(monomialSub Tag.F4 K))
    (hs : monomialSubHom (τ := Tag.F4) (K := K) s = wordW Tag.F4 lAB) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨D1, D2, D3, hΞ, hXY, hf₁, hf₂⟩ := boundB_ab_data
  obtain ⟨hW1, hW2, hWy⟩ := ys_ab_W
  exact boundB_core K lAB ys_ab _ _ _ _ _ _ boundB_ab_data_tab D1 D2 D3 hΞ hXY _ _ 1 3 hf₁
    hf₂ (by decide) (by decide) (by decide) (by decide) hW1 hW2 hWy h3 s hs

theorem ys_ab2_W :
    SM (lAB2 ++ lAB2 ++ lAB2) = SM [] ∧ SM lAB2 ≠ SM [] ∧ ∀ i : Fin 4,
      SM (ys_ab2 i ++ ys_ab2 i ++ ys_ab2 i) = SM [] ∧ SM (ys_ab2 i) ≠ SM lAB2 ∧
      SM (ys_ab2 i) ≠ SM [] ∧ SM (ys_ab2 i) ≠ SM (lAB2 ++ lAB2) ∧
      SM (lAB2 ++ ys_ab2 i) = SM (ys_ab2 i ++ lAB2) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel

theorem bound_ab2 (h3 : 3 ∣ Nat.card K - 1) (s : ↥(monomialSub Tag.F4 K))
    (hs : monomialSubHom (τ := Tag.F4) (K := K) s = wordW Tag.F4 lAB2) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨D1, D2, D3, hΞ, hXY, hf₁, hf₂⟩ := boundB_ab2_data
  obtain ⟨hW1, hW2, hWy⟩ := ys_ab2_W
  exact boundB_core K lAB2 ys_ab2 _ _ _ _ _ _ boundB_ab2_data_tab D1 D2 D3 hΞ hXY _ _ 1 3 hf₁
    hf₂ (by decide) (by decide) (by decide) (by decide) hW1 hW2 hWy h3 s hs

@[expose] def BdF4 (x : WeylGroup Tag.F4) : Prop :=
  ∀ s : ↥(monomialSub Tag.F4 K), monomialSubHom (τ := Tag.F4) (K := K) s = x → s ^ 3 = 1 →
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K)))

theorem BdF4.inv {x : WeylGroup Tag.F4} (h : BdF4 K x) : BdF4 K x⁻¹ := by
  intro s hs hs3
  have h1 := h s⁻¹ (by rw [map_inv, hs, inv_inv]) (by rw [inv_pow, hs3, inv_one])
  have : Subgroup.centralizer ({s⁻¹} : Set ↥(monomialSub Tag.F4 K)) =
      Subgroup.centralizer ({s} : Set ↥(monomialSub Tag.F4 K)) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  rwa [this] at h1

theorem bdF4_wa (h3 : 3 ∣ Nat.card K - 1) : BdF4 K wa := fun s hs hs3 => boundA_a K h3 s hs hs3

theorem bdF4_wb (h3 : 3 ∣ Nat.card K - 1) : BdF4 K wb := fun s hs hs3 => boundA_b K h3 s hs hs3

theorem bdF4_ab (h3 : 3 ∣ Nat.card K - 1) : BdF4 K (wa * wb) := fun s hs _ =>
  bound_ab K h3 s (by rw [hs, lAB, wordW_append]; rfl)

theorem bdF4_ab2 (h3 : 3 ∣ Nat.card K - 1) : BdF4 K (wa * wb * wb) := fun s hs _ =>
  bound_ab2 K h3 s (by rw [hs, lAB2, wordW_append, wordW_append]; rfl)

theorem inv_eq_sq_of_cube {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) : g⁻¹ = g ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  exact h

theorem inv_wa_wb : (wa * wb)⁻¹ = wa ^ 2 * wb ^ 2 := by
  rw [mul_inv_rev, inv_eq_sq_of_cube wb_cube, inv_eq_sq_of_cube wa_cube]
  exact ((show Commute wa wb from wa_wb_comm).symm.pow_pow 2 2).eq

theorem inv_wa_wb_wb : (wa * wb * wb)⁻¹ = wa ^ 2 * wb := by
  rw [mul_inv_rev, mul_inv_rev, inv_eq_sq_of_cube wb_cube, inv_eq_sq_of_cube wa_cube]
  have h4 : wb ^ 2 * wb ^ 2 = wb := by
    rw [← pow_add]; calc wb ^ (2 + 2) = wb ^ 3 * wb := by rw [← pow_succ]
      _ = wb := by rw [wb_cube, one_mul]
  rw [← mul_assoc, h4]
  simpa using ((show Commute wa wb from wa_wb_comm).symm.pow_pow 1 2).eq

theorem bdF4_of_QF4 (h3 : 3 ∣ Nat.card K - 1) {x : WeylGroup Tag.F4} (hx : x ∈ QF4)
    (hx1 : x ≠ 1) : BdF4 K x := by
  obtain ⟨i, j, rfl⟩ := mem_QF4 hx
  rw [pow_eq_pow_mod i wa_cube, pow_eq_pow_mod j wb_cube] at hx1 ⊢
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = a at hi hx1 ⊢
  generalize j % 3 = b at hj hx1 ⊢
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hx1
  · simpa using bdF4_wb K h3
  · have := (bdF4_wb K h3).inv
    rwa [inv_eq_sq_of_cube wb_cube, ← one_mul (wb ^ 2), ← pow_zero wa] at this
  · simpa using bdF4_wa K h3
  · simpa using bdF4_ab K h3
  · have := bdF4_ab2 K h3
    simpa [pow_two, mul_assoc] using this
  · have := (bdF4_wa K h3).inv
    rwa [inv_eq_sq_of_cube wa_cube, ← mul_one (wa ^ 2), ← pow_zero wb] at this
  · have := (bdF4_ab2 K h3).inv
    rwa [inv_wa_wb_wb] at this
  · have := (bdF4_ab K h3).inv
    rwa [inv_wa_wb] at this

theorem bd_torus (h3 : 3 ∣ Nat.card K - 1) (n : ↥(monomialSub Tag.F4 K))
    (hn : monomialSubHom (τ := Tag.F4) (K := K) n = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({n} : Set ↥(monomialSub Tag.F4 K))) := by
  obtain ⟨t, rfl⟩ := exists_torusN_of_psi_eq_one Tag.F4 K hn
  have hle : (torusN Tag.F4 K).range ≤
      Subgroup.centralizer ({torusN Tag.F4 K t} : Set ↥(monomialSub Tag.F4 K)) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (torusN_comm Tag.F4 t u).symm
  have hcard : Nat.card (torusN Tag.F4 K).range = (Nat.card K - 1) ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (torusN_injective_F4 K)).toEquiv, Nat.card_pi]
    simp [Nat.card_units]
    rfl
  have h81 : 81 ∣ (Nat.card K - 1) ^ 4 := by
    have : (3 : ℕ) ^ 4 ∣ (Nat.card K - 1) ^ 4 := pow_dvd_pow_of_dvd h3 4
    simpa using this
  exact (hcard ▸ h81).trans (Subgroup.card_dvd_of_le hle)

theorem eightyOne_dvd_centralizer_F4 (h3 : 3 ∣ Nat.card K - 1) (n : ↥(monomialSub Tag.F4 K))
    (hn : orderOf n = 3) :
    81 ∣ Nat.card (Subgroup.centralizer ({n} : Set ↥(monomialSub Tag.F4 K))) := by
  have hn3 : n ^ 3 = 1 := by rw [← hn]; exact pow_orderOf_eq_one n
  by_cases hz1 : monomialSubHom (τ := Tag.F4) (K := K) n = 1
  · exact bd_torus K h3 n hz1
  · have hz3 : (monomialSubHom (τ := Tag.F4) (K := K) n) ^ 3 = 1 := by
      rw [← map_pow, hn3, map_one]
    obtain ⟨w, hw⟩ := exists_conj_mem_QF4 _ hz3
    obtain ⟨g, -, hg⟩ := What_surj Tag.F4 K w
    have hconj : monomialSubHom (τ := Tag.F4) (K := K) (g * n * g⁻¹) =
        w * monomialSubHom (τ := Tag.F4) (K := K) n * w⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg]
    have hne : w * monomialSubHom (τ := Tag.F4) (K := K) n * w⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have h' := mul_inv_eq_one.1 h
      exact mul_left_cancel (h'.trans (mul_one w).symm)
    have hQ := bdF4_of_QF4 K h3 hw hne (g * n * g⁻¹) hconj (by rw [conj_pow, hn3]; simp)
    rwa [card_centralizer_conj] at hQ

end Core

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
