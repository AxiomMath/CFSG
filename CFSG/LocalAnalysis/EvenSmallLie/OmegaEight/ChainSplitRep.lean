module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTil
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeMat
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitLift

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem rep_pow {Φ : (Fin 6 → ZMod 4) → G} {x : G} {M : Matrix (Fin 6) (Fin 6) (ZMod 4)}
    (h : Rep Φ x M) (n : ℕ) : Rep Φ (x ^ n) (M ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Coord4.rep_one
  | succ n ih => rw [pow_succ, pow_succ]; exact Coord4.rep_mul ih h

section Table


theorem table_mul {ε : Eps} {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    ∃ m < 128, toMat4 (tilGet ε i) * toMat4 (tilGet ε j) = toMat4 (tilGet ε m) :=
  ⟨_, (tab_facts ε).2.2.2.1 i hi j hj, by rw [tilIdx_spec ((tab_facts ε).2.2.2.1 i hi j hj),
    toMat4_mul4]⟩

theorem table_pow {ε : Eps} {i : ℕ} (hi : i < 128) (n : ℕ) :
    ∃ j < 128, toMat4 (tilGet ε i) ^ n = toMat4 (tilGet ε j) := by
  induction n with
  | zero => exact ⟨0, by norm_num, by rw [pow_zero, (tab_facts ε).1, toMat4_one4]⟩
  | succ n ih =>
    obtain ⟨j, hj, hjn⟩ := ih
    obtain ⟨m, hm, hmn⟩ := table_mul (ε := ε) hj hi
    exact ⟨m, hm, by rw [pow_succ, hjn, hmn]⟩

theorem rep_inv_table [Finite G] {ε : Eps} {Φ : (Fin 6 → ZMod 4) → G} {x : G} {i : ℕ}
    (hi : i < 128) (h : Rep Φ x (toMat4 (tilGet ε i))) :
    ∃ j < 128, Rep Φ x⁻¹ (toMat4 (tilGet ε j)) := by
  have hpos := orderOf_pos x
  have hx : x⁻¹ = x ^ (orderOf x - 1) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  obtain ⟨j, hj, hjn⟩ := table_pow (ε := ε) hi (orderOf x - 1)
  exact ⟨j, hj, hx ▸ hjn ▸ rep_pow h _⟩

end Table

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A)
include hS hC

theorem levelB [Finite G] : Level Q 2 (pw A (2 ^ (k - 2))) := by
  have hk := hC.two_le
  have := hC.level_mX hS (m := k - 2) (by omega)
  rwa [show k - (k - 2) = 2 by omega] at this

omit hS in
theorem K_conj_memB {x : G} (hx : x ∈ P ⊔ zpowers x₀) {y : G} (hy : y ∈ pw A (2 ^ (k - 2))) :
    x * y * x⁻¹ ∈ pw A (2 ^ (k - 2)) :=
  pw_conj_mem_gen hC.level.comm (hC.P_norm x hx) hy

omit hS in
theorem t_invB {y : G} (hy : y ∈ pw A (2 ^ (k - 2))) : t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨b, hb, rfl⟩ := (mem_pw hC.level.comm).1 hy
  rw [← conj_pow]
  rcases hC.act with h | ⟨hk, h⟩
  · rw [h b hb, inv_pow]
  · rw [h b hb, (Commute.inv_left ((Commute.refl b).pow_right _)).mul_pow, inv_pow, ← pow_mul,
      ← pow_add]
    rw [show k - 1 + (k - 2) = k + (k - 3) by omega, pow_add, pow_mul,
      hC.level.pow_eq_one b hb, one_pow, mul_one]

theorem exists_coordB [Finite G] :
    ∃ Φ : (Fin 6 → ZMod 4) → G, Coord4 (pw A (2 ^ (k - 2))) ψ Φ ∧
      (∀ w, Rep Φ (wordElt p w) (prodW ε (c0Mat ε) w)) ∧ Rep Φ t (-1) ∧
      ∃ ρ : G, (ρ = x₀ ∨ ρ = t * x₀) ∧ Rep Φ ρ (toMat4 (xTil ε)) ∧
        ∀ h ∈ U ⊔ zpowers ρ, ∃ i < 128, Rep Φ h (toMat4 (tilGet ε i)) := by
  have hR := hS.rad
  have hB := hC.levelB hS
  have hPQ : ∀ x ∈ P, x ∈ centralizer (Q : Set G) → x ∈ Q := fun x hx hc =>
    hS.mem_Q_of_mem_P hx hc
  obtain ⟨Φ, hΦ, hw⟩ := exists_coord_lift_of hR hPQ hB fun x hx y hy =>
    hC.K_conj_memB (mem_sup_left hx) hy
  have hrept : Rep Φ t (-1) := fun v => by
    rw [hC.t_invB (hΦ.mem v), neg_mulVec, one_mulVec, hΦ.neg]
  obtain ⟨hX2, hXred, hXconj⟩ := xTil_facts ε
  set X := toMat4 (xTil ε)
  set r := toMat 6 6 (CPrime.reflRows ε (n0 ε))
  have hr2 : r * r = 1 := by rw [← hXred, ← Matrix.map_mul, hX2, Matrix.map_one _ (map_zero _)
    (map_one _)]
  have hx₀K : x₀ ∈ P ⊔ zpowers x₀ := mem_sup_right (mem_zpowers x₀)
  obtain ⟨Y, hYr⟩ := hΦ.exists_rep (g := x₀) fun y hy => hC.K_conj_memB hx₀K hy
  have hYred : Y.map red4 = r := hΦ.map_red4_of_rep hYr hR.ψ_inj hS.inputs.outer.act
  have hx₀N := hS.x₀_mem_normalizer_Q
  have hlinx : ∀ v, lin ψ x₀ v = r *ᵥ v := fun v =>
    (hR.lin_eq_iff hx₀N v _).2 (hS.inputs.outer.act v)
  have hlinx' : ∀ v, lin ψ x₀⁻¹ v = r *ᵥ v := fun v => by
    have h1 := hR.lin_inv hx₀N v
    rw [hlinx] at h1
    calc lin ψ x₀⁻¹ v = (r * r) *ᵥ lin ψ x₀⁻¹ v := by rw [hr2, one_mulVec]
      _ = r *ᵥ (r *ᵥ lin ψ x₀⁻¹ v) := by rw [mulVec_mulVec]
      _ = r *ᵥ v := by rw [h1]
  have hcomm : ∀ s < 6, X * Y * liftW ε (c0Mat ε) s = liftW ε (c0Mat ε) s * (X * Y) := by
    intro s hs
    have hps : Rep Φ (pAt p s) (liftW ε (c0Mat ε) s) := by
      have := hw [s]
      rwa [show wordElt p [s] = pAt p s by simp [wordElt], show prodW ε (c0Mat ε) [s] =
        liftW ε (c0Mat ε) s by rw [prodW_cons, prodW_nil, mul_one]] at this
    have hpP := hR.pAt_mem s
    have hcP := hS.x₀_conj_mem_P hpP
    have hcl : ∀ v, lin ψ (x₀ * pAt p s * x₀⁻¹) v =
        toMat 6 6 (wordRows ε ((reflWords ε).getD s [])) *ᵥ v := fun v => by
      rw [hR.lin_mul (mul_mem hx₀N (hR.P_le_normalizer hpP)) (inv_mem hx₀N),
        hR.lin_mul hx₀N (hR.P_le_normalizer hpP), hlinx', hR.lin_pAt, hlinx,
        (hXconj s hs).2, mulVec_mulVec, mulVec_mulVec]
    have hrc := rep_of_mem_P hR hPQ hB hΦ hw hcP hcl
    have h1 := Coord4.rep_mul hYr hps
    have h2 := Coord4.rep_mul hrc hYr
    rw [show x₀ * pAt p s * x₀⁻¹ * x₀ = x₀ * pAt p s by group] at h2
    have h3 := hΦ.rep_unique h1 h2
    rw [← (hXconj s hs).1] at h3
    calc X * Y * liftW ε (c0Mat ε) s = X * (Y * liftW ε (c0Mat ε) s) := mul_assoc _ _ _
      _ = X * (X * liftW ε (c0Mat ε) s * X * Y) := by rw [h3]
      _ = (X * X) * liftW ε (c0Mat ε) s * (X * Y) := by simp only [mul_assoc]
      _ = liftW ε (c0Mat ε) s * (X * Y) := by rw [hX2, one_mul]
  have hZred : (X * Y).map red4 = 1 := by
    rw [Matrix.map_mul, hXred, hYred, hr2]
  obtain ⟨N, hN⟩ := eq_lift4_add (X * Y)
  rw [hZred, lift4_one'] at hN
  have hNcomm : ∀ i : Fin 6, N * genMat ε i = genMat ε i * N := by
    intro i
    have h := hcomm i i.isLt
    rw [hN, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm] at h
    have h' := add_left_cancel h
    rw [two_smul_lift4_mul_right, two_smul_lift4_mul_left, map_red4_liftW] at h'
    exact (two_smul_lift4_inj h').symm ▸ rfl
  have hY : Y = X ∨ Y = -X := by
    have hXY : Y = X * (X * Y) := by rw [← mul_assoc, hX2, one_mul]
    rcases endF2 ε (fun v => N *ᵥ v) (fun v w => mulVec_add _ _ _) (fun i v => by
      rw [mulVec_mulVec, mulVec_mulVec, hNcomm]) with h0 | h1
    · left
      have : N = 0 := Matrix.ext_iff_mulVec.2 fun v => by rw [h0 v, zero_mulVec]
      rw [hXY, hN, this, lift4_zero', smul_zero, add_zero, mul_one]
    · right
      have : N = 1 := Matrix.ext_iff_mulVec.2 fun v => by rw [h1 v, one_mulVec]
      rw [hXY, hN, this, lift4_one']
      have : (1 : Matrix (Fin 6) (Fin 6) (ZMod 4)) + (2 : ZMod 4) • 1 = -1 := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, one_apply, smul_eq_mul]
        split_ifs <;> decide
      rw [this, mul_neg_one]
  obtain ⟨ρ, hρ, hρX⟩ : ∃ ρ : G, (ρ = x₀ ∨ ρ = t * x₀) ∧ Rep Φ ρ X := by
    rcases hY with h | h
    · exact ⟨x₀, Or.inl rfl, h ▸ hYr⟩
    · refine ⟨t * x₀, Or.inr rfl, ?_⟩
      have := Coord4.rep_mul hrept hYr
      rwa [h, neg_mul_neg, one_mul] at this
  refine ⟨Φ, hΦ, hw, hrept, ρ, hρ, hρX, fun h hh => ?_⟩
  have hlink := hS.inputs.link
  have hle : U ⊔ zpowers ρ ≤ closure ((Q : Set G) ∪ Set.range u ∪ {ρ}) :=
    sup_le (hlink.U_le.trans (closure_mono Set.subset_union_left))
      (zpowers_le.2 (subset_closure (Set.mem_union_right _ rfl)))
  refine closure_induction (p := fun x _ => ∃ i < 128, Rep Φ x (toMat4 (tilGet ε i)))
    ?_ ?_ ?_ ?_ (hle hh)
  · rintro x ((hxQ | ⟨k', rfl⟩) | hx)
    · exact ⟨0, by norm_num, by
        rw [(tab_facts ε).1, toMat4_one4]; exact hΦ.rep_of_mem_A hB.comm (hB.Q_le hxQ)⟩
    · obtain ⟨hwk, hidx⟩ := (tab_facts ε).2.2.1 k' k'.isLt
      refine ⟨_, hidx, ?_⟩
      rw [tilIdx_spec hidx, toMat4_prod4]
      have hkP := hR.U_le_P (hlink.u_mem k')
      refine rep_of_mem_P hR hPQ hB hΦ hw hkP fun v => ?_
      rw [(hR.lin_eq_iff (hR.P_le_normalizer hkP) _ _).2 (hlink.u_act k' v), hwk,
        urRows_eq_uRows]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, (tab_facts ε).2.1, by rw [tilIdx_spec (tab_facts ε).2.1]; exact hρX⟩
  · exact ⟨0, by norm_num, by rw [(tab_facts ε).1, toMat4_one4]; exact Coord4.rep_one⟩
  · rintro x y - - ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩
    obtain ⟨m, hm, hmn⟩ := table_mul (ε := ε) hi hj
    exact ⟨m, hm, hmn ▸ Coord4.rep_mul hxi hyj⟩
  · rintro x - ⟨i, hi, hxi⟩
    exact rep_inv_table hi hxi

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
