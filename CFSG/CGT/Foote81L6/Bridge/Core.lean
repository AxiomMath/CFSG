module

public import CFSG.CGT.Foote81L6.Bridge.Parts
public import CFSG.CGT.Foote81L6.Basic

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

variable {n : ℕ} (hn : 3 ≤ n)
include hn

theorem AT_le_map_Atil : AT hn ≤ (Atil n).map (πT n) := by
  apply dihedralLift_range_le
  · exact ⟨toP (Gen.rA n), mem_Atil.2 (by rw [coe_toP Gen.det_rA]; exact ⟨rfl, rfl, rfl⟩), rfl⟩
  · exact ⟨toP (Gen.sA n), mem_Atil.2 (by
      rw [coe_toP (Gen.det_sA (n := n) (by omega))]; exact ⟨rfl, rfl, rfl⟩), rfl⟩

theorem B₀T_le_map_Btil : B₀T hn ≤ (Btil n).map (πT n) := by
  apply dihedralLift_range_le
  · exact ⟨toP (Gen.ρ₀ n), mem_Btil.2 (by rw [coe_toP Gen.det_ρ₀]; rfl), rfl⟩
  · exact ⟨toP (Gen.κ₀ n), mem_Btil.2 (by rw [coe_toP Gen.det_κ₀]; rfl), rfl⟩

theorem B₁T_le_map_Btil : B₁T hn ≤ (Btil n).map (πT n) := by
  apply dihedralLift_range_le
  · exact ⟨toP (Gen.ρ₁ n), mem_Btil.2 (by rw [coe_toP Gen.det_ρ₁]; rfl), rfl⟩
  · exact ⟨toP (Gen.κ₁ n), mem_Btil.2 (by rw [coe_toP Gen.det_κ₁]; rfl), rfl⟩

theorem BT_le_map_Btil : BT hn ≤ (Btil n).map (πT n) := by
  refine sup_le (sup_le (B₀T_le_map_Btil hn) (B₁T_le_map_Btil hn)) (zpowers_le.2 ?_)
  exact ⟨toP (Gen.s n), mem_Btil.2 (by rw [coe_toP (Gen.det_s hn)]; rfl), rfl⟩

theorem AT_inf_BT : AT hn ⊓ BT hn = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf (AT_le_map_Atil hn) (BT_le_map_Btil hn)).trans
    (inf_map_Atil_Btil (by omega)).le)

theorem AT_comm_BT : ∀ x ∈ AT hn, ∀ y ∈ BT hn, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := AT_le_map_Atil hn hx
  obtain ⟨b, hb, rfl⟩ := BT_le_map_Btil hn hy
  rw [← map_mul, ← map_mul, Atil_comm_Btil ha hb]

theorem conj_tT_AT : ∀ x ∈ AT hn, tT n * x * (tT n)⁻¹ ∈ AT hn := by
  intro x hx
  have h := map_conj_dihedralLift_range_le _ (rAT n) (sAT n) (rAT_pow_qr hn) (sAT_mul_sAT hn)
    (sAT_conj_rAT hn) (tT n) (H := AT hn)
    (by rw [tT_conj_rAT hn]; exact inv_mem (rAT_mem_AT hn))
    (by rw [tT_conj_sAT hn]; exact mul_mem (pow_mem (rAT_mem_AT hn) _) (sAT_mem_AT hn))
  exact h ⟨x, hx, rfl⟩

theorem map_conj_tT_B₀T : (B₀T hn).map (MulAut.conj (tT n)).toMonoidHom ≤ B₁T hn :=
  map_conj_dihedralLift_range_le _ _ _ _ _ _ _
    (by rw [tT_conj_ρ₀T hn]; exact ρ₁T_mem_B₁T hn)
    (by rw [tT_conj_κ₀T hn]; exact κ₁T_mem_B₁T hn)

theorem map_conj_tT_B₁T : (B₁T hn).map (MulAut.conj (tT n)).toMonoidHom ≤ B₀T hn :=
  map_conj_dihedralLift_range_le _ _ _ _ _ _ _
    (by rw [tT_conj_ρ₁T hn]; exact ρ₀T_mem_B₀T hn)
    (by rw [tT_conj_κ₁T hn]; exact κ₀T_mem_B₀T hn)

theorem conj_tT_mem_B₁T {x : TM n} (hx : x ∈ B₀T hn) : tT n * x * (tT n)⁻¹ ∈ B₁T hn :=
  map_conj_tT_B₀T hn ⟨x, hx, rfl⟩

theorem conj_tT_mem_B₀T {x : TM n} (hx : x ∈ B₁T hn) : tT n * x * (tT n)⁻¹ ∈ B₀T hn :=
  map_conj_tT_B₁T hn ⟨x, hx, rfl⟩

theorem b₀T_mem : b₀T hn ∈ B₀T hn := ⟨_, rfl⟩

theorem b₁T_mem : b₁T hn ∈ B₁T hn := ⟨_, rfl⟩

theorem conj_tT_BT : ∀ x ∈ BT hn, tT n * x * (tT n)⁻¹ ∈ BT hn := by
  have hle : (BT hn).map (MulAut.conj (tT n)).toMonoidHom ≤ BT hn := by
    rw [BT, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ((map_conj_tT_B₀T hn).trans (B₁T_le_BT hn))
      ((map_conj_tT_B₁T hn).trans (B₀T_le_BT hn))) ?_
    rw [MonoidHom.map_zpowers, zpowers_le]
    change tT n * sT n * (tT n)⁻¹ ∈ BT hn
    rw [tT_conj_sT hn, ← b₀T_eq hn, ← b₁T_eq hn]
    exact mul_mem (mul_mem (sT_mem_BT hn) (B₀T_le_BT hn (b₀T_mem hn)))
      (B₁T_le_BT hn (b₁T_mem hn))
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem card_B₀T : Nat.card (B₀T hn) = 2 ^ n := by
  rw [B₀T, ← Nat.card_congr (MonoidHom.ofInjective (f₀_injective hn)).toEquiv,
    DihedralGroup.nat_card, ← pow_succ', show n - 1 + 1 = n by omega]

theorem card_B₁T : Nat.card (B₁T hn) = 2 ^ n := by
  rw [B₁T, ← Nat.card_congr (MonoidHom.ofInjective (f₁_injective hn)).toEquiv,
    DihedralGroup.nat_card, ← pow_succ', show n - 1 + 1 = n by omega]

theorem card_AT : Nat.card (AT hn) = 2 ^ (n - 1) := by
  rw [AT, ← Nat.card_congr (MonoidHom.ofInjective (fA_injective hn)).toEquiv,
    DihedralGroup.nat_card, ← pow_succ', show n - 2 + 1 = n - 1 by omega]

theorem B₀T_comm_B₁T : ∀ x ∈ B₀T hn, ∀ y ∈ B₁T hn, x * y = y * x := fun _ hx _ hy =>
  commute_of_mem_dihedralLift_range _ _ _ _ _ _ (commute_ρ₀T_ρ₁T hn) (commute_ρ₀T_κ₁T hn)
    (commute_κ₀T_ρ₁T hn) (commute_κ₀T_κ₁T hn) hx hy

theorem b₀T_not_mem_B₁T : b₀T hn ∉ B₁T hn := by
  intro h
  obtain ⟨j, hj | hj⟩ := (mem_dihedralLift_range_iff _ _ _ _ _ _).1 h
  ·
    rw [b₀T_eq hn, ρ₀T, ρ₁T, ← map_pow, ← map_pow, πT_eq_iff] at hj
    obtain ⟨ν, hν, hν'⟩ := hj
    have h1 := congrArg (fun y : P n => (y : PHat n).x₁.i) hν'
    have h2 := congrArg (fun y : P n => (y : PHat n).x₂.i) hν'
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP Gen.det_ρ₀, coe_toP Gen.det_ρ₁,
      Gen.ρ₁_pow, Gen.ρ₀_pow_qr hn, Gen.b₀H, PHat.mul_x₁, PHat.mul_x₂, PHat.sw₁_zero,
      PHat.sw₂_zero, SD.mul_i, tw_zero] at h1 h2
    apply hf_ne_zero (n := n) (by omega)
    rcases hν with rfl | rfl | rfl | rfl <;>
      simp only [Subgroup.coe_mul, coe_cP, coe_zP, PHat.c, PHat.zF, PHat.mul_x₁, PHat.mul_x₂,
        PHat.sw₁_zero, PHat.sw₂_zero, SD.mul_i, tw_zero, SD.z, SD.one_i, OneMemClass.coe_one,
        PHat.one_x₁, PHat.one_x₂, add_zero, zero_add] at h1 h2
    · linear_combination -(h1 + h2) + hf_eq_two_mul_qr n
    · linear_combination -(h1 + h2) + hf_eq_two_mul_qr n - two_mul_hf n
    · linear_combination -(h1 + h2) + hf_eq_two_mul_qr n
    · linear_combination -(h1 + h2) + hf_eq_two_mul_qr n - two_mul_hf n
  ·
    have := congrArg (eT n) hj
    rw [map_mul, map_pow, eT_ρ₁T, one_pow, mul_one, eT_κ₁T, b₀T_eq hn, map_pow, eT_ρ₀T,
      one_pow] at this
    exact ofAdd_one_ne_one this.symm

theorem B₀T_inf_B₁T : B₀T hn ⊓ B₁T hn = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx₀, hx₁⟩
  rw [mem_bot]
  obtain ⟨d, rfl⟩ := hx₀
  have hc : ∀ g : DihedralGroup (2 ^ (n - 1)), g * d = d * g := by
    intro g
    apply f₀_injective hn
    rw [map_mul, map_mul]
    exact B₀T_comm_B₁T hn _ ⟨g, rfl⟩ _ hx₁
  rcases eq_one_or_zc_of_comm (by omega) hc with rfl | rfl
  · exact map_one _
  · exact absurd hx₁ (b₀T_not_mem_B₁T hn)

theorem map_conj_sT_B₀T_le : (B₀T hn).map (MulAut.conj (sT n)).toMonoidHom ≤ B₁T hn :=
  map_conj_dihedralLift_range_le _ _ _ _ _ _ _
    (by rw [sT_conj_ρ₀T hn]; exact pow_mem (ρ₁T_mem_B₁T hn) _)
    (by rw [sT_conj_κ₀T hn]; exact mul_mem (κ₁T_mem_B₁T hn) (pow_mem (inv_mem (ρ₁T_mem_B₁T hn)) _))

theorem map_conj_sT_B₁T_le : (B₁T hn).map (MulAut.conj (sT n)).toMonoidHom ≤ B₀T hn :=
  map_conj_dihedralLift_range_le _ _ _ _ _ _ _
    (by rw [sT_conj_ρ₁T hn]; exact pow_mem (ρ₀T_mem_B₀T hn) _)
    (by rw [sT_conj_κ₁T hn]; exact mul_mem (κ₀T_mem_B₀T hn) (pow_mem (ρ₀T_mem_B₀T hn) _))

theorem map_conj_sT_B₀T : (B₀T hn).map (MulAut.conj (sT n)).toMonoidHom = B₁T hn := by
  apply eq_of_le_of_card_ge (map_conj_sT_B₀T_le hn)
  rw [card_map_of_injective (MulAut.conj (sT n)).injective, card_B₀T hn, card_B₁T hn]

theorem conj_sT_mem_B₁T {x : TM n} (hx : x ∈ B₀T hn) : sT n * x * (sT n)⁻¹ ∈ B₁T hn :=
  map_conj_sT_B₀T_le hn ⟨x, hx, rfl⟩

theorem conj_sT_mem_B₀T {x : TM n} (hx : x ∈ B₁T hn) : sT n * x * (sT n)⁻¹ ∈ B₀T hn :=
  map_conj_sT_B₁T_le hn ⟨x, hx, rfl⟩

theorem B₁T_le_normalizer : B₁T hn ≤ normalizer (B₀T hn : Set (TM n)) :=
  le_normalizer_of_comm (B₀T_comm_B₁T hn)

theorem conj_sT_B₀B₁ : ∀ x ∈ B₀T hn ⊔ B₁T hn, sT n * x * (sT n)⁻¹ ∈ B₀T hn ⊔ B₁T hn := by
  have hle : (B₀T hn ⊔ B₁T hn).map (MulAut.conj (sT n)).toMonoidHom ≤ B₀T hn ⊔ B₁T hn := by
    rw [Subgroup.map_sup]
    exact sup_le ((map_conj_sT_B₀T_le hn).trans le_sup_right)
      ((map_conj_sT_B₁T_le hn).trans le_sup_left)
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem zpowers_sT_le_normalizer : zpowers (sT n) ≤ normalizer ((B₀T hn ⊔ B₁T hn : Subgroup _) :
    Set (TM n)) :=
  zpowers_le.2 (mem_normalizer_of_involution (sT_mul_sT hn) (conj_sT_B₀B₁ hn))

theorem B₀B₁_le_ker_jT : B₀T hn ⊔ B₁T hn ≤ (jT n).ker :=
  sup_le (dihedralLift_range_le _ _ _ _ _ _ jT_ρ₀T jT_κ₀T)
    (dihedralLift_range_le _ _ _ _ _ _ jT_ρ₁T jT_κ₁T)

theorem sT_not_mem : sT n ∉ B₀T hn ⊔ B₁T hn := fun h =>
  ofAdd_one_ne_one ((jT_sT hn).symm.trans (B₀B₁_le_ker_jT hn h))

theorem B₀B₁_inf_zpowers_sT : (B₀T hn ⊔ B₁T hn) ⊓ zpowers (sT n) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxs⟩
  rcases (mem_zpowers_of_mul_self_eq_one (sT_mul_sT hn)).1 hxs with rfl | rfl
  · exact one_mem _
  · exact absurd hx (sT_not_mem hn)

theorem mem_BT_iff {x : TM n} : x ∈ BT hn ↔
    (∃ u ∈ B₀T hn, ∃ v ∈ B₁T hn, x = u * v) ∨ (∃ u ∈ B₀T hn, ∃ v ∈ B₁T hn, x = u * v * sT n) := by
  rw [BT, mem_sup_iff_of_le_normalizer (zpowers_sT_le_normalizer hn)]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (B₁T_le_normalizer hn)).1 hy
    rcases (mem_zpowers_of_mul_self_eq_one (sT_mul_sT hn)).1 hw with rfl | rfl
    · exact Or.inl ⟨u, hu, v, hv, mul_one _⟩
    · exact Or.inr ⟨u, hu, v, hv, rfl⟩
  · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩)
    · exact ⟨u * v, mul_mem (mem_sup_left hu) (mem_sup_right hv), 1, one_mem _, (mul_one _).symm⟩
    · exact ⟨u * v, mul_mem (mem_sup_left hu) (mem_sup_right hv), sT n, mem_zpowers _, rfl⟩

theorem card_B₀B₁ : Nat.card ↥(B₀T hn ⊔ B₁T hn) = 2 ^ (2 * n) := by
  rw [card_sup_of_le_normalizer (B₁T_le_normalizer hn) (B₀T_inf_B₁T hn), card_B₀T hn,
    card_B₁T hn, ← pow_add, two_mul]

theorem orderOf_sT : orderOf (sT n) = 2 :=
  orderOf_eq_prime (by rw [pow_two, sT_mul_sT hn]) (fun h => sT_not_mem hn (h ▸ one_mem _))

theorem card_BT : Nat.card (BT hn) = 2 ^ (2 * n + 1) := by
  rw [BT, card_sup_of_le_normalizer (zpowers_sT_le_normalizer hn) (B₀B₁_inf_zpowers_sT hn),
    card_B₀B₁ hn, Nat.card_zpowers, orderOf_sT hn, pow_succ]

theorem AT_le_ker_d3T : AT hn ≤ (d3T n).ker := by
  apply dihedralLift_range_le
  · change d3T n (πT n (toP (Gen.rA n))) = 1
    rw [d3T_πT, coe_toP Gen.det_rA]
    change Multiplicative.ofAdd (par (2 : ZMod (2 ^ n)) + 0) = 1
    rw [show (2 : ZMod (2 ^ n)) = 1 + 1 by norm_num, par_add, CharTwo.add_self_eq_zero, add_zero]
    rfl
  · change d3T n (πT n (toP (Gen.sA n))) = 1
    rw [d3T_πT, coe_toP (Gen.det_sA (n := n) (by omega))]
    change Multiplicative.ofAdd (par (1 : ZMod (2 ^ n)) + 1) = 1
    rw [par_one (by omega), CharTwo.add_self_eq_zero]
    rfl

theorem BT_le_ker_d3T : BT hn ≤ (d3T n).ker := by
  refine (BT_le_map_Btil hn).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [MonoidHom.mem_ker, d3T_πT, mem_Btil.1 hy, SD.det_one]
  rfl

theorem tT_not_mem : tT n ∉ AT hn ⊔ BT hn := fun h =>
  ofAdd_one_ne_one (d3T_tT.symm.trans (sup_le (AT_le_ker_d3T hn) (BT_le_ker_d3T hn) h))

theorem BT_le_normalizer_AT : BT hn ≤ normalizer (AT hn : Set (TM n)) :=
  le_normalizer_of_comm (AT_comm_BT hn)

theorem conj_tT_AB : ∀ x ∈ AT hn ⊔ BT hn, tT n * x * (tT n)⁻¹ ∈ AT hn ⊔ BT hn := by
  have hle : (AT hn ⊔ BT hn).map (MulAut.conj (tT n)).toMonoidHom ≤ AT hn ⊔ BT hn := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_sup_left (conj_tT_AT hn x hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_sup_right (conj_tT_BT hn x hx)
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem orderOf_tT : orderOf (tT n) = 2 :=
  orderOf_eq_prime (by rw [pow_two, tT_mul_tT hn]) (fun h => tT_not_mem hn (h ▸ one_mem _))

theorem top_eq : (⊤ : Subgroup (TM n)) = AT hn ⊔ BT hn ⊔ zpowers (tT n) := by
  symm
  apply eq_top_of_card_eq
  have hnt : zpowers (tT n) ≤ normalizer ((AT hn ⊔ BT hn : Subgroup _) : Set (TM n)) :=
    zpowers_le.2 (mem_normalizer_of_involution (tT_mul_tT hn) (conj_tT_AB hn))
  have hint : (AT hn ⊔ BT hn) ⊓ zpowers (tT n) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxt⟩
    rcases (mem_zpowers_of_mul_self_eq_one (tT_mul_tT hn)).1 hxt with rfl | rfl
    · exact one_mem _
    · exact absurd hx (tT_not_mem hn)
  rw [card_sup_of_le_normalizer hnt hint, card_sup_of_le_normalizer (BT_le_normalizer_AT hn)
    (AT_inf_BT hn), card_AT hn, card_BT hn, Nat.card_zpowers, orderOf_tT hn, card_TM (by omega),
    ← pow_add, ← pow_succ, show n - 1 + (2 * n + 1) + 1 = 3 * n + 1 by omega]

theorem AT_le_AtT : AT hn ≤ AtT hn :=
  dihedralLift_range_le _ _ _ _ _ _
    (by rw [← ωtT_mul_ωtT hn]; exact mul_mem (ωtT_mem_AtT hn) (ωtT_mem_AtT hn))
    (by
      rw [sAT_eq hn]
      exact mul_mem (mul_mem (mul_mem (ωtT_mem_AtT hn) (ωtT_mem_AtT hn)) (tT_mem_AtT hn))
        (ωtT_mem_AtT hn))

theorem AT_sup_tT : AT hn ⊔ zpowers (tT n) = AtT hn := by
  apply le_antisymm (sup_le (AT_le_AtT hn) (zpowers_le.2 (tT_mem_AtT hn)))
  apply dihedralLift_range_le
  · have h : ωtT n = tT n * ((rAT n)⁻¹ * sAT n) := by
      rw [sAT_eq hn, ← ωtT_mul_ωtT hn]
      calc ωtT n = tT n * tT n * ωtT n := by rw [tT_mul_tT hn, one_mul]
        _ = tT n * ((ωtT n * ωtT n)⁻¹ * (ωtT n * ωtT n * tT n * ωtT n)) := by group
    rw [h]
    exact mul_mem (mem_sup_right (mem_zpowers _))
      (mem_sup_left (mul_mem (inv_mem (rAT_mem_AT hn)) (sAT_mem_AT hn)))
  · exact mem_sup_right (mem_zpowers _)

theorem aT_mem_AT : aT n ∈ AT hn := by rw [aT_eq_fA hn]; exact ⟨_, rfl⟩

theorem orderOf_aT : orderOf (aT n) = 2 := by
  rw [aT_eq_fA hn, orderOf_injective _ (fA_injective hn), orderOf_zc (by omega)]

theorem aT_comm : ∀ x ∈ AT hn ⊔ zpowers (tT n), x * aT n = aT n * x := by
  rw [AT_sup_tT hn]
  rintro _ ⟨d, rfl⟩
  rw [aT_eq_fAt hn, ← map_mul, ← map_mul, zc_comm (by omega)]

theorem orderOf_b₀T : orderOf (b₀T hn) = 2 := by
  rw [b₀T, orderOf_injective _ (f₀_injective hn), orderOf_zc (by omega)]

theorem orderOf_b₁T : orderOf (b₁T hn) = 2 := by
  rw [b₁T, orderOf_injective _ (f₁_injective hn), orderOf_zc (by omega)]

theorem b₀T_comm : ∀ x ∈ B₀T hn, x * b₀T hn = b₀T hn * x := by
  rintro _ ⟨d, rfl⟩
  rw [b₀T, ← map_mul, ← map_mul, zc_comm (by omega)]

theorem b₁T_comm : ∀ x ∈ B₁T hn, x * b₁T hn = b₁T hn * x := by
  rintro _ ⟨d, rfl⟩
  rw [b₁T, ← map_mul, ← map_mul, zc_comm (by omega)]

end CFSG.CGT.Foote81L6.Bridge
