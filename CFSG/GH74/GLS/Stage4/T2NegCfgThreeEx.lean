module

public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeDefs
public import CFSG.GH74.GLS.Stage4.T2FourBuild

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.T2

section Half

variable {G : Type} [Group G]

structure NegSkelHalf (q : ℕ) (z : G) (K T : Subgroup G) (x w : G) : Prop where
  T_le : T ≤ K
  T_cyc : IsCyclic ↥T
  T_card : Nat.card ↥T = q + 1
  T_cent : ∀ y ∈ T, y * y ≠ 1 → ∀ d ∈ K, d * y = y * d → d ∈ T
  x_mem : x ∈ T
  x_sq : x * x = z
  T_iff : ∀ k ∈ K, k ∈ T ↔ k * x = x * k
  w_mem : w ∈ K
  w_sq : w * w = z
  w_x : w * x * w⁻¹ = x * z
  w_inv : ∀ y ∈ T, w * y * w⁻¹ = y⁻¹

theorem negSkelHalf_of_factor {q : ℕ} {z : G} {K : Subgroup G} {F : Type} [Field F] {φ : SL2 F →* G}
    (hinj : Function.Injective φ) (hrange : φ.range = K) (hneg : φ (negOne F) = z)
    {g : GL (Fin 2) F} {W V A : SL2 F} (hN : NegFactor q g W V A) :
    NegSkelHalf q z K ((Subgroup.centralizer ({W} : Set (SL2 F))).map φ) (φ W) (φ V) := by
  have hmemK : ∀ M : SL2 F, φ M ∈ K := fun M => hrange ▸ ⟨M, rfl⟩
  have heq := Subgroup.equivMapOfInjective (Subgroup.centralizer ({W} : Set (SL2 F))) φ hinj
  refine
    { T_le := ?_, T_cyc := heq.isCyclic.1 hN.T_cyc, T_card := ?_, T_cent := ?_, x_mem := ?_,
      x_sq := ?_, T_iff := ?_, w_mem := hmemK V, w_sq := ?_, w_x := ?_, w_inv := ?_ }
  · rintro _ ⟨M, -, rfl⟩
    exact hmemK M
  · rw [Subgroup.card_map_of_injective hinj]
    exact hN.T_card
  · rintro _ ⟨Y, hY, rfl⟩ hyy d hdK hdy
    obtain ⟨D, rfl⟩ : d ∈ φ.range := hrange ▸ hdK
    have hYY : Y * Y ≠ 1 := fun h => hyy (by rw [← map_mul, h, map_one])
    have hDY : D * Y = Y * D := hinj (by rw [map_mul, map_mul]; exact hdy)
    exact ⟨D, hN.T_cent Y hY hYY D hDY, rfl⟩
  · exact ⟨W, Subgroup.mem_centralizer_singleton_iff.2 rfl, rfl⟩
  · rw [← map_mul, hN.W_sq, hneg]
  · intro k hk
    obtain ⟨D, rfl⟩ : k ∈ φ.range := hrange ▸ hk
    rw [Subgroup.mem_map_iff_mem hinj, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
      ← map_mul, hinj.eq_iff]
  · rw [← map_mul, hN.V_sq, hneg]
  · have hWi : W⁻¹ = W * negOne F :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hN.W_sq, negOne_mul_self])
    calc φ V * φ W * (φ V)⁻¹ = φ (V * W * V⁻¹) := by simp only [map_mul, map_inv]
      _ = φ (W * negOne F) := by rw [hN.VW, hWi]
      _ = φ W * z := by rw [map_mul, hneg]
  · rintro _ ⟨Y, hY, rfl⟩
    calc φ V * φ Y * (φ V)⁻¹ = φ (V * Y * V⁻¹) := by simp only [map_mul, map_inv]
      _ = φ Y⁻¹ := by rw [hN.T_inv Y hY]
      _ = (φ Y)⁻¹ := map_inv φ Y

end Half

section Cross

variable {G : Type} [Group G] {P : Type} [Group P] {ψ : P →* G} {τ : P →* P} {t : G}

theorem negSkel_t_mul (hτ : ∀ x, t * ψ x * t⁻¹ = ψ (τ x)) (x : P) : t * ψ x = ψ (τ x) * t :=
  mul_inv_eq_iff_eq_mul.1 (hτ x)

theorem negSkel_s_sq (htt : t * t = 1) (hτ : ∀ x, t * ψ x * t⁻¹ = ψ (τ x)) (A : P) :
    (ψ A * t) * (ψ A * t) = ψ (A * τ A) := by
  calc ψ A * t * (ψ A * t) = ψ A * (t * ψ A) * t := by group
    _ = ψ A * (ψ (τ A) * t) * t := by rw [negSkel_t_mul hτ A]
    _ = ψ A * ψ (τ A) * (t * t) := by group
    _ = ψ (A * τ A) := by rw [htt, mul_one, map_mul]

theorem negSkel_s_comm (hτ : ∀ x, t * ψ x * t⁻¹ = ψ (τ x)) {A y : P} (h : A * τ y = y * A) :
    (ψ A * t) * ψ y = ψ y * (ψ A * t) := by
  calc ψ A * t * ψ y = ψ A * (t * ψ y) := by group
    _ = ψ A * (ψ (τ y) * t) := by rw [negSkel_t_mul hτ y]
    _ = ψ (A * τ y) * t := by rw [map_mul]; group
    _ = ψ (y * A) * t := by rw [h]
    _ = ψ y * (ψ A * t) := by rw [map_mul]; group

theorem negSkel_w₀_s (htt : t * t = 1) (hτ : ∀ x, t * ψ x * t⁻¹ = ψ (τ x)) {A V n : P}
    (hn : ψ n = 1) (hAV : V * A * τ V⁻¹ = n * τ A⁻¹) :
    ψ V * (ψ A * t) * (ψ V)⁻¹ = (ψ A * t)⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  calc ψ V * (ψ A * t) * (ψ V)⁻¹ = ψ (V * A) * (t * ψ V⁻¹) := by
        simp only [map_mul, map_inv]; group
    _ = ψ (V * A) * (ψ (τ V⁻¹) * t) := by rw [negSkel_t_mul hτ]
    _ = ψ (V * A * τ V⁻¹) * t := by simp only [map_mul]; group
    _ = ψ (n * τ A⁻¹) * t := by rw [hAV]
    _ = ψ (τ A⁻¹) * t := by rw [map_mul, hn, one_mul]
    _ = t * ψ A⁻¹ := (negSkel_t_mul hτ _).symm
    _ = (ψ A * t)⁻¹ := by rw [mul_inv_rev, hti, map_inv]

end Cross

section Assembly

theorem negSkel_of_coords {G : Type} [Group G] {Gs : Type} [Group Gs] {q : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {g₁ : GL (Fin 2) F₁} {g₂ : GL (Fin 2) F₂}
    (hinj₁ : Function.Injective φ₁) (hrange₁ : φ₁.range = K₁) (hneg₁ : φ₁ (negOne F₁) = z)
    (hτ₁ : ∀ x, t * φ₁ x * t⁻¹ = φ₁ (slConj g₁ x))
    (hinj₂ : Function.Injective φ₂) (hrange₂ : φ₂.range = K₂) (hneg₂ : φ₂ (negOne F₂) = z)
    (hτ₂ : ∀ x, t * φ₂ x * t⁻¹ = φ₂ (slConj g₂ x))
    {W₁ V₁ A₁ : SL2 F₁} {W₂ V₂ A₂ : SL2 F₂}
    (hN₁ : NegFactor q g₁ W₁ V₁ A₁) (hN₂ : NegFactor q g₂ W₂ V₂ A₂) :
    NegSkel (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z K₁ K₂
      ((Subgroup.centralizer ({W₁} : Set (SL2 F₁))).map φ₁)
      ((Subgroup.centralizer ({W₂} : Set (SL2 F₂))).map φ₂) (φ₁ W₁) (φ₂ W₂) (φ₁ V₁) (φ₂ V₂)
      (φ₁ A₁ * φ₂ A₂ * t) := by
  have hmem₁ : ∀ M : SL2 F₁, φ₁ M ∈ K₁ := fun M => hrange₁ ▸ ⟨M, rfl⟩
  have hmem₂ : ∀ M : SL2 F₂, φ₂ M ∈ K₂ := fun M => hrange₂ ▸ ⟨M, rfl⟩
  have hcomm : ∀ (a : SL2 F₁) (b : SL2 F₂), Commute (φ₁ a) (φ₂ b) := fun a b =>
    hSet.comm _ (hmem₁ a) _ (hmem₂ b)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SL2 F₁ × SL2 F₂ →* G, ∀ a b, ψ (a, b) = φ₁ a * φ₂ b :=
    ⟨φ₁.noncommCoprod φ₂ hcomm, fun a b => rfl⟩
  obtain ⟨τ, hτ'⟩ : ∃ τ : SL2 F₁ × SL2 F₂ →* SL2 F₁ × SL2 F₂,
      ∀ a b, τ (a, b) = (slConj g₁ a, slConj g₂ b) :=
    ⟨(slConj g₁).prodMap (slConj g₂), fun a b => rfl⟩
  have htt : t * t = 1 := hRem.sq
  have hzz : z * z = 1 := t2C_zz hSet
  have htK : t ∉ K₁ ⊔ K₂ := t2B_t_notin hSet hRem
  have hτ : ∀ p, t * ψ p * t⁻¹ = ψ (τ p) := by
    rintro ⟨a, b⟩
    rw [hτ' a b, hψ a b, hψ (slConj g₁ a) (slConj g₂ b)]
    calc t * (φ₁ a * φ₂ b) * t⁻¹ = (t * φ₁ a * t⁻¹) * (t * φ₂ b * t⁻¹) := by group
      _ = φ₁ (slConj g₁ a) * φ₂ (slConj g₂ b) := by rw [hτ₁ a, hτ₂ b]
  have hψK : ∀ a b, ψ (a, b) ∈ K₁ ⊔ K₂ := fun a b => by
    rw [hψ a b]
    exact Subgroup.mul_mem_sup (hmem₁ a) (hmem₂ b)
  have htC : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hRem.gen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hh₁ := negSkelHalf_of_factor hinj₁ hrange₁ hneg₁ hN₁
  have hh₂ := negSkelHalf_of_factor hinj₂ hrange₂ hneg₂ hN₂
  have hs : φ₁ A₁ * φ₂ A₂ * t = ψ (A₁, A₂) * t := by rw [hψ]
  have hw : φ₁ V₁ * φ₂ V₂ = ψ (V₁, V₂) := (hψ V₁ V₂).symm
  rw [hs]
  refine
    { s_mem := ?_, s_not_mem := ?_, T₁_le := hh₁.T_le, T₂_le := hh₂.T_le, T₁_cyc := hh₁.T_cyc,
      T₂_cyc := hh₂.T_cyc, T₁_card := hh₁.T_card, T₂_card := hh₂.T_card, T₁_cent := hh₁.T_cent,
      T₂_cent := hh₂.T_cent, x₁_mem := hh₁.x_mem, x₂_mem := hh₂.x_mem, x₁_sq := hh₁.x_sq,
      x₂_sq := hh₂.x_sq, T₁_iff := hh₁.T_iff, T₂_iff := hh₂.T_iff, w₁_mem := hh₁.w_mem,
      w₂_mem := hh₂.w_mem, w₁_sq := hh₁.w_sq, w₂_sq := hh₂.w_sq, w₁_x := hh₁.w_x,
      w₂_x := hh₂.w_x, w₁_inv := hh₁.w_inv, w₂_inv := hh₂.w_inv, s_comm₁ := ?_, s_comm₂ := ?_,
      s_sq := ?_, w₀_s := ?_ }
  · exact Subgroup.mul_mem _ (hSet.le_residual (hψK A₁ A₂)) htC
  · intro hst
    apply htK
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hψK A₁ A₂)) hst
    rwa [inv_mul_cancel_left] at this
  · rintro _ ⟨Y, hY, rfl⟩
    have hY1 : φ₁ Y = ψ (Y, 1) := by rw [hψ, map_one, mul_one]
    rw [hY1]
    refine negSkel_s_comm hτ ?_
    rw [hτ', Prod.mk_mul_mk, Prod.mk_mul_mk, map_one, mul_one, one_mul]
    exact congrArg (fun x => (x, A₂)) (mul_inv_eq_iff_eq_mul.1 (hN₁.A_cent Y hY))
  · rintro _ ⟨Y, hY, rfl⟩
    have hY1 : φ₂ Y = ψ (1, Y) := by rw [hψ, map_one, one_mul]
    rw [hY1]
    refine negSkel_s_comm hτ ?_
    rw [hτ', Prod.mk_mul_mk, Prod.mk_mul_mk, map_one, mul_one, one_mul]
    exact congrArg (fun x => (A₁, x)) (mul_inv_eq_iff_eq_mul.1 (hN₂.A_cent Y hY))
  · rw [negSkel_s_sq htt hτ, hτ', Prod.mk_mul_mk, hψ]
    exact Subgroup.mul_mem_sup ⟨_, hN₁.A_sq, rfl⟩ ⟨_, hN₂.A_sq, rfl⟩
  · rw [hw]
    refine negSkel_w₀_s htt hτ (n := (negOne F₁, negOne F₂)) ?_ ?_
    · rw [hψ, hneg₁, hneg₂, hzz]
    · simp only [Prod.inv_mk, hτ', Prod.mk_mul_mk]
      exact Prod.ext hN₁.A_V hN₂.A_V

theorem negSkel_exists {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hfac₁ : ∀ g : GL (Fin 2) F₁, (g : Matrix (Fin 2) (Fin 2) F₁) * (g : Matrix (Fin 2) (Fin 2) F₁) =
      (-((g : Matrix (Fin 2) (Fin 2) F₁).det)) • (1 : Matrix (Fin 2) (Fin 2) F₁) →
        ∃ W V A : SL2 F₁, NegFactor q g W V A)
    (hfac₂ : ∀ g : GL (Fin 2) F₂, (g : Matrix (Fin 2) (Fin 2) F₂) * (g : Matrix (Fin 2) (Fin 2) F₂) =
      (-((g : Matrix (Fin 2) (Fin 2) F₂).det)) • (1 : Matrix (Fin 2) (Fin 2) F₂) →
        ∃ W V A : SL2 F₂, NegFactor q g W V A) :
    ∃ (T₁ T₂ : Subgroup G) (x₁ x₂ w₁ w₂ s : G),
      NegSkel (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z K₁ K₂ T₁ T₂ x₁ x₂ w₁ w₂ s := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hzord : orderOf z = 2 := hSet.central.1
  have htt : t * t = 1 := hRem.sq
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card hodd₁
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card hodd₂
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  obtain ⟨φ₁, hinj₁, hrange₁, hneg₁, hτ₁, hsq₁⟩ :=
    exists_coords0 h2₁ hzord hSet.z_mem₁ htt e₁ g₁ hact₁
  obtain ⟨φ₂, hinj₂, hrange₂, hneg₂, hτ₂, hsq₂⟩ :=
    exists_coords0 h2₂ hzord hSet.z_mem₂ htt e₂ g₂ hact₂
  obtain ⟨W₁, V₁, A₁, hN₁⟩ := hfac₁ g₁ (sq_eq_neg_det_of_slConj_sq g₁ hns₁ hsq₁)
  obtain ⟨W₂, V₂, A₂, hN₂⟩ := hfac₂ g₂ (sq_eq_neg_det_of_slConj_sq g₂ hns₂ hsq₂)
  exact ⟨_, _, _, _, _, _, _,
    negSkel_of_coords hSet hRem hinj₁ hrange₁ hneg₁ hτ₁ hinj₂ hrange₂ hneg₂ hτ₂ hN₁ hN₂⟩

end Assembly

end CFSG.GH74.GLS.Stage4.Rest
