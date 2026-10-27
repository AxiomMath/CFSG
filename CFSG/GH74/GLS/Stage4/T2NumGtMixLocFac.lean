module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocDefs
public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeEx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.T2

section Half

variable {G : Type} [Group G]

theorem mixSkelHalf_of_factor {c : ℕ} {z : G} {K : Subgroup G} {F : Type} [Field F] {φ : SL2 F →* G}
    (hinj : Function.Injective φ) (hrange : φ.range = K) (hneg : φ (negOne F) = z)
    {g : GL (Fin 2) F} {W V A : SL2 F} (hN : MixFactor c g W V A) :
    MixSkelHalf c z K ((Subgroup.centralizer ({W} : Set (SL2 F))).map φ) (φ W) (φ V) := by
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

section Assembly

theorem mixSkel_of_coords {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ c₁ c₂ : ℕ}
    {z t : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {g₁ : GL (Fin 2) F₁} {g₂ : GL (Fin 2) F₂}
    (hinj₁ : Function.Injective φ₁) (hrange₁ : φ₁.range = K₁) (hneg₁ : φ₁ (negOne F₁) = z)
    (hτ₁ : ∀ x, t * φ₁ x * t⁻¹ = φ₁ (slConj g₁ x))
    (hinj₂ : Function.Injective φ₂) (hrange₂ : φ₂.range = K₂) (hneg₂ : φ₂ (negOne F₂) = z)
    (hτ₂ : ∀ x, t * φ₂ x * t⁻¹ = φ₂ (slConj g₂ x))
    {W₁ V₁ A₁ : SL2 F₁} {W₂ V₂ A₂ : SL2 F₂}
    (hN₁ : MixFactor c₁ g₁ W₁ V₁ A₁) (hN₂ : MixFactor c₂ g₂ W₂ V₂ A₂) :
    MixSkel (oPrimeResidualOf 2 (centralizer ({z} : Set G))) c₁ c₂ z K₁ K₂
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
  have hh₁ := mixSkelHalf_of_factor hinj₁ hrange₁ hneg₁ hN₁
  have hh₂ := mixSkelHalf_of_factor hinj₂ hrange₂ hneg₂ hN₂
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

end Assembly

section Split

variable {F : Type} [Field F]

theorem cent_tSub_of_sq_ne {a : Fˣ} (ha : (sl2D a : SL2 F) * sl2D a ≠ 1)
    {D : SL2 F} (h : D * sl2D a = sl2D a * D) : D ∈ tSub F := by
  have ha2 : (a : F) ^ 2 - 1 ≠ 0 := by
    intro h0
    apply ha
    have h1 : a * a = 1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_one]
      linear_combination h0
    rw [sl2D_mul, h1, sl2D_one]
  have e01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have e10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have hi : (a : F) * (a : F)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
  refine ⟨?_, ?_⟩
  · have h0 : ((a : F) ^ 2 - 1) * (D : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      linear_combination (-(a : F)) * e01 + (D : Matrix (Fin 2) (Fin 2) F) 0 1 * hi
    exact (mul_eq_zero.1 h0).resolve_left ha2
  · have h0 : ((a : F) ^ 2 - 1) * (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      linear_combination (a : F) * e10 + (D : Matrix (Fin 2) (Fin 2) F) 1 0 * hi
    exact (mul_eq_zero.1 h0).resolve_left ha2

theorem centralizer_sl2D_eq (h2 : (2 : F) ≠ 0) {ι : Fˣ} (hι : (ι : F) * (ι : F) = -1) :
    Subgroup.centralizer ({sl2D ι} : Set (SL2 F)) = tSub F := by
  have hW : (sl2D ι : SL2 F) * sl2D ι = negOne F := sl2D_sq_of_sqrt ι hι
  ext D
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact cent_tSub_of_sq_ne (a := ι) (by rw [hW]; exact negOne_ne_one h2) h
  · intro hD
    obtain ⟨b, rfl⟩ := mem_tSub.1 hD
    rw [sl2D_mul, sl2D_mul, mul_comm]

theorem mixFactor_split [Finite F] (h2 : (2 : F) ≠ 0) {ι : Fˣ} (hι : (ι : F) * (ι : F) = -1)
    (g : GL (Fin 2) F)
    (hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (-((g : Matrix (Fin 2) (Fin 2) F).det)) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    MixFactor (Nat.card F - 1) g (sl2D ι) (sl2W F) (adjSL g) := by
  have hcent := centralizer_sl2D_eq h2 hι
  have hAA : adjSL g * slConj g (adjSL g) =
      sl2D (-(Matrix.GeneralLinearGroup.det g : Fˣ)⁻¹) := adjSL_mul_conj_self g hg2
  refine ⟨sl2D_sq_of_sqrt ι hι, sl2W_sq, sl2W_inv_tSub _ (sl2D_mem_tSub ι), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hcent]
    exact isCyclic_tSub
  · rw [hcent]
    exact card_tSub
  · intro Y hY hYY D hD
    rw [hcent] at hY ⊢
    obtain ⟨b, rfl⟩ := mem_tSub.1 hY
    exact cent_tSub_of_sq_ne hYY hD
  · intro Y hY
    rw [hcent] at hY
    exact sl2W_inv_tSub Y hY
  · intro Y hY
    rw [hcent] at hY
    rw [adjSL_conj, slConj_diag_tSub _ _ Y hY]
  · rw [hAA, hcent]
    exact sl2D_mem_tSub _
  · set d : Fˣ := Matrix.GeneralLinearGroup.det g with hd
    have hA1 : adjSL g * slConj g (sl2W F)⁻¹ = slConj (diagGL 1 d) (sl2W F)⁻¹ * adjSL g := by
      have h := adjSL_conj g (sl2W F)⁻¹
      calc adjSL g * slConj g (sl2W F)⁻¹
          = (adjSL g * slConj g (sl2W F)⁻¹ * (adjSL g)⁻¹) * adjSL g := by group
        _ = _ := by rw [h]
    have hs : slConj g (adjSL g)⁻¹ = sl2D (-d) * adjSL g := by
      rw [map_inv]
      have h1 : slConj g (adjSL g) = (adjSL g)⁻¹ * sl2D (-d⁻¹) := by
        rw [← hAA]
        group
      rw [h1, mul_inv_rev, inv_inv, t2A_sl2D_inv, inv_neg, inv_inv]
    have e : (sl2D d : SL2 F) = negOne F * sl2D (-d) := by
      rw [← sl2D_neg_one, sl2D_mul]
      congr 1
      simp
    calc sl2W F * adjSL g * slConj g (sl2W F)⁻¹ = sl2W F * (adjSL g * slConj g (sl2W F)⁻¹) := by
          group
      _ = sl2W F * (slConj (diagGL 1 d) (sl2W F)⁻¹ * adjSL g) := by rw [hA1]
      _ = (sl2W F * slConj (diagGL 1 d) (sl2W F)⁻¹) * adjSL g := by group
      _ = sl2D d * adjSL g := by rw [sl2W_mul_slConj_diagGL_one]
      _ = negOne F * (sl2D (-d) * adjSL g) := by rw [e, mul_assoc]
      _ = negOne F * slConj g (adjSL g)⁻¹ := by rw [hs]

end Split

end CFSG.GH74.GLS.Stage4.Rest
