module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cross
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.GH74.GLS.IVK.Proofs2.Pgl2Three

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.PSL2Table
open scoped MatrixGroups commutatorElement

section CharStd

variable {F : Type} [Field F]

theorem borel_not_fix_unip (h2 : (2 : F) ≠ 0) {g : PSL(2, F)} (hg : g ∈ borel F)
    (hgU : g ∉ unipotent F) {t : F} (ht : t ≠ 0) : g * mk (unip t) * g⁻¹ ≠ mk (unip t) := by
  intro hfix
  obtain ⟨M, hM, rfl⟩ := hg
  have hM10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (mem_borelSL_iff M).mp hM
  rw [mk_conj, conj_unip_of_borel hM10, mk_unip_eq_mk_unip_iff h2] at hfix
  have ha2 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 1 := by
    have : ((M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 - 1) * t = 0 := by linear_combination hfix
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h ht
  have hdet := det_entries M
  rw [hM10, mul_zero, sub_zero] at hdet
  have ha : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∨ (M : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 :=
    eq_or_eq_neg_of_sq_eq_sq _ 1 (by rw [ha2, one_pow])
  apply hgU
  refine (mk_mem_unipotent_iff M).mpr ⟨hM10, ?_⟩
  rcases ha with ha | ha
  · rw [ha] at hdet ⊢
    linear_combination -hdet
  · rw [ha] at hdet ⊢
    linear_combination hdet

omit [Field F] in
theorem card_subtype_ne_one {G : Type} [Group G] [Finite G] :
    Nat.card {y : G // y ≠ 1} + 1 = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun y : G => y = 1),
    Fintype.card_subtype_eq]
  have : 0 < Fintype.card G := Fintype.card_pos
  omega

theorem fl2_char_free_std [Finite F] (hF2 : ringChar F ≠ 2) (hodd : Odd (Nat.card F)) {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : Nat.card F = p ^ n) (Y : Subgroup PSL(2, F)) (hYU : Y ≤ unipotent F) (hY1 : Y ≠ ⊥)
    (C : Subgroup PSL(2, F)) (hCN : ∀ c ∈ C, c ∈ normalizer (Y : Set PSL(2, F)))
    (hCp : ¬ p ∣ Nat.card ↥C) (hCbig : (Nat.card F - 1) / 2 ≤ Nat.card ↥C) :
    Nat.card ↥Y = Nat.card F ∧ Nat.card ↥C ≤ (Nat.card F - 1) / 2 ∧
      ∀ n ∈ normalizer (Y : Set PSL(2, F)), ∃ y ∈ Y, ∃ c ∈ C, n = y * c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hcardU : Nat.card (unipotent F) = Nat.card F := by
    rw [card_unipotent h2, Nat.card_eq_fintype_card]
  obtain ⟨y₁, hy₁Y, hy₁1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hY1 ((Subgroup.eq_bot_iff_forall Y).mpr hcon)
  obtain ⟨t₁, rfl⟩ := (mem_unipotent_iff_exists y₁).mp (hYU hy₁Y)
  have ht₁ : t₁ ≠ 0 := fun h => hy₁1 ((mk_unip_eq_one_iff h2 t₁).mpr h)
  have hNB : ∀ c ∈ normalizer (Y : Set PSL(2, F)), c ∈ borel F := by
    intro c hc
    have hmem : c * mk (unip t₁) * c⁻¹ ∈ unipotent F :=
      hYU ((mem_normalizer_iff.mp hc _).mp hy₁Y)
    exact (unipotent_TI hF2 _ (hYU hy₁Y) hy₁1 c).mp hmem
  have hCB : ∀ c ∈ C, c ∈ borel F := fun c hc => hNB c (hCN c hc)
  have hCU : ∀ c ∈ C, c ∈ unipotent F → c = 1 := by
    intro c hc hcU
    have h1 : orderOf c ∣ Nat.card (unipotent F) := by
      have := orderOf_dvd_natCard (⟨c, hcU⟩ : unipotent F)
      rwa [Subgroup.orderOf_mk] at this
    have h2' : orderOf c ∣ Nat.card C := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
      rwa [Subgroup.orderOf_mk] at this
    rw [hcardU, hn] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exfalso
      apply hCp
      rw [hj] at h2'
      exact (dvd_pow_self p hj0).trans h2'
  have hCle : Nat.card C ≤ (Nat.card F - 1) / 2 := by
    have hUB : unipotent F ≤ borel F := by
      rw [← L2Borel.normalizer_unipotent_eq h2]; exact Subgroup.le_normalizer
    have hCB' : C ≤ borel F := fun c hc => hCB c hc
    have h1 := card_mul_le_of_inf_trivial hCB' hUB (fun x hxC hxU => hCU x hxC hxU)
    have h3 := card_borel h2 (F := F)
    rw [card_unipotent h2] at h1
    have hq0 : 0 < Fintype.card F := Fintype.card_pos
    have h4 : Nat.card C * 2 ≤ Fintype.card F - 1 := by
      have : (Nat.card C * 2) * Fintype.card F ≤ (Fintype.card F - 1) * Fintype.card F := by
        calc (Nat.card C * 2) * Fintype.card F = (Nat.card C * Fintype.card F) * 2 := by ring
          _ ≤ Nat.card (borel F) * 2 := Nat.mul_le_mul_right 2 h1
          _ = (Fintype.card F - 1) * Fintype.card F := h3
      exact Nat.le_of_mul_le_mul_right this hq0
    rw [Nat.card_eq_fintype_card (α := F)]
    omega
  let f : C → {y : Y // y ≠ 1} := fun c =>
    ⟨⟨c * mk (unip t₁) * (c : PSL(2, F))⁻¹, (mem_normalizer_iff.mp (hCN c c.2) _).mp hy₁Y⟩, by
      intro h
      apply hy₁1
      have h' : (c : PSL(2, F)) * mk (unip t₁) * (c : PSL(2, F))⁻¹ = 1 := congrArg Subtype.val h
      calc mk (unip t₁) = (c : PSL(2, F))⁻¹ * ((c : PSL(2, F)) * mk (unip t₁) * (c : PSL(2, F))⁻¹) * c := by
            group
        _ = 1 := by rw [h']; group⟩
  have hf : Function.Injective f := by
    intro c c' h
    have h1 : (c : PSL(2, F)) * mk (unip t₁) * (c : PSL(2, F))⁻¹ =
        c' * mk (unip t₁) * (c' : PSL(2, F))⁻¹ := congrArg (fun z : {y : Y // y ≠ 1} => (z.1 : PSL(2, F))) h
    set d : PSL(2, F) := (c' : PSL(2, F))⁻¹ * c with hd
    have hdC : d ∈ C := C.mul_mem (C.inv_mem c'.2) c.2
    have hfixd : d * mk (unip t₁) * d⁻¹ = mk (unip t₁) := by
      calc d * mk (unip t₁) * d⁻¹ = (c' : PSL(2, F))⁻¹ * ((c : PSL(2, F)) * mk (unip t₁) * (c : PSL(2, F))⁻¹) * c' := by
            rw [hd]; group
        _ = mk (unip t₁) := by rw [h1]; group
    by_contra hne
    have hd1 : d ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      have : (c : PSL(2, F)) = c' := by
        rw [hd] at h
        exact (inv_mul_eq_one.mp h).symm
      exact this
    have hdU : d ∉ unipotent F := fun hU => hd1 (hCU d hdC hU)
    exact borel_not_fix_unip h2 (hCB d hdC) hdU ht₁ hfixd
  have hle : Nat.card C ≤ Nat.card Y - 1 := by
    have h1 := Nat.card_le_card_of_injective f hf
    have h2 := card_subtype_ne_one (G := Y)
    omega
  have hYdvd : Nat.card Y ∣ Nat.card F := by
    have := Subgroup.card_dvd_of_le hYU
    rwa [hcardU] at this
  have hYcard : Nat.card ↥Y = Nat.card F := by
    rw [hn] at hYdvd ⊢
    obtain ⟨j, hjn, hj⟩ := (Nat.dvd_prime_pow hp).mp hYdvd
    by_cases hjeq : j = n
    · rw [hj, hjeq]
    · exfalso
      have hlt : j + 1 ≤ n := by omega
      have hpow : p ^ j * p ≤ p ^ n := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right hp.pos hlt
      have hq : Nat.card F = p ^ n := hn
      have hYq : Nat.card Y * p ≤ Nat.card F := by rw [hj, hq]; exact hpow
      have hp2 := hp.two_le
      have h2y : 2 * Nat.card Y ≤ Nat.card F :=
        calc 2 * Nat.card Y ≤ p * Nat.card Y := Nat.mul_le_mul_right _ hp2
          _ = Nat.card Y * p := mul_comm _ _
          _ ≤ Nat.card F := hYq
      have hpos : 0 < Nat.card Y := Nat.card_pos
      obtain ⟨k, hk⟩ := hodd
      omega
  refine ⟨hYcard, hCle, ?_⟩
  have hCeq : Nat.card ↥C = (Nat.card F - 1) / 2 := le_antisymm hCle hCbig
  set N : Subgroup PSL(2, F) := normalizer (Y : Set PSL(2, F)) with hN
  have hNle : N ≤ borel F := fun c hc => hNB c hc
  have hcardN : Nat.card N ≤ Nat.card (borel F) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hNle) (Subgroup.inclusion_injective _)
  have hB := card_borel h2 (F := F)
  have hNYC : Nat.card N ≤ Nat.card ↥Y * Nat.card ↥C := by
    obtain ⟨k, hk⟩ := hodd
    have hq : Fintype.card F = 2 * k + 1 := by rw [← Nat.card_eq_fintype_card]; exact hk
    rw [hYcard, hCeq, Nat.card_eq_fintype_card (α := F), hq]
    rw [hq] at hB
    have h1 : (2 * k + 1 - 1) / 2 = k := by omega
    rw [h1]
    have h3 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [h3] at hB
    nlinarith
  exact exists_mul_of_card_le Subgroup.le_normalizer (fun c hc => hCN c hc)
    (fun x hxY hxC => hCU x hxC (hYU hxY)) hNYC

end CharStd

section CharK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem exists_std_position (e : K ≃* L2 F) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F) (Y : Subgroup K) (hY : IsPGroup p ↥Y) :
    ∃ (n : ℕ) (ψ : K ≃* PSL(2, F)), Nat.card F = p ^ n ∧ Y.map ψ.toMonoidHom ≤ unipotent F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hpchar : ringChar F = p := by
    obtain ⟨n, hpr, hn⟩ := FiniteField.card F (ringChar F)
    have : p ∣ ringChar F ^ (n : ℕ) := hn ▸ (Nat.card_eq_fintype_card (α := F) ▸ hpF)
    exact ((Nat.prime_dvd_prime_iff_eq hp hpr).mp (hp.dvd_of_dvd_pow this)).symm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card F = p ^ n := by
    obtain ⟨n, hpr, hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn, hpchar]⟩
  let φ : K ≃* PSL(2, F) := toPSL e
  have hY' : IsPGroup p ↥(Y.map φ.toMonoidHom) :=
    hY.of_equiv (Y.equivMapOfInjective φ.toMonoidHom φ.injective)
  obtain ⟨W, hYW⟩ := hY'.exists_le_sylow
  obtain ⟨c, hc⟩ := L2Borel.exists_conj_eq_unipotent hn W
  refine ⟨n, φ.trans (MulAut.conj c⁻¹), hn, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : φ y ∈ (W : Subgroup PSL(2, F)) := hYW ⟨y, hy, rfl⟩
  rw [hc, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h1
  simpa [MulEquiv.trans_apply, MulAut.conj_apply] using h1

omit [Finite K] in
theorem ringChar_ne_two_of_odd (hodd : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  intro h
  have : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at h1
  obtain ⟨k, hk⟩ := hodd
  omega

omit [Finite K] in
theorem fl2_char_free (hF : L2Field F) (e : K ≃* L2 F) {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F)
    (Y : Subgroup K) (hY : IsPGroup p ↥Y) (hY1 : Y ≠ ⊥) (C : Subgroup K)
    (hCN : ∀ c ∈ C, c ∈ normalizer (Y : Set K)) (hCp : ¬ p ∣ Nat.card ↥C)
    (hCbig : (Nat.card F - 1) / 2 ≤ Nat.card ↥C) :
    Nat.card ↥Y = Nat.card F ∧ Nat.card ↥C ≤ (Nat.card F - 1) / 2 ∧
      ∀ m ∈ normalizer (Y : Set K), ∃ y ∈ Y, ∃ c ∈ C, m = y * c := by
  obtain ⟨n, ψ, hn, hYU⟩ := exists_std_position e hp hpF Y hY
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd hF.1
  have hY1' : Y.map ψ.toMonoidHom ≠ ⊥ := by
    intro h
    apply hY1
    exact (Subgroup.map_eq_bot_iff_of_injective Y (f := ψ.toMonoidHom) ψ.injective).mp h
  have hCN' : ∀ c ∈ C.map ψ.toMonoidHom,
      c ∈ normalizer ((Y.map ψ.toMonoidHom : Subgroup PSL(2, F)) : Set PSL(2, F)) := by
    intro c hc
    rw [L2Borel.normalizer_map_equiv]
    obtain ⟨c', hc', rfl⟩ := hc
    exact ⟨c', hCN c' hc', rfl⟩
  have hcardC : Nat.card ↥(C.map ψ.toMonoidHom) = Nat.card ↥C :=
    Subgroup.card_map_of_injective ψ.injective
  obtain ⟨h1, h2, h3⟩ :=
    fl2_char_free_std hF2 hF.1 hp hn _ hYU hY1' _ hCN' (by rwa [hcardC]) (by rwa [hcardC])
  refine ⟨by rwa [Subgroup.card_map_of_injective ψ.injective] at h1, by rwa [hcardC] at h2, ?_⟩
  intro m hm
  have hmψ : ψ m ∈ normalizer ((Y.map ψ.toMonoidHom : Subgroup PSL(2, F)) : Set PSL(2, F)) := by
    rw [L2Borel.normalizer_map_equiv]
    exact ⟨m, hm, rfl⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨c, hc, rfl⟩, hyc⟩ := h3 _ hmψ
  exact ⟨y, hy, c, hc, ψ.injective (by rw [map_mul]; exact hyc)⟩

end CharK

section BorelFacts

variable {F : Type} [Field F]

theorem borel_commutator_mem_unipotent {g h : PSL(2, F)} (hg : g ∈ borel F) (hh : h ∈ borel F) :
    g * h * g⁻¹ * h⁻¹ ∈ unipotent F := by
  obtain ⟨M, hM, rfl⟩ := hg
  obtain ⟨N, hN, rfl⟩ := hh
  have hM10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (mem_borelSL_iff M).mp hM
  have hN10 : (N : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (mem_borelSL_iff N).mp hN
  have hc : mk M * mk N * (mk M)⁻¹ * (mk N)⁻¹ = mk (M * N * M⁻¹ * N⁻¹) := by
    simp [map_mul, map_inv]
  rw [hc, mk_mem_unipotent_iff]
  have hMdet := det_entries M
  have hNdet := det_entries N
  rw [hM10, mul_zero, sub_zero] at hMdet
  rw [hN10, mul_zero, sub_zero] at hNdet
  simp only [mul_apply_SL, coe_inv_SL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, hM10, hN10, Matrix.cons_val_one, neg_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  exact ⟨trivial, by ring⟩

theorem unipotent_involution_eq_one (h2 : (2 : F) ≠ 0) {a : PSL(2, F)} (ha : a ∈ unipotent F)
    (ha2 : a * a = 1) : a = 1 := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists a).mp ha
  rw [← map_mul, ← unip_add, mk_unip_eq_one_iff h2] at ha2
  have : t = 0 := by
    have h3 : (2 : F) * t = 0 := by linear_combination ha2
    exact (mul_eq_zero.mp h3).resolve_left h2
  rw [this, unip_zero, map_one]

theorem borel_involution_cases (h2 : (2 : F) ≠ 0) {M : SL(2, F)}
    (hM10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (hM2 : mk M * mk M = 1) (hM1 : mk M ≠ 1) :
    (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 ∧
      (M : Matrix (Fin 2) (Fin 2) F) 1 1 = -(M : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have hdet := det_entries M
  rw [hM10, mul_zero, sub_zero] at hdet
  have hsq : M * M = 1 ∨ M * M = -1 := by
    rw [← map_mul] at hM2
    exact (mk_eq_one_iff _).mp hM2
  rcases hsq with h | h
  · exfalso
    apply hM1
    have e00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [mul_apply_SL, hM10, mul_zero, add_zero] at e00
    have e00' : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      simpa using e00
    have hx0 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hw : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = (M : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      apply mul_left_cancel₀ hx0
      rw [hdet, e00']
    have hin : mk M ∈ unipotent F := (mk_mem_unipotent_iff M).mpr ⟨hM10, hw⟩
    exact unipotent_involution_eq_one h2 hin hM2
  · have e00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [mul_apply_SL, hM10, mul_zero, add_zero, neg_apply_SL] at e00
    have e00' : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := by
      simpa using e00
    refine ⟨e00', ?_⟩
    have hx0 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    apply mul_left_cancel₀ hx0
    linear_combination hdet + e00'

theorem borel_klein (h2 : (2 : F) ≠ 0) {a b : PSL(2, F)} (ha : a ∈ borel F) (hb : b ∈ borel F)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) : b = 1 ∨ b = a := by
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  right
  obtain ⟨M, hM, rfl⟩ := ha
  obtain ⟨N, hN, rfl⟩ := hb
  have hM10 := (mem_borelSL_iff M).mp hM
  have hN10 := (mem_borelSL_iff N).mp hN
  obtain ⟨hMx, hMw⟩ := borel_involution_cases h2 hM10 ha2 ha1
  obtain ⟨hNx, hNw⟩ := borel_involution_cases h2 hN10 hb2 hb1
  have hdetM := det_entries M
  have hdetN := det_entries N
  rw [hM10, mul_zero, sub_zero] at hdetM
  rw [hN10, mul_zero, sub_zero] at hdetN
  have hx0 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdetM
  have hx0' : (N : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdetN
  rw [← map_mul, ← map_mul, mk_eq_mk_iff] at hab
  have hMN00 : ((M * N : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    simp [mul_apply_SL, hN10]
  have hNM00 : ((N * M : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (N : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    simp [mul_apply_SL, hM10]
  have hMN01 : ((M * N : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 0 1 +
        (M : Matrix (Fin 2) (Fin 2) F) 0 1 * (N : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simp [mul_apply_SL]
  have hNM01 : ((N * M : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (N : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 1 +
        (N : Matrix (Fin 2) (Fin 2) F) 0 1 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simp [mul_apply_SL]
  rcases hab with hab | hab
  ·
    have e01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hab
    rw [hNM01, hMN01, hMw, hNw] at e01
    have hxy : (N : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      have h3 : (2 : F) * ((N : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 1 -
          (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 0 1) = 0 := by
        linear_combination e01
      have := (mul_eq_zero.mp h3).resolve_left h2
      linear_combination this
    have hsq : (N : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = (M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 := by
      linear_combination hNx - hMx
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hxx | hxx
    · have hyy : (N : Matrix (Fin 2) (Fin 2) F) 0 1 = (M : Matrix (Fin 2) (Fin 2) F) 0 1 := by
        apply mul_left_cancel₀ hx0
        rw [← hxy, hxx]
      have hNM : N = M := by
        apply SL_ext
        · exact hxx
        · exact hyy
        · rw [hM10, hN10]
        · rw [hNw, hMw, hxx]
      rw [hNM]
    · have hyy : (N : Matrix (Fin 2) (Fin 2) F) 0 1 = -(M : Matrix (Fin 2) (Fin 2) F) 0 1 := by
        apply mul_left_cancel₀ hx0
        have : (N : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 1 =
            -((M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 1) := by
          rw [hxx]; ring
        rw [mul_neg, ← hxy, this]
      have hNM : N = -M := by
        apply SL_ext
        · rw [neg_apply_SL]; exact hxx
        · rw [neg_apply_SL]; exact hyy
        · rw [neg_apply_SL, hM10, hN10, neg_zero]
        · rw [neg_apply_SL, hNw, hMw, hxx]
      rw [hNM, mk_neg]
  ·
    have e00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hab
    simp only [neg_apply_SL] at e00
    rw [hNM00, hMN00] at e00
    have h3 : (2 : F) * ((M : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      linear_combination e00
    exact absurd ((mul_eq_zero.mp h3).resolve_left h2) (mul_ne_zero hx0 hx0')

theorem borel_no_simple_nonabelian (h2 : (2 : F) ≠ 0) {P : Subgroup PSL(2, F)} (hPB : P ≤ borel F)
    (hs : IsSimpleGroup ↥P) (hna : ∃ a b : P, a * b ≠ b * a) : False := by
  classical
  let N : Subgroup ↥P := (unipotent F).subgroupOf P
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : PSL(2, F)) ∈ unipotent F := hn
    have hgB : (g : PSL(2, F)) ∈ normalizer (unipotent F : Set PSL(2, F)) := by
      rw [L2Borel.normalizer_unipotent_eq h2]; exact hPB g.2
    have := (mem_normalizer_iff.mp hgB (n : PSL(2, F))).mp hn'
    exact this
  have := hN
  rcases hs.eq_bot_or_eq_top_of_normal N with hbot | htop
  · obtain ⟨a, b, hab⟩ := hna
    apply hab
    have hcomm : (a : PSL(2, F)) * b * (a : PSL(2, F))⁻¹ * (b : PSL(2, F))⁻¹ ∈ unipotent F :=
      borel_commutator_mem_unipotent (hPB a.2) (hPB b.2)
    have hmem : (a * b * a⁻¹ * b⁻¹ : P) ∈ N := hcomm
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := hmem
    calc a * b = a * b * a⁻¹ * b⁻¹ * b * a := by group
      _ = b * a := by rw [h1, one_mul]
  · obtain ⟨a, b, hab⟩ := hna
    apply hab
    have ha : (a : PSL(2, F)) ∈ unipotent F := by
      have : a ∈ N := by rw [htop]; exact Subgroup.mem_top a
      exact this
    have hb : (b : PSL(2, F)) ∈ unipotent F := by
      have : b ∈ N := by rw [htop]; exact Subgroup.mem_top b
      exact this
    exact Subtype.ext (unipotent_mul_comm ha hb)

theorem psl2_not_comm (h2 : (2 : F) ≠ 0) (h5 : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    ∃ g h : PSL(2, F), g * h ≠ h * g := by
  obtain ⟨a, ha0, ha2⟩ := h5
  refine ⟨mk (diag (Units.mk0 a ha0)), mk (unip 1), fun hcomm => ?_⟩
  have h1 : mk (diag (Units.mk0 a ha0)) * mk (unip 1) * (mk (diag (Units.mk0 a ha0)))⁻¹ = mk (unip 1) := by
    rw [hcomm]; group
  rw [← map_mul, ← map_inv, ← map_mul, diag_conj_unip, mk_unip_eq_mk_unip_iff h2] at h1
  simp only [Units.val_mk0, mul_one] at h1
  exact ha2 h1

theorem mem_borel_of_mem_normalizer (h2 : (2 : F) ≠ 0) {Y : Subgroup PSL(2, F)} (hYU : Y ≤ unipotent F)
    (hY1 : Y ≠ ⊥) {c : PSL(2, F)} (hc : c ∈ normalizer (Y : Set PSL(2, F))) : c ∈ borel F := by
  obtain ⟨y₁, hy₁Y, hy₁1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hY1 ((Subgroup.eq_bot_iff_forall Y).mpr hcon)
  have hmem : c * y₁ * c⁻¹ ∈ unipotent F := hYU ((mem_normalizer_iff.mp hc _).mp hy₁Y)
  exact (unipotent_conj_mem_iff h2 (hYU hy₁Y) hy₁1 c).mp hmem

end BorelFacts

theorem commutator_mem_of_index_le_two {G : Type} [Group G] [Finite G] (D : Subgroup G)
    (hD : D.index ≤ 2) (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ D := by
  have hpos : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h12 : D.index = 1 ∨ D.index = 2 := by omega
  rcases h12 with h | h
  · have : D = ⊤ := Subgroup.index_eq_one.mp h
    rw [this]; exact Subgroup.mem_top _
  · have h1 : ∀ x y : G, x * y ∈ D ↔ (x ∈ D ↔ y ∈ D) := fun x y => Subgroup.mul_mem_iff_of_index_two h
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ D ↔ (a * b ∈ D ↔ a⁻¹ * b⁻¹ ∈ D) := by
      rw [mul_assoc]; exact h1 _ _
    rw [h2, h1 a b, h1 a⁻¹ b⁻¹, inv_mem_iff, inv_mem_iff]


section CharPGL

theorem exists_sq_ne_one {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀) :
    ∃ a : F₀, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic F₀ˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F₀, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at h4
  omega

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem fl2_char_pgl (hF : L2Field F) (e : K ≃* L2 F) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F) (Y : Subgroup K) (hY : IsPGroup p ↥Y) (hY1 : Y ≠ ⊥) (G : Subgroup K)
    {F₀ : Type} [Field F₀] [Finite F₀] (h3 : 3 ≤ Nat.card F₀) (hodd₀ : Odd (Nat.card F₀))
    (eG : ↥G ≃* PGL2 F₀) (C : Subgroup K) (hidx : C.relIndex G ≤ 2)
    (hCN : ∀ c ∈ C, c ∈ normalizer (Y : Set K)) : False := by
  classical
  obtain ⟨n, ψ, hn, hYU⟩ := exists_std_position e hp hpF Y hY
  have hF2 := ringChar_ne_two_of_odd hF.1
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hY1' : Y.map ψ.toMonoidHom ≠ ⊥ := by
    intro h
    apply hY1
    exact (Subgroup.map_eq_bot_iff_of_injective Y (f := ψ.toMonoidHom) ψ.injective).mp h
  have hCB : ∀ c ∈ C, ψ c ∈ borel F := by
    intro c hc
    apply mem_borel_of_mem_normalizer h2 hYU hY1'
    rw [L2Borel.normalizer_map_equiv]
    exact ⟨c, hCN c hc, rfl⟩
  have hD : (C.subgroupOf G).index ≤ 2 := hidx
  have hcomm : ∀ x ∈ commutator ↥G, (x : K) ∈ C := by
    have hle : commutator ↥G ≤ C.subgroupOf G := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      exact commutator_mem_of_index_le_two (C.subgroupOf G) hD a b
    intro x hx
    exact hle hx
  let f : ↥(commutator ↥G) →* PSL(2, F) := ψ.toMonoidHom.comp (G.subtype.comp (commutator ↥G).subtype)
  have hfinj : Function.Injective f := ψ.injective.comp (G.subtype_injective.comp Subtype.val_injective)
  have hfB : ∀ x, f x ∈ borel F := fun x => hCB _ (hcomm x x.2)
  by_cases h4 : 4 ≤ Nat.card F₀
  · have hK₀ : IsOddPrimePower (Nat.card F₀) := isOddPrimePower_of_L2Field ⟨hodd₀, by omega⟩
    obtain ⟨eP⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three F₀ hK₀ (by omega) eG
    let Q : Subgroup PSL(2, F) := f.range
    have hQB : Q ≤ borel F := by
      rintro _ ⟨x, rfl⟩
      exact hfB x
    let eQ : ↥(commutator ↥G) ≃* Q := MonoidHom.ofInjective hfinj
    let eR : Q ≃* PSL2 F₀ := eQ.symm.trans eP
    have hsimple : IsSimpleGroup (PSL2 F₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    have hs : IsSimpleGroup ↥Q := eR.isSimpleGroup
    have hF₀2 : (2 : F₀) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd hodd₀)
    obtain ⟨g, h, hgh⟩ := psl2_not_comm hF₀2 (exists_sq_ne_one h4)
    refine borel_no_simple_nonabelian h2 hQB hs ⟨eR.symm g, eR.symm h, fun hc => hgh ?_⟩
    have := congrArg eR hc
    simpa using this
  · have h3' : Nat.card F₀ = 3 := by omega
    obtain ⟨eS⟩ := CFSG.GH74.GLS.IVK.Proofs2.exists_pgl2_equiv_perm h3'
    obtain ⟨eA⟩ := commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four (eG.trans eS)
    have hmemA : Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 4) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    have hmemB : Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3 ∈ alternatingGroup (Fin 4) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    let a₀ : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, hmemA⟩
    let b₀ : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, hmemB⟩
    have pa : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 2 3) = 1 := by decide
    have pb : (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) * (Equiv.swap 0 2 * Equiv.swap 1 3) = 1 := by decide
    have pab : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) * (Equiv.swap 0 2 * Equiv.swap 1 3) =
        (Equiv.swap 0 2 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 2 3) := by decide
    have pa1 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) ≠ 1 := by decide
    have pb1 : (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) ≠ 1 := by decide
    have pne : (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) ≠ (Equiv.swap 0 1 * Equiv.swap 2 3) := by decide
    have ha₀ : a₀ * a₀ = 1 := Subtype.ext pa
    have hb₀ : b₀ * b₀ = 1 := Subtype.ext pb
    have hab₀ : a₀ * b₀ = b₀ * a₀ := Subtype.ext pab
    have ha₀1 : a₀ ≠ 1 := fun h => pa1 (congrArg Subtype.val h)
    have hba₀ : b₀ ≠ 1 := fun h => pb1 (congrArg Subtype.val h)
    have hne₀ : b₀ ≠ a₀ := fun h => pne (congrArg Subtype.val h)
    set x₀ := eA.symm a₀ with hx₀
    set y₀ := eA.symm b₀ with hy₀
    have hxx : f x₀ * f x₀ = 1 := by
      rw [← map_mul, hx₀, ← map_mul, ha₀, map_one, map_one]
    have hyy : f y₀ * f y₀ = 1 := by
      rw [← map_mul, hy₀, ← map_mul, hb₀, map_one, map_one]
    have hxy : f x₀ * f y₀ = f y₀ * f x₀ := by
      rw [← map_mul, ← map_mul, hx₀, hy₀, ← map_mul, ← map_mul, hab₀]
    have hx1 : f x₀ ≠ 1 := by
      intro h
      apply ha₀1
      have := hfinj (h.trans (map_one f).symm)
      rw [hx₀] at this
      simpa using this
    have hyne : f y₀ ≠ 1 ∧ f y₀ ≠ f x₀ := by
      constructor
      · intro h
        apply hba₀
        have := hfinj (h.trans (map_one f).symm)
        rw [hy₀] at this
        simpa using this
      · intro h
        apply hne₀
        have := hfinj h
        rw [hx₀, hy₀] at this
        simpa using this
    rcases borel_klein h2 (hfB x₀) (hfB y₀) hxx hyy hxy hx1 with h | h
    · exact hyne.1 h
    · exact hyne.2 h

end CharPGL

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
