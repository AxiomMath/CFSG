module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Plane
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Main
public import CFSG.CGT.Timmesfeld75.ListWCSzU3

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open scoped MatrixGroups Pointwise

section Generic

variable {Λ : Type} [Group Λ]

@[expose] def cenS (S : Sylow 2 Λ) : Subgroup Λ :=
  (Subgroup.center ↥(S : Subgroup Λ)).map (S : Subgroup Λ).subtype

theorem mem_cenS {S : Sylow 2 Λ} {x : Λ} :
    x ∈ cenS S ↔ x ∈ (S : Subgroup Λ) ∧ ∀ y ∈ (S : Subgroup Λ), x * y = y * x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hxS, hx⟩
    refine ⟨⟨x, hxS⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext (hx y y.2).symm

theorem mem_smul_sylow {S : Sylow 2 Λ} {k x : Λ} :
    x ∈ ((k • S : Sylow 2 Λ) : Subgroup Λ) ↔ k⁻¹ * x * k ∈ (S : Subgroup Λ) := by
  show x ∈ MulAut.conj k • (S : Subgroup Λ) ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem exists_conj_cenS [Finite Λ] (S S₀ : Sylow 2 Λ) :
    ∃ k : Λ, cenS S = CFSG.CGT.Timmesfeld75.conjSubgroup k (cenS S₀) := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq Λ S₀ S
  refine ⟨k, ?_⟩
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, mem_cenS, mem_cenS]
  have hS : ∀ z, z ∈ (S : Subgroup Λ) ↔ k⁻¹ * z * k ∈ (S₀ : Subgroup Λ) := by
    intro z
    rw [← hk, mem_smul_sylow]
  constructor
  · rintro ⟨hxS, hx⟩
    refine ⟨(hS x).mp hxS, fun y hy => ?_⟩
    have hyS : k * y * k⁻¹ ∈ (S : Subgroup Λ) := by
      rw [hS]
      simpa [mul_assoc] using hy
    have := hx _ hyS
    calc k⁻¹ * x * k * y = k⁻¹ * (x * (k * y * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * y * k⁻¹) * x) * k := by rw [this]
      _ = y * (k⁻¹ * x * k) := by group
  · rintro ⟨hxS, hx⟩
    refine ⟨(hS x).mpr hxS, fun y hy => ?_⟩
    have hyS : k⁻¹ * y * k ∈ (S₀ : Subgroup Λ) := (hS y).mp hy
    have := hx _ hyS
    calc x * y = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by rw [this]
      _ = y * x := by group

end Generic

section Transport

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup ConjTwoTransitive conjSubgroup_conjSubgroup
  conjSubgroup_one conjSubgroup_sup_eq_sup)

variable {Λ Λ' : Type} [Group Λ] [Group Λ'] (φ : Λ ≃* Λ')

theorem map_conjSubgroup_equiv (a : Λ) (T : Subgroup Λ) :
    (conjSubgroup a T).map φ.toMonoidHom = conjSubgroup (φ a) (T.map φ.toMonoidHom) :=
  CFSG.CGT.Timmesfeld75.map_conjSubgroup φ.toMonoidHom a T

theorem exists_cenS_map_equiv [Finite Λ] (S : Sylow 2 Λ) :
    ∃ S' : Sylow 2 Λ', (cenS S).map φ.toMonoidHom = cenS S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective φ.toMonoidHom := φ.surjective
  refine ⟨Sylow.mapSurjective hf S, ?_⟩
  have hS' : ((Sylow.mapSurjective hf S : Sylow 2 Λ') : Subgroup Λ') =
      (S : Subgroup Λ).map φ.toMonoidHom := Sylow.coe_mapSurjective hf S
  ext x'
  obtain ⟨x, rfl⟩ := φ.surjective x'
  rw [CFSG.CGT.Timmesfeld75.mem_map_mulEquiv_iff φ, mem_cenS, mem_cenS, hS']
  constructor
  · rintro ⟨hxS, hx⟩
    refine ⟨Subgroup.mem_map_of_mem _ hxS, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := congrArg φ (hx y hy)
    rw [map_mul, map_mul] at this
    exact this
  · rintro ⟨hxS, hx⟩
    refine ⟨(Subgroup.mem_map_iff_mem φ.injective).mp hxS, fun y hy => ?_⟩
    apply φ.injective
    rw [map_mul, map_mul]
    exact hx (φ y) (Subgroup.mem_map_of_mem φ.toMonoidHom hy)

theorem conjTwoTransitive_map_equiv (T : Subgroup Λ) (h2 : ConjTwoTransitive Λ T) :
    ConjTwoTransitive Λ' (T.map φ.toMonoidHom) := by
  intro a b c d hab hcd
  obtain ⟨a, rfl⟩ := φ.surjective a
  obtain ⟨b, rfl⟩ := φ.surjective b
  obtain ⟨c, rfl⟩ := φ.surjective c
  obtain ⟨d, rfl⟩ := φ.surjective d
  rw [← map_conjSubgroup_equiv, ← map_conjSubgroup_equiv] at hab hcd
  have hab' : conjSubgroup a T ≠ conjSubgroup b T := fun e => hab (by rw [e])
  have hcd' : conjSubgroup c T ≠ conjSubgroup d T := fun e => hcd (by rw [e])
  obtain ⟨x, hx1, hx2⟩ := h2 a b c d hab' hcd'
  refine ⟨φ x, ?_, ?_⟩
  · rw [← map_mul, ← map_conjSubgroup_equiv, hx1, map_conjSubgroup_equiv]
  · rw [← map_mul, ← map_conjSubgroup_equiv, hx2, map_conjSubgroup_equiv]

theorem U3FrameConcl.of_equiv (s : ℕ) (T : Subgroup Λ) (g : Λ)
    (H : U3FrameConcl s Λ' (T.map φ.toMonoidHom) (φ g)) : U3FrameConcl s Λ T g := by
  obtain ⟨k₁, k₃, d, y, y₃, hy, hy₃, hy1, hy₃1, hyr, hy₃r, hdc₃, hdc₁, hyc₃⟩ := H
  have hL : (T ⊔ conjSubgroup g T).map φ.toMonoidHom =
      T.map φ.toMonoidHom ⊔ conjSubgroup (φ g) (T.map φ.toMonoidHom) := by
    rw [Subgroup.map_sup, map_conjSubgroup_equiv]
  have hmem : ∀ (k : Λ') (z : Λ), z ∈ conjSubgroup (φ.symm k) (T ⊔ conjSubgroup g T) ↔
      φ z ∈ conjSubgroup k (T.map φ.toMonoidHom ⊔ conjSubgroup (φ g) (T.map φ.toMonoidHom)) := by
    intro k z
    rw [mem_conjSubgroup, mem_conjSubgroup, ← hL]
    have : φ ((φ.symm k)⁻¹ * z * φ.symm k) = k⁻¹ * φ z * k := by simp [map_mul, map_inv]
    rw [← this]
    exact (CFSG.CGT.Timmesfeld75.mem_map_mulEquiv_iff φ).symm
  refine ⟨φ.symm k₁, φ.symm k₃, φ.symm d, φ.symm y, φ.symm y₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem]
    simpa using hy
  · rw [hmem]
    simpa using hy₃
  · exact fun e => hy1 (by simpa using congrArg φ e)
  · exact fun e => hy₃1 (by simpa using congrArg φ e)
  · rw [← map_pow, hyr, map_one]
  · rw [← map_pow, hy₃r, map_one]
  · intro x hx
    rw [hmem] at hx
    apply φ.injective
    simpa using hdc₃ (φ x) hx
  · intro x hx
    rw [hmem] at hx
    apply φ.injective
    simpa using hdc₁ (φ x) hx
  · intro x hx
    rw [hmem] at hx
    apply φ.injective
    simpa using hyc₃ (φ x) hx

end Transport

section Kappa

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

theorem exists_kappa (hs : 2 ≤ s) : ∃ κ : F, NO h κ ∧ κ ^ (2 ^ s + 1) = 1 ∧ κ ^ 6 ≠ 1 := by
  classical
  have hfin := h.finite
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = (2 ^ s) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card, ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (2 ^ s) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      hcard]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ s := ⟨_, rfl⟩
  rw [← hq] at hord ⊢
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hqeven : 2 ∣ q := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), show 1 ≤ q by omega]
    ring
  have hdvd : q - 1 ∣ orderOf g := by
    rw [hord, hsq]
    exact dvd_mul_right _ _
  have hordκ : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hsq]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hκq : (((g ^ (q - 1) : Fˣ) : F)) ^ (q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hordκ, pow_orderOf_eq_one, Units.val_one]
  refine ⟨((g ^ (q - 1) : Fˣ) : F), ?_, hκq, ?_⟩
  · unfold NO
    rw [h.bar_apply, ← hq, ← pow_succ]
    exact hκq
  · intro h6
    have : (g ^ (q - 1)) ^ 6 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, h6, Units.val_one]
    have hd := orderOf_dvd_of_pow_eq_one this
    rw [hordκ] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hq4' : q = 4 := by omega
    rw [hq4'] at hd
    norm_num at hd

theorem stated_model_pu (hs : 2 ≤ s) :
    StatedClassicalModel (unitaryPSU h 3) StatedLieTag.PSU 3 2 s := by
  have hfin := h.finite
  refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_⟩, F, inferInstance, hfin, ?_,
    ⟨unitaryPSUEquiv h (by norm_num)⟩⟩
  · intro hh
    have h2 : 2 ^ s = 2 := (Prod.mk.inj hh).2
    have : s = 1 := Nat.pow_right_injective le_rfl (by simpa using h2)
    omega
  · rw [h.card, ← pow_mul, mul_comm]

theorem dg_mulVec_a₀ {κ : F} (hκ : NO h κ) :
    (((dg h hκ 0 1 (-1) (by norm_num) : unitarySU 2 s F 3) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ (a₀ : Fin 3 → F) = b₀ κ := by
  rw [coe_dg]
  funext i
  fin_cases i <;> simp [a₀, b₀, Matrix.mulVec_diagonal]

theorem conj_T0_eq {κ : F} (hκ : NO h κ) :
    CFSG.CGT.Timmesfeld75.conjSubgroup
      (unitaryProj h 3 (dg h hκ 0 1 (-1) (by norm_num))) (T0 h) =
      (TGsub h (b₀ κ) (sqNorm3_b₀ h hκ)).map (unitaryProj h 3) := by
  unfold T0
  rw [← CFSG.CGT.Timmesfeld75.map_conjSubgroup, conjSubgroup_TGsub]
  congr 1
  simp only [dg_mulVec_a₀ h hκ]

end Kappa

section FrameG

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F) {κ : F} (hκ : NO h κ)

theorem dg_congr {a b c a' b' c' : ℤ} {hs : a + b + c = 0} {hs' : a' + b' + c' = 0} (ha : a = a')
    (hb : b = b') (hc : c = c') : dg h hκ a b c hs = dg h hκ a' b' c' hs' := by
  subst ha hb hc
  rfl

theorem frame_B (σ : unitarySU 2 s F 3) (hσ : σ ∈ Sig01 h) :
    (dg h hκ (-4) (-4) 8 (by norm_num) * (dg h hκ 0 (-6) 6 (by norm_num))⁻¹) *
        (PG h * σ * (PG h)⁻¹) =
      (PG h * σ * (PG h)⁻¹) *
        (dg h hκ (-4) (-4) 8 (by norm_num) * (dg h hκ 0 (-6) 6 (by norm_num))⁻¹) := by
  set D := dg h hκ (-4) (-4) 8 (by norm_num) with hD
  set Y := dg h hκ 0 (-6) 6 (by norm_num) with hY
  have hE : (PG h)⁻¹ * (D * Y⁻¹) * PG h = dg h hκ 2 2 (-4) (by norm_num) := by
    calc (PG h)⁻¹ * (D * Y⁻¹) * PG h = ((PG h)⁻¹ * D * PG h) * ((PG h)⁻¹ * Y * PG h)⁻¹ := by group
      _ = dg h hκ (-4) 8 (-4) (by norm_num) * (dg h hκ (-6) 6 0 (by norm_num))⁻¹ := by
          rw [hD, hY, PG_inv_dg_PG, PG_inv_dg_PG]
      _ = dg h hκ (-4) 8 (-4) (by norm_num) * dg h hκ 6 (-6) 0 (by norm_num) := by
          rw [dg_inv]
          congr 1
      _ = dg h hκ 2 2 (-4) (by norm_num) := by
          rw [dg_mul]
          exact dg_congr h hκ (by norm_num) (by norm_num) (by norm_num)
  have hcomm := dg_comm_Sig01 h hκ 2 (-4) (by norm_num) σ hσ
  have hDY : D * Y⁻¹ = PG h * dg h hκ 2 2 (-4) (by norm_num) * (PG h)⁻¹ := by
    rw [← hE]
    group
  rw [hDY]
  calc PG h * dg h hκ 2 2 (-4) (by norm_num) * (PG h)⁻¹ * (PG h * σ * (PG h)⁻¹)
      = PG h * (dg h hκ 2 2 (-4) (by norm_num) * σ) * (PG h)⁻¹ := by group
    _ = PG h * (σ * dg h hκ 2 2 (-4) (by norm_num)) * (PG h)⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem frame_C (σ : unitarySU 2 s F 3) (hσ : σ ∈ Sig01 h) :
    (dg h hκ 0 (-6) 6 (by norm_num) * (dg h hκ 3 (-3) 0 (by norm_num))⁻¹) * σ =
      σ * (dg h hκ 0 (-6) 6 (by norm_num) * (dg h hκ 3 (-3) 0 (by norm_num))⁻¹) := by
  have e : dg h hκ 0 (-6) 6 (by norm_num) * (dg h hκ 3 (-3) 0 (by norm_num))⁻¹ =
      dg h hκ (-3) (-3) 6 (by norm_num) := by
    rw [dg_inv, dg_mul]
    exact dg_congr h hκ (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  exact dg_comm_Sig01 h hκ (-3) 6 (by norm_num) σ hσ

theorem dg_mem_Sig01' (a b : ℤ) (hab : a + b = 0) :
    dg h hκ a b 0 (by omega) ∈ Sig01 h := by
  have := dg_mem_Sig01 h hκ a
  have e : b = -a := by omega
  subst e
  exact this

end FrameG

section PuFrame

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup ConjTwoTransitive conjSubgroup_conjSubgroup
  conjSubgroup_one conjSubgroup_sup_eq_sup)

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

theorem frame_pu (hs : 2 ≤ s)
    (T : Subgroup (unitaryPSU h 3)) (hT : ∃ S : Sylow 2 (unitaryPSU h 3), T = cenS S)
    (h2 : ConjTwoTransitive (unitaryPSU h 3) T)
    (g : unitaryPSU h 3) (hne : conjSubgroup g T ≠ T)
    (hcard : Nat.card ↥(T ⊔ conjSubgroup g T) = 2 ^ s * ((2 ^ s) ^ 2 - 1)) :
    U3FrameConcl s (unitaryPSU h 3) T g := by
  classical
  have hfin := h.finite
  have hmodel := stated_model_pu h hs
  obtain ⟨⟨-, ⟨S₀, hS₀⟩, -⟩, -⟩ := CFSG.CGT.Timmesfeld75.psu3_wc hs hmodel (T0_isWC h) (T0_ne_bot h)
  obtain ⟨S, hS⟩ := hT
  obtain ⟨k, hk⟩ := exists_conj_cenS S S₀
  have hcen₀ : T0 h = cenS S₀ := hS₀
  have hTk : T = conjSubgroup k (T0 h) := by rw [hS, hk, hcen₀]
  obtain ⟨κ, hκ, hκq, hκ6⟩ := exists_kappa h hs
  have hκ1 : κ ≠ 1 := fun e => hκ6 (by rw [e, one_pow])
  set π := unitaryProj h 3 with hπ
  set w := dg h hκ 0 1 (-1) (by norm_num) with hw
  have hT1 := conj_T0_eq h hκ
  have hne10 : conjSubgroup (π w) (T0 h) ≠ T0 h := by
    rw [hT1]
    exact map_TGsub_b₀_ne h hκ hκ1
  have hA : conjSubgroup 1 T ≠ conjSubgroup g T := by
    rw [conjSubgroup_one]
    exact hne.symm
  have e1 : conjSubgroup k⁻¹ T = T0 h := by
    rw [hTk, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have e2 : conjSubgroup (π w * k⁻¹) T = conjSubgroup (π w) (T0 h) := by
    rw [hTk, conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one]
  have hB : conjSubgroup k⁻¹ T ≠ conjSubgroup (π w * k⁻¹) T := by
    rw [e1, e2]
    exact hne10.symm
  obtain ⟨x, hx1, hx2⟩ := h2 1 g k⁻¹ (π w * k⁻¹) hA hB
  have hxT : conjSubgroup x T = T0 h := by
    rw [mul_one, e1] at hx1
    exact hx1
  have hxgT : conjSubgroup (x * g) T = conjSubgroup (π w) (T0 h) := by
    rw [← e2]
    exact hx2
  have hL : conjSubgroup x (T ⊔ conjSubgroup g T) = T0 h ⊔ conjSubgroup (π w) (T0 h) := by
    rw [conjSubgroup_sup_eq_sup, hxT, conjSubgroup_conjSubgroup, hxgT]
  have hle : T0 h ⊔ conjSubgroup (π w) (T0 h) ≤ (Sig01 h).map π := by
    refine sup_le (Subgroup.map_mono (TGsub_le_Sig01 h _ _ (by simp [a₀]))) ?_
    rw [hT1]
    exact Subgroup.map_mono (TGsub_le_Sig01 h _ _ (by simp [b₀]))
  have hcardL : Nat.card ↥(conjSubgroup x (T ⊔ conjSubgroup g T)) =
      2 ^ s * ((2 ^ s) ^ 2 - 1) := by
    unfold conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hcard
  have hΛ : conjSubgroup x (T ⊔ conjSubgroup g T) = (Sig01 h).map π := by
    rw [hL]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_map_Sig01 h, ← hL, hcardL]
  have hΛ' : conjSubgroup (π (PG h) * x) (T ⊔ conjSubgroup g T) =
      conjSubgroup (π (PG h)) ((Sig01 h).map π) := by
    rw [← conjSubgroup_conjSubgroup, hΛ]
  have h0 := hκ.ne_zero
  have hneg6 : κ ^ (0 : ℤ) ≠ κ ^ (-6 : ℤ) := by
    intro e
    apply hκ6
    rw [zpow_zero] at e
    have h6 : (κ ^ (6 : ℤ))⁻¹ = 1 := by rw [← _root_.zpow_neg]; exact e.symm
    simpa using inv_eq_one.mp h6
  have hne33 : κ ^ (3 : ℤ) ≠ κ ^ (-3 : ℤ) := by
    intro e
    apply hκ6
    have h6 : κ ^ (6 : ℤ) = κ ^ (3 : ℤ) * κ ^ (3 : ℤ) := by
      rw [← zpow_add₀ h0]
      norm_num
    have h6' : κ ^ (6 : ℤ) = 1 := by
      rw [h6]
      nth_rewrite 2 [e]
      rw [← zpow_add₀ h0]
      norm_num
    simpa using h6'
  have hker : ∀ z : unitarySU 2 s F 3, z ∉ unitaryScalars h 3 → π z ≠ 1 := by
    intro z hz e
    apply hz
    rw [← ker_unitaryProj, MonoidHom.mem_ker]
    exact e
  refine ⟨π (PG h) * x, x, π (dg h hκ (-4) (-4) 8 (by norm_num)),
    π (dg h hκ 0 (-6) 6 (by norm_num)), π (dg h hκ 3 (-3) 0 (by norm_num)), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  ·
    rw [hΛ', mem_conjSubgroup]
    refine ⟨(PG h)⁻¹ * dg h hκ 0 (-6) 6 (by norm_num) * PG h, ?_, ?_⟩
    · rw [PG_inv_dg_PG]
      exact dg_mem_Sig01' h hκ (-6) 6 (by norm_num)
    · simp only [map_mul, map_inv]
  ·
    rw [hΛ]
    exact ⟨_, dg_mem_Sig01' h hκ 3 (-3) (by norm_num), rfl⟩
  · exact hker _ (dg_not_mem_scalars h hκ 0 (-6) 6 (by norm_num) hneg6)
  · exact hker _ (dg_not_mem_scalars h hκ 3 (-3) 0 (by norm_num) hne33)
  · rw [← map_pow, dg_pow_orderdvd h hκ (2 ^ s + 1) hκq, map_one]
  · rw [← map_pow, dg_pow_orderdvd h hκ (2 ^ s + 1) hκq, map_one]
  · rw [hΛ]
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_mul, ← map_mul, dg_comm_Sig01 h hκ (-4) 8 (by norm_num) σ hσ]
  · rw [hΛ']
    intro z hz
    rw [mem_conjSubgroup] at hz
    obtain ⟨σ, hσ, hσz⟩ := hz
    have hz' : z = π (PG h * σ * (PG h)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hσz]
      group
    have := congrArg π (frame_B h hκ σ hσ)
    rw [hz']
    simpa only [map_mul, map_inv] using this
  · rw [hΛ]
    rintro _ ⟨σ, hσ, rfl⟩
    have := congrArg π (frame_C h hκ σ hσ)
    simpa only [map_mul, map_inv] using this

end PuFrame

section Final

open CFSG.CGT.Timmesfeld75 (conjSubgroup)

theorem u3Frame : U3Frame := by
  intro s hs Λ _ _ hmodel T hT h2 g hne hcard
  obtain ⟨-, F, _, hFfin, hFcard, ⟨e₀⟩⟩ := hmodel
  have h : UnitaryFieldData 2 s F :=
    ⟨Nat.prime_two, by omega, by rw [hFcard, ← pow_mul, mul_comm]⟩
  let e : Λ ≃* unitaryPSU h 3 := e₀.trans (unitaryPSUEquiv h (by norm_num)).symm
  obtain ⟨S, hS⟩ := hT
  obtain ⟨S', hS'⟩ := exists_cenS_map_equiv e S
  have hT' : T.map e.toMonoidHom = cenS S' := by rw [hS]; exact hS'
  have hL : (T ⊔ conjSubgroup g T).map e.toMonoidHom =
      T.map e.toMonoidHom ⊔ conjSubgroup (e g) (T.map e.toMonoidHom) := by
    rw [Subgroup.map_sup, map_conjSubgroup_equiv]
  have hne' : conjSubgroup (e g) (T.map e.toMonoidHom) ≠ T.map e.toMonoidHom := by
    intro heq
    apply hne
    have hinj : Function.Injective e.toMonoidHom := e.injective
    apply Subgroup.map_injective hinj
    rw [map_conjSubgroup_equiv]
    exact heq
  have hcard' : Nat.card ↥(T.map e.toMonoidHom ⊔ conjSubgroup (e g) (T.map e.toMonoidHom)) =
      2 ^ s * ((2 ^ s) ^ 2 - 1) := by
    have hinj : Function.Injective e.toMonoidHom := e.injective
    rw [← hL, Subgroup.card_map_of_injective hinj]
    exact hcard
  exact U3FrameConcl.of_equiv e s T g
    (frame_pu h hs (T.map e.toMonoidHom) ⟨S', hT'⟩ (conjTwoTransitive_map_equiv e T h2) (e g) hne'
      hcard')

end Final

end CFSG.CGT.PushingUpLit.CGT6
